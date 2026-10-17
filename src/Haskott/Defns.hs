{-# LANGUAGE OverloadedStrings #-}

-- | Processing the definitions: Ott's @defns.ml@ up to the point where the
-- rules are symbolic terms. Each rule's premises and conclusion are parsed
-- against the term grammar, the conclusion restricted to the judgement
-- being defined; premises may be named (@[[:name]]@) or be embedded prover
-- code with quoted terms; lineless blocks become rules without premises;
-- function clauses split into a left-hand side and a right-hand side.
-- Every problem is a diagnostic and processing continues, as in Ott.
module Haskott.Defns
  ( Drule (..)
  , RuleItem (..)
  , ProcessedDefn (..)
  , ProcessedClass (..)
  , Funclause (..)
  , ProcessedFun (..)
  , ProcessedFunClass (..)
  , Processed (..)
  , processDefns
  ) where

import Control.Monad (forM, unless)
import Control.Monad.Trans.Writer.Strict (Writer, runWriter, tell)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Graft.Range (TextRange)
import qualified Haskott.Raw as R
import Haskott.Spec
import Haskott.Term.Parse
import Haskott.Term.Requests (embeddedQuotations, ruleNameParse)
import Haskott.Term.Symterm

data Drule = Drule
  { druleName :: Text
  , druleCategories :: Set.Set Text
  , drulePremises :: [(Maybe Text, Symterm)]
  -- ^ each with its name, when the premise ends with @[[:name]]@
  , druleConclusion :: Symterm
  , druleHoms :: [Hom]
  , druleRange :: TextRange
  }
  deriving (Eq, Show)

data RuleItem
  = ItemRule Drule
  | ItemComment [EmbedEl]
  deriving (Eq, Show)

data ProcessedDefn = ProcessedDefn
  { pdName :: Text
  , pdForm :: Symterm
  -- ^ the canonical term of the definition's production
  , pdWrapper :: Text
  , pdRules :: [RuleItem]
  , pdHoms :: [Hom]
  }
  deriving (Eq, Show)

data ProcessedClass = ProcessedClass
  { pcName :: Text
  , pcWrapper :: Text
  , pcDefns :: [ProcessedDefn]
  }
  deriving (Eq, Show)

data Funclause = Funclause
  { fcLhs :: Symterm
  , fcRhs :: Symterm
  , fcRange :: TextRange
  }
  deriving (Eq, Show)

data ProcessedFun = ProcessedFun
  { pfName :: Text
  , pfClauses :: [Funclause]
  }
  deriving (Eq, Show)

data ProcessedFunClass = ProcessedFunClass
  { pfcName :: Text
  , pfcFuns :: [ProcessedFun]
  }
  deriving (Eq, Show)

data Processed = Processed
  { processedClasses :: [ProcessedClass]
  , processedFunClasses :: [ProcessedFunClass]
  }
  deriving (Eq, Show)

type P = Writer [Diagnostic]

report :: TextRange -> Text -> P ()
report r m = tell [Diagnostic r m]

-- | Process every definition and function class. With @picky@, several
-- parses of a term are an error; otherwise the first is taken, as Ott
-- does when no output target is requested.
processDefns :: Bool -> TermParser -> Spec -> (Processed, [Diagnostic])
processDefns picky tp spec = runWriter $ do
  classes <- forM (specDefnClasses spec) $ \dc -> do
    defns <- forM (dcDefns dc) (processDefn picky tp dc)
    pure (ProcessedClass (dcName dc) (dcWrapper dc) defns)
  funs <- forM (specFunClasses spec) $ \fc -> do
    fs <- forM (fcDefns fc) $ \fd -> do
      clauses <- forM (fdClauses fd) (processClause picky tp fc fd)
      pure (ProcessedFun (fdName fd) (mapMaybe id clauses))
    pure (ProcessedFunClass (fcName fc) fs)
  pure (Processed classes funs)

processDefn :: Bool -> TermParser -> DefnClass -> Defn -> P ProcessedDefn
processDefn picky tp dc d = do
  let prodName' = dcWrapper dc <> dName d
  rules <- forM (dBody d) (processRule picky tp dc d prodName')
  pure
    ProcessedDefn
      { pdName = dName d
      , pdForm = StNode (dcName dc) prodName' (canonicalElements (dElements d))
      , pdWrapper = dWrapper d
      , pdRules = mapMaybe id rules
      , pdHoms = dHoms d
      }

-- | The canonical symbolic term of a production: each element as itself.
canonicalElements :: [Element] -> [Ste]
canonicalElements = mapMaybe el
  where
    el e = case e of
      Nonterm p n suff -> Just (SteSt (StNonterm p (n, suff)))
      Metavar p m suff -> Just (SteMetavar p (m, suff))
      Terminal _ -> Nothing
      ListForm lb -> Just (SteList [StliListform b (canonicalElements (lbElements lb)) | Just b <- [lbBound lb]])

processRule :: Bool -> TermParser -> DefnClass -> Defn -> Text -> SemirawRule -> P (Maybe RuleItem)
processRule picky tp dc d prodName' sr = case sr of
  LinedRule premises _ annot conclusions range -> do
    ps <- forM premises (premise range)
    conclusion <- case conclusions of
      [] -> do
        report range "rule with no conclusion"
        pure (StUninterpreted "no conclusion")
      [c] -> parseWith (defnTransform prodName') "formula" c range
      _ -> do
        report range "rule with multiple conclusions"
        pure (StUninterpreted "multiple conclusions")
    homs <- forM (raHoms annot) (druleHom range)
    pure . Just . ItemRule $
      Drule
        { druleName = dcWrapper dc <> dWrapper d <> raName annot
        , druleCategories = Set.fromList (raCategories annot)
        , drulePremises = ps
        , druleConclusion = conclusion
        , druleHoms = homs
        , druleRange = range
        }
  LinelessRule ls range
    | null ls -> pure Nothing
    | otherwise -> do
        -- Ott's test-harness hack: a block of lines with no dashed line is
        -- a rule with no premises, named fake, in category F
        st <- parseWith userSyntaxTransform "formula" (T.intercalate " " ls) range
        pure . Just . ItemRule $ Drule "fake" (Set.singleton "F") [] st [] range
  DefnComRule es _ -> pure (Just (ItemComment es))
  where
    parseWith transform root s range = case justOneParse picky transform tp root False s of
      Parsed p -> pure (parseTerm p)
      NoParses -> do
        report range ("no parses of \"" <> s <> "\"")
        pure (StUninterpreted ("no parses of " <> s))
      MultipleParses ps -> do
        report range ("multiple parses of \"" <> s <> "\":\n" <> T.unlines (map (ppPlainSymterm . parseTerm) ps))
        pure (StUninterpreted "multiple parses")
    premise range s = do
      let (s', name) = ruleNameParse s
      st <- case embeddedQuotations s' of
        Just qs -> do
          -- embedded prover code: each quotation is a term of user syntax,
          -- and the code with -ARG- in their place names the node
          terms <- forM qs $ \q -> parseWith userSyntaxTransform "user_syntax" q range
          pure (StNode "fancy_formula" (embeddingString s') (map SteSt terms))
        Nothing -> parseWith userSyntaxTransform "formula" s' range
      pure (name, st)
    -- a rule's homs are checked with no elements in scope: references
    -- become terminals (Ott's cd_hom Hu_drule)
    druleHom range h = do
      let hn = R.homName h
      unless (hn == "com") $
        report range ("illegal hom \"" <> hn <> "\" for definition rule  (the allowable homs here are com)")
      pure (hn, agglomerate (map homEl (stripBlanks (R.homSpec h))))
    homEl el = case el of
      R.HomString t -> HomString t
      R.HomBlanks t -> HomString t
      R.HomIdent ris -> HomTerminal (lastIdent ris)
      R.HomIdentDots ris n ris' -> HomTerminal (T.concat ris <> T.replicate (n + 2) "." <> T.concat ris')
      R.HomIdentComp ris _ -> HomTerminal (T.concat ris)
    lastIdent ris = case reverse (filter (not . T.all (`elem` (" \t\f" :: String))) ris) of
      (i : _) -> i
      [] -> ""
    stripBlanks = reverse . dropWhile isBlanks . reverse . dropWhile isBlanks
    isBlanks el = case el of
      R.HomBlanks _ -> True
      _ -> False
    agglomerate xs = case xs of
      HomString a : HomString b : more -> agglomerate (HomString (a <> b) : more)
      x : more -> x : agglomerate more
      [] -> []

-- | The text of an embedded premise with each @[[ ... ]]@ replaced by
-- @-ARG-@, as Ott names the resulting node.
embeddingString :: Text -> Text
embeddingString s =
  let inner = maybe s id (T.stripPrefix "{{" (T.strip s) >>= T.stripSuffix "}}")
   in go inner
  where
    go t = case T.breakOn "[[" t of
      (before, rest)
        | T.null rest -> before
        | otherwise ->
            let (_, after) = T.breakOn "]]" (T.drop 2 rest)
             in before <> "-ARG-" <> go (T.drop 2 after)

processClause :: Bool -> TermParser -> FunClass -> FunDefn -> Text -> P (Maybe Funclause)
processClause picky tp fc fd s = case mapOutcome parseTerm (justOneParse picky userSyntaxTransform tp (fcName fc) False s) of
  POut (StNode _ _ es) | not (null es) ->
    case (init es, last es) of
      (lhsEs, SteSt rhs) ->
        pure (Just (Funclause (StNode (fdResult fd) (fdResultPrefix fd <> fdName fd) lhsEs) rhs (fdRange fd)))
      _ -> do
        report (fdRange fd) ("function clause \"" <> s <> "\" has no right-hand side")
        pure Nothing
  POut _ -> do
    report (fdRange fd) ("function clause \"" <> s <> "\" lost")
    pure Nothing
  NOut -> do
    report (fdRange fd) ("no parses of \"" <> s <> "\"")
    pure Nothing
  MOut sts -> do
    report (fdRange fd) ("multiple parses of \"" <> s <> "\":\n" <> T.unlines (map ppPlainSymterm sts))
    pure Nothing

-- | An outcome over symbolic terms.
data Out a = POut a | NOut | MOut [a]

mapOutcome :: (Parse -> a) -> Outcome -> Out a
mapOutcome f o = case o of
  Parsed p -> POut (f p)
  NoParses -> NOut
  MultipleParses ps -> MOut (map f ps)
