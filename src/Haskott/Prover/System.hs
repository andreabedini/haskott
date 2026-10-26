{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @system_pp.ml@ for the provers: the file for a target, made of
-- the entries of the specification's structure in source order (each
-- metavariable declaration, group of rules, subrules, auxiliary functions,
-- substitutions, free variables, context rules, embed and definition
-- class), between a standard preamble and postamble. Also the checks Ott
-- makes only when a prover is a target, and the dependencies it computes
-- for each target while checking, with ocamlgraph's vertex counter.
module Haskott.Prover.System
  ( Input (..)
  , Prepared (..)
  , prepareProvers
  , ProverJob (..)
  , proverOutputs
  , outputFileName
  , debugStructure
  ) where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Trans.State.Strict (get, modify)
import qualified Data.ByteString as B
import Data.List (find, sortBy)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Ord (comparing)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Graft.Range as Range
import Haskott.Defns (ProcessedClass (..), ProcessedFunClass (..), ProcessedItem (..), Processed (..))
import Graft (TextRange)
import Haskott.Prover.Bounds
import Haskott.Prover.Context
import Haskott.Prover.CoqInduct
import Haskott.Prover.Defns
import Haskott.Prover.Dependency
import Haskott.Prover.LocallyNameless
import Haskott.Term.Grammar (nonterminalCount)
import Haskott.Term.Parse (makeTermParser, termGrammar)
import Haskott.Prover.ExpandLists
import Haskott.Prover.Pp
import Haskott.Prover.Subrules
import Haskott.Prover.Substs
import Haskott.Prover.Transform
import Haskott.Prover.Types
import Haskott.SourceLoc
import Haskott.Spec
import Haskott.Term.Symterm

-- | A source file, at its offset in the concatenation of the sources.
data Input = Input
  { inPath :: FilePath
  , inText :: Text
  , inBase :: Int
  }

data Prepared = Prepared
  { prDeps :: M.Map Target Deps
  , prAuxfnTypes :: [(Text, ([Text], RootRef))]
  , prVertex :: Int
  -- ^ ocamlgraph's vertex counter when Ott starts printing
  }

------------------------------------------------------------------------
-- Checks

-- | Ott's checks for the prover targets of a run, its dependencies for
-- each, and the vertex counter after the checker and the term parser
-- (which builds a graph of the term grammar's nonterminals).
prepareProvers :: Bool -> [Target] -> [Input] -> Spec -> Int -> Either Diagnostic Prepared
prepareProvers merge targets inputs spec grammarNonterminals = do
  metaHoms targets spec
  axs <- auxfnTypes spec
  let auxfnNames = Set.size (Set.fromList (map fst (specAuxfns spec)))
      possibleNtrs = length [() | r <- specRules spec, _ <- ruleNames r]
      -- the checker's graphs: a vertex per auxiliary function (typing
      -- them) and one per nonterminal root (trivial cycles)
      c0 = auxfnNames + possibleNtrs
      step (acc, c) t = let (d, c') = computeDependencies spec t c in (acc ++ [(t, d)], c')
      -- Ott computes the dependencies for ascii too, and its vertices count
      (deps, c1) = foldl' step ([], c0) ("ascii" : map targetName targets)
      structure = collapsedStructure inputs (structureOf spec axs)
  unless merge $ forM_ deps $ \(_, d) -> checkStructure spec (depGraphNontran d) structure
  pure
    Prepared
      { prDeps = M.fromList [(t, d) | t <- targets, Just d <- [lookup (targetName t) deps]]
      , prAuxfnTypes = axs
      , prVertex = c1 + grammarNonterminals
      }

-- | A meta or sugar production must have a hom for each target.
metaHoms :: [Target] -> Spec -> Either Diagnostic ()
metaHoms targets spec =
  forM_ [p | r <- specRules spec, ruleName r /= "terminals", p <- ruleProds r, prodMeta p] $ \p ->
    forM_ targets $ \t ->
      unless (targetName t `elem` map fst (prodHoms p)) $
        Left (Diagnostic (prodRange p) ("(in checking and disambiguating quotiented syntax)\nmeta or sugar production must have a hom for each target - here \"" <> targetName t <> "\" is missing"))

-- | Ott's check that the dependencies of each group of rules are in the
-- group or earlier in the source.
checkStructure :: Spec -> [(RootRef, [RootRef])] -> [(FilePath, Entry)] -> Either Diagnostic ()
checkStructure spec depGr = go []
  where
    go seen es = case es of
      [] -> Right ()
      (_, EntryRs rg) : more -> do
        inner seen rg
        go (rg ++ seen) more
      _ : more -> go seen more
    inner rgseen rgtosee = case rgtosee of
      [] -> Right ()
      r : rs -> do
        let rule = ruleOfName r
        unless (ruleSemiMeta rule) $
          forM_ (fromMaybe [] (lookup (Ntr r) depGr)) $ \rd -> case rd of
            Mvr _ -> pure ()
            Ntr d ->
              unless (d `elem` (rgtosee ++ rgseen)) $
                Left (Diagnostic (ruleRange rule) ("(in checking and disambiguating quotiented syntax)\nrule \"" <> r <> "\" depends on rule \"" <> d <> "\" which belongs to a future group of rules.\n"))
        inner (r : rgseen) rs
    ruleOfName n = fromMaybe (error "Haskott.Prover.System: no rule") (find ((== n) . ruleName) (specRules spec))

-- | Ott's typing of auxiliary functions: the rules each is defined over,
-- and its result type, from the bindspecs that constrain it.
auxfnTypes :: Spec -> Either Diagnostic [(Text, ([Text], RootRef))]
auxfnTypes spec = do
  let names = removeDuplicates (map fst (specAuxfns spec))
      constraints =
        [ ty
        | r <- specRules spec
        , not (ruleMeta r)
        , p <- ruleProds r
        , not (prodMeta p)
        , b <- prodBindspecs p
        , let ty = removeDuplicates (bindspecType b)
        , length ty > 1
        ]
      auxOf x = case x of
        Left f -> Just f
        Right _ -> Nothing
      component f =
        let grow fs =
              let fs' = Set.union fs (Set.fromList [g | c <- constraints, any (\x -> auxOf x `elem` map Just (Set.toList fs)) c, Just g <- map auxOf c])
               in if fs' == fs then fs else grow fs'
         in grow (Set.singleton f)
      resultOf f =
        let comp = component f
            ntmvrs = removeDuplicates [r | c <- constraints, any (\x -> maybe False (`Set.member` comp) (auxOf x)) c, Right r <- c]
         in case ntmvrs of
              [r] -> Right r
              [] -> Left (Diagnostic (auxRange f) ("(in checking and disambiguating quotiented syntax)\nauxfns " <> T.unwords (Set.toList comp) <> " have unconstrained result type"))
              _ -> Left (Diagnostic (auxRange f) ("(in checking and disambiguating quotiented syntax)\nauxfns " <> T.unwords (Set.toList comp) <> " have overconstrained result type: " <> T.unwords [rootName r | r <- ntmvrs]))
      auxRange f = case [prodRange p | r <- specRules spec, p <- ruleProds r, AuxFnDef g _ _ <- prodBindspecs p, g == f] of
        (rg : _) -> rg
        [] -> error "Haskott.Prover.System: auxfn without a definition"
  forM names $ \f -> do
    r <- resultOf f
    pure (f, ([n | (g, n) <- specAuxfns spec, g == f], r))
  where
    rootName r = case r of
      Ntr n -> n
      Mvr n -> n
    primaryNtr n = maybe n ruleName (find (\r -> n `elem` map fst (ruleNames r)) (specRules spec))
    primaryMvr n = maybe n mvdName (find (\md -> n `elem` map fst (mvdNames md)) (specMetavars spec))
    bindspecType b = case b of
      Bind m _ _ -> mseType m
      AuxFnDef f m _ -> Left f : mseType m
      NamesEqual a c _ -> mseType a ++ mseType c
      NamesDistinct a c _ -> mseType a ++ mseType c
      AllNamesDistinct a _ -> mseType a
    mseType m = case m of
      MetaVarExp (mv, _) -> [Right (Mvr (primaryMvr mv))]
      MetaVarListExp (mv, _) _ -> [Right (Mvr (primaryMvr mv))]
      NonTermExp (nt, _) -> [Right (Ntr (primaryNtr nt))]
      NonTermListExp (nt, _) _ -> [Right (Ntr (primaryNtr nt))]
      Aux f _ -> [Left f]
      AuxList f _ _ -> [Left f]
      Union a c -> mseType a ++ mseType c
      Empty -> []

------------------------------------------------------------------------
-- The structure

-- | A location: the range's start, at which the entry is sorted (by file
-- and line, as Ott compares locations), or none for the synthesised.
type Loc = Maybe Int

data Entry
  = EntryMd Text
  | EntryRs [Text]
  | EntrySrs [(Text, Text)]
  | EntryCrs [(Text, Text, Text)]
  | EntryAxs [Text]
  | EntrySbs [(Text, Text, RootRef)]
  | EntryFvs [(Text, Text, RootRef)]
  | EntryEmbed Embed
  | EntryClass Text
  deriving (Eq, Show)

start :: TextRange -> Loc
start r = Just (fromIntegral (Range.start r))

-- | Ott's step 11 of @check_and_disambiguate@: the entries, before they are
-- sorted by location and collapsed.
structureOf :: Spec -> [(Text, ([Text], RootRef))] -> [(Loc, Entry)]
structureOf spec axs =
  let mds = [(start (mvdRange md), EntryMd (mvdName md)) | md <- specMetavars spec]
      rs = [(start (ruleRange r), EntryRs [ruleName r]) | r <- specRules spec, not (ruleSemiMeta r)]
      srs = [(start (srRange sr), EntrySrs [(srLower sr, srUpper sr)]) | sr <- specSubrules spec]
      crs = [(start (crRange cr), EntryCrs [(crNtr cr, crTarget cr, crHole cr)]) | cr <- specContextrules spec]
      axsE =
        [ (maximum' [l | (l, EntryRs [n]) <- rs, n `elem` ntrl], EntryAxs [f])
        | (f, (ntrl, _)) <- axs
        ]
      sbs = [(start (sbRange sb), EntrySbs [(sbName sb, sbThis sb, sbThat sb)]) | sb <- specSubstitutions spec]
      fvs = [(start (fvRange fv), EntryFvs [(fvName fv, fvThis fv, fvThat fv)]) | fv <- specFreevars spec]
      embeds = [(start (embedRange e), EntryEmbed e) | e <- preambleEmbeds spec ++ specEmbeds spec]
      dcs = [(start (classRange c), EntryClass (className c)) | c <- specClasses spec]
   in mds ++ rs ++ srs ++ crs ++ axsE ++ sbs ++ fvs ++ embeds ++ dcs
  where
    maximum' ls = foldl1 max ls
    classRange c = case c of
      ClassReln dc -> dcRange dc
      ClassFuns fc -> fcRange fc
    className c = case c of
      ClassReln dc -> dcName dc
      ClassFuns fc -> fcName fc

-- | The sorted, collapsed structure, with each entry's file.
collapsedStructure :: [Input] -> [(Loc, Entry)] -> [(FilePath, Entry)]
collapsedStructure inputs entries =
  let place l = case l of
        Nothing -> Nothing
        Just off -> Just (inputAt off)
      inputAt off = case [i | i <- inputs, inBase i <= off] of
        [] -> fromMaybe (error "Haskott.Prover.System: no input") (listToMaybe inputs)
        is -> last is
      lineOf off =
        let i = inputAt off
            bytes = TE.encodeUtf8 (inText i)
         in B.count 10 (B.take (off - inBase i) bytes)
      fileIndex i = length (takeWhile ((/= inPath i) . inPath) inputs)
      key l = case l of
        Nothing -> Nothing
        Just off -> Just (fileIndex (inputAt off), lineOf off)
      cmp (a, _) (b, _) = case (key a, key b) of
        (Nothing, Nothing) -> EQ
        (Nothing, Just _) -> LT
        (Just _, Nothing) -> GT
        (Just x, Just y) -> compare x y
      sorted = sortBy cmp entries
      sameFile a b = (inPath <$> place a) == (inPath <$> place b)
      mustCollapse e = case e of
        EntryRs _ -> True
        EntrySrs _ -> True
        EntryCrs _ -> True
        EntryAxs _ -> True
        EntrySbs _ -> True
        EntryFvs _ -> True
        _ -> False
      collapsible a b = case (a, b) of
        (EntryRs _, EntryRs _) -> True
        (EntrySrs _, EntrySrs _) -> True
        (EntryCrs _, EntryCrs _) -> True
        (EntryAxs _, EntryAxs _) -> True
        (EntrySbs _, EntrySbs _) -> True
        (EntryFvs _, EntryFvs _) -> True
        _ -> False
      joined a b = case (a, b) of
        (EntryRs x, EntryRs y) -> EntryRs (x ++ y)
        (EntrySrs x, EntrySrs y) -> EntrySrs (x ++ y)
        (EntryCrs x, EntryCrs y) -> EntryCrs (x ++ y)
        (EntryAxs x, EntryAxs y) -> EntryAxs (x ++ y)
        (EntrySbs x, EntrySbs y) -> EntrySbs (x ++ y)
        (EntryFvs x, EntryFvs y) -> EntryFvs (x ++ y)
        _ -> error "Haskott.Prover.System: collapsing incompatible structure elements"
      out current auxfns = case (current, auxfns) of
        (Nothing, []) -> []
        (Just c, []) -> [c]
        (Nothing, _) -> error "Haskott.Prover.System: auxfns but undefined current"
        (Just c@(l, _), xs) -> [c, (l, EntryAxs xs)]
      collapseFrom current auxfns strs = case strs of
        [] -> out current auxfns
        (l, s) : ss
          | mustCollapse s -> case current of
              Nothing -> collapseFrom (Just (l, s)) [] ss
              Just (lc, sc)
                | collapsible sc s && sameFile l lc -> collapseFrom (Just (lc, joined sc s)) auxfns ss
                | otherwise -> case s of
                    EntryAxs axs' -> collapseFrom (Just (lc, sc)) (axs' ++ auxfns) ss
                    _ -> out current auxfns ++ collapseFrom (Just (l, s)) [] ss
          | otherwise -> out current auxfns ++ ((l, s) : collapseFrom Nothing [] ss)
   in [(maybe "" inPath (place l), e) | (l, e) <- collapseFrom Nothing [] sorted]

------------------------------------------------------------------------
-- The output

data ProverJob = ProverJob
  { pjTarget :: Target
  , pjOptions :: ProverOptions
  , pjSpec :: Spec
  , pjProcessed :: Processed
  , pjInputs :: [Input]
  , pjQuotation :: Text -> Symterm
  , pjOutputs :: [(FilePath, [FilePath])]
  -- ^ each output file with its input files, in Ott's order
  , pjParse :: Text -> Text -> [Symterm]
  -- ^ every parse of a text as a term of a root, in order
  , pjMerge :: Bool
  -- ^ Ott's @-merge true@: the output ignores the structure
  , pjSources :: Sources
  -- ^ the sources, for @-output_source_locations@
  }

-- | The file name Ott names the theory by: without @.thy@ or
-- @Script.sml@.
outputFileName :: Target -> FilePath -> Either Text Text
outputFileName t o = case t of
  Isa -> maybe (Left "Isabelle filenames must end with .thy\n") Right (T.stripSuffix ".thy" (T.pack o))
  Hol -> maybe (Left "HOL filenames must end with Script.sml\n") Right (T.stripSuffix "Script.sml" (T.pack o))
  _ -> Right (T.pack o)

-- | The files of a target, and the vertex counter after them; or the
-- error Ott stops with.
proverOutputs :: Prepared -> ProverJob -> Int -> Either Text ([(FilePath, Text)], Int)
proverOutputs prepared job vertex0 = do
  let t = pjTarget job
      opts = pjOptions job
      deps0 = fromMaybe (error "Haskott.Prover.System: no dependencies") (M.lookup t (prDeps prepared))
      structure0 = collapsedStructure (pjInputs job) (structureOf (pjSpec job) (prAuxfnTypes prepared))
  (spec, processed, deps, structure) <- case t of
    Coq
      | optCoqAvoid opts `elem` [1, 2] ->
          let (s, p) = avoidPrimaries (optCoqAvoid opts == 2) (pjSpec job) (pjProcessed job) in Right (s, p, deps0, structure0)
      | optCoqAvoid opts == 0 -> Right (pjSpec job, pjProcessed job, deps0, structure0)
      | otherwise -> Left "coq type-name avoidance must be in {0,1,2}"
    Caml -> case camlRename (pjSpec job) (pjProcessed job) of
      Left d -> Left (diagMessage d <> "\n")
      Right (s, p, mvr, ntr) -> Right (s, p, renameDeps mvr ntr deps0, [(f, renameEntry mvr ntr e) | (f, e) <- structure0])
    _ -> Right (pjSpec job, pjProcessed job, deps0, structure0)
  let env = (makeEnv t opts deps (prAuxfnTypes prepared) (pjQuotation job) spec) {envParse = pjParse job, envLoc = locText (pjInputs job), envSources = pjSources job}
  if pjMerge job
    then mergedOutput env processed structure job vertex0
    else
      if requireLocallyNameless spec
        then case pjOutputs job of
          [(o, _)] -> do
            let ln =
                  LnJob
                    { lnSources = T.unwords [T.pack (inPath i) | i <- pjInputs job]
                    , lnProcessed = processed
                    , lnGrammarNonterminals = nonterminalCount . termGrammar . makeTermParser
                    , lnEmbed = ppEmbed
                    }
            (txt, st) <- runP (initialPState vertex0) (lnOutput env ln)
            pure ([(o, txt)], psVertex st)
          _ -> Left "must specify only one output file in the Coq locally-nameless backend.\n"
        else structuredOutput env processed structure job vertex0

-- | Ott's @pp_systemdefn@, used with @-merge true@: one file, the
-- metavariables, rules, functions, embeds and definitions each together.
mergedOutput :: Env -> Processed -> [(FilePath, Entry)] -> ProverJob -> Int -> Either Text ([(FilePath, Text)], Int)
mergedOutput env processed structure job vertex0 = do
  o <- case pjOutputs job of
    [(o, _)] -> Right o
    _ -> Left "must specify only one output file .\n"
  fn <- outputFileName (envTarget env) o
  let spec = envSpec env
      sources = T.unwords [T.pack (inPath i) | i <- pjInputs job]
      header = "(* generated by Ott 0.34 from: " <> sources <> " *)\n"
  let (envX, _, state0) = expansion env structure vertex0
  (txt, st) <- runP state0 $ do
    pre <- T.concat <$> mapM (ppEmbed env) (preambleEmbeds spec)
    _ <- auxiliaryLemmas envX
    let syntax0 = T.concat (map (ppMetavardefn envX) (specMetavars spec))
    rules <- ppRuleList envX (specRules (envSpec envX))
    srs <- ppSubrules env (specSubrules spec)
    axs <- ppAuxfns env (envAuxfnTypes env)
    sbs <- ppSubsts env (specSubstitutions spec)
    fvs <- ppFreevars env (specFreevars spec)
    crs <- ppContext env (specContextrules spec)
    (library, _) <- psLibrary <$> get
    auxList <- if isCoq env then psCoqListAuxFuncs <$> get else pure ""
    srsT <- compute env srs
    axsT <- compute env axs
    fvsT <- compute env fvs
    sbsT <- compute env sbs
    crsT <- compute env crs
    let functions =
          bigLineComment env "auxiliary functions on the new list types" <> auxList
            <> bigLineComment env "library functions" <> library
            <> bigLineComment env "subrules" <> srsT
            <> bigLineComment env "auxiliary functions" <> axsT
            <> bigLineComment env "free variables" <> fvsT
            <> bigLineComment env "substitutions" <> sbsT
            <> bigLineComment env "context application" <> crsT
    embedsT <- T.concat <$> mapM (ppEmbed env) (specEmbeds spec)
    defns <- ppFunOrRelnDefnclassList env (processedItems processed)
    ip <-
      if isCoq env && not (optCoqExpandLists (envOpts env))
        then do
          i <- ppInduction env (specRules spec)
          pure (if T.null i then "" else bigLineComment env "induction principles" <> i <> "\n")
        else pure ""
    let core =
          bigLineComment env "warning: the backend selected ignores the file structure informations"
            <> pre
            <> bigLineComment env "syntax"
            <> syntax0 <> rules
            <> "\n"
            <> functions
            <> embedsT
            <> "\n"
            <> defns
            <> "\n\n"
            <> ip
    pure $ case envTarget env of
      Isa -> header <> "theory " <> fn <> "\nimports " <> T.unwords ("Main" : isaImports spec) <> "\n" <> "begin\n\n" <> core <> "\nend\n"
      Hol -> standardPreamble env spec fn [inPath i | i <- pjInputs job] <> core <> "\nval _ = export_theory ();\n"
      Coq -> header <> T.concat ["Require Import " <> th <> ".\n" | th <- ["Arith", "Bool", "List"] ++ (if optCoqExpandLists (envOpts env) then [] else ["Ott.ott_list_core"])] <> core
      Twf -> "%% generated by Ott 0.34 from: " <> sources <> "\n\n" <> core
      _ -> header <> core
  pure ([(o, txt)], psVertex st)

structuredOutput :: Env -> Processed -> [(FilePath, Entry)] -> ProverJob -> Int -> Either Text ([(FilePath, Text)], Int)
structuredOutput env processed structure0 job vertex0 = do
  let t = envTarget env
      -- Ott names the sources of the first output in every header
      firstInputs = case pjOutputs job of
        (_, is) : _ -> is
        [] -> []
      single = case pjOutputs job of
        [(_, [_])] -> True
        _ -> False
      (envX, structure, state0) = expansion env structure0 vertex0
  (files, st) <- runP state0 $ forM (pjOutputs job) $ \(o, is) -> do
    fn <- either failP pure (outputFileName t o)
    let entries = if single then structure else [(f, e) | (f, e) <- structure, f `elem` is]
    pre <- ppEmbedmorphism env (preambleName t) (standardPreamble env (envSpec env) fn firstInputs)
    lemmas <- auxiliaryLemmas envX
    body <- T.concat <$> mapM (ppStructEntryX env envX processed) (map snd entries)
    post <- case t of
      Isa -> structPrefixed env (EntryEmbed (Embed "isa" [EmbedString "\nend\n"] dummyRange))
      Hol -> structPrefixed env (EntryEmbed (Embed "hol" [EmbedString "\nval _ = export_theory ();\n"] dummyRange))
      _ -> pure ""
    pure (o, pre <> lemmas <> body <> post <> "\n\n")
  pure (files, psVertex st)
  where
    structPrefixed env' e = ppStructEntry env' processed e
    dummyRange = fromMaybe (error "range") (Range.fromEnds 0 0)

preambleName :: Target -> Text
preambleName = targetName

-- | Ott's standard preamble.
standardPreamble :: Env -> Spec -> Text -> [FilePath] -> Text
standardPreamble env spec fn is =
  let sources = if null is then "no input files" else T.unwords (map T.pack is)
      header = "(* generated by Ott 0.34 from: " <> sources <> " *)\n"
   in case envTarget env of
        Isa ->
          let imports = "Main" : isaImports spec
           in header <> "theory " <> fn <> "\n" <> "imports " <> T.unwords imports <> "\n" <> "begin\n"
        Hol ->
          header
            <> "(* to compile: Holmake " <> fn <> "Theory.uo   *)\n"
            <> "(* for interactive use:\n"
            <> "  app load [\"pred_setTheory\",\"finite_mapTheory\",\"stringTheory\",\"containerTheory\",\"ottLib\"];\n"
            <> "*)\n\n"
            <> "open HolKernel boolLib Parse bossLib ottLib;\n"
            <> "infix THEN THENC |-> ## ;\n"
            <> "local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory \n"
            <> "  finite_mapTheory in end;\n\n"
            <> "val _ = new_theory \"" <> fn <> "\";\n"
        Coq ->
          "(* generated by Ott 0.34 from: " <> sources <> " *)\n\n"
            <> T.intercalate "\n" ["Require Import " <> th <> "." | th <- ["Arith", "Bool", "List"] ++ (if optCoqExpandLists (envOpts env) then [] else ["Ott.ott_list_core"])]
            <> "\n\n"
        Caml -> header
        Lem -> header <> "open import Pervasives\n"
        Twf -> "%% generated by Ott 0.34 from: " <> sources <> " \n"

isaImports :: Spec -> [Text]
isaImports spec = [s | e <- specEmbeds spec, embedName e == "isa-import", EmbedString s <- embedSpec e]

-- | An embed printed for the target: the synthesised preamble.
ppEmbedmorphism :: Env -> Text -> Text -> P Text
ppEmbedmorphism env _ txt = do
  lib <- ppLibrary env
  pure (lib <> sourceLocation env 2 [] <> txt <> "\n")

-- | Ott's @pp_auxiliary_lemmas@: the list lemmas, when some rule uses
-- lists.
auxiliaryLemmas :: Env -> P Text
auxiliaryLemmas env = do
  let usesLists = or [True | r <- specRules (envSpec env), not (ruleMeta r), p <- ruleProds r, not (prodMeta p), any isList (prodElements p)]
      isList e = case e of
        ListForm _ -> True
        _ -> False
  when usesLists $ do
    ppListAllCongLemma env
    ppListSimpLemmas env
  pure ""

-- | Ott's @pp_library@: the library functions added since the last time,
-- under a heading.
ppLibrary :: Env -> P Text
ppLibrary env = do
  (txt, names) <- psLibrary <$> get
  if T.null txt
    then pure ""
    else do
      modify (\s -> s {psLibrary = ("", names)})
      pure (bigLineComment env "library functions" <> txt)

-- | Ott's @Transform.expand_lists_in_syntaxdefn@ for a Coq target with
-- @-coq_expand_list_types true@: the environment with the expanded rules
-- (for printing the groups of rules), the structure with the new list
-- types and their functions, and the initial state; otherwise as given.
expansion :: Env -> [(FilePath, Entry)] -> Int -> (Env, [(FilePath, Entry)], PState)
expansion env structure vertex0
  | isCoq env && optCoqExpandLists (envOpts env) =
      let dummy = fromMaybe (error "range") (Range.fromEnds 0 0)
          ex = expandLists env (\funcs -> EntryEmbed (Embed "coq" [EmbedString funcs] dummy)) [(f, case e of EntryRs ns -> Left ns; _ -> Right e) | (f, e) <- structure] vertex0
          envX = (makeEnv (envTarget env) (envOpts env) (exDeps ex) (exAuxfns ex) (envQuotation env) (exSpec ex)) {envParse = envParse env, envLoc = envLoc env, envSources = envSources env}
          st = (initialPState (exVertex ex)) {psCoqListTypes = exListTypes ex, psCoqListAuxFuncs = exListAuxFuncs ex}
       in (envX, [(f, either EntryRs id e) | (f, e) <- exStructure ex], st)
  | otherwise = (env, structure, initialPState vertex0)

-- | Ott's @pp_struct_entry@.
ppStructEntry :: Env -> Processed -> Entry -> P Text
ppStructEntry env = ppStructEntryX env env

-- | Ott's @pp_struct_entry@, with the expanded syntax for the groups of
-- rules.
ppStructEntryX :: Env -> Env -> Processed -> Entry -> P Text
ppStructEntryX env envX processed e = do
  lib <- ppLibrary env
  body <- case e of
    EntryMd mvr ->
      let md = mvdOfMvr env mvr
       in pure (sourceLocation env 2 (itemLoc (envSources env) (mvdRange md)) <> ppMetavardefn env md)
    EntryRs ntrs -> do
      let rs = map (ruleOfNtr envX) ntrs
      def <- (sourceLocation env 2 (concatMap (ruleLoc (envSources env)) rs) <>) <$> ppRuleList envX rs
      ip <-
        if isCoq env && not (optCoqExpandLists (envOpts env))
          then do
            ip <- ppInduction envX rs
            pure (if T.null ip then "" else bigLineComment env "induction principles" <> ip)
          else pure ""
      pure (def <> ip)
    EntryAxs xs -> do
      funcs <- ppAuxfns env [ax | f <- xs, ax@(f', _) <- envAuxfnTypes env, f' == f]
      compute env funcs
    EntryClass n -> ppFunOrRelnDefnclassList env [it | it <- processedItems processed, itemName it == n]
    EntrySrs xs -> do
      let srs = [sr | (l, u) <- xs, sr <- take 1 [s | s <- specSubrules (envSpec env), srLower s == l, srUpper s == u]]
      funcs <- ppSubrules env srs
      printWithComment env "\n" "subrules" . (locs (map srRange srs) <>) <$> compute env funcs
    EntryFvs xs -> do
      let fvs = [fv | (n, ntr, that) <- xs, fv <- take 1 [f | f <- specFreevars (envSpec env), fvName f == n, fvThis f == ntr, fvThat f == that]]
      funcs <- ppFreevars env fvs
      -- the functions add library functions, which Ott prints first
      lib' <- ppLibrary env
      (lib' <>) . printWithComment env "\n" "free variables" . (locs (map fvRange fvs) <>) <$> compute env funcs
    EntrySbs xs -> do
      let sbs = [sb | (n, ntr, that) <- xs, sb <- take 1 [s | s <- specSubstitutions (envSpec env), sbName s == n, sbThis s == ntr, sbThat s == that]]
      funcs <- ppSubsts env sbs
      lib' <- ppLibrary env
      (lib' <>) . printWithComment env "\n" "substitutions" . (locs (map sbRange sbs) <>) <$> compute env funcs
    EntryCrs xs -> do
      let crs = [cr | (n, t, h) <- xs, cr <- take 1 [c | c <- specContextrules (envSpec env), crNtr c == n, crTarget c == t, crHole c == h]]
      funcs <- ppContext env crs
      printWithComment env "\n" "context application" . (locs (map crRange crs) <>) <$> compute env funcs
    EntryEmbed em -> ppEmbed env em
  pure (lib <> body)
  where
    locs rs = sourceLocation env 2 (concatMap (itemLoc (envSources env)) rs)
    itemName it = case it of
      PReln pc -> pcName pc
      PFuns pfc -> pfcName pfc

-- | Ott's @pp_embedmorphism@ for a prover: the embeds of the target, and
-- the names its library embed defines.
ppEmbed :: Env -> Embed -> P Text
ppEmbed env em = (sourceLocation env 2 (itemLoc (envSources env) (embedRange em)) <>) <$> ppEmbedBody env em

ppEmbedBody :: Env -> Embed -> P Text
ppEmbedBody env em
  | embedName em == tn = do
      body <- T.concat <$> mapM el (embedSpec em)
      pure (body <> "\n")
  | (isCoq env && embedName em == "coq-lib") || (isIsa env && embedName em == "isa-lib") = do
      let names = reverse (concat [filter (not . T.null) (T.split (`elem` (" \t" :: String)) s) | EmbedString s <- embedSpec em])
      modify (\s -> let (txt, ns) = psLibrary s in s {psLibrary = (txt, reverse names ++ ns)})
      pure ""
  | otherwise = pure ""
  where
    tn = targetName (envTarget env)
    el x = case x of
      EmbedString s -> pure s
      EmbedInner s -> do
        let st = envQuotation env s
        (de, _) <- either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env [st])
        ppSymterm env [] de st

-- | Ott's @pp_loc@ of a range of the sources (Ott's rule lines end after
-- their newline).
locText :: [Input] -> Maybe (Int, Int) -> Text
locText inputs r = case r of
  Nothing -> ""
  Just (s, e) ->
    let i = case [x | x <- inputs, inBase x <= s] of
          [] -> fromMaybe (error "Haskott.Prover.System: no input") (listToMaybe inputs)
          xs -> last xs
        bytes = TE.encodeUtf8 (inText i)
        s' = s - inBase i
        e0 = e - inBase i
        e' = if e0 < B.length bytes && B.index bytes e0 == 10 then e0 + 1 else e0
        pos o =
          let before = B.take o bytes
           in (B.count 10 before + 1, o - maybe 0 (+ 1) (B.elemIndexEnd 10 before))
        (l1, c1) = pos s'
        (l2, c2) = pos e'
        file = "File " <> T.pack (inPath i) <> " on "
        n = T.pack . show
     in if l1 == l2
          then file <> "line " <> n l1 <> ", column " <> n c1 <> " - " <> n c2
          else
            if c1 == 0 && c2 == 0
              then file <> "line " <> n l1 <> " - " <> n l2
              else file <> "line " <> n l1 <> ", column " <> n c1 <> " - " <> "line " <> n l2 <> ", column " <> n c2

-- | The collapsed structure, for debugging.
debugStructure :: [Input] -> Spec -> Text
debugStructure inputs spec = case auxfnTypes spec of
  Left d -> diagMessage d
  Right axs -> T.unlines [T.pack (f ++ ": " ++ show e) | (f, e) <- collapsedStructure inputs (structureOf spec axs)]

renameDeps :: (Text -> Text) -> (Text -> Text) -> Deps -> Deps
renameDeps mvr ntr d =
  Deps
    { depTs = map (map root) (depTs d)
    , depGraph = [(root a, map root bs) | (a, bs) <- depGraph d]
    -- from depGraph, as Ott's rename_dependencies does
    , depGraphNontran = [(root a, map root bs) | (a, bs) <- depGraph d]
    }
  where
    root r = case r of
      Mvr x -> Mvr (mvr x)
      Ntr x -> Ntr (ntr x)

renameEntry :: (Text -> Text) -> (Text -> Text) -> Entry -> Entry
renameEntry mvr ntr e = case e of
  EntryMd m -> EntryMd (mvr m)
  EntryRs ns -> EntryRs (map ntr ns)
  EntrySrs xs -> EntrySrs [(ntr a, ntr b) | (a, b) <- xs]
  EntryCrs xs -> EntryCrs [(ntr a, ntr b, ntr c) | (a, b, c) <- xs]
  _ -> e

_unused :: ()
_unused = const () (isJust (Nothing :: Maybe ()), comparing fst ((), ()) ((), ()))
