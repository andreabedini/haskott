{-# LANGUAGE OverloadedStrings #-}

-- | From the raw specification to the checked one.
--
-- This follows Ott's @check_and_disambiguate@ (@grammar_typecheck.ml@)
-- step by step: synthesise the grammars of judgements and user syntax from
-- the definitions, merge hom sections, collect the roots, build the
-- identifier lexer, convert each construct (resolving roots to their
-- primary names, classifying elements, merging dot forms, resolving hom
-- references, checking binding specifications), then check the result.
-- The first error stops the check, as in Ott.
--
-- Not implemented from Ott's step 10: the matching of each production of
-- a subrule against the productions of its upper rule, context-rule
-- checks, productivity, the auxiliary-function typing, and the dependency
-- analysis.
module Haskott.Spec.Check
  ( checkDocument
  ) where

import Control.Monad (forM, forM_, unless, when, zipWithM)
import Data.List (find, nub, sort)
import Data.Maybe (fromMaybe, isJust, isNothing, listToMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Graft.Range (TextRange)
import qualified Haskott.Raw as R
import Haskott.Spec

type Check = Either Diagnostic

err :: TextRange -> Text -> Check a
err r m = Left (Diagnostic r m)

quote :: Text -> Text
quote s = "\"" <> s <> "\""

------------------------------------------------------------------------
-- Raw rules, before and after synthesis

-- | A raw rule as the checker sees it: the user's and the synthesised ones.
data XRule = XRule
  { xName :: Text
  , xNames :: [(Text, [R.Hom])]
  , xPrefix :: Text
  , xProds :: [R.Prod]
  , xHoms :: [R.Hom]
  , xCategories :: [Text]
  , xRange :: TextRange
  }

data Class = ClassDefn R.DefnClass | ClassFun R.FunClass

checkDocument :: R.Document -> Check Spec
checkDocument doc = do
  let mds = [d | R.ItemMetavar d <- doc]
      userRules = [xruleOf r | R.ItemGrammar rs <- doc, r <- rs]
      srs = concat [s | R.ItemSubrules s <- doc]
      crs = concat [c | R.ItemContextrules c <- doc]
      sbs = concat [s | R.ItemSubstitutions s <- doc]
      fvs = concat [f | R.ItemFreevars f <- doc]
      embeds = concat [e | R.ItemEmbed e <- doc]
      pas = concat [p | R.ItemParsing p <- doc]
      hss = [h | R.ItemHomSection h <- doc]
      classes = concat [classesOf it | it <- doc]

  -- 2: function results and usage productions, rules for the classes
  (userRules', classes') <- addUsageProds userRules classes
  let judgementRoots = [R.dcName dc | ClassDefn dc <- classes']
      formulaRule =
        [ XRule "formula" [("formula", [])] "formula_"
            [R.Prod [R.EIdent "judgement"] [] "judgement" [] [] noRange]
            [] ["formula"] noRange
        | not (any ((== "formula") . xName) userRules)
        ]
      classRules = map classRule classes'
      prodOfRoot ntr = R.Prod [R.EIdent ntr] [] ntr [] [] noRange
      judgementRule = XRule "judgement" [("judgement", [])] "judgement_" (map prodOfRoot judgementRoots) [] ["judgement"] noRange
      userSyntaxRule =
        XRule "user_syntax" [("user_syntax", [])] "user_syntax__"
          (map prodOfRoot (map primaryMvdName mds ++ map xName userRules)) [] ["user_syntax"] noRange
      allRules0 = userRules' ++ formulaRule ++ classRules ++ [judgementRule, userSyntaxRule]
      noRange = case doc of
        (it : _) -> itemRange it
        [] -> error "checkDocument: empty document"

  -- 3d: hom sections
  (allRules, classes'') <- appendHomSections hss allRules0 classes'

  -- 4, 5: roots
  let mvrsAssocOp = [(syn, primaryMvdName md) | md <- mds, (syn, _) <- R.mvdNames md]
      primaryMvr m = lookup m mvrsAssocOp
      mvrsNonindex = [syn | md <- mds, not (R.mvdIndexvar md), (syn, _) <- R.mvdNames md]
      mvrsIndex = [syn | md <- mds, R.mvdIndexvar md, (syn, _) <- R.mvdNames md]
      ntrsAssocOp = [(syn, xName r) | r <- allRules, (syn, _) <- xNames r]
      primaryNtr n = lookup n ntrsAssocOp
      ntrsAll = map fst ntrsAssocOp
  forM_ srs $ \sr ->
    when (isNothing (primaryNtr (R.srLower sr))) $
      err (R.srRange sr) (quote (R.srLower sr) <> " in subrule declaration is not a nonterminal root ")
  let srsLowers = mapMaybe (primaryNtr . R.srLower) srs
      ctx =
        Ctx
          { cRoots = Roots mvrsNonindex mvrsIndex ntrsAll
          , cPrimaryMvr = primaryMvr
          , cPrimaryNtr = primaryNtr
          , cIndexvars = mvrsIndex
          }

  -- 9: the preliminary syntax definition
  (subrules, srd) <- cdSubrules ctx srs
  rules <- mapM (cdRule ctx judgementRoots srsLowers) allRules
  metavars <- mapM (cdMetavardefn ctx) mds
  contextrules <- mapM (cdContextrule ctx) crs
  substitutions <- mapM (cdSubst ctx subrules) sbs
  freevars <- mapM (cdFreevar ctx subrules) fvs
  embeds' <- mapM cdEmbed embeds
  let allProdNames = [prodName p | r <- rules, p <- ruleProds r]
  parsing <- mapM (cdParsingAnnotation allProdNames) pas
  defnClasses <- forM [dc | ClassDefn dc <- classes''] (cdDefnClass ctx)
  funClasses <- forM [fc | ClassFun fc <- classes''] (cdFunClass ctx userRules')

  -- auxiliary functions, from the non-meta rules
  let auxfns =
        nub
          (sort
            [ (f, ruleName r)
            | r <- rules
            , not (ruleMeta r)
            , p <- ruleProds r
            , AuxFnDef f _ _ <- prodBindspecs p
            ])

  -- 10: checks
  checkSpec subrules rules auxfns
  pure
    Spec
      { specMetavars = metavars
      , specRules = rules
      , specSubrules = subrules
      , specSubruleData = srd
      , specContextrules = contextrules
      , specSubstitutions = substitutions
      , specFreevars = freevars
      , specEmbeds = embeds'
      , specParsing = parsing
      , specIndexvars = mvrsIndex
      , specDefnClasses = defnClasses
      , specFunClasses = funClasses
      , specAuxfns = auxfns
      }

itemRange :: R.Item -> TextRange
itemRange it = case it of
  R.ItemMetavar d -> R.mvdRange d
  R.ItemGrammar (r : _) -> R.ruleRange r
  R.ItemDefns dc -> R.dcRange dc
  R.ItemFuns fc -> R.fcRange fc
  R.ItemSubrules (s : _) -> R.srRange s
  R.ItemContextrules (c : _) -> R.crRange c
  R.ItemSubstitutions (s : _) -> R.sbRange s
  R.ItemFreevars (f : _) -> R.fvRange f
  R.ItemEmbed (e : _) -> R.embedRange e
  R.ItemParsing (p : _) -> R.paRange p
  R.ItemHomSection h -> R.hsRange h
  _ -> error "itemRange: item without a range"

primaryMvdName :: R.MetavarDefn -> Text
primaryMvdName md = case R.mvdNames md of
  ((n, _) : _) -> n
  [] -> ""

xruleOf :: R.Rule -> XRule
xruleOf r = XRule (fst (head' (R.ruleNames r))) (R.ruleNames r) (R.rulePrefix r) (R.ruleProds r) (R.ruleHoms r) ["user"] (R.ruleRange r)
  where
    head' xs = case xs of
      (x : _) -> x
      [] -> ("", [])

classesOf :: R.Item -> [Class]
classesOf it = case it of
  R.ItemDefns dc -> [ClassDefn dc]
  R.ItemFuns fc -> [ClassFun fc]
  _ -> []

-- | Ott's step 2: each function's result must name a rule, which gains a
-- usage production for the function.
addUsageProds :: [XRule] -> [Class] -> Check ([XRule], [Class])
addUsageProds rules classes = do
  extras <- forM [fd | ClassFun fc <- classes, fd <- R.fcDefns fc] $ \fd ->
    case find (\r -> R.fdResult fd `elem` map fst (xNames r)) rules of
      Nothing -> err (R.fdRange fd) ("function result " <> quote (R.fdResult fd) <> " must be a nonterminal root")
      Just r -> pure (xName r, usageProd fd)
  let rules' = [r {xProds = xProds r ++ [p | (n, p) <- extras, n == xName r]} | r <- rules]
  pure (rules', classes)
  where
    usageProd fd =
      R.Prod
        { R.prodElements = R.fdElements fd
        , R.prodCategories = ["M", "F"]
        , R.prodName = R.fdName fd
        , R.prodBindspecs = []
        , R.prodHoms = filter ((/= "coq-struct") . R.homName) (R.fdHoms fd)
        , R.prodRange = R.fdRange fd
        }

classRule :: Class -> XRule
classRule cl = case cl of
  ClassDefn dc ->
    XRule (R.dcName dc) [(R.dcName dc, [])] (R.dcWrapper dc) (map prodOfDefn (R.dcDefns dc)) [] ["defnclass"] (R.dcRange dc)
  ClassFun fc ->
    XRule (R.fcName fc) [(R.fcName fc, [])] "fundefn_" (map prodOfFundefn (R.fcDefns fc)) [] ["fundefnclass"] (R.fcRange fc)
  where
    prodOfDefn d =
      R.Prod (R.dElements d) (R.dCategories d) (R.dName d) [] (filter ((/= "lemwcf") . R.homName) (R.dHoms d)) (R.dRange d)
    prodOfFundefn fd =
      R.Prod (R.fdElements fd ++ [R.EIdent "===", R.EIdent (R.fdResult fd)]) [] (R.fdName fd) []
        (filter ((/= "coq-struct") . R.homName) (R.fdHoms fd)) (R.fdRange fd)

-- | Ott's step 3d: the items of hom sections go to the production or
-- definition they name, each item once, in order.
appendHomSections :: [R.HomSection] -> [XRule] -> [Class] -> Check ([XRule], [Class])
appendHomSections hss rules classes = do
  let entries = [(R.hsWrapper hs <> R.hsiName i, i) | hs <- hss, i <- R.hsItems hs]
      (rules', rest1) = mapAccum rulesStep entries rules
      rulesStep es r =
        let (ps, es') = mapAccum (prodStep (xPrefix r)) es (xProds r)
         in (r {xProds = ps}, es')
      prodStep prefix es p =
        let (mine, others) = partitionKey (prefix <> R.prodName p) es
         in ( p
                { R.prodHoms = R.prodHoms p ++ concatMap R.hsiHoms mine
                , R.prodBindspecs = R.prodBindspecs p ++ concatMap R.hsiBindspecs mine
                }
            , others
            )
  (classes', rest2) <- mapAccumM classStep rest1 classes
  case rest2 of
    [] -> pure (rules', classes')
    ((k, i) : _) ->
      err (R.hsiRange i) ("hom section contains items for nonexistent production or defn names: " <> T.intercalate ", " (map fst rest2) <> " (" <> k <> ")")
  where
    partitionKey k es = ([i | (k', i) <- es, k' == k], [e | e@(k', _) <- es, k' /= k])
    classStep es cl = case cl of
      ClassDefn dc -> do
        (ds, es') <- mapAccumM (defnStep (R.dcWrapper dc)) es (R.dcDefns dc)
        pure (ClassDefn dc {R.dcDefns = ds}, es')
      ClassFun fc -> do
        (fds, es') <- mapAccumM fundefnStep es (R.fcDefns fc)
        pure (ClassFun fc {R.fcDefns = fds}, es')
    defnStep wrapper es d = do
      let (mine, others) = partitionKey (wrapper <> R.dName d) es
      unless (all (null . R.hsiBindspecs) mine) $
        err (R.dRange d) "cannot have a bindspec for a defn (in a hom section)"
      pure (d {R.dHoms = R.dHoms d ++ concatMap R.hsiHoms mine}, others)
    fundefnStep es fd = do
      let (mine, others) = partitionKey (R.fdName fd) es
      unless (all (null . R.hsiBindspecs) mine) $
        err (R.fdRange fd) "cannot have a bindspec for a fundefn (in a hom section)"
      pure (fd {R.fdHoms = R.fdHoms fd ++ concatMap R.hsiHoms mine}, others)

mapAccum :: (acc -> a -> (b, acc)) -> acc -> [a] -> ([b], acc)
mapAccum f acc xs = case xs of
  [] -> ([], acc)
  x : more ->
    let (y, acc') = f acc x
        (ys, acc'') = mapAccum f acc' more
     in (y : ys, acc'')

mapAccumM :: Monad m => (acc -> a -> m (b, acc)) -> acc -> [a] -> m ([b], acc)
mapAccumM f acc xs = case xs of
  [] -> pure ([], acc)
  x : more -> do
    (y, acc') <- f acc x
    (ys, acc'') <- mapAccumM f acc' more
    pure (y : ys, acc'')

------------------------------------------------------------------------
-- The conversion environment

data Ctx = Ctx
  { cRoots :: Roots
  , cPrimaryMvr :: Text -> Maybe Text
  , cPrimaryNtr :: Text -> Maybe Text
  , cIndexvars :: [Text]
  }

-- | The one parse of an identifier, 'Nothing' for none, an error for several.
lexOne :: Ctx -> TextRange -> Text -> Check (Maybe IdentTok)
lexOne c r s = case lexIdent (cRoots c) s of
  [] -> pure Nothing
  [t] -> pure (Just t)
  toks -> err r ("raw ident " <> quote s <> " has multiple lexes: " <> T.unwords (map ppTok toks))
  where
    ppTok t = case t of
      TokMetavar m suff -> m <> ppSuffix suff
      TokNonterm n suff -> n <> ppSuffix suff

primaryMvrOf :: Ctx -> Text -> Text
primaryMvrOf c m = fromMaybe m (cPrimaryMvr c m)

primaryNtrOf :: Ctx -> Text -> Text
primaryNtrOf c n = fromMaybe n (cPrimaryNtr c n)

------------------------------------------------------------------------
-- Elements and dot forms (cd_element, cd_elements)

data SR = SrEl Element | SrDots Int

cdElement :: Ctx -> TextRange -> R.Element -> Check SR
cdElement c r e = case e of
  R.EIdent i -> do
    t <- lexOne c r i
    pure . SrEl $ case t of
      Just (TokMetavar m suff) -> Metavar (primaryMvrOf c m) m suff
      Just (TokNonterm n suff) -> Nonterm (primaryNtrOf c n) n suff
      Nothing -> Terminal i
  R.EQuoted i -> case lexIdent (cRoots c) i of
    [TokMetavar _ []] -> cdElement c r (R.EIdent i)
    [TokNonterm _ []] -> cdElement c r (R.EIdent i)
    _ -> pure (SrEl (Terminal i))
  R.EDots n -> pure (SrDots n)
  R.EComp res mi rcb -> do
    (b, ivr) <- cdCompBound c r rcb
    es <- cdElements c r res
    es' <- mapM (abstractIndexvarElement r ivr 0) es
    pure (SrEl (ListForm (ListBody (Just b) mi es')))

abstractIndexvarElement :: TextRange -> Text -> Int -> Element -> Check Element
abstractIndexvarElement r ivr depth e = case e of
  Nonterm p n suff -> Nonterm p n <$> abstractSuffix suff
  Metavar p m suff -> Metavar p m <$> abstractSuffix suff
  Terminal _ -> pure e
  ListForm lb -> do
    es <- mapM (abstractIndexvarElement r ivr (depth + 1)) (lbElements lb)
    pure (ListForm lb {lbElements = es})
  where
    abstractSuffix suff = case abstractIndexvarSuffix ivr depth suff of
      Abstracted s -> pure s
      NotLinear -> err r ("index " <> quote ivr <> " not used linearly in each nonterm and metavar")

cdCompBound :: Ctx -> TextRange -> R.CompBound -> Check (Bound, Text)
cdCompBound c r rcb = case rcb of
  R.Bound v -> do
    checkIndex v
    pure (BoundComp v, v)
  R.BoundU v u -> do
    checkIndex v
    unless (u `elem` cIndexvars c) $
      err r (quote u <> " used as an upper bound but not declared as an indexvar")
    pure (BoundCompU v (SiVar u 0), v)
  R.BoundLU v l n u -> do
    checkIndex v
    siv <- case parseUpperBound (cIndexvars c) u of
      [] -> err r (quote u <> " used as an upper bound but not declared as an indexvar")
      [s] -> pure s
      ss -> err r (quote u <> " has multiple lexes: " <> T.unwords (map ppSuffixItem ss))
    unless (l == "0" || l == "1") $
      err r (quote l <> " used as a lower bound but not a literal number")
    pure (BoundCompLU v (SiNum l) siv n, v)
  where
    checkIndex v =
      unless (v `elem` cIndexvars c) $
        err r (quote v <> " used as an index but not declared as an indexvar")

-- | The elements of a production, with dot forms merged into list forms.
cdElements :: Ctx -> TextRange -> [R.Element] -> Check [Element]
cdElements c r res = do
  sres <- mapM (cdElement c r) res
  let len = length sres
      dotIndices = [i | (i, SrDots _) <- zip [0 ..] sres]
  extents <- mapM (dotFormExtent sres len) dotIndices
  es <- processEs sres 0 extents
  -- no non-empty bound is repeated
  let bounds = [b | ListForm lb <- es, Just b <- [lbBound lb]]
  case firstDuplicate bounds of
    Just b -> err r ("bound " <> ppBound b <> " used for multiple dot forms in production")
    Nothing -> pure ()
  when (any (\e -> case e of ListForm lb -> isNothing (lbBound lb); _ -> False) es) $
    err r "empty bound in dot form in production"
  case firstDuplicate (ntsUsed [] es) of
    Just (_, (n, suff), _) -> err r ("repeated nonterminal " <> quote (n <> ppSuffix suff) <> " in production")
    Nothing -> pure ()
  case firstDuplicate (mvsUsed [] es) of
    Just (_, (m, suff), _) -> err r ("repeated metavar " <> quote (m <> ppSuffix suff) <> " in production")
    Nothing -> pure ()
  pure es
  where
    dotFormExtent sres len d = do
      when (d <= 0 || d >= len - 1) $ err r "dot form at left or right end"
      let dotLength = case sres !! d of
            SrDots n -> n
            _ -> 0
          terminalSeparated = case (sres !! (d - 1), sres !! (d + 1)) of
            (SrEl (Terminal a), SrEl (Terminal b)) -> a == b
            _ -> False
          maxPossible
            | terminalSeparated = min (d - 1) (len - d - 1 - 1)
            | otherwise = min d (len - d - 1)
          sublist n i = take n (drop i sres)
          mergeSublist n i j = do
            l <- noDots (sublist n i)
            u <- noDots (sublist n j)
            mergeElementList dotLength l u
          mergeEachSide n
            | terminalSeparated = mergeSublist n (d - 1 - n) (d + 2)
            | otherwise = mergeSublist n (d - n) (d + 1)
          maxSameEachSide n = case mergeEachSide n of
            Just res' -> (n, res')
            Nothing -> maxSameEachSide (n - 1)
          (width, (bo, es')) = maxSameEachSide maxPossible
      when (width <= 0) $
        err r "dot form has no non-empty identical sequence on each side (perhaps due to a missing indexvar declaration)"
      pure $
        if terminalSeparated
          then
            let tm = case sres !! (d - 1) of
                  SrEl (Terminal t) -> t
                  _ -> ""
             in (d - 1 - width, d + 1 + width + 1, ListForm (ListBody bo (Just tm) es'))
          else (d - width, d + width + 1, ListForm (ListBody bo Nothing es'))
    noDots sres' = mapM (\s -> case s of SrEl e -> Just e; SrDots _ -> Nothing) sres'
    processEs sres i extents = case extents of
      [] -> pure (plain (drop i sres))
      (left, right, e) : more -> do
        when (left < i) $ err r "overlapping dot forms"
        rest <- processEs sres right more
        pure (plain (take (left - i) (drop i sres)) ++ [e] ++ rest)
    plain = mapMaybe (\s -> case s of SrEl e -> Just e; SrDots _ -> Nothing)

mergeElement :: Element -> Element -> Maybe (Maybe (SuffixItem, SuffixItem), Element)
mergeElement e e' = case (e, e') of
  (Nonterm p n s, Nonterm _ n' s') | n == n' -> do
    (pbo, s'') <- mergeSuffix 0 s s'
    pb <- pbo
    Just (Just pb, Nonterm p n s'')
  (Metavar p m s, Metavar _ m' s') | m == m' -> do
    (pbo, s'') <- mergeSuffix 0 s s'
    pb <- pbo
    Just (Just pb, Metavar p m s'')
  (Terminal a, Terminal b) | a == b -> Just (Nothing, Terminal a)
  _ -> Nothing

mergeElementList :: Int -> [Element] -> [Element] -> Maybe (Maybe Bound, [Element])
mergeElementList dotLength es es' = do
  when (length es /= length es') Nothing
  xs <- zipWithM mergeElement es es'
  let pbs = [p | (Just p, _) <- xs]
  pbo <- case pbs of
    [] -> Just Nothing
    (p : more) -> if all (== p) more then Just (Just p) else Nothing
  let bound = fmap (\(lo, up) -> BoundDotform lo up dotLength) pbo
  Just (bound, map snd xs)

ppBound :: Bound -> Text
ppBound b = case b of
  BoundDotform lo up _ -> ppSuffixItem lo <> ".." <> ppSuffixItem up
  BoundComp v -> v
  BoundCompU v u -> v <> " IN " <> ppSuffixItem u
  BoundCompLU v l u _ -> v <> " IN " <> ppSuffixItem l <> ".." <> ppSuffixItem u

type Pe = [Maybe Bound]

ntsUsed :: Pe -> [Element] -> [(Text, (Text, Suffix), Pe)]
ntsUsed pe = concatMap go
  where
    go e = case e of
      Nonterm p n s -> [(p, (n, s), pe)]
      ListForm lb -> ntsUsed (lbBound lb : pe) (lbElements lb)
      _ -> []

mvsUsed :: Pe -> [Element] -> [(Text, (Text, Suffix), Pe)]
mvsUsed pe = concatMap go
  where
    go e = case e of
      Metavar p m s -> [(p, (m, s), pe)]
      ListForm lb -> mvsUsed (lbBound lb : pe) (lbElements lb)
      _ -> []

firstDuplicate :: Eq a => [a] -> Maybe a
firstDuplicate xs = case xs of
  [] -> Nothing
  x : more -> if x `elem` more then Just x else firstDuplicate more

------------------------------------------------------------------------
-- Homs (cd_hom)

data HomUse
  = HuRoot | HuMetavar | HuRule | HuRuleMeta | HuProd | HuProdTm | HuDefn | HuFundefn
  | HuSubrule | HuSubst | HuFreevar | HuDeadcode
  deriving (Eq)

allowableHoms :: HomUse -> ([Text], Text)
allowableHoms hu = case hu of
  HuRoot -> (["isa", "coq", "hol", "lem", "tex", "typst", "ocaml"], "nonterminal, metavar or indexvar root")
  HuMetavar ->
    ( [ "isa", "coq", "hol", "lem", "tex", "typst", "ocaml", "com", "coq-equality", "coq-notation", "coq-universe", "lex"
      , "texvar", "typstvar", "isavar", "holvar", "lemvar", "ocamlvar", "repr-locally-nameless", "phantom", "ocamllex"
      , "ocamllex-remove", "ocamllex-of-string", "pp", "pp-raw", "pp-suppress"
      ]
    , "metavar declaration"
    )
  HuRule ->
    ( [ "isa", "coq", "hol", "lem", "tex", "typst", "ocaml", "com", "coq-equality", "coq-notation", "coq-universe", "icho", "ichlo"
      , "ich", "ichl", "ic", "ch", "ih", "phantom", "aux", "auxparam", "menhir-start", "menhir-start-type", "quotient-with", "pp"
      , "pp-raw", "pp-suppress", "pp-params", "lex-comment"
      ]
    , "rule"
    )
  HuRuleMeta -> (["com"], "special rule")
  HuProd ->
    ( [ "isa", "coq", "hol", "lem", "tex", "typst", "texlong", "ocaml", "com", "order", "isasyn", "isaprec", "icho", "ichlo", "ich"
      , "ichl", "ic", "ch", "ih", "disambiguate", "prec", "leftassoc", "rightassoc", "menhir", "quotient-remove", "menhir-prec"
      , "pp", "pp-raw"
      ]
    , "production"
    )
  HuProdTm -> (["isa", "tex", "typst", "lex", "com", "prec", "leftassoc", "rightassoc"], "production of the terminals grammar")
  HuDefn -> (["tex", "typst", "com", "isasyn", "isaprec", "disambiguate", "lemwcf"], "definition")
  HuFundefn ->
    ( ["isa", "coq", "hol", "lem", "tex", "typst", "com", "order", "isasyn", "isaprec", "icho", "ichlo", "ich", "ichl", "ic", "ch", "ih", "coq-struct"]
    , "function definition"
    )
  HuSubrule -> (["isa-proof"], "subrule definition")
  HuSubst -> (["isa-proof"], "substitution definition")
  HuFreevar -> (["isa-proof", "isa-set"], "free variable definition")
  HuDeadcode -> ([], "Internal error: Hu_deadcode")

embedAllowableHoms :: [Text]
embedAllowableHoms =
  [ "coq", "coq-lib", "coq-preamble", "isa", "isa-import", "isa-auxfn-proof", "isa-subrule-proof", "isa-lib", "isa-preamble"
  , "hol", "hol-preamble", "lem", "lem-preamble", "tex", "tex-preamble", "tex-wrap-pre", "tex-wrap-post", "typst", "typst-preamble"
  , "ocaml", "ocaml-preamble", "menhir"
  ]

listFormAllowableHoms :: [Text]
listFormAllowableHoms = ["isa", "coq", "hol", "lem", "ic", "ch", "ih", "ich", "ichl", "icho", "ichlo", "coq-struct", "ocaml"]

isBlankish :: Text -> Bool
isBlankish = T.all (\ch -> ch == ' ' || ch == '\t' || ch == '\f')

cdHom :: HomUse -> Ctx -> [Element] -> R.Hom -> Check Hom
cdHom hu c es (R.Hom hn hs l0) = do
  let (allowed, what) = allowableHoms hu
  unless (hn `elem` allowed) $
    err l0 ("illegal hom " <> quote hn <> " for " <> what <> "  (the allowable homs here are " <> T.intercalate ", " allowed <> ")")
  els <- mapM cdHomEl (stripBlanks hs)
  pure (hn, agglomerate els)
  where
    stripBlanks = reverse . dropWhile isBlanks . reverse . dropWhile isBlanks
    isBlanks x = case x of
      R.HomBlanks _ -> True
      _ -> False
    agglomerate xs = case xs of
      HomString a : HomString b : more -> agglomerate (HomString (a <> b) : more)
      x : more -> x : agglomerate more
      [] -> []
    cdHomEl hse = case hse of
      R.HomString s -> pure (HomString s)
      R.HomBlanks s -> pure (HomString s)
      R.HomIdent ris ->
        case reverse (filter (not . isBlankish) ris) of
          [] -> err l0 ("hom inner must have either a singleton or a dot form in [[" <> T.concat ris <> "]]")
          (ident : fvsRev) ->
            let fvs = reverse fvsRev
             in pure $ case (indexOfIdent ident es 0, mapM (\i -> indexOfIdent i es 0) fvs) of
                  (Just inx, Just fvis)
                    | null fvs -> HomIndex inx
                    | otherwise -> HomLnFreeIndex fvis inx
                  _ -> HomTerminal ident
      R.HomIdentDots ris1 n ris2 -> do
        let reconstructed = T.concat ris1 <> dotsText n <> T.concat ris2
        unless (hn `elem` listFormAllowableHoms) $
          err l0 ("hom " <> quote hn <> " cannot refer to a dot form (the only homs here that can are " <> T.intercalate ", " listFormAllowableHoms <> ")")
        let res = map R.EIdent (filter (not . isBlankish) ris1) ++ [R.EDots n] ++ map R.EIdent (filter (not . isBlankish) ris2)
        inner <- cdElements c l0 res
        lb <- case inner of
          [ListForm lb] -> pure lb
          _ -> err l0 ("hom inner [[" <> reconstructed <> "]] is not a single dot form")
        case lbSeparator lb of
          Nothing -> pure ()
          Just tm -> err l0 ("hom inner [[" <> reconstructed <> "]] should not have any terminals (here " <> quote tm <> ")")
        case indexOfDotform lb es 0 of
          Just i -> pure (HomIndex i)
          Nothing -> err l0 ("dotform hom inner [[" <> reconstructed <> "]] not found in production")
      R.HomIdentComp ris1 rcb -> do
        (b, ivr) <- cdCompBound c l0 rcb
        let reconstructed = "</" <> T.concat ris1 <> "//" <> ppBound b <> "/>"
        unless (hn `elem` listFormAllowableHoms) $
          err l0 ("hom " <> quote hn <> " cannot refer to a list form (the only homs here that can are " <> T.intercalate ", " listFormAllowableHoms <> ")")
        inner0 <- cdElements c l0 (map R.EIdent (filter (not . isBlankish) ris1))
        inner <- mapM (abstractIndexvarElement l0 ivr 0) inner0
        let lb = ListBody (Just b) Nothing inner
        case indexOfDotform lb es 0 of
          Just i -> pure (HomIndex i)
          Nothing -> err l0 ("dotform hom inner [[" <> reconstructed <> "]] not found in production")

dotsText :: Int -> Text
dotsText n = T.replicate (n + 2) "."

-- | The position of a named element among the non-terminal elements.
indexOfIdent :: Text -> [Element] -> Int -> Maybe Int
indexOfIdent s es i = case es of
  [] -> Nothing
  e : more -> case e of
    Nonterm _ n suff
      | s == n <> ppSuffix suff -> Just i
      | otherwise -> indexOfIdent s more (i + 1)
    Metavar _ m suff
      | s == m <> ppSuffix suff -> Just i
      | otherwise -> indexOfIdent s more (i + 1)
    Terminal _ -> indexOfIdent s more i
    ListForm _ -> indexOfIdent s more (i + 1)

indexOfDotform :: ListBody -> [Element] -> Int -> Maybe Int
indexOfDotform lb es i = case es of
  [] -> Nothing
  e : more -> case e of
    Nonterm {} -> indexOfDotform lb more (i + 1)
    Metavar {} -> indexOfDotform lb more (i + 1)
    Terminal _ -> indexOfDotform lb more i
    ListForm lb'
      | lbBound lb == lbBound lb' && filterEs (lbElements lb) == filterEs (lbElements lb') -> Just i
      | otherwise -> indexOfDotform lb more (i + 1)
  where
    filterEs = mapMaybe filterE
    filterE e = case e of
      Terminal _ -> Nothing
      ListForm b -> Just (ListForm b {lbElements = filterEs (lbElements b)})
      _ -> Just e

-- | The combined homs @ic@, @ih@, @ch@, @ich@, @icho@, @ichl@ and @ichlo@
-- stand for several targets.
expandIcho :: [Hom] -> [Hom]
expandIcho = concatMap expand
  where
    expand (hn, hs) = case hn of
      "ic" -> [("isa", hs), ("coq", hs)]
      "ih" -> [("isa", hs), ("hol", hs)]
      "ch" -> [("hol", hs), ("coq", hs)]
      "ich" -> [("isa", hs), ("hol", hs), ("coq", hs)]
      "icho" -> [("isa", hs), ("hol", hs), ("coq", hs), ("ocaml", hs)]
      "ichl" -> [("isa", hs), ("hol", hs), ("coq", hs), ("lem", hs)]
      "ichlo" -> [("isa", hs), ("hol", hs), ("coq", hs), ("lem", hs), ("ocaml", hs)]
      _ -> [(hn, hs)]

------------------------------------------------------------------------
-- Binding specifications (cd_mse, cd_bindspec)

cdMse :: Ctx -> TextRange -> R.Mse -> Check Mse
cdMse c r m = case m of
  R.MseVar s -> do
    t <- lexOne c r s
    case t of
      Just (TokMetavar mv suff) -> pure (MetaVarExp (mv, suff))
      Just (TokNonterm nt suff) -> pure (NonTermExp (nt, suff))
      Nothing -> err r ("MSE: " <> quote s <> " is not a metavar or nonterm")
  R.MseDots s1 n s2 -> do
    t1 <- lexOne c r s1
    t2 <- lexOne c r s2
    case (t1, t2) of
      (Just (TokMetavar mv suff), Just (TokMetavar mv' suff')) ->
        case mergeNamed n (mv, suff) (mv', suff') of
          Just (b, mv'') -> pure (MetaVarListExp mv'' b)
          Nothing -> err r ("MSE: no nontrivial bound for metavars " <> mv <> ppSuffix suff <> " and " <> mv' <> ppSuffix suff')
      (Just (TokNonterm nt suff), Just (TokNonterm nt' suff')) ->
        case mergeNamed n (nt, suff) (nt', suff') of
          Just (b, nt'') -> pure (NonTermListExp nt'' b)
          Nothing -> err r ("MSE: no nontrivial bound for nonterms " <> nt <> ppSuffix suff <> " and " <> nt' <> ppSuffix suff')
      _ -> err r "MSE: not a metavar or nonterm"
  R.MseComp s1 rcb -> do
    (b, ivr) <- cdCompBound c r rcb
    t <- lexOne c r s1
    case t of
      Just (TokMetavar mv suff) -> do
        suff' <- abstractLinear ivr mv suff "metavar"
        pure (MetaVarListExp (mv, suff') b)
      Just (TokNonterm nt suff) -> do
        suff' <- abstractLinear ivr nt suff "nonterm"
        pure (NonTermListExp (nt, suff') b)
      Nothing -> err r "MSE: not a metavar or nonterm"
  R.MseAux f nt -> do
    t <- lexOne c r nt
    case t of
      Just (TokNonterm n suff) -> pure (Aux f (n, suff))
      _ -> err r ("MSE: not a nonterm in application of auxiliary " <> f)
  R.MseAuxDots f nt1 n nt2 -> do
    t1 <- lexOne c r nt1
    t2 <- lexOne c r nt2
    case (t1, t2) of
      (Just (TokNonterm a suff), Just (TokNonterm a' suff')) ->
        case mergeNamed n (a, suff) (a', suff') of
          Just (b, nt'') -> pure (AuxList f nt'' b)
          Nothing -> err r ("MSE: no nontrivial bound for nonterms " <> a <> ppSuffix suff <> " and " <> a' <> ppSuffix suff')
      _ -> err r ("MSE: auxiliary " <> f <> " applied to a dot form which does not consist of two nonterms")
  R.MseAuxComp f nt1 rcb -> do
    (b, ivr) <- cdCompBound c r rcb
    t <- lexOne c r nt1
    case t of
      Just (TokNonterm n suff) -> do
        suff' <- abstractLinear ivr n suff "nonterm"
        pure (AuxList f (n, suff') b)
      _ -> err r ("MSE: auxiliary " <> f <> " applied to a list form which does not consist of a nonterm")
  R.MseUnion a b -> Union <$> cdMse c r a <*> cdMse c r b
  R.MseEmpty -> pure Empty
  where
    abstractLinear ivr root suff what = case abstractIndexvarSuffix ivr 0 suff of
      Abstracted s -> pure s
      NotLinear -> err r ("MSE: indexvar " <> quote ivr <> " does not occur linearly in " <> what <> root <> ppSuffix suff)
    -- Ott's merge_metavar / merge_nonterm
    mergeNamed n (root, suff) (root', suff')
      | root /= root' = Nothing
      | otherwise = do
          (pbo, suff'') <- mergeSuffix 0 suff suff'
          (lo, up) <- pbo
          Just (BoundDotform lo up n, (root, suff''))

cdBindspec :: Ctx -> R.Bindspec -> Check Bindspec
cdBindspec c b = case b of
  R.Bind m nt r -> do
    t <- lexOne c r nt
    case t of
      Just (TokNonterm n suff) -> do
        m' <- cdMse c r m
        pure (Bind m' (n, suff) r)
      _ -> err r ("bindspec must have a nonterminal on the right hand side, not " <> quote nt)
  R.AuxFnDef f m r -> (\m' -> AuxFnDef f m' r) <$> cdMse c r m
  R.NamesEqual m m' r -> NamesEqual <$> cdMse c r m <*> cdMse c r m' <*> pure r
  R.NamesDistinct m m' r -> NamesDistinct <$> cdMse c r m <*> cdMse c r m' <*> pure r
  R.AllNamesDistinct m r -> (\m' -> AllNamesDistinct m' r) <$> cdMse c r m

------------------------------------------------------------------------
-- Productions, rules, metavariables (cd_prod, cd_rule, cd_metavarrep)

cdProd :: Ctx -> Text -> Text -> R.Prod -> Check Prod
cdProd c rn prefix p = do
  es <- cdElements c (R.prodRange p) (R.prodElements p)
  let hu = if rn == "terminals" then HuProdTm else HuProd
      cats = R.prodCategories p
      sugar = "S" `elem` cats
      meta = sugar || "M" `elem` cats
      funmeta = "F" `elem` cats
      name = prefix <> R.prodName p
  homs0 <- mapM (cdHom hu c es) (R.prodHoms p)
  let homs = cdOrder funmeta name (R.prodName p) es (expandIcho homs0)
  disamb <- cdDisambiguate name (R.prodHoms p) homs
  bs <- mapM (cdBindspec c) (R.prodBindspecs p)
  when (meta && rn /= "terminals") $
    when ("order" `elem` map fst homs && not funmeta) $
      err (R.prodRange p) "illegal hom \"order\" in meta or sugar production"
  pure
    Prod
      { prodName = name
      , prodMeta = meta
      , prodSugar = sugar
      , prodCategories = Set.fromList cats
      , prodElements = es
      , prodHoms = filter ((/= "disambiguate") . fst) homs
      , prodDisambiguate = disamb
      , prodBindspecs = bs
      , prodRange = R.prodRange p
      }

cdDisambiguate :: Text -> [R.Hom] -> [Hom] -> Check (Maybe (Text, Text))
cdDisambiguate name rawHoms homs = case (find ((== "disambiguate") . R.homName) rawHoms, lookup "disambiguate" homs) of
  (Just rh, Just els) -> case els of
    [] -> pure (Just (":" <> name <> ":", ""))
    [HomString s] -> case T.words s of
      [] -> pure (Just (":" <> name <> ":", ""))
      [x] -> pure (Just (x, ""))
      [x, y] -> pure (Just (x, y))
      _ -> bad rh
    _ -> bad rh
  _ -> pure Nothing
  where
    bad rh = err (R.homRange rh) "invalid argument to disambiguate hom (must be '' or '<terminal>' or '<terminal> <terminal>')"

-- | The homs the @order@ hom and the @F@ category add.
cdOrder :: Bool -> Text -> Text -> [Element] -> [Hom] -> [Hom]
cdOrder funmeta name kernel es homs
  | funmeta =
      let oh = case lookup "order" homs of
            Just hs -> [h | h@(HomIndex _) <- hs]
            Nothing -> map HomIndex [0 .. countNamed - 1]
          wrap' = [HomString ("(" <> kernel)] ++ oh ++ [HomString ")"]
       in filter ((/= "order") . fst) homs
            ++ [("coq", wrap'), ("lem", wrap'), ("isa", wrap'), ("hol", wrap'), ("ocaml", wrap'), ("order", oh)]
  | otherwise = case lookup "order" homs of
      Nothing -> homs
      Just hs ->
        let oh = [h | h@(HomIndex _) <- hs]
            wrap' = [HomString ("(" <> name)] ++ oh ++ [HomString ")"]
            ofS = if null oh then "" else " of "
            holH = [HomString ("(" <> name <> ofS)] ++ oh ++ [HomString ")"]
            camlH = [HomString ("(" <> name)] ++ bracketCommas oh ++ [HomString ")"]
         in homs ++ [("coq", wrap'), ("isa", wrap'), ("hol", holH), ("ocaml", camlH), ("lem", wrap')]
  where
    countNamed = length [() | e <- es, isNamed e]
    isNamed e = case e of
      Nonterm {} -> True
      Metavar {} -> True
      _ -> False
    bracketCommas xs = case xs of
      [] -> []
      [x] -> [x]
      _ -> HomString "(" : goComma xs ++ [HomString ")"]
    goComma xs = case xs of
      [] -> []
      [x] -> [x]
      x : more -> x : HomString "," : goComma more

cdRule :: Ctx -> [Text] -> [Text] -> XRule -> Check Rule
cdRule c judgementRoots srsLowers r = do
  let semiMeta =
        "defnclass" `elem` xCategories r
          || "fundefnclass" `elem` xCategories r
          || xName r `elem` ["judgement", "formula", "terminals", "user_syntax"]
      judgement = xName r `elem` judgementRoots
      self = [Nonterm (xName r) (xName r) []]
  homs0 <- mapM (cdHom (if semiMeta then HuRuleMeta else HuRule) c self) (xHoms r)
  let homs
        | xName r == "formula" =
            [("coq", [HomString "Prop"]), ("hol", [HomString "bool"]), ("lem", [HomString "bool"]), ("isa", [HomString "bool"]), ("ocaml", [HomString "bool"])]
        | otherwise = expandIcho homs0
      phantom = isJust (lookup "phantom" homs) || xName r == "formula"
  names <- forM (xNames r) $ \(n, hs) -> (,) n <$> mapM (cdHom HuRoot c []) hs
  prods <- mapM (cdProd c (xName r) (xPrefix r)) (xProds r)
  pure
    Rule
      { ruleName = xName r
      , ruleNames = names
      , rulePrefix = xPrefix r
      , ruleProds = prods
      , ruleHoms = homs
      , ruleMeta = semiMeta || xName r `elem` srsLowers || phantom
      , ruleSemiMeta = semiMeta
      , rulePhantom = phantom
      , ruleJudgement = judgement
      , ruleCategories = xCategories r
      , ruleRange = xRange r
      }

cdMetavardefn :: Ctx -> R.MetavarDefn -> Check MetavarDefn
cdMetavardefn c md = do
  let name = primaryMvdName md
  rep <- mapM (cdHom HuMetavar c [Metavar name name []]) (R.mvdHoms md)
  names <- forM (R.mvdNames md) $ \(n, hs) -> (,) n <$> mapM (cdHom HuRoot c []) hs
  let ln = isJust (lookup "repr-locally-nameless" rep)
      rep' = if ln then ("coq", [HomString "var"]) : rep else rep
      phantom = (ln && name == "var") || isJust (lookup "phantom" rep)
  pure
    MetavarDefn
      { mvdName = name
      , mvdNames = names
      , mvdHoms = rep'
      , mvdIndexvar = R.mvdIndexvar md
      , mvdLocallyNameless = ln
      , mvdPhantom = phantom
      , mvdRange = R.mvdRange md
      }

------------------------------------------------------------------------
-- Subrules and the other declarations

cdSubrules :: Ctx -> [R.Subrule] -> Check ([Subrule], SubruleData)
cdSubrules c rsrs = do
  srs0 <- forM rsrs $ \sr -> do
    let bad = err (R.srRange sr) ("undefined nonterminal root (" <> R.srLower sr <> " or " <> R.srUpper sr <> ") used in subgrammar declaration")
    lo <- maybe bad pure (cPrimaryNtr c (R.srLower sr))
    hi <- maybe bad pure (cPrimaryNtr c (R.srUpper sr))
    homs <- mapM (cdHom HuSubrule c []) (R.srHoms sr)
    pure (Subrule lo hi "" homs (R.srRange sr))
  let nodes = nub (concat [[srLower s, srUpper s] | s <- srs0])
      edges0 = Set.fromList [(srLower s, srUpper s) | s <- srs0]
      close es =
        let l = Set.toList es
            new = Set.fromList [(a, d) | (a, b) <- l, (c', d) <- l, b == c']
            es' = Set.union es new
         in if es' == es then es else close es'
      tc = Set.toList (close edges0)
      cycles = [a | (a, b) <- tc, a == b]
      firstRange = case srs0 of
        (s : _) -> srRange s
        [] -> error "cdSubrules: no subrules"
  unless (null cycles) $
    err firstRange ("subrule order has a cycle containing: " <> T.unwords (map quote cycles))
  let tops = [n | n <- nodes, not (any ((== n) . fst) tc)]
      topsAbove n = [b | (a, b) <- tc, a == n, b `elem` tops]
  forM_ nodes $ \n -> case topsAbove n of
    _ : _ : _ -> err firstRange ("subrule order has multiple tops above " <> quote n <> ", ie " <> T.unwords (map quote (topsAbove n)))
    _ -> pure ()
  let promote n = if n `elem` tops then n else fromMaybe n (listToMaybe (topsAbove n))
      srs1 = [s {srTop = promote (srUpper s)} | s <- srs0]
      psd = [(n, [a | (a, b) <- tc, b == n]) | n <- nodes]
  pure (srs1, SubruleData psd tc)

cdContextrule :: Ctx -> R.Contextrule -> Check Contextrule
cdContextrule c cr = do
  let bad = err (R.crRange cr) "undefined nonterminal root used in context rule declaration"
      resolve n = maybe bad pure (cPrimaryNtr c n)
  Contextrule <$> resolve (R.crNtr cr) <*> resolve (R.crTarget cr) <*> resolve (R.crHole cr) <*> pure (R.crRange cr)

cdSubst :: Ctx -> [Subrule] -> R.Substitution -> Check Substitution
cdSubst c srs sb = do
  let l = R.sbRange sb
  this <- maybe (err l ("undefined nonterminal root " <> quote (R.sbThis sb) <> " used in substitution declaration")) pure (cPrimaryNtr c (R.sbThis sb))
  when (any ((== this) . srLower) srs) $
    err l ("nonterminal root " <> quote (R.sbThis sb) <> " of a subrule used in substitution declaration")
  that <- thatRoot c srs l (R.sbThat sb) "substitution declaration" "substitution declaration"
  homs <- mapM (cdHom HuSubst c []) (R.sbHoms sb)
  pure (Substitution (R.sbName sb) this that (R.sbMultiple sb) homs l)

cdFreevar :: Ctx -> [Subrule] -> R.Freevar -> Check Freevar
cdFreevar c srs fv = do
  let l = R.fvRange fv
  this <- maybe (err l ("undefined nonterminal root " <> quote (R.fvThis fv) <> " used in freevar declaration")) pure (cPrimaryNtr c (R.fvThis fv))
  when (any ((== this) . srLower) srs) $
    err l ("nonterminal root " <> quote (R.fvThis fv) <> " of a subrule used in freevar declaration")
  that <- thatRoot c srs l (R.fvThat fv) "freevars declaration" "freevars declaration"
  homs <- mapM (cdHom HuFreevar c []) (R.fvHoms fv)
  pure (Freevar (R.fvName fv) this that homs l)

thatRoot :: Ctx -> [Subrule] -> TextRange -> Text -> Text -> Text -> Check RootRef
thatRoot c srs l that whatSub whatUndef = case cPrimaryMvr c that of
  Just m -> pure (Mvr m)
  Nothing -> case cPrimaryNtr c that of
    Just n -> do
      when (any ((== n) . srLower) srs) $
        err l ("nonterminal root " <> quote that <> " of a subrule used in " <> whatSub)
      pure (Ntr n)
    Nothing -> err l ("undefined nonterm or metavar root " <> quote that <> " used in " <> whatUndef)

cdEmbed :: R.Embed -> Check Embed
cdEmbed e = do
  unless (R.embedName e `elem` embedAllowableHoms) $
    err (R.embedRange e) ("illegal hom " <> quote (R.embedName e) <> " for embed (the allowable homs here are " <> T.intercalate ", " embedAllowableHoms <> ")")
  pure (Embed (R.embedName e) (R.embedSpec e) (R.embedRange e))

cdParsingAnnotation :: [Text] -> R.ParsingAnnotation -> Check ParsingAnnotation
cdParsingAnnotation allProdNames pa = do
  forM_ [R.paLeft pa, R.paRight pa] $ \pn ->
    unless (pn `elem` allProdNames) $
      err (R.paRange pa) ("undefined prodname " <> quote pn <> " used in parsing annotation declaration")
  pure (ParsingAnnotation (R.paLeft pa) (R.paOperator pa) (R.paRight pa) (R.paRange pa))

cdDefnClass :: Ctx -> R.DefnClass -> Check DefnClass
cdDefnClass c dc = do
  homs <- mapM (cdHom HuDeadcode c []) [] -- the class homs are checked by the back ends (Hu_defnclass)
  defns <- forM (R.dcDefns dc) $ \d -> do
    es <- cdElements c (R.dRange d) (R.dElements d)
    dhoms <- mapM (cdHom HuDefn c es) (R.dHoms d)
    pure (Defn (R.dName d) (R.dWrapper d) es (R.dCategories d) dhoms (R.dBody d) (R.dRange d))
  pure (DefnClass (R.dcName dc) (R.dcWrapper dc) (homs ++ rawHoms (R.dcHoms dc)) defns (R.dcRange dc))
  where
    rawHoms = map (\h -> (R.homName h, [HomString (T.concat (map rawText (R.homSpec h)))]))
    rawText el = case el of
      R.HomString s -> s
      R.HomBlanks s -> s
      _ -> ""

cdFunClass :: Ctx -> [XRule] -> R.FunClass -> Check FunClass
cdFunClass c rules fc = do
  defns <- forM (R.fcDefns fc) $ \fd -> do
    es <- cdElements c (R.fdRange fd) (R.fdElements fd)
    homs <- mapM (cdHom HuFundefn c es) (R.fdHoms fd)
    let r = find (\x -> R.fdResult fd `elem` map fst (xNames x)) rules
    pure
      FunDefn
        { fdName = R.fdName fd
        , fdElements = es
        , fdResult = maybe (R.fdResult fd) xName r
        , fdResultPrefix = maybe "" xPrefix r
        , fdHoms = homs
        , fdClauses = R.fdClauses fd
        , fdRange = R.fdRange fd
        }
  pure (FunClass (R.fcName fc) [] defns (R.fcRange fc))

------------------------------------------------------------------------
-- Step 10 (the part implemented)

checkSpec :: [Subrule] -> [Rule] -> [(Text, Text)] -> Check ()
checkSpec srs rules auxfns = do
  let allProdNames = [(prodName p, prodRange p) | r <- rules, p <- ruleProds r]
  case firstDuplicateBy fst allProdNames of
    Just (pn, l) -> err l ("production name " <> quote pn <> " is used for multiple productions")
    Nothing -> pure ()
  forM_ rules $ \r -> do
    case firstDuplicateBy prodName (ruleProds r) of
      Just p -> err (prodRange p) ("Repeated production name " <> quote (prodName p))
      Nothing -> pure ()
    unless (ruleMeta r) $
      forM_ (ruleProds r) $ \p ->
        if prodMeta p
          then unless (null (prodBindspecs p)) $ err (prodRange p) "nonempty bindspec in a meta or sugar production"
          else do
            forM_ (prodBindspecs p) (tBindspec (prodElements p) (prodRange p))
            let here = sort [f | AuxFnDef f _ _ <- prodBindspecs p]
                should = sort [f | (f, n) <- auxfns, n == ruleName r]
            when (here /= should) $
              err (prodRange p) ("auxiliaries are not uniquely defined in production " <> prodName p)
  case firstDuplicateBy ruleName rules of
    Just r -> err (ruleRange r) ("repeated rule name " <> ruleName r)
    Nothing -> pure ()
  forM_ rules $ \r ->
    when (ruleSemiMeta r && any (\s -> srLower s == ruleName r || srUpper s == ruleName r) srs) $
      err (ruleRange r) ("cannot have semi-meta rule " <> quote (ruleName r) <> " in a subrule relationship")
  where
    promote n = maybe n srTop (find ((== n) . srLower) srs)
    primaryOf = id -- roots in the checked elements are already primary where it matters
    ntIn es (p, nt, pe) = (p, nt, pe) `elem` ntsUsed [] es
    mvIn es (p, mv, pe) = (p, mv, pe) `elem` mvsUsed [] es
    primaryNtrIn es n = case [p | (p, (n', _), _) <- ntsUsed [] es, n' == n] of
      (p : _) -> p
      [] -> primaryOf n
    primaryMvrIn es m = case [p | (p, (m', _), _) <- mvsUsed [] es, m' == m] of
      (p : _) -> p
      [] -> m
    tMse es l m = case m of
      MetaVarExp mv@(mvr, suff) ->
        unless (mvIn es (primaryMvrIn es mvr, mv, [])) $
          err l ("metavariable " <> mvr <> ppSuffix suff <> " in MSE not in scope")
      NonTermExp nt@(ntr, suff) ->
        unless (ntIn es (primaryNtrIn es ntr, nt, [])) $
          err l ("nonterminal " <> ntr <> ppSuffix suff <> " in MSE not in scope")
      MetaVarListExp mv@(mvr, suff) b ->
        unless (mvIn es (primaryMvrIn es mvr, mv, [Just b])) $
          err l ("Metavariable " <> mvr <> ppSuffix suff <> " in MSE not in scope")
      NonTermListExp nt@(ntr, suff) b ->
        unless (ntIn es (primaryNtrIn es ntr, nt, [Just b])) $
          err l ("Nonterminal " <> ntr <> ppSuffix suff <> " in MSE not in scope")
      Aux f nt@(ntr, suff) -> do
        unless (ntIn es (primaryNtrIn es ntr, nt, [])) $
          err l ("Nonterminal " <> ntr <> ppSuffix suff <> " in MSE not in scope")
        unless (any (\(f', n') -> f == f' && promote (primaryNtrIn es ntr) == n') auxfns) $
          err l ("Auxiliary " <> f <> " in MSE not defined over nonterminal root " <> ntr)
      AuxList f nt@(ntr, suff) b -> do
        unless (ntIn es (primaryNtrIn es ntr, nt, [Just b])) $
          err l ("nonterminal " <> ntr <> ppSuffix suff <> " in MSE not in scope")
        unless (any (\(f', n') -> f == f' && promote (primaryNtrIn es ntr) == n') auxfns) $
          err l ("auxiliary " <> f <> " in MSE not defined over nonterminal root " <> ntr)
      Union a b -> tMse es l a >> tMse es l b
      Empty -> pure ()
    tBindspec es l b = case b of
      Bind m nt@(ntr, suff) _ -> do
        tMse es l m
        unless (ntIn es (primaryNtrIn es ntr, nt, [])) $
          err l ("nonterminal " <> ntr <> ppSuffix suff <> " in MSE not in scope")
        when (isNullMse m) $ err l "manifestly null mse"
      AuxFnDef _ m _ -> tMse es l m
      NamesEqual m m' _ -> tMse es l m >> tMse es l m'
      NamesDistinct m m' _ -> tMse es l m >> tMse es l m'
      AllNamesDistinct m _ -> tMse es l m
    isNullMse m = case m of
      Union a b -> isNullMse a && isNullMse b
      Empty -> True
      _ -> False

firstDuplicateBy :: Eq k => (a -> k) -> [a] -> Maybe a
firstDuplicateBy key xs = case xs of
  [] -> Nothing
  x : more -> if any ((== key x) . key) more then Just x else firstDuplicateBy key more
