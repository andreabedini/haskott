{-# LANGUAGE OverloadedStrings #-}

-- | Ott's locally nameless back end for Coq (@ln_transform.ml@ and the
-- locally nameless path of @system_pp.ml@), used when a metavariable has a
-- @repr-locally-nameless@ hom.
--
-- The syntax is transformed before it is printed: each production made of
-- a bindable metavariable alone is split into a bound variable (a de
-- Bruijn index, @_b@) and a free one (@_f@), binders are erased from the
-- productions that bind them, meta productions for opening a term with
-- respect to each kind of variable are added, with local closure
-- judgements and cofinite quantification. The rules of the definitions are
-- transformed to match: a nonterminal under a binder is opened with a
-- fresh variable, and each premise so opened is cofinitely quantified.
-- Then come the functions opening terms, the local closure relations, free
-- variables, substitutions, the definitions and hints.
module Haskott.Prover.LocallyNameless
  ( requireLocallyNameless
  , LnJob (..)
  , lnOutput
  ) where

import Control.Monad (forM, unless, when)
import Control.Monad.Trans.State.Strict (get, modify)
import Data.List (find, partition)
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Graft (TextRange)
import qualified Graft.Range as Range
import Haskott.Defns
import Haskott.Prover.Bounds
import Haskott.Prover.CoqInduct
import Haskott.Prover.Defns
import Haskott.Prover.Dependency
import Haskott.Prover.Pp
import Haskott.Prover.Subrules
import Haskott.Prover.Substs
import Haskott.Prover.Transform (freshNt)
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

-- | Ott's @require_locally_nameless@.
requireLocallyNameless :: Spec -> Bool
requireLocallyNameless spec = any (isJust . lookup "repr-locally-nameless" . mvdHoms) (specMetavars spec)

-- | What the locally nameless output needs beyond the environment.
data LnJob = LnJob
  { lnSources :: Text
  -- ^ the source files, as Ott names them in the header
  , lnProcessed :: Processed
  , lnGrammarNonterminals :: Spec -> Int
  -- ^ the nonterminals of the term grammar of a specification: Ott builds
  -- a term parser for the transformed syntax, which adds them to
  -- ocamlgraph's vertex counter
  , lnEmbed :: Env -> Embed -> P Text
  -- ^ the printer of embeds
  }

oops :: String -> a
oops m = error ("Haskott.Prover.LocallyNameless: " ++ m)

dummyRange :: TextRange
dummyRange = fromMaybe (oops "range") (Range.fromEnds 0 0)

------------------------------------------------------------------------
-- Library

ntmvrlistToNtrlist :: [RootRef] -> [Text]
ntmvrlistToNtrlist l = [n | Ntr n <- l]

-- | The rules reachable from a rule, in the dependency graph's order.
reachable :: Env -> Text -> [Text]
reachable env ntr = ntmvrlistToNtrlist (fromMaybe (oops ("no dependencies of " ++ T.unpack ntr)) (lookup (Ntr ntr) (depGraph (envDeps env))))

collectMvInMse :: Mse -> [(Text, Suffix)]
collectMvInMse mse = case mse of
  MetaVarExp mv -> [mv]
  Union a b -> collectMvInMse a ++ collectMvInMse b
  _ -> []

-- | Ott's @defined_rule@: a rule printed as a type.
definedRule :: Env -> Rule -> Bool
definedRule env r = not (ruleMeta r) && homSpecForTarget env (ruleHoms r) == Nothing

openName :: Env -> Bool -> Text -> Text -> Text
openName env b ntr wrt = "open_" <> promoteNtr env ntr <> "_wrt_" <> promoteNtr env wrt <> (if b then "_rec" else "")

arityName :: Text -> Text -> Text
arityName f ntr = "arity_" <> f <> "_" <> ntr

lnMvrs :: Spec -> [Text]
lnMvrs spec = [mvdName md | md <- specMetavars spec, mvdLocallyNameless md]

-- | The binders of a production.
binders :: Prod -> [(Text, Suffix)]
binders p = concat (mapMaybe b (prodBindspecs p))
  where
    b bs = case bs of
      Bind (MetaVarExp mv) _ _ -> Just [mv]
      AuxFnDef _ mse _ -> Just (collectMvInMse mse)
      _ -> Nothing

bindersForNt :: Prod -> (Text, Suffix) -> [(Text, Suffix)]
bindersForNt p nt = concat [[mv] | Bind (MetaVarExp mv) nt1 _ <- prodBindspecs p, nt1 == nt]

-- | Ott's @is_bindable@.
isBindable :: Env -> (Text, Suffix) -> Prod -> Bool
isBindable env mv p =
  let md = mvdOfMvr env (primaryMvrOfMvr env (fst mv))
   in mvdLocallyNameless md && mv `notElem` binders p

-- | The metavariable a production consists of, when it is bindable.
bindableSingleton :: Env -> Prod -> Maybe Text
bindableSingleton env p = case prodElements p of
  [Metavar mvr1 m s] | isBindable env (m, s) p -> Just mvr1
  _ -> Nothing

rulesWithBindableMvr :: Env -> Text -> [Rule]
rulesWithBindableMvr env mvr =
  [r | r <- specRules (envSpec env), not (ruleMeta r), any (\p -> bindableSingleton env p == Just mvr) (ruleProds r)]

allRulesWithBindableMvr :: Env -> [(Text, Text)]
allRulesWithBindableMvr env = concat [[(mvr, ruleName r) | r <- rulesWithBindableMvr env mvr] | mvr <- lnMvrs (envSpec env)]

dependOnSplitted :: Env -> Text -> Text -> Bool
dependOnSplitted env ntr mvr = any (\n -> any (\p -> bindableSingleton env p == Just mvr) (ruleProds (ruleOfNtr env n))) (reachable env ntr)

alwaysLocallyClosed :: Env -> Text -> Bool
alwaysLocallyClosed env ntr = not (any (dependOnSplitted env ntr) (lnMvrs (envSpec env)))

boundByAuxfn :: Env -> Text -> Bool
boundByAuxfn env mvr = or [m == mvr | (_, (_, Mvr m)) <- envAuxfnTypes env]

secondaryNtr :: Env -> Text -> Text
secondaryNtr env ntr = case ruleNames (ruleOfNtrNonprimary env ntr) of
  [] -> oops "secondary_ntr, empty list of rule names"
  [_] -> ntr
  _ : (q, _) : _ -> q

------------------------------------------------------------------------
-- The transformed syntax

prod0 :: Text -> [Element] -> [Hom] -> Bool -> Prod
prod0 n es homs meta =
  Prod
    { prodName = n
    , prodMeta = meta
    , prodSugar = False
    , prodCategories = Set.empty
    , prodElements = es
    , prodHoms = homs
    , prodDisambiguate = Nothing
    , prodBindspecs = []
    , prodRange = dummyRange
    }

rule0 :: Text -> Text -> [Prod] -> Bool -> Bool -> Bool -> Rule
rule0 n prefix ps meta semiMeta phantom =
  Rule
    { ruleName = n
    , ruleNames = [(n, [])]
    , rulePrefix = prefix
    , ruleProds = ps
    , ruleHoms = []
    , ruleMeta = meta
    , ruleSemiMeta = semiMeta
    , rulePhantom = phantom
    , ruleJudgement = False
    , ruleCategories = []
    , ruleRange = dummyRange
    }

mvd0 :: Text -> [Text] -> Text -> MetavarDefn
mvd0 n names coq =
  MetavarDefn
    { mvdName = n
    , mvdNames = [(x, []) | x <- names]
    , mvdHoms = [("coq", [HomString coq])]
    , mvdIndexvar = False
    , mvdLocallyNameless = False
    , mvdPhantom = True
    , mvdRange = dummyRange
    }

isLnBinder :: Env -> Prod -> Element -> Bool
isLnBinder env p e = case e of
  Metavar mvr m s ->
    let isLn = maybe False mvdLocallyNameless (find ((== mvr) . mvdName) (specMetavars (envSpec env)))
     in isLn && (m, s) `elem` binders p
  _ -> False

-- | Ott's @ln_transform_rule@.
lnTransformRule :: Env -> Rule -> Rule
lnTransformRule env r =
  let split p = case prodElements p of
        [Metavar mvr _ _] | isJust (bindableSingleton env p) ->
          [ (prod0 (prodName p <> "_b") (if boundByAuxfn env mvr then [Metavar "nat" "nat" [SiNum "1"], Metavar "nat" "nat" [SiNum "2"]] else [Metavar "nat" "nat" []]) (("coq-ln_splitted", [HomString mvr]) : prodHoms p) (prodMeta p))
              { prodSugar = prodSugar p
              , prodCategories = prodCategories p
              , prodRange = prodRange p
              }
          , p {prodDisambiguate = Nothing, prodBindspecs = []}
              { prodName = prodName p <> "_f"
              }
          ]
        _ -> [p]
      splitProds = concatMap split (ruleProds r)
      erased = [p {prodElements = filter (not . isLnBinder env p) (prodElements p)} | p <- splitProds]
      makeOpen wrt =
        prod0
          (rulePrefix r <> "open_wrt_" <> wrt)
          [Terminal (openName env False (ruleName r) wrt), Nonterm wrt wrt [], Nonterm (ruleName r) (ruleName r) []]
          [("coq", [HomString "(", HomString (openName env False (ruleName r) wrt), HomIndex 0, HomIndex 1, HomString ")"])]
          True
      opens
        | definedRule env r =
            let bindable = map snd (allRulesWithBindableMvr env)
             in [makeOpen rd | rd <- reachable env (ruleName r), rd `elem` bindable]
        | otherwise = []
   in r {ruleProds = erased ++ opens}

findSplit :: Text -> [Rule] -> ([Rule], Rule, [Rule])
findSplit s rs = case break ((== s) . ruleName) rs of
  (before, r : after) -> (before, r, after)
  _ -> oops ("find-split not found: " ++ T.unpack s)

-- | Ott's @ln_transform_syntaxdefn@ without the dependencies.
lnTransformSyntaxdefn :: Env -> Spec
lnTransformSyntaxdefn env =
  let spec = envSpec env
      lngen = optCoqLngen (envOpts env)
      mvs =
        [mvd0 "var" ["var"] "var" | not (any ((== "var") . mvdName) (specMetavars spec))]
          ++ (mvd0 "nat" ["nat"] "nat" : mvd0 "vars" ["vars", "L"] "vars" : specMetavars spec)
      varSets =
        (rule0 "var_sets" "var_sets_" [prod0 "var_sets_vars" [Metavar "vars" "vars" []] [("coq", [HomIndex 0])] False, prod0 "var_sets_union" [Nonterm "var_sets" "var_sets" [], Terminal "union", Metavar "var" "var" []] [("coq", [HomIndex 0, HomString "\\u {{", HomIndex 1, HomString "}}"])] False] True True True)
      rules1 = varSets : map (lnTransformRule env) (specRules spec)
      -- the local closure judgements
      defined = [ruleName r | r <- rules1, definedRule env r]
      defLc ntr = rule0 ("def_lc_" <> ntr) "lc_" [prod0 ("lc_" <> ntr) [Terminal ("lc_" <> ntr), Nonterm ntr ntr []] [] False] True False False
      judgementProd ntr = prod0 ("judgement_def_lc_" <> ntr) [Nonterm ("def_lc_" <> ntr) ("def_lc_" <> ntr) []] [] False
      (r1, j, r2) = findSplit "judgement" rules1
      rules2 = r1 ++ [j {ruleProds = map judgementProd defined ++ ruleProds j}] ++ map defLc defined ++ r2
      -- cofinite (and, for lngen, universal) quantification
      lns = [mvdName md | md <- mvs, mvdLocallyNameless md]
      cofinite mvr =
        prod0
          ("formula_cofinite_formula_" <> mvr)
          [Terminal "cofin", Nonterm "var_sets" "var_sets" [], Metavar mvr mvr [], Nonterm "formula" "formula" []]
          [("coq", [HomString "(", HomString "forall", HomIndex 1, HomString ",", HomIndex 1, HomString "\\notin", HomIndex 0, HomString "->", HomIndex 2, HomString ")"])]
          False
      universal mvr =
        prod0
          ("formula_universal_formula_" <> mvr)
          [Terminal "univ", Metavar mvr mvr [], Nonterm "formula" "formula" []]
          [("coq", [HomString "(", HomString "forall", HomIndex 0, HomString ",", HomIndex 1, HomString ")"])]
          False
      addFormula mk rs = let (a, f, b) = findSplit "formula" rs in a ++ [f {ruleProds = ruleProds f ++ map mk lns}] ++ b
      rules3 = addFormula cofinite rules2
      rules4 = if lngen then addFormula universal rules3 else rules3
   in spec {specMetavars = mvs, specRules = rules4}

------------------------------------------------------------------------
-- Opening

-- | Ott's @nts_used_in_lhss@: the nonterminals of the canonical terms of
-- a rule's productions.
ntsUsedInLhss :: Rule -> [(Text, Suffix)]
ntsUsedInLhss r = concatMap (nts . canonicalNode (ruleName r)) (ruleProds r)
  where
    nts st = case st of
      StNode _ _ es -> concatMap ste es
      StNonterm _ nt -> [nt]
      StNontermSub _ _ nt -> [nt]
      StUninterpreted _ _ -> []
    ste e = case e of
      SteSt s -> nts s
      SteList items -> concatMap stli items
      _ -> []
    stli s = case s of
      StliSingle es -> concatMap ste es
      StliListform _ es -> concatMap ste es

bounds :: Env -> [Symterm] -> P (De, De3)
bounds env sts = either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env sts)

ppOpenSte :: Env -> Text -> Text -> [(Text, Suffix)] -> Text -> Suffix -> De -> Ste -> P (Text, [Text])
ppOpenSte env mvr wrt unshifted ov sie de ste = case ste of
  SteSt (StNonterm ntrp nt) -> do
    ntS <- ppNontermWithDeWithSie env sie de nt
    if dependOnSplitted env ntrp mvr
      then do
        let idCall = openName env True ntrp wrt
            sk = if nt `elem` unshifted then " (S k) " else " k "
        pure ("(" <> idCall <> sk <> ov <> " " <> ntS <> ")", [idCall])
      else pure (ntS, [])
  SteMetavar _ mv -> (\s -> (s, [])) <$> ppMetavarWithDeWithSie env sie de mv
  SteList [StliListform bound es] -> do
    let de1i = de1Lookup (fst de) bound
    parts <- mapM (ppOpenSte env mvr wrt unshifted ov (SiVar "_" 0 : sie) de) es
    let tmp = T.intercalate "," (map fst parts)
        body = if length es > 1 then "(" <> tmp <> ")" else tmp
        funcs = concatMap snd parts
    pure $
      if optCoqExpandLists (envOpts env)
        then ("<<internal: only Coq + native lists supported>>", [])
        else
          if length (splitParensCommas (de1Pattern de1i)) == 1
            then ("(map (fun (" <> de1Pattern de1i <> ":" <> de1CoqTypeOfPattern de1i <> ") => " <> body <> ") " <> de1CompoundId de1i <> ")", funcs)
            else ("(map (fun (pat_:" <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> de1Pattern de1i <> " => " <> body <> " end) " <> de1CompoundId de1i <> ")", funcs)
  _ -> pure (oops "pp_open_symterm_element: not canonical")

ppOpenProd :: Env -> Text -> Text -> Text -> Text -> Prod -> P ([Text], (Text, Text, Text))
ppOpenProd env mvr wrt ov ruleNtrName p = do
  let lhsSt = canonicalNode ruleNtrName p
      stEs = case lhsSt of
        StNode _ _ es -> es
        _ -> []
  (de, _) <- bounds env [lhsSt]
  lhs <- ppSymterm env [] de lhsSt
  let splits = case lookup "coq-ln_splitted" (prodHoms p) of
        Just [HomString mvr1] -> mvr == mvr1
        _ -> False
  (rhs, deps) <-
    if splits
      then case stEs of
        [SteMetavar _ mv] -> do
          mvS <- ppMetavarWithDeWithSie env [] de mv
          let s = prodName p
          pure $
            if optCoqLngen (envOpts env)
              then
                ( "\n      match lt_eq_lt_dec " <> mvS <> " k with\n"
                    <> "        | inleft (left _) => " <> s <> " " <> mvS <> "\n"
                    <> "        | inleft (right _) => " <> ov <> "\n"
                    <> "        | inright _ => " <> s <> " (" <> mvS <> " - 1)\n"
                    <> "      end"
                , []
                )
              else ("if (k === " <> mvS <> ") then " <> ov <> " else (" <> s <> " " <> mvS <> ")", [])
        [SteMetavar _ mv1, SteMetavar _ mv2] -> do
          mv1S <- ppMetavarWithDeWithSie env [] de mv1
          mv2S <- ppMetavarWithDeWithSie env [] de mv2
          let s = prodName p
          pure ("if (k === " <> mv1S <> ") then (List.nth " <> mv2S <> " " <> ov <> " " <> "(" <> prodName p <> " 0 0)" <> ") else (" <> s <> " " <> mv1S <> " " <> mv2S <> ")", [])
        _ -> failP "internal: weird lhs_stnb in pp_open_prod\n"
      else do
        let unshifted = [nt | Bind (MetaVarExp (mvr1, _)) nt _ <- prodBindspecs p, primaryMvrOfMvr env mvr1 == mvr]
        parts <- mapM (ppOpenSte env mvr wrt unshifted ov [SiVar "_" 0] de) stEs
        pure (prodName p <> " " <> T.unwords (map fst parts), concatMap snd parts)
  pure (deps, ("", lhs, rhs))

ppOpenRule :: Env -> Rule -> Text -> Text -> P [IntFunc]
ppOpenRule env r wrt mvr = do
  let ntsUsed = ntsUsedInLhss r
      var1 = freshNt ntsUsed (secondaryNtr env wrt, [])
      var2 = freshNt (var1 : ntsUsed) (secondaryNtr env (ruleName r), [])
      v1 = ppNonterm env var1
      v2 = ppNonterm env var2
  opened <- mapM (ppOpenProd env mvr wrt v1 (ruleName r)) (filter (not . prodMeta) (ruleProds r))
  let clauses = map snd opened
      dep = concatMap fst opened
      idRec = openName env True (ruleName r) wrt
      ident = openName env False (ruleName r) wrt
      header =
        ( idRec <> " (k:nat)" <> " (" <> v1 <> ":" <> (if boundByAuxfn env mvr then "list " else "") <> ppNontermrootTy env wrt
            <> ") (" <> v2 <> ":" <> ppNontermrootTy env (ruleName r) <> ") "
            <> (if idRec `elem` dep then "{struct " <> v2 <> "}" else "")
        , ""
        , ": " <> ppNontermrootTy env (ruleName r) <> " :=\n  match " <> v2 <> " with\n"
        )
  pure
    [ IntFunc idRec dep (ruleName r) header clauses
    , IntFunc ident [idRec] (ruleName r) (ident <> " " <> v1 <> " " <> v2 <> " := " <> idRec <> " 0 " <> v2 <> " " <> v1, "", "") []
    ]

-- | Ott's @pp_open@.
ppOpen :: Env -> P Collapsed
ppOpen env = do
  let pairs = allRulesWithBindableMvr env
  funcs <- fmap concat $ forM (specRules (envSpec env)) $ \r ->
    if definedRule env r
      then fmap concat $ forM [(mvr, ntr) | (mvr, ntr) <- pairs, ntr `elem` reachable env (ruleName r)] $ \(mvr, ntr) -> ppOpenRule env r ntr mvr
      else pure []
  pure (collapse env (IntFuncs funcs Nothing))

------------------------------------------------------------------------
-- Arities

ppArities :: Env -> Env -> P Collapsed
ppArities env envT = do
  funcs <- forM [(f, ntr) | (f, (ntrs, _)) <- envAuxfnTypes env, ntr <- ntrs] $ \(f, ntr) -> do
    let ident = arityName f ntr
        r = ruleOfNtr env ntr
        patVar = freshNt (ntsUsedInLhss r) (secondaryNtr env ntr, [])
        header =
          ( ident <> " (" <> ppNonterm env patVar <> ":" <> ppNontermrootTy env ntr <> ")"
          , ""
          , " : nat :=\n" <> "  match " <> ppNonterm env patVar <> " with\n"
          )
    cs <- forM (filter (not . prodMeta) (ruleProds (ruleOfNtr envT ntr))) $ \p -> do
      let lhsSt = canonicalNode ntr p
      (de, _) <- bounds envT [lhsSt]
      lhs <- ppSymterm envT [] de lhsSt
      let mse = case [m | AuxFnDef f' m _ <- prodBindspecs p, f' == f] of
            (m : _) -> m
            [] -> oops "pp_arity_prod: no mse"
          toRhs m = case m of
            Empty -> ("0", [])
            MetaVarExp _ -> ("1", [])
            -- Ott's typo, kept: both operands are the first
            Union m1 _ -> let (c1, d1) = toRhs m1 in ("(" <> c1 <> ") + (" <> c1 <> ")", d1 ++ d1)
            Aux f1 nt1 ->
              let nm = arityName f1 (promoteNtr envT (primaryNtrOfNtr envT (fst nt1)))
               in (nm <> " " <> ppNonterm envT nt1, [nm])
            _ -> oops "pp_arity_prod: mse"
          (rhs, deps) = toRhs mse
      pure (("", lhs, rhs), deps)
    pure (IntFunc ident (concatMap snd cs) ntr header (map fst cs))
  pure (collapse env (IntFuncs funcs Nothing))

------------------------------------------------------------------------
-- Local closure

-- | Ott's @required_ntc@: a group of rules needs a local closure
-- predicate when a rule of it, or a rule it reaches, splits a variable.
requiredNtc :: Env -> [RootRef] -> Bool
requiredNtc env ntc = any requiredNtr (ntmvrlistToNtrlist ntc)
  where
    requiredNtr ntr0 =
      let ntr = promoteNtr env (primaryNtrOfNtr env ntr0)
          splitted n = any (\p -> isJust (bindableSingleton env p)) (ruleProds (ruleOfNtr env n))
       in splitted ntr || any splitted (reachable env ntr)

stVarSetVars :: Ste
stVarSetVars = SteSt (StNode "var_sets" "var_sets_vars" [SteMetavar "vars" ("L", [])])

stVarSetUnion :: [Ste] -> Ste
stVarSetUnion mvrs = case mvrs of
  [] -> stVarSetVars
  m : more -> SteSt (StNode "var_sets" "var_sets_union" [stVarSetUnion more, m])

plainMetavar :: (Text, Suffix) -> Text
plainMetavar (m, s) = m <> T.concat (map ppPlainSuffixItem s)

buildTermCall :: Env -> Text -> Symterm -> Symterm
buildTermCall env ntr0 st =
  let ntr = promoteNtr env (primaryNtrOfNtr env ntr0)
   in StNode ("def_lc_" <> ntr) ("lc_" <> ntr) [SteSt st]

-- | Ott's @pp_lcs@: the local closure relations, as definition classes.
lcsClasses :: Env -> P [ProcessedItem]
lcsClasses env = do
  let lngen = optCoqLngen (envOpts env)
      makePremises r p = do
        let st = canonicalNode (ruleName r) p
            x = ntOrMvOfSymterms [st]
            nobounds = [(n, s) | (((Ntr n, s), _), Nothing) <- x]
            withBounds = [((n, s), b) | (((Ntr n, s), _), Just b) <- x]
        prem1 <- fmap concat $ forM nobounds $ \(ntr, s) -> do
          let ntrp = primaryNtrOfNtr env ntr
              mvs = bindersForNt p (ntr, s)
          when (length mvs > 1) $ failP "locally_nameless - not implemented: several mvs bind the same nt\n"
          case mvs of
            [mv] -> do
              let r' = ruleOfNtrNonprimary env ntr
                  mvp = primaryMvrOfMvr env (fst mv)
                  isVarProd p' = case prodElements p' of
                    [Metavar mv2 _ _] -> mvp == mv2
                    _ -> False
                  accessible = reachable env (ruleName r')
              prodS <- case find isVarProd (concatMap (ruleProds . ruleOfNtr env) accessible) of
                Just p' -> pure (prodName p')
                Nothing -> failP ("internal: lns, make_premises, cannot find singleton production for " <> fst mv <> " starting from rule " <> ruleName r' <> "\n")
              ruleS <- case find (any isVarProd . ruleProds) (map (ruleOfNtr env) accessible) of
                Just r'' -> pure (ruleName r'')
                Nothing -> pure (oops "find_var_rule")
              let var = SteVar (fst mv) (plainMetavar mv)
                  opened =
                    StNode ntr (rulePrefix (ruleOfNtr env ntrp) <> "open_wrt_" <> ruleS) [SteSt (StNonterm ntr (ntr, s)), SteSt (StNode ruleS prodS [var])]
                  judgement = StNode "formula" "formula_judgement" [SteSt (StNode "judgement" ("def_lc_" <> ntrp) [SteSt (StNode ("def_lc_" <> ntrp) ("lc_" <> ntrp) [SteSt opened])])]
              pure
                [ StNode
                    "formula"
                    ((if lngen then "formula_universal_formula_" else "formula_cofinite_formula_") <> mvp)
                    ((if lngen then [] else [stVarSetVars]) ++ [var, SteSt judgement])
                ]
            _
              | alwaysLocallyClosed env (primaryNtrOfNtr env ntr) -> pure []
              | otherwise -> pure [buildTermCall env ntr (StNonterm ntr (ntr, s))]
        let prem2 =
              [ StNode "formula" "formula_dots" [SteList [StliListform b [SteSt (buildTermCall env ntr (StNonterm ntr (ntr, s)))]]]
              | ((ntr, s), b) <- withBounds
              , not (alwaysLocallyClosed env (primaryNtrOfNtr env ntr))
              ]
        pure (prem1 ++ prem2)
      druleOf r p
        | isJust (lookup "coq-ln_splitted" (prodHoms p)) = pure Nothing
        | otherwise = do
            premises <- makePremises r p
            let conclusion = buildTermCall env (ruleName r) (canonicalNode (ruleName r) p)
            pure (Just (ItemRule (Drule ("lc_" <> prodName p) Set.empty [(Nothing, st) | st <- premises] conclusion [] dummyRange)))
      defnOf r = do
        let ntr = ruleName r
        rules <- fmap concat (mapM (fmap (maybe [] pure) . druleOf r) (filter (not . prodMeta) (ruleProds r)))
        pure (ProcessedDefn ("lc_" <> ntr) (buildTermCall env ntr (StNonterm ntr (ntr, []))) "lc_" rules [])
  fmap concat $ forM (filter (requiredNtc env) (depTs (envDeps env))) $ \ntcl -> do
    let rules = [r | r <- map (ruleOfNtr env) (ntmvrlistToNtrlist ntcl), not (ruleMeta r), homSpecForTarget env (ruleHoms r) == Nothing]
    case rules of
      [] -> pure []
      _ -> do
        defns <- mapM defnOf rules
        pure [PReln (ProcessedClass ("LC_" <> T.intercalate "_" (map ruleName rules)) "" defns)]

------------------------------------------------------------------------
-- The rules of the definitions

-- | Ott's @find_occurrence_mv@: the position of a metavariable among the
-- nonterminals and metavariables of the elements.
findOccurrenceMv :: [Element] -> Int -> (Text, Suffix) -> Maybe Int
findOccurrenceMv els c mv = case els of
  Metavar _ m s : tl -> if (m, s) == mv then Just c else findOccurrenceMv tl (c + 1) mv
  Nonterm {} : tl -> findOccurrenceMv tl (c + 1) mv
  _ : tl -> findOccurrenceMv els' c mv where els' = tl
  [] -> Nothing

findOccurrenceNt :: (Text, Suffix) -> [Element] -> Int -> Maybe Int
findOccurrenceNt nt els o = case els of
  Nonterm _ n s : tl -> if (n, s) == nt then Just o else findOccurrenceNt nt tl (o + 1)
  Metavar {} : tl -> findOccurrenceNt nt tl (o + 1)
  _ : tl -> findOccurrenceNt nt tl o
  [] -> Nothing

occStes :: [Ste] -> [(Ste, Int)]
occStes es = zip es [1 ..]

plainSte :: Ste -> Text
plainSte ste = case ste of
  SteSt st -> ppPlainSymterm st
  SteMetavar _ mv -> "(Ste_metavar " <> plainMetavar mv <> ")"
  SteVar _ v -> "(Ste_var " <> v <> ")"
  SteList _ -> "(Ste_list)"

prodOf :: Env -> Text -> Maybe Prod
prodOf env pn = find ((== pn) . prodName) (concatMap ruleProds (specRules (envSpec env)))

lookupNode :: Env -> Text -> P Prod
lookupNode env pn = maybe (failP ("internal: prod_of_prodname: searching pn = " <> pn <> "\n")) pure (prodOf env pn)

-- | Ott's @ln_transform_symterms@: the premises and conclusion of a rule
-- with each nonterminal under binders opened, the opened premises
-- cofinitely quantified and binders removed; with the nonterminals bound
-- in the premises and in the conclusion.
lnTransformSymterms ::
  Env -> [(Maybe Text, Symterm)] -> Symterm ->
  P (([(Maybe Text, Symterm)], Symterm), ([((Text, Suffix), Maybe Symterm)], [((Text, Suffix), Maybe Symterm)]))
lnTransformSymterms env stlp stlc = do
  let removeBinders st = case st of
        StNode ntr pn es -> case prodOf env pn of
          Just p
            | Just occs <- mapM (findOccurrenceMv (prodElements p) 1) (binders p) ->
                let pn' = if isJust (bindableSingleton env p) then prodName p <> "_f" else prodName p
                 in StNode ntr pn' (mapMaybe (removeBindersSte occs) (occStes es))
          _ -> StNode ntr pn (mapMaybe (removeBindersSte []) (occStes es))
        _ -> st
      removeBindersSte occs (ste, o) = case ste of
        SteSt st -> Just (SteSt (removeBinders st))
        SteMetavar {} -> if o `elem` occs then Nothing else Just ste
        SteVar {} -> if o `elem` occs then Nothing else Just ste
        SteList _ -> Just ste
  -- the binders around each nonterminal
  let collect current bindSt st = case st of
        StNode _ pn es -> do
          p <- lookupNode env pn
          bss <- fmap concat $ forM (prodBindspecs p) $ \bs -> case bs of
            Bind (MetaVarExp mv) nt _ -> case (findOccurrenceMv (prodElements p) 0 mv, findOccurrenceNt nt (prodElements p) 1) of
              (Just i, Just o) | i < length es -> pure [(es !! i, nt, o, st)]
              _ -> failP "internal: Not_found in collect_binders_symterm\n"
            _ -> pure []
          fmap concat $ forM (occStes es) $ \(ste, o) -> do
            let extra = [mv | (mv, _, o1, _) <- bss, o == o1]
                stBinder = case bindSt of
                  Just b -> Just b
                  Nothing -> case [b | (_, _, o1, b) <- bss, o == o1] of
                    (b : _) -> Just b
                    [] -> Nothing
            case ste of
              SteSt s -> collect (current ++ extra) stBinder s
              _ -> pure []
        StNonterm _ nt -> pure [(nt, current, bindSt)]
        StNontermSub _ _ nt -> pure [(nt, current, bindSt)]
        StUninterpreted _ _ -> pure []
  ntBoundP <- concat <$> mapM (collect [] Nothing . snd) stlp
  ntBoundC <- collect [] Nothing stlc
  let ntBound = ntBoundP ++ ntBoundC
      findLongest nb acc = case nb of
        [] -> acc
        (nt, bvars, _) : tl -> case lookup nt acc of
          Just longest
            | length bvars > length longest -> findLongest tl ((nt, bvars) : filter ((/= nt) . fst) acc)
            | otherwise -> findLongest tl acc
          Nothing -> findLongest tl ((nt, bvars) : acc)
  ntLongest <- forM (findLongest ntBound []) $ \(nt, stel) -> do
    vs <- forM stel $ \ste -> case ste of
      SteMetavar mvr mv -> pure (ste, SteVar mvr (plainMetavar mv))
      _ -> failP "internal: nt_longest"
    pure (nt, vs)
  let openingMvs = concatMap snd ntLongest
      -- opening a term with respect to the binders not around it
      openTerm current st = case st of
        StNode ntr pn es -> do
          p <- lookupNode env pn
          bss <- fmap concat $ forM (prodBindspecs p) $ \bs -> case bs of
            Bind (MetaVarExp mv) nt _ -> case (findOccurrenceMv (prodElements p) 0 mv, findOccurrenceNt nt (prodElements p) 1) of
              (Just i, Just o) | i < length es -> pure [(es !! i, o)]
              _ -> failP "internal: Not_found in open_nonterm_symterm\n"
            _ -> pure []
          let nbss = case lookup "coq" (prodHoms p) of
                Just h -> [(nti + 1, [es !! i | i <- fvis]) | HomLnFreeIndex fvis nti <- h]
                Nothing -> []
          es' <- forM (occStes es) $ \(ste, o) -> do
            let extra = [mvo | (mvo, o1) <- bss, o == o1]
                removed = concat [fvis | (o1, fvis) <- nbss, o == o1]
                currentStr = map plainSte current
            mapM_
              ( \b ->
                  let str = plainSte b
                   in when (str `elem` currentStr) $
                        failP ("locally-nameless: a rule definition contains a repeated binder: " <> str <> ";\n  try alpha-converting one of the occurrences.\n")
              )
              extra
            openSte (removed ++ current ++ extra) ste
          pure (StNode ntr pn es')
        StNonterm _ nt -> openNt current nt st
        StNontermSub _ _ nt -> openNt current nt st
        StUninterpreted _ _ -> pure st
      openSte current ste = case ste of
        SteSt st -> SteSt <$> openTerm current st
        SteMetavar mvrp mv
          | ste `elem` map fst openingMvs -> pure (SteVar mvrp (plainMetavar mv))
          | otherwise -> pure ste
        _ -> pure ste
      openNt current nt st = do
        longest <- maybe (failP "internal: nt_longest lookup") pure (lookup nt ntLongest)
        buildOpenSymterm env [v | (mv, v) <- longest, mv `notElem` current] st
      openNonterm st = do
        modify (\s -> s {psOpeningVars = []})
        nst <- openTerm [] st
        vs <- psOpeningVars <$> get
        pure (nst, vs)
      cofiniteQuantify (st, mvs) = go (reverse mvs) st
        where
          go mvsr s = case mvsr of
            [] -> s
            mv : tl ->
              let mvr = case mv of
                    SteMetavar m _ -> m
                    SteVar m _ -> m
                    _ -> oops "cofinite quantify not metavar"
               in go tl (StNode "formula" ("formula_cofinite_formula_" <> mvr) [stVarSetUnion tl, mv, SteSt s])
  openedP <- forM stlp $ \(hn, st) -> (,) hn <$> openNonterm st
  openedC <- openNonterm stlc
  let quantifiedP = [(hn, cofiniteQuantify o) | (hn, o) <- openedP]
      quantifiedC = cofiniteQuantify openedC
      stlpT = [(hn, removeBinders st) | (hn, st) <- quantifiedP]
      stlcT = removeBinders quantifiedC
      dedup = removeDuplicates
      ntBoundP' = dedup [(nt, removeBinders <$> sto) | (nt, _, sto) <- ntBoundP]
      ntBoundC' = dedup [(nt, removeBinders <$> sto) | (nt, _, sto) <- ntBoundC]
  pure ((stlpT, stlcT), (ntBoundP', ntBoundC'))

-- | Ott's @build_open_symterm@: a nonterminal opened with each variable,
-- recording the variables in the opening variables.
buildOpenSymterm :: Env -> [Ste] -> Symterm -> P Symterm
buildOpenSymterm env openWrt st = do
  modify (\s -> s {psOpeningVars = removeDuplicates (openWrt ++ psOpeningVars s)})
  let ntr = case st of
        StNonterm n _ -> primaryNtrOfNtr env n
        StNontermSub _ n _ -> primaryNtrOfNtr env n
        _ -> oops "build_open_symterm, not a nonterm"
      r = ruleOfNtr env ntr
      accessible = reachable env (ruleName r)
      mvOf mv = case mv of
        SteMetavar m _ -> m
        SteVar m _ -> m
        _ -> oops "find_var_prod ln not ste_metavar"
      isVarProd m p = case prodElements p of
        [Metavar m2 _ _] -> m == m2
        _ -> False
      findVarProd mv = maybe (oops "find_var_prod") prodName (find (isVarProd (mvOf mv)) (concatMap (ruleProds . ruleOfNtr env) accessible))
      findVarRule mv = maybe (oops "find_var_rule") ruleName (find (any (isVarProd (mvOf mv)) . ruleProds) (map (ruleOfNtr env) accessible))
      prefix = rulePrefix (ruleOfNtr env ntr)
      go wrt s = case wrt of
        [] -> s
        mv : tl ->
          go tl (StNode ntr (prefix <> "open_wrt_" <> findVarRule mv) [SteSt s, SteSt (StNode ntr (findVarProd mv <> "_f") [mv])])
  pure (go (reverse openWrt) st)

-- | Ott's @ln_add_lc_premise@: a local closure premise for each
-- nonterminal of the conclusion the premises do not mention.
lnAddLcPremise :: Env -> [((Text, Suffix), Maybe Symterm)] -> [((Text, Suffix), Maybe Symterm)] -> [Symterm]
lnAddLcPremise env ntsPremises ntsConclusion =
  let dupl = [x | x@(nt, _) <- ntsConclusion, nt `notElem` map fst ntsPremises]
      filtered = [x | x@((ntr, _), _) <- dupl, homSpecForTarget env (ruleHoms (ruleOfNtr env (primaryNtrOfNtr env ntr))) == Nothing]
      internal l = case l of
        [] -> []
        (nt, Just st) : tl -> (nt, Just st) : internal (filter ((/= nt) . fst) tl)
        (nt, Nothing) : tl ->
          if any (\(nt1, s) -> nt1 == nt && isJust s) tl then internal tl else (nt, Nothing) : internal tl
      ntsLc = [x | x@((n, _), _) <- internal filtered, requiredNtc env [Ntr n]]
      premise (nt, stBind) =
        let p = promoteNtr env (primaryNtrOfNtr env (fst nt))
         in StNode
              "formula"
              "formula_judgement"
              [ SteSt
                  ( StNode
                      "judgement"
                      ("judgement_def_lc_" <> p)
                      [SteSt (StNode ("def_lc_" <> p) ("lc_" <> p) [SteSt (fromMaybe (StNonterm (fst nt) nt) stBind)])]
                  )
              ]
   in map premise ntsLc

-- | Ott's @ln_transform_fun_or_reln_defnclass_list@.
lnTransformRelations :: Env -> Processed -> P [ProcessedItem]
lnTransformRelations env processed = forM (processedItems processed) $ \it -> case it of
  PFuns _ -> failP "internal: fdc transform not implemented"
  PReln pc -> do
    defns <- forM (pcDefns pc) $ \d -> do
      rules <- forM (pdRules d) $ \ri -> case ri of
        ItemComment {} -> failP "internal: ln transform defncom not implemented"
        ItemRule dr -> do
          let isFancy (_, st) = case st of
                StNode "fancy_formula" _ _ -> True
                _ -> False
              (fancy, nonFancy) = partition isFancy (drulePremises dr)
          ((psT, cT), (nbP, nbC)) <- lnTransformSymterms env nonFancy (druleConclusion dr)
          let extra = lnAddLcPremise env nbP nbC
          pure (ItemRule dr {drulePremises = fancy ++ [(Nothing, st) | st <- extra] ++ psT, druleConclusion = cT})
      pure d {pdRules = rules}
    pure (PReln pc {pcDefns = defns})

------------------------------------------------------------------------
-- Infrastructure

lnInfrastructure :: Env -> [ProcessedItem] -> Text
lnInfrastructure env rd =
  let bodyRules =
        concat
          [ [r | r <- map (ruleOfNtr env) (ntmvrlistToNtrlist ntcl), not (ruleMeta r), homSpecForTarget env (ruleHoms r) == Nothing]
          | ntcl <- depTs (envDeps env)
          , requiredNtc env ntcl
          ]
      hintsRel = concat [map pdName (pcDefns pc) | PReln pc <- rd]
      hintsLc = ["lc_" <> ruleName r | r <- bodyRules]
      h = hintsRel ++ hintsLc
      hints = if null h then "" else "#[export] Hint Constructors " <> T.unwords h <> " : core.\n"
   in "\n(** infrastructure *)\n" <> hints <> "\n"

------------------------------------------------------------------------
-- The output

-- | Ott's @pp_systemdefn_core_io@ for a locally nameless specification:
-- the one output file. The environment is that of the (avoided)
-- specification, for Coq.
lnOutput :: Env -> LnJob -> P Text
lnOutput env job = do
  unless (isCoq env) $ failP "internal: pp_systemdefn_core_io, locally nameless with a non-coq backend\n"
  let opts = envOpts env
      lngen = optCoqLngen opts
      header =
        "(* generated by Ott 0.34, locally-nameless " <> (if lngen then "lngen " else "") <> "from: " <> lnSources job <> " *)\n"
          <> T.concat ["Require Import " <> th <> ".\n" | th <- if optCoqExpandLists opts then ["Metalib.Metatheory"] else ["Bool", "Metalib.Metatheory", "List", "Ott.ott_list_core"]]
  modify (\s -> s {psCoqLocallyNameless = True})
  -- the transformed syntax and its dependencies
  let specT0 = lnTransformSyntaxdefn env
  c0 <- psVertex <$> get
  let (depsT, c1) = computeDependencies specT0 (targetName (envTarget env)) c0
  modify (\s -> s {psVertex = c1})
  let mkEnv sp = (makeEnv (envTarget env) opts depsT (envAuxfnTypes env) (envQuotation env) sp) {envSources = envSources env}
      envT0 = mkEnv specT0
  relations <- lnTransformRelations env (lnProcessed job)
  pre <- T.concat <$> mapM (lnEmbed job env) (preambleEmbeds (envSpec env))
  -- the syntax
  let mvds = T.concat (map (ppMetavardefn envT0) (specMetavars specT0))
  rulesTxt <- ppRuleList envT0 (specRules specT0)
  -- the functions
  lcs <- lcsClasses envT0
  let lcDefnClasses = [DefnClass (pcName pc) "" [] [] dummyRange | PReln pc <- lcs]
      specT = specT0 {specDefnClasses = specDefnClasses specT0 ++ lcDefnClasses}
      envT = mkEnv specT
      eraseBinders s = s {specRules = [r {ruleProds = [p {prodBindspecs = []} | p <- ruleProds r]} | r <- specRules s]}
      envErased = mkEnv (eraseBinders specT)
  funcsOpen <- ppOpen envT
  funcsSubrules <- ppSubrules envT (specSubrules specT)
  arities <- ppArities env envT
  substs <- ppSubsts envErased (specSubstitutions specT)
  freevars <- ppFreevars envErased (specFreevars specT)
  library <- fst . psLibrary <$> get
  auxList <- psCoqListAuxFuncs <$> get
  subrulesTxt <- compute envT funcsSubrules
  aritiesTxt <- compute env arities
  openTxt <- compute envT funcsOpen
  bumpGrammar specT
  lcsTxt <- ppFunOrRelnDefnclassList envT lcs
  freevarsTxt <- compute envT freevars
  substsTxt <- compute env substs
  let functions =
        "(* EXPERIMENTAL *)\n"
          <> bigLineComment env "auxiliary functions on the new list types"
          <> auxList
          <> bigLineComment env "library functions"
          <> library
          <> bigLineComment env "subrules"
          <> subrulesTxt
          <> bigLineComment env "arities"
          <> aritiesTxt
          <> bigLineComment env "opening up abstractions"
          <> openTxt
          <> bigLineComment env "terms are locally-closed pre-terms"
          <> lcsTxt
          <> bigLineComment env "free variables"
          <> freevarsTxt
          <> bigLineComment env "substitutions"
          <> substsTxt
  embeds <- T.concat <$> mapM (lnEmbed job env) (specEmbeds (envSpec env))
  bumpGrammar specT
  defns <- ppFunOrRelnDefnclassList envT relations
  let infra = lnInfrastructure envT relations
  ip <-
    if optCoqExpandLists opts
      then pure ""
      else do
        i <- ppInduction envT (specRules specT)
        pure (if T.null i then "" else bigLineComment env "induction principles" <> i <> "\n")
  pure
    ( header
        <> pre
        <> bigLineComment env "syntax"
        <> mvds
        <> rulesTxt
        <> "\n"
        <> functions
        <> embeds
        <> "\n"
        <> defns
        <> "\n"
        <> infra
        <> "\n"
        <> ip
    )
  where
    bumpGrammar s = modify (\st -> st {psVertex = psVertex st + lnGrammarNonterminals job s})
