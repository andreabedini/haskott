{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @subrules_pp.ml@: the predicates that carve each subrule out of
-- the type of its top rule. For each root with a non-free definition
-- (one on the left of a subrule, or one whose productions mention such a
-- root), a function @is_lower_of_top@ tests, production by production of
-- the upper rule, whether a term is in the lower rule; in Isabelle with
-- @primrec@ the tests over lists are functions of their own.
module Haskott.Prover.Subrules
  ( ppSubrules
  , subprod
  ) where

import Control.Monad (forM)
import Control.Monad.Trans.State.Strict (get, modify)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Prover.Bounds
import Haskott.Prover.Defns (nonFreeNtrs)
import Haskott.Prover.Dependency
import Haskott.Prover.Pp
import Haskott.Prover.Transform (freshNt)
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

-- | Ott's @Grammar_typecheck.subprod@: the elements of the lower
-- production match those of the upper one, a nonterminal matching one of
-- the same root or of a root above it.
subprod :: [(Text, Text)] -> Prod -> Prod -> Bool
subprod graph pl pu = subelements (prodElements pl) (prodElements pu)
  where
    subelements els eus = length els == length eus && and (zipWith subelement els eus)
    subelement el eu = case (el, eu) of
      (Nonterm pl' _ _, Nonterm pu' _ _) -> pl' == pu' || (pl', pu') `elem` graph
      (Metavar {}, Metavar {}) -> el == eu
      (Terminal _, Terminal _) -> el == eu
      (ListForm a, ListForm b) -> lbSeparator a == lbSeparator b && lbBound a == lbBound b && subelements (lbElements a) (lbElements b)
      _ -> False

-- | Ott's @compute_isa_list_name_flag@: whether two list forms of the
-- rule's productions have the same elements.
isaListNameFlag :: Rule -> Bool
isaListNameFlag r = scan (concatMap prodElements (filter (not . prodMeta) (ruleProds r)))
  where
    scan ess = case ess of
      [] -> False
      ListForm lb : xs -> scanInt (lbElements lb) xs || scan xs
      _ : xs -> scan xs
    scanInt x xs = case xs of
      [] -> False
      ListForm lb : ys -> x == lbElements lb || scanInt x ys
      _ : ys -> scanInt x ys

-- | Ott's @secondary_ntr@.
secondaryNtr :: Env -> Text -> Text
secondaryNtr env ntr = case ruleNames (ruleOfNtrNonprimary env ntr) of
  _ : (n, _) : _ -> n
  _ -> ntr

-- | The nonterminals of the canonical terms of a rule's productions
-- (Ott's @Context_pp.nts_used_in_lhss@).
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
      SteList stlis -> concatMap stli stlis
      _ -> []
    stli s = case s of
      StliSingle es -> concatMap ste es
      StliListform _ es -> concatMap ste es

-- | The split counter of the list functions of one production.
splitKey :: Text
splitKey = "subrules_list_split_inprod"

resetSplit :: P ()
resetSplit = modify (\s -> s {psCounters = M.insert splitKey M.empty (psCounters s)})

bumpSplit :: Text -> P Text
bumpSplit n = do
  s <- get
  let m = M.findWithDefault M.empty splitKey (psCounters s)
  case M.lookup n m of
    Nothing -> do
      modify (\st -> st {psCounters = M.insert splitKey (M.insert n 0 m) (psCounters st)})
      pure ""
    Just c -> do
      modify (\st -> st {psCounters = M.insert splitKey (M.insert n (c + 1) m) (psCounters st)})
      pure (T.pack (show (c + 1)))

-- | Ott's @skip_nt_mv@ and @head_nt_mv@.
skipNtMv :: [Element] -> [Element]
skipNtMv es = case es of
  [] -> []
  Nonterm {} : tl -> tl
  Metavar {} : tl -> tl
  _ : tl -> skipNtMv tl

headNtMv :: [Element] -> Element
headNtMv es = case es of
  [] -> error "Haskott.Prover.Subrules: head_nt_mv"
  e@(Nonterm {}) : _ -> e
  e@(Metavar {}) : _ -> e
  _ : tl -> headNtMv tl

type Result = ([Text], [Text], [IntFunc])

-- | Ott's @pp_subrules@ for the subrules of a structure entry.
ppSubrules :: Env -> [Subrule] -> P Collapsed
ppSubrules env srs = do
  let nonFree = nonFreeNtrs env srs
  funcs <- concat <$> mapM (\(l, u) -> ppSubrule env nonFree l u) nonFree
  pure (collapse env (IntFuncs funcs Nothing))

ppSubrule :: Env -> [(Text, Text)] -> Text -> Text -> P [IntFunc]
ppSubrule env nonFree srl sru = do
  let rl = ruleOfNtr env srl
      ru = ruleOfNtr env sru
      flag = isaListNameFlag ru
      graph = srdGraph (specSubruleData (envSpec env))
  perProd <- forM (filter (not . prodMeta) (ruleProds ru)) $ \pu -> do
    let pls = filter (not . prodMeta) (filter (\pl -> subprod graph pl pu) (ruleProds rl))
        lhsSt = canonicalNode sru pu
    (de, _) <- either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env [lhsSt])
    lhs <- ppSymterm env [] de lhsSt
    rhss <- forM pls $ \pl -> do
      resetSplit
      (conjuncts, deps, newFuncs) <- ppSubelements env nonFree [] de flag pu (prodElements pl) (prodElements pu) srl sru
      let rhs
            | isTwf env = T.concat [" <- " <> c | c <- conjuncts]
            | null conjuncts = ppTrue env False
            | otherwise = T.intercalate (ppAnd env False) conjuncts
      pure (rhs, deps, newFuncs)
    let rhs = case rhss of
          [] -> ppFalse env False
          [(r, _, _)] -> "(" <> r <> ")"
          _ -> T.intercalate (ppOr env False) ["(" <> r <> ")" | (r, _, _) <- rhss]
        clauses'
          | isTwf env = [(prodName pu, lhs, r) | (r, _, _) <- rhss]
          | otherwise = [("", lhs, rhs)]
    pure (clauses', [(d, f) | (_, d, f) <- rhss])
  let clauses = concatMap fst perProd
      -- dep := deps @ !dep, funcs := !funcs @ new_funcs, production by
      -- production
      steps = concatMap snd perProd
      deps = foldl (\acc (d, _) -> d ++ acc) [] steps
      funcs = concatMap snd steps
      ntsUsed = ntsUsedInLhss ru
      freshVar = freshNt ntsUsed (secondaryNtr env sru, [])
      freshText = ppNonterm env freshVar
      header = case envTarget env of
        Isa -> (ppIs srl sru <> " :: \"" <> ppNontermrootTy env sru <> " => bool\"\n", "", "")
        Hol -> ("", "", "")
        Twf -> (ppIs srl sru <> " : " <> ppNontermrootTy env sru <> " -> type.\n", "", "")
        Coq ->
          ( ppIs srl sru <> " (" <> freshText <> ":" <> ppNontermrootTy env sru <> ")"
          , ""
          , " : " <> (if optCoqExpandLists (envOpts env) then "Prop :=\n" else "bool :=\n") <> "  match " <> freshText <> " with\n"
          )
        _ ->
          ( ppIs srl sru <> " (" <> freshText <> ":" <> ppNontermrootTy env sru <> ")"
          , ""
          , " : bool =\n" <> "  match " <> freshText <> " with\n"
          )
  pure (IntFunc (ppIs srl sru) deps sru header clauses : funcs)

ppSubelements :: Env -> [(Text, Text)] -> Suffix -> De -> Bool -> Prod -> [Element] -> [Element] -> Text -> Text -> P Result
ppSubelements env nonFree sie de flag pu els eus srl sru = do
  rs <- sequence (zipWith (ppSubelement env nonFree sie de flag pu srl sru) els eus)
  pure (concat [a | (a, _, _) <- rs], concat [b | (_, b, _) <- rs], concat [c | (_, _, c) <- rs])

ppSubelement :: Env -> [(Text, Text)] -> Suffix -> De -> Bool -> Prod -> Text -> Text -> Element -> Element -> P Result
ppSubelement env nonFree sie de flag pu srl sru el eu = case (el, eu) of
  (Nonterm ntrpl _ _, Nonterm _ ntu su) -> pure $ case lookup ntrpl nonFree of
    Just up -> (["(" <> ppIs ntrpl up <> " " <> ppNontermWithSie env sie (ntu, su) <> ")"], [ppIs ntrpl up], [])
    Nothing -> ([], [], [])
  (Metavar {}, Metavar {}) -> pure ([], [], [])
  (Terminal _, Terminal _) -> pure ([], [], [])
  (ListForm elbl, ListForm elbu) -> do
    let bound = fromMaybe (error "null bounds in pp_subelement") (lbBound elbl)
        de1i = de1Lookup (fst de) bound
        sie' = SiVar "_" 0 : sie
        cid = de1CompoundId de1i
        pattern = de1Pattern de1i
    (conjuncts, deps, _) <- ppSubelements env nonFree sie' de flag pu (lbElements elbl) (lbElements elbu) srl sru
    let conj = if null conjuncts then ppTrue env False else T.intercalate (ppAnd env False) conjuncts
    case envTarget env of
      Twf -> failP "internal (Twelf): pp_true"
      Isa
        | optIsaPrimrec (envOpts env) -> isaPrimrecList env nonFree sie de flag pu srl sru elbl elbu de1i conj deps
        | otherwise -> pure (["(list_all (% " <> pattern <> " . " <> conj <> ") " <> cid <> ")"], deps, [])
      Hol -> pure (["(EVERY (\\" <> pattern <> ". " <> conj <> ") " <> cid <> ")"], deps, [])
      Caml -> pure (["(List.for_all (fun " <> pattern <> " -> " <> conj <> ") " <> cid <> ")"], deps, [])
      Lem -> pure ([" (List.all (fun " <> pattern <> " -> " <> conj <> ") " <> cid <> ")"], deps, [])
      Coq
        | optCoqExpandLists (envOpts env) -> do
            let tyList = splitParensStars (de1CoqTypeOfPattern de1i)
                varList = splitParensCommas pattern
                suf = "list_" <> T.intercalate "_" tyList
                postName = T.intercalate "_" [ppNtOrMvWithSie env (SiPunct "" : sie) (promoteNtmvr env r, s) | ((r, s), _) <- de1Ntmvsns de1i]
                ident = ppIs srl postName <> "_list"
                header = (ident <> " (l:" <> suf <> ")", "", " : Prop :=\n" <> "  match l with\n")
                func =
                  IntFunc
                    { rFunId = ident
                    , rFunDep = ident : deps
                    , rFunType = suf
                    , rFunHeader = header
                    , rFunClauses =
                        [ ("", "Nil_" <> suf, "True")
                        , ("", "Cons_" <> suf <> " " <> T.unwords varList <> " " <> cid <> "_", conj <> " /\\ " <> "(" <> ident <> " " <> cid <> "_)")
                        ]
                    }
            pure ([ident <> " " <> cid], ident : deps, [func])
        | length (splitParensCommas pattern) == 1 ->
            pure (["(forall_list (fun (" <> pattern <> ":" <> de1CoqTypeOfPattern de1i <> ") => " <> conj <> ") " <> cid <> ")"], deps, [])
        | otherwise ->
            pure (["(forall_list (fun (pat_:" <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> pattern <> " => " <> conj <> " end) " <> cid <> ")"], deps, [])
  _ -> error "Haskott.Prover.Subrules: pp_subelement"

-- | The Isabelle primrec case of a list form: a function over the list,
-- and for a list of tuples, functions over the tuples.
isaPrimrecList :: Env -> [(Text, Text)] -> Suffix -> De -> Bool -> Prod -> Text -> Text -> ListBody -> ListBody -> De1i -> Text -> [Text] -> P Result
isaPrimrecList env nonFree sie de flag pu srl sru elbl elbu de1i conj deps = do
  let hide = hideIsaTrailingUnderscore env
      typ = fromMaybe (error "Haskott.Prover.Subrules: the") (ppElements env (SiPunct "_" : sie) (lbElements elbu) True False True True) <> " list"
      args = T.intercalate "_" [ppNtOrMvWithSie env (SiPunct "" : sie) x | (x, _) <- de1Ntmvsns de1i]
      postName = T.intercalate "_" [ppNtOrMvRoot env (promoteNtmvr env r) | ((r, _), _) <- de1Ntmvsns de1i]
      preSplit = if flag then "_" <> prodName pu else ""
  counter <- bumpSplit (typ <> preSplit)
  let splitSuffix = preSplit <> counter
      ident = ppIs srl postName <> "_list" <> splitSuffix
      cid = de1CompoundId de1i
  (rhsSc, tupleAuxFun, listDeps) <-
    case de1Ntmvsns de1i of
      [_] -> pure (conj, [], deps)
      _ -> do
        let listNames = [ppNtOrMvWithSie env (SiPunct "" : sie) (promoteNtmvr env r, s) | ((r, s), _) <- de1Ntmvsns de1i]
            listPatterns = [ppNtOrMvWithSie env (SiPunct "" : sie) x | (x, _) <- de1Ntmvsns de1i]
            listTypes = splitParensStars (fromMaybe (error "Haskott.Prover.Subrules: the") (ppElements env (SiPunct "_" : sie) (lbElements elbu) True False True True))
            makeTupleFunc lNames lPatterns lTypes elblEs elbuEs = case (lNames, lPatterns, lTypes) of
              (_ : namesTl, pHd : pTl, tHd : tTl) -> do
                let name = ppIs srl (tHd <> "_" <> T.intercalate "_" tTl) <> splitSuffix
                if length lNames == 2
                  then do
                    let ty = "(" <> T.intercalate "*" lTypes <> ")"
                        lhs = "(" <> T.intercalate "," [hide (s <> "_") | s <- lPatterns] <> ")"
                    (cs, ds, _) <- ppSubelements env nonFree (SiVar "_" 0 : sie) de flag pu elblEs elbuEs srl sru
                    let rhs = case cs of
                          [] -> "True"
                          [c] -> c
                          _ -> "(" <> T.intercalate " & " cs <> ")"
                    pure ("(" <> name <> " " <> hide (args <> "_") <> ")", [IntFunc name ds (ty <> splitSuffix) (name <> " :: \"" <> ty <> " => bool\"\n", "", "") [("", lhs, rhs)]], [name])
                  else do
                    let ty = "(" <> tHd <> "*(" <> T.intercalate "*" tTl <> "))"
                        depLhs = hide (T.intercalate "_" pTl <> "_")
                        lhs = "(" <> hide (pHd <> "_") <> "," <> depLhs <> ")"
                    (_, f, d) <- makeTupleFunc namesTl pTl tTl (skipNtMv elblEs) (skipNtMv elbuEs)
                    let depName = ppIs srl (T.intercalate "_" tTl) <> splitSuffix
                    (c, _, _) <- ppSubelement env nonFree (SiVar "_" 0 : sie) de flag pu srl sru (headNtMv elblEs) (headNtMv elbuEs)
                    let recCall = if null c then "" else T.intercalate " & " c <> " & "
                        rhs = recCall <> "(" <> depName <> " " <> depLhs <> ")"
                    pure ("(" <> name <> " " <> hide (args <> "_") <> ")", IntFunc name (depName : d) (ty <> splitSuffix) (name <> " :: \"" <> ty <> " => bool\"\n", "", "") [("", lhs, rhs)] : f, [name])
              _ -> error "Haskott.Prover.Subrules: make_tuple_func"
        makeTupleFunc listNames listPatterns listTypes (lbElements elbl) (lbElements elbu)
  let listFunc =
        IntFunc
          ident
          (ident : listDeps)
          (typ <> splitSuffix)
          (ident <> " :: \"" <> typ <> " => bool\"\n", "", "")
          [ ("", "Nil", "True")
          , ("", "(" <> hide (args <> "_") <> "#" <> hide (cid <> "_") <> ")", "(" <> rhsSc <> " & " <> "(" <> ident <> " " <> hide (cid <> "_") <> "))")
          ]
  pure ([ident <> " " <> cid], ident : deps, listFunc : tupleAuxFun)
