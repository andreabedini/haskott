{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @substs_pp.ml@: the auxiliary functions of binding
-- specifications, the substitutions and free-variable functions declared
-- in @substitutions@ and @freevars@ sections, and the library functions
-- they use (@list_mem@, @list_minus@, @list_assoc@, ...), for every
-- prover target.
--
-- A substitution or free-variable function is defined over every rule
-- that needs one: those with a production that is the variable itself,
-- and those that depend on them. Each production is a clause, built from
-- its canonical term; a nonterminal under a binder gets the binder's names
-- removed (Ott's \"glommed bound things\"). Under Isabelle with primrec,
-- the lists and tuples of a list form become functions of their own.
module Haskott.Prover.Substs
  ( ppAuxfns
  , ppSubsts
  , ppFreevars
  , ppListAllCongLemma
  , ppListSimpLemmas
  ) where

import Control.Monad (forM, when, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, modify, put, runStateT)
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Prover.Bounds
import Haskott.Prover.Dependency
import Haskott.Prover.Pp
import Haskott.Prover.Transform (freshNt)
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

------------------------------------------------------------------------
-- Library functions

ppListFilterCoq, ppListMinusCaml, ppListMinusLem, ppListMinusIsa, ppListMinusCoq, ppListMinus2Coq, ppListMemCoq :: Text
ppListFilterCoq =
  "Fixpoint list_filter A (f:A->bool) (l:list A) {struct l} : list A :=\n"
    <> "  match l with\n"
    <> "  | nil => nil\n"
    <> "  | cons h t => if (f h) then cons h (list_filter A f t) else (list_filter A f t)\n"
    <> "end.\n"
    <> "Arguments list_filter [A] _ _.\n\n"
ppListMinusCaml =
  "let rec list_minus (l1:'a list) (l2:'a list) : 'a list =\n"
    <> "  match l1 with\n"
    <> "  | [] -> []\n"
    <> "  | h::t -> if (List.mem h l2) then list_minus t l2 else h::(list_minus t l2)\n"
    <> "\n"
ppListMinusLem =
  "let rec list_minus (l1:list 'a) (l2:list 'a) : list 'a=\n"
    <> "  match l1 with\n"
    <> "  | [] -> []\n"
    <> "  | h::t -> if (List.elem h l2) then list_minus t l2 else h::(list_minus t l2)\n"
    <> "  end\n"
    <> "\n"
ppListMinusIsa =
  "primrec\n"
    <> "list_minus :: \"'a list => 'a list => 'a list\"\n"
    <> "where\n"
    <> "  \"list_minus Nil ys = Nil\"\n"
    <> "| \"list_minus (Cons x xs) ys = (if Not(x : set ys) then Cons x (list_minus xs ys) else list_minus xs ys)\"\n\n"
ppListMinusCoq =
  "Fixpoint list_minus A (eq:forall a b:A,{a=b}+{a<>b}) (l1:list A) (l2:list A) {struct l1} : list A :=\n"
    <> "  match l1 with\n"
    <> "  | nil => nil\n"
    <> "  | cons h t => if (list_mem (A:=A) eq h l2) then list_minus A eq t l2 else cons h (list_minus A eq t l2)\n"
    <> "end.\n"
    <> "Arguments list_minus [A] _ _ _.\n\n"
ppListMinus2Coq =
  "Fixpoint list_minus2 A B (eq:forall a b:A,{a=b}+{a<>b}) (l1:list (A*B)) (l2:list A) {struct l1} : list (A*B) :=\n"
    <> "  match l1 with\n"
    <> "  | nil => nil\n"
    <> "  | cons a t => if (list_mem (A:=A) eq (@fst A B a) l2) then list_minus2 A B eq t l2 else cons a (list_minus2 A B eq t l2)\n"
    <> "end.\n"
    <> "Arguments list_minus2 [A B] _ _ _.\n\n"
ppListMemCoq =
  "Fixpoint list_mem A (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=\n"
    <> "  match l with\n"
    <> "  | nil => false\n"
    <> "  | cons h t => if eq h x then true else list_mem A eq x t\n"
    <> "end.\n"
    <> "Arguments list_mem [A] _ _ _.\n\n"

ppListAssocIsa, ppListAssocCoq, ppListAssocLem, ppListAllCongLemmaIsa :: Text
ppListAssocIsa =
  "primrec\n"
    <> "list_assoc :: \"'a => ('a*'b) list => 'b option\"\n"
    <> "where\n"
    <> "  \"list_assoc x0 Nil = None\"\n"
    <> "| \"list_assoc x0 (Cons xy  xys) = (if x0=fst xy then Some (snd xy) else list_assoc x0 xys)\"\n\n"
ppListAssocCoq =
  "Fixpoint list_assoc A B (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list (A*B)) {struct l} : option B :=\n"
    <> "  match l with\n"
    <> "  | nil => None\n"
    <> "  | cons (a,b) t => if (eq a x) then Some b else list_assoc A B eq x t\n"
    <> "end.\n"
    <> "Arguments list_assoc [A B] _ _ _.\n\n"
ppListAssocLem =
  "let rec list_assoc_option x0 xys =\n"
    <> "  match xys with\n"
    <> "  | [] -> Nothing\n"
    <> "  | (x,y)::xys' -> if x0=x then Just y else list_assoc_option x0 xys'\n"
    <> "  end\n\n"
ppListAllCongLemmaIsa =
  "\n(* general lemma, should be in isa lib *)\n"
    <> "lemma list_all_cong[fundef_cong]:\n"
    <> "     \"xs = ys ==> (!!x. x:set ys ==> P x = Q x) ==> list_all P xs = list_all Q ys\"\n"
    <> "  unfolding list_all_iff\n"
    <> "  by auto\n\n"

ppListMem :: Env -> P ()
ppListMem env = when (isCoq env) (addToLib "list_mem" ppListMemCoq)

ppListFilter :: Env -> P ()
ppListFilter env = when (isCoq env) (addToLib "list_filter" ppListFilterCoq)

ppListMinus :: Env -> P ()
ppListMinus env = case envTarget env of
  Caml -> addToLib "list_minus" ppListMinusCaml
  Lem -> addToLib "list_minus" ppListMinusLem
  Isa -> addToLib "list_minus" ppListMinusIsa
  Hol -> pure ()
  Coq -> ppListMem env >> addToLib "list_minus" ppListMinusCoq
  Twf -> failP "internal (Twelf): pp_list_minus"

ppListMinus2 :: Env -> P ()
ppListMinus2 env = when (isCoq env) (ppListMem env >> addToLib "list_minus2" ppListMinus2Coq)

ppListAssoc :: Env -> P ()
ppListAssoc env = case envTarget env of
  Isa -> addToLib "list_assoc" ppListAssocIsa
  Lem -> addToLib "list_assoc" ppListAssocLem
  Coq -> addToLib "list_assoc" ppListAssocCoq
  _ -> pure ()

-- | Ott's @pp_list_all_cong_lemma@.
ppListAllCongLemma :: Env -> P ()
ppListAllCongLemma env =
  when (isIsa env && not (optIsaPrimrec (envOpts env))) $
    addToLib "list_all_cong_lemma" ppListAllCongLemmaIsa

-- | Ott's @pp_list_simp_lemmas@, which prints nothing.
ppListSimpLemmas :: Env -> P ()
ppListSimpLemmas _ = pure ()

------------------------------------------------------------------------
-- Helpers

substName :: Text -> Text -> Text
substName s ntr = s <> "_" <> ntr

-- | The split counters of the function printers: empty the first time a
-- name is seen, then 1, 2, ...
bumpCounter :: Text -> Text -> P Text
bumpCounter k n = do
  s <- get
  let m = M.findWithDefault M.empty k (psCounters s)
  case M.lookup n m of
    Nothing -> do
      put s {psCounters = M.insert k (M.insert n 0 m) (psCounters s)}
      pure ""
    Just c -> do
      put s {psCounters = M.insert k (M.insert n (c + 1) m) (psCounters s)}
      pure (T.pack (show (c + 1)))

resetCounter :: Text -> P ()
resetCounter k = modify (\s -> s {psCounters = M.delete k (psCounters s)})

boundExtraction' :: Env -> [Symterm] -> P (De, De3)
boundExtraction' env sts = either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env sts)

-- | The canonical terms of the productions of a rule.
stsForLhss :: Env -> Rule -> [Symterm]
stsForLhss _ r = [canonicalNode (ruleName r) p | p <- ruleProds r]

ntsOfSymterms, mvsOfSymterms :: [Symterm] -> [(Text, Suffix)]
ntsOfSymterms = concatMap st
  where
    st s = case s of
      StNode _ _ es -> concatMap ste es
      StNonterm _ nt -> [nt]
      StNontermSub _ _ nt -> [nt]
      StUninterpreted _ _ -> []
    ste e = case e of
      SteSt s -> st s
      SteList stlis -> concatMap stli stlis
      _ -> []
    stli s = case s of
      StliSingle es -> concatMap ste es
      StliListform _ es -> concatMap ste es
mvsOfSymterms = concatMap st
  where
    st s = case s of
      StNode _ _ es -> concatMap ste es
      _ -> []
    ste e = case e of
      SteSt s -> st s
      SteMetavar _ mv -> [mv]
      SteList stlis -> concatMap stli stlis
      _ -> []
    stli s = case s of
      StliSingle es -> concatMap ste es
      StliListform _ es -> concatMap ste es

-- | Ott's @secondary_ntr@: the second name of the rule, if any.
secondaryNtr :: Env -> Text -> Text
secondaryNtr env ntr = case ruleNames (ruleOfNtrNonprimary env ntr) of
  _ : (q, _) : _ -> q
  _ -> ntr

secondaryMvr :: Env -> Text -> Text
secondaryMvr env mvr = case mvdNames (mvdOfMvrNonprimary env mvr) of
  _ : (q, _) : _ -> q
  _ -> mvr

-- | Ott's @fresh_mv@ is @fresh_nt@ on metavariables.
freshMv :: [(Text, Suffix)] -> (Text, Suffix) -> (Text, Suffix)
freshMv = freshNt

-- | Ott's @compute_isa_list_name_flag@: whether two list forms of the
-- rule's productions have the same elements.
isaListNameFlag :: Rule -> Bool
isaListNameFlag r = scan (concatMap prodElements (filter (not . prodMeta) (ruleProds r)))
  where
    scan ess = case ess of
      [] -> False
      ListForm lb : xs -> scanInt (lbElements lb) xs || scan xs
      _ : xs -> scan xs
    scanInt x xs = or [lbElements lb == x | ListForm lb <- xs]

-- | Ott's @Auxl.insert_append@ for Twelf: each list named by a fresh
-- @NL@ variable, appended with @append/natlist@ premises.
insertAppendTwf :: [Text] -> P Text
insertAppendTwf l = case l of
  [] -> pure "natlist/nil"
  [x] -> pure x
  _ -> do
    resultNl <- mapM (const freshNl) (drop 1 l)
    listNl <- mapM (const freshNl) l
    let internal current rs ls = case (rs, ls) of
          ([], _) -> " <- append/natlist " <> T.unwords ls <> " " <> current
          (r' : rt, lh : lt) -> " <- append/natlist " <> lh <> " " <> current <> " " <> r' <> internal r' rt lt
          (_ : _, []) -> error "Haskott.Prover.Substs: insert_append"
        final = case resultNl of
          r' : rt -> internal r' rt listNl
          [] -> error "Haskott.Prover.Substs: insert_append"
    pure (last resultNl <> " <- " <> T.intercalate " <- " (zipWith (\x nl -> x <> " " <> nl) l listNl) <> final)

-- | Ott's @Auxl.insert_append@ for Coq.
insertAppend :: [Text] -> Text
insertAppend l = case l of
  [] -> "nil"
  [x] -> "(" <> x <> ")"
  _ -> foldr (\x s -> "(app " <> x <> " " <> s <> ")") (last l) (init l)

nonMetaProds :: Rule -> [Prod]
nonMetaProds r = filter (not . prodMeta) (ruleProds r)

-- | Ott's @result_type_of_mse@.
resultTypeOfMse :: Env -> Mse -> RootRef
resultTypeOfMse env mse = fromMaybe (error "result_type_of_mse applied to an mse with unconstained type") (f mse)
  where
    f m = case m of
      MetaVarExp (mv, _) -> Just (Mvr (primaryMvrOfMvr env mv))
      MetaVarListExp (mv, _) _ -> Just (Mvr (primaryMvrOfMvr env mv))
      NonTermExp (nt, _) -> Just (Ntr (primaryNtrOfNtr env nt))
      NonTermListExp (nt, _) _ -> Just (Ntr (primaryNtrOfNtr env nt))
      Aux g _ -> snd <$> lookup g (envAuxfnTypes env)
      AuxList g _ _ -> snd <$> lookup g (envAuxfnTypes env)
      Union a b -> case (f a, f b) of
        (Just x, Nothing) -> Just x
        (Nothing, Just x) -> Just x
        (Just x, Just y) | x == y -> Just x
        (Nothing, Nothing) -> Nothing
        _ -> error "result_type_of_mse applied to an mse with inconsistent type constraints"
      Empty -> Nothing

auxfnUsagesInMse :: Mse -> [(Text, (Text, Suffix))]
auxfnUsagesInMse mse = case mse of
  Aux f nt -> [(f, nt)]
  AuxList f nt _ -> [(f, nt)]
  Union a b -> auxfnUsagesInMse a ++ auxfnUsagesInMse b
  _ -> []

auxfnUsages :: [Bindspec] -> [(Text, (Text, Suffix))]
auxfnUsages bs = removeDuplicates (concat [auxfnUsagesInMse m | Bind m _ _ <- bs])

-- | Ott's @glommed_bound_things_for_nonterm@: the names a production
-- binds in a nonterminal, of the type of the variable.
glommedBoundThings :: Env -> Prod -> RootRef -> (Text, Suffix) -> Mse
glommedBoundThings env p thatRoot nt =
  let relevantBinds = [m | Bind m nt' _ <- prodBindspecs p, nt' == nt, resultTypeOfMse env m == thatRoot]
      relevantAux
        | optNoRbcatn (envOpts env) = []
        | otherwise = [f | (f, nt'') <- auxfnUsages (prodBindspecs p), nt'' == nt, Just (_, r) <- [lookup f (envAuxfnTypes env)], r == thatRoot]
      ntOccurs m = case m of
        NonTermExp nt' -> nt == nt'
        NonTermListExp nt' _ -> nt == nt'
        Union a b -> ntOccurs a || ntOccurs b
        _ -> False
      directly = or [ntOccurs m | Bind m _ _ <- prodBindspecs p]
      things = relevantBinds ++ [Aux f nt | f <- relevantAux] ++ [NonTermExp nt | directly]
      glom ms = case ms of
        [] -> Empty
        [m] -> m
        m : more -> Union m (glom more)
   in glom things

-- | Ott's @foo_with_dependencies@: the free rules that need the function,
-- because a production is the variable itself or because they depend on
-- such a rule, each with its functions.
fooWithDependencies :: Env -> (Text -> Prod -> Bool) -> ([Text] -> Rule -> P [IntFunc]) -> P IntFuncs
fooWithDependencies env needed fooRule = do
  let spec = envSpec env
      freeRs = [r | r <- specRules spec, not (ruleMeta r), homSpecForTarget env (ruleHoms r) == Nothing]
      neededRule r = not (ruleMeta r) && any (\p -> not (prodMeta p) && needed (ruleName r) p) (ruleProds r)
      neededRules = map ruleName (filter neededRule freeRs)
      depsOf r = fromMaybe (error "Haskott.Prover.Substs: no dependencies") (lookup (Ntr (ruleName r)) (depGraph (envDeps env)))
      domainRs = [r | r <- freeRs, ruleName r `elem` neededRules || any (\r' -> Ntr r' `elem` depsOf r) neededRules]
      domain = map ruleName domainRs
  funcs <- mapM (fooRule domain) domainRs
  pure (IntFuncs (concat funcs) Nothing)

ppNtOrMv :: Env -> NtMv -> Text
ppNtOrMv env = ppNtOrMvWithSie env []

------------------------------------------------------------------------
-- Auxiliary functions

-- | Ott's @pp_auxfns@.
ppAuxfns :: Env -> [(Text, ([Text], RootRef))] -> P Collapsed
ppAuxfns env axs = do
  funcs <- forM axs $ \(f, (ntrs, ntmvr)) -> concat <$> mapM (\ntr -> ppAuxfnClauses env f ntr ntmvr) ntrs
  pure (collapse env (IntFuncs (concat funcs) Nothing))

ppAuxfnClauses :: Env -> Text -> Text -> RootRef -> P [IntFunc]
ppAuxfnClauses env _ _ _
  | isTwf env = failP "internal (Twelf): pp_auxfn_clauses"
ppAuxfnClauses env f ntr ntmvr = do
  let r = ruleOfNtr env ntr
      ntrn = ppNontermrootTy env ntr
      ident = auxfnName f ntrn ntrn
      mseDep mse = [let n' = ppNontermroot env (promoteNtr env (primaryNtrOfNtr env n)) in auxfnName g n' n' | (g, (n, _)) <- auxfnUsagesInMse mse]
      patVar = freshNt (ntsOfSymterms (stsForLhss env r)) (secondaryNtr env ntr, [])
      header = case envTarget env of
        Isa -> (ident <> " :: \"" <> ppNontermrootTy env ntr <> " => " <> ppNtOrMvRootTy env ntmvr <> " list\"\n", "", "")
        Hol -> ("", "", "")
        Coq ->
          ( ident <> " (" <> ppNonterm env patVar <> ":" <> ppNontermrootTy env ntr <> ")"
          , ""
          , " : list " <> ppNtOrMvRootTy env ntmvr <> " :=\n" <> "  match " <> ppNonterm env patVar <> " with\n"
          )
        _ ->
          ( ident <> " (" <> ppNonterm env patVar <> ":" <> ppNontermrootTy env ntr <> ")"
          , ""
          , " : " <> (if isCaml env then ppNtOrMvRootTy env ntmvr <> " list" else "list " <> ppNtOrMvRootTy env ntmvr) <> " =\n" <> "  match " <> ppNonterm env patVar <> " with\n"
          )
      flag = isaListNameFlag r
  results <- forM (nonMetaProds r) $ \p -> do
    let lhsSt = canonicalNode ntr p
    (de, _) <- boundExtraction' env [lhsSt]
    lhs <- ppSymterm env [] de lhsSt
    resetCounter "mse_split_inprod"
    let mse = case [m | AuxFnDef f' m _ <- prodBindspecs p, f' == f] of
          [m] -> m
          _ -> error "Haskott.Prover.Substs: no unique definition of an auxiliary function"
    (rhs, deps, aux) <- ppMse env [] de flag (prodName p) (Just ntmvr) mse
    pure (mseDep mse ++ deps, ("", lhs, rhs), aux)
  let deps = concat (reverse [d | (d, _, _) <- results])
  pure (IntFunc ident deps ntr header [c | (_, c, _) <- results] : concat [a | (_, _, a) <- results])

------------------------------------------------------------------------
-- Substitutions

-- | What the printers of a substitution's clauses share.
data SubstCtx = SubstCtx
  { scSubst :: Substitution
  , scDomain :: [Text]
  , scFlag :: Bool
  , scRule :: Text
  , scThis :: (Text, Suffix)
  , scThat :: NtMv
  , scSub :: Text
  , scProd :: Prod
  , scIn :: (Text, Suffix)
  -- ^ the variable the function matches on
  }

-- | The dependencies a clause collects, as Ott's reference.
type D = StateT [Text] P

liftP :: P a -> D a
liftP = lift

-- | Ott's @pp_substs@.
ppSubsts :: Env -> [Substitution] -> P Collapsed
ppSubsts env sbs = concat <$> forM sbs (\sb -> collapse env <$> fooWithDependencies env (substNeeded sb) (ppSubstRule env sb))

substNeeded :: Substitution -> Text -> Prod -> Bool
substNeeded sb ntr p
  | sbThis sb == ntr = case prodElements p of
      [Nonterm ntrp _ _] -> sbThat sb == Ntr ntrp
      [Metavar mvrp _ _] -> sbThat sb == Mvr mvrp
      _ -> False
  | otherwise = False

ppSubstRule :: Env -> Substitution -> [Text] -> Rule -> P [IntFunc]
ppSubstRule env sb domain r = do
  let lhss = stsForLhss env r
      nts0 = ntsOfSymterms lhss
      mvs0 = mvsOfSymterms lhss
      thisVar = freshNt nts0 (secondaryNtr env (sbThis sb), [])
      nts1 = thisVar : nts0
      (thatVar, nts2) = case sbThat sb of
        Ntr ntr -> let nt = freshNt nts1 (secondaryNtr env ntr, []) in ((Ntr (fst nt), snd nt), nt : nts1)
        Mvr mvr -> let mv = freshMv mvs0 (secondaryMvr env mvr, []) in ((Mvr (fst mv), snd mv), nts1)
      inVar = freshNt nts2 (secondaryNtr env (ruleName r), [])
      subVar = "sub"
      flag = isaListNameFlag r
  results <- fmap concat $ forM (nonMetaProds r) $ \p ->
    ppSubstProd env (SubstCtx sb domain flag (ruleName r) thisVar thatVar subVar p inVar)
  let deps = concat [d | (d, _, _) <- results]
      clauses = [c | (_, c, _) <- results]
      listFuncs = concat [f | (_, _, f) <- results]
      ident = substName (sbName sb) (ppNontermroot env (ruleName r))
      tyThis = ppNontermrootTy env (sbThis sb)
      tyThat = ppNtOrMvRootTy env (sbThat sb)
      tyR = ppNontermrootTy env (ruleName r)
      args
        | sbMultiple sb = case envTarget env of
            Coq -> " (" <> subVar <> ":list (" <> tyThat <> "*" <> tyThis <> "))"
            Caml -> " (" <> subVar <> ": " <> "(" <> tyThat <> "*" <> tyThis <> ") list" <> ")"
            _ -> " (" <> subVar <> ": " <> "list " <> "(" <> tyThat <> "*" <> tyThis <> ")" <> ")"
        | otherwise = " (" <> ppNonterm env thisVar <> ":" <> tyThis <> ")" <> " (" <> ppNtOrMv env thatVar <> ":" <> tyThat <> ")"
      header = case envTarget env of
        Coq ->
          ( ident <> args <> " (" <> ppNonterm env inVar <> ":" <> tyR <> ")"
          , " {struct " <> ppNonterm env inVar <> "}"
          , " : " <> tyR <> " :=\n" <> "  match " <> ppNonterm env inVar <> " with\n"
          )
        Isa ->
          ( ident <> " :: \""
              <> ( if sbMultiple sb
                     then "(" <> tyThat <> "*" <> tyThis <> ") list => " <> tyR <> " => " <> tyR
                     else tyThis <> " => " <> tyThat <> " => " <> tyR <> " => " <> tyR
                 )
              <> "\"\n"
          , ""
          , ""
          )
        Hol -> ("", "", "")
        Twf ->
          ( ident <> " : "
              <> ( if sbMultiple sb
                     then " <<<FZ mult not impl>> "
                     else tyThis <> " -> " <> tyThat <> " -> " <> tyR <> " -> " <> tyR <> " -> type.\n"
                 )
          , ""
          , ""
          )
        _ ->
          ( ident <> args <> " (" <> ppNonterm env inVar <> ":" <> tyR <> ")"
          , ""
          , " : " <> tyR <> " =\n" <> "  match " <> ppNonterm env inVar <> " with\n"
          )
  pure (IntFunc ident (deps ++ map rFunId listFuncs) (ruleName r) header clauses : listFuncs)

ppSubstProd :: Env -> SubstCtx -> P [([Text], (Text, Text, Text), [IntFunc])]
ppSubstProd env sc = do
  let sb = scSubst sc
      p = scProd sc
      lhsSt = canonicalNode (scRule sc) p
      lhsEs = case lhsSt of
        StNode _ _ es -> es
        _ -> []
  (de, _) <- boundExtraction' env [lhsSt]
  lhsPat <- ppSymterm env [] de lhsSt
  let one rhs = [("", rhs)]
      lhs
        | isIsa env || isHol env || isTwf env =
            (if sbMultiple sb then scSub sc else ppNonterm env (scThis sc) <> " " <> ppNtOrMv env (scThat sc)) <> " " <> lhsPat
        | otherwise = lhsPat
      tyThat = ppNtOrMvRootTy env (sbThat sb)
      thisS = ppNonterm env (scThis sc)
      singleton thingS
        | isTwf env =
            pure $
              if sbMultiple sb
                then one "<<<multiple subst not implemented>>>"
                else [("/same", thisS), ("/diff", lhsPat <> " <- neq " <> thingS <> " " <> ppNtOrMv env (scThat sc))]
        | otherwise = one <$> singleton' thingS
      singleton' thingS
        | sbMultiple sb = case envTarget env of
            Twf -> error "Haskott.Prover.Substs: singleton'"
            Isa -> do
              ppListAssoc env
              pure ("(case list_assoc " <> thingS <> " " <> scSub sc <> " of None => " <> lhsPat <> " | Some " <> thisS <> " => " <> thisS <> ")")
            Hol -> do
              ppListAssoc env
              pure ("(case list_assoc " <> thingS <> " " <> scSub sc <> " of NONE => " <> lhsPat <> " | SOME " <> thisS <> " => " <> thisS <> ")")
            Lem -> do
              ppListAssoc env
              pure ("(match list_assoc_option " <> thingS <> " " <> scSub sc <> " with " <> "| Nothing -> " <> lhsPat <> "| Just " <> thisS <> " -> " <> thisS <> " end)")
            Coq -> do
              ppListAssoc env
              pure ("(match list_assoc " <> "eq_" <> tyThat <> " " <> thingS <> " " <> scSub sc <> " with None => " <> lhsPat <> " | Some " <> thisS <> " => " <> thisS <> " end)")
            Caml -> pure ("(try List.assoc " <> thingS <> " " <> scSub sc <> " with Not_found -> " <> lhsPat <> ")")
        | otherwise =
            let thatS = ppNtOrMv env (scThat sc)
                eqS
                  | isCoq env = (if requireLocallyNameless env then "eq_var" else "eq_" <> tyThat) <> " " <> thingS <> " " <> thatS
                  | otherwise = thingS <> "=" <> thatS
             in pure ("(if " <> eqS <> " then " <> thisS <> " else " <> lhsPat <> ")")
  -- the dependencies Ott collects in a reference, read at the end
  case prodElements p of
    [Nonterm ntrp _ _]
      | scRule sc == sbThis sb && sbThat sb == Ntr ntrp -> do
          let ntS = case lhsEs of
                [SteSt (StNonterm _ nt0)] -> ppNonterm env nt0
                _ -> error "internal error: lhs_stnb not of the right form"
          rhss <- singleton ntS
          pure [([], (prodName p <> pfx, lhs, rhs), []) | (pfx, rhs) <- rhss]
    [Metavar mvrp _ _]
      | scRule sc == sbThis sb && sbThat sb == Mvr mvrp -> do
          let mvS = case lhsEs of
                [SteMetavar _ mv0] -> ppMetavar env mv0
                _ -> error "internal error: lhs_stnb not of the right form"
          rhss <- singleton mvS
          pure [([], (prodName p <> pfx, lhs, rhs), []) | (pfx, rhs) <- rhss]
    _ -> do
      resetCounter "subst_split_inprod"
      (results, deps) <- runD (mapM (ppSubstSte env sc [] de) lhsEs)
      let body = map fst results
          listFuncs = concatMap snd results
          pn = nodePn lhsSt
      rhs <- case envTarget env of
        Caml -> pure (capitalize pn <> " " <> (case body of [] -> ""; [x] -> x; _ -> "(" <> T.intercalate "," body <> ")"))
        Lem -> pure (capitalize pn <> " " <> (case body of [] -> ""; [x] -> x; _ -> T.unwords body))
        Twf -> twfSubstRhs pn body lhsPat
        _ -> pure (pn <> " " <> T.unwords body)
      pure [(deps, (prodName p, lhs, rhs), listFuncs)]
  where
    nodePn st = case st of
      StNode _ pn _ -> pn
      _ -> ""

-- | Ott's Twelf right-hand side of a substitution clause: each argument
-- the substitution changes is named by a fresh @NL@ variable, computed
-- by a premise.
twfSubstRhs :: Text -> [Text] -> Text -> P Text
twfSubstRhs pn body lhsPat = do
  let comp = drop 1 (strSplit lhsPat)
  if length comp /= length body
    then failP "Fatal error: exception Invalid_argument(\"List.map2\")"
    else pure ()
  freshVars <- forM (zip body comp) $ \(x, y) -> if x == y then pure "" else freshNl
  let pat = [if x == y then y else v | ((x, y), v) <- zip (zip body comp) freshVars]
      premise (x, y) v
        | x == y = pure Nothing
        | T.null x = failP "Fatal error: exception Invalid_argument(\"String.sub / Bytes.sub\")"
        | otherwise = pure (Just (T.init x <> " " <> v <> ")"))
  premises <- catMaybes <$> zipWithM premise (zip body comp) freshVars
  pure ("(" <> pn <> " " <> T.unwords pat <> ")" <> " <- " <> T.intercalate " <- " premises)
  where
    -- @Str.split (Str.regexp "(\\| \\|)")@: a delimiter at either end
    -- does not delimit an empty string
    strSplit t =
      let ps = T.split (\c -> c == '(' || c == ' ' || c == ')') t
          ps' = case ps of
            "" : more -> more
            _ -> ps
       in case reverse ps' of
            "" : more -> reverse more
            _ -> ps'

requireLocallyNameless :: Env -> Bool
requireLocallyNameless env = any (\md -> any ((== "repr-locally-nameless") . fst) (mvdHoms md)) (specMetavars (envSpec env))

-- | Run a clause printer, with the dependencies it collects.
runD :: D a -> P (a, [Text])
runD m = runStateT m []

addDep :: Text -> D ()
addDep d = modify (d :)

ppSubstSte :: Env -> SubstCtx -> Suffix -> De -> Ste -> D (Text, [IntFunc])
ppSubstSte env sc sie de ste = case ste of
  SteSt (StNonterm ntrp nt) -> (\s -> (s, [])) <$> ppSubstNonterm env sc sie de ntrp nt
  SteMetavar _ mv -> (\s -> (s, [])) <$> liftP (ppMetavarWithDeWithSie env sie de mv)
  SteList [StliListform b es] -> ppSubstListBody env sc sie de b es
  _ -> error "Haskott.Prover.Substs: not a canonical symterm element"

ppSubstNonterm :: Env -> SubstCtx -> Suffix -> De -> Text -> (Text, Suffix) -> D Text
ppSubstNonterm env sc sie de ntrp nt = do
  ntS <- liftP (ppNontermWithDeWithSie env sie de nt)
  let sb = scSubst sc
  if ntrp `notElem` scDomain sc
    then pure ntS
    else do
      let bound = glommedBoundThings env (scProd sc) (sbThat sb) nt
          thisS = ppNonterm env (scThis sc)
          thatS = ppNtOrMv env (scThat sc)
          tyThat = ppNtOrMvRootTy env (sbThat sb)
          thatInBound = liftP $ case envTarget env of
            Isa -> (\m -> thatS <> " : set " <> m) <$> ppMseString env sie de bound
            Hol -> (\m -> "MEM " <> thatS <> " " <> m) <$> ppMseString env sie de bound
            Caml -> (\m -> "List.mem " <> thatS <> " " <> "(" <> m <> ")") <$> ppMseString env sie de bound
            Lem -> (\m -> " List.elem " <> thatS <> " " <> "(" <> m <> ")") <$> ppMseString env sie de bound
            Coq -> do
              ppListMem env
              (m, _, _) <- ppMse env sie de False "" (Just (sbThat sb)) bound
              pure ("list_mem " <> "eq_" <> tyThat <> " " <> thatS <> " " <> m)
            Twf -> pure "<<< mem FZ no idea >>>"
          isEmpty = case bound of
            Empty -> True
            _ -> False
      if sbMultiple sb
        then do
          let depName = ppNontermroot env (promoteNtr env ntrp)
              sname = substName (sbName sb) depName
          addDep sname
          if isTwf env then pure "<<< filter FZ no idea >>>" else do
           filtered <-
            if isEmpty
              then pure (scSub sc)
              else case envTarget env of
                Isa -> (\t -> "(List.filter " <> "(%(" <> thatS <> "," <> thisS <> ")." <> "Not(" <> t <> ")" <> ")" <> " " <> scSub sc <> ")") <$> thatInBound
                Hol -> (\t -> "(FILTER " <> "(\\(" <> thatS <> "," <> thisS <> "). " <> "~(" <> t <> "))" <> " " <> scSub sc <> ")") <$> thatInBound
                Coq
                  | optCoqUseFilterFn (envOpts env) -> do
                      liftP (ppListFilter env)
                      t <- thatInBound
                      pure
                        ( "(list_filter " <> "(fun (tmp:" <> tyThat <> "*" <> ppNontermrootTy env (sbThis sb) <> ") => "
                            <> "match tmp with (" <> thatS <> "," <> thisS <> ") => negb (" <> t <> ") end)" <> " " <> scSub sc <> ")"
                        )
                  | otherwise -> do
                      liftP (ppListMinus2 env)
                      (m, _, _) <- liftP (ppMse env sie de False "" (Just (sbThat sb)) bound)
                      pure ("(list_minus2 " <> "eq_" <> tyThat <> " " <> scSub sc <> " " <> m <> ")")
                _ -> (\t -> "(List.filter " <> "(fun (" <> thatS <> "," <> thisS <> ") -> " <> "not(" <> t <> ")" <> ")" <> " " <> scSub sc <> ")") <$> thatInBound
           pure ("(" <> sname <> " " <> filtered <> " " <> ntS <> ")")
        else do
          let ident = ppNontermroot env (promoteNtr env ntrp)
              sname = substName (sbName sb) ident
          addDep sname
          let substituted = "(" <> sname <> " " <> thisS <> " " <> ppNtOrMv env (scThat sc) <> " " <> ntS <> ")"
          if isEmpty
            then pure substituted
            else (\t -> "(" <> "if " <> t <> " then " <> ntS <> " else " <> substituted <> ")") <$> thatInBound

-- | Ott's @freshen@: each name numbered by its occurrences so far.
freshen :: [Text] -> [Text]
freshen = go (M.empty :: M.Map Text Int)
  where
    go seen xs = case xs of
      [] -> []
      h : t ->
        let n = M.findWithDefault 0 h seen + 1
         in (h <> T.pack (show n)) : go (M.insert h n seen) t

makeDepElements :: [Ste] -> [Text]
makeDepElements es = makeDepSymterm (StNode "" "" es)

ppSubstListBody :: Env -> SubstCtx -> Suffix -> De -> Bound -> [Ste] -> D (Text, [IntFunc])
ppSubstListBody env sc sie de bound els = do
  let sb = scSubst sc
      de1i = de1Lookup (fst de) bound
  bodyTmp <- map fst <$> mapM (ppSubstSte env sc (SiVar "_" 0 : sie) de) els
  let ppBody = let tmp = T.intercalate "," bodyTmp in if length els > 1 then "(" <> tmp <> ")" else tmp
      commonLhs
        | sbMultiple sb = scSub sc
        | otherwise = ppNonterm env (scThis sc) <> " " <> ppNtOrMv env (scThat sc)
  if de1Pattern de1i == ppBody
    then pure (de1CompoundId de1i, [])
    else do
      (ident, funcs) <- liftP (makeAuxFuncsList env sc els commonLhs)
      let body = "(" <> ident <> " " <> commonLhs <> " " <> de1CompoundId de1i <> ")"
          pat = de1Pattern de1i
          cid = de1CompoundId de1i
      case envTarget env of
        Isa -> pure (body, funcs)
        Hol -> pure ("(MAP (\\" <> pat <> ". " <> ppBody <> ") " <> cid <> ")", [])
        Coq
          | optCoqExpandLists (envOpts env) -> pure (body, funcs)
          | length (splitParensCommas pat) == 1 -> pure ("(map (fun (" <> pat <> ":" <> de1CoqTypeOfPattern de1i <> ") => " <> ppBody <> ") " <> cid <> ")", [])
          | otherwise -> pure ("(map (fun (pat_:" <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> pat <> " => " <> ppBody <> " end) " <> cid <> ")", [])
        Caml -> pure ("(List.map (fun " <> pat <> " -> " <> ppBody <> ") " <> cid <> ")", [])
        Lem -> pure (" (List.map (fun " <> pat <> " -> " <> ppBody <> ") " <> cid <> ")", [])
        Twf -> liftP (failP "internal (Twelf): make_aux_funcs")

substHeaderOf :: Env -> Substitution -> Text -> Text
substHeaderOf env sb typ
  | not (sbMultiple sb) = ppNontermrootTy env (sbThis sb) <> " => " <> ppNtOrMvRootTy env (sbThat sb) <> " => " <> typ <> " => " <> typ <> "\"\n"
  | otherwise = "(" <> ppNtOrMvRootTy env (sbThat sb) <> "*" <> ppNontermrootTy env (sbThis sb) <> ") list => " <> typ <> " => " <> typ <> "\"\n"

makeAuxFuncsList :: Env -> SubstCtx -> [Ste] -> Text -> P (Text, [IntFunc])
makeAuxFuncsList env sc els commonLhs = do
  let sb = scSubst sc
      nm = makeNameElements env False els
      ident = substName (sbName sb) nm <> "_list"
      depId0 = substName (sbName sb) nm
  case envTarget env of
    Twf -> failP "internal (Twelf): make_aux_func_list"
    Coq
      | optCoqExpandLists (envOpts env) -> do
          let suf = "list_" <> nm
              tyThis = ppNontermrootTy env (sbThis sb)
              tyThat = ppNtOrMvRootTy env (sbThat sb)
              inV = ppNonterm env (scIn sc)
              header =
                ( ident
                    <> ( if sbMultiple sb
                           then " (" <> scSub sc <> ":list (" <> tyThat <> "*" <> tyThis <> "))"
                           else " (" <> ppNonterm env (scThis sc) <> ":" <> tyThis <> ")" <> " (" <> ppNtOrMv env (scThat sc) <> ":" <> tyThat <> ")"
                       )
                    <> " (" <> inV <> ":" <> suf <> ")"
                , " {struct " <> inV <> "}"
                , " : " <> suf <> " :=\n" <> "  match " <> inV <> " with\n"
                )
              args = splitParensStars (makeNameElements env True els)
              freshArgs = if length args > 1 then [x <> T.pack (show i) | (i, x) <- zip [1 :: Int ..] args] else args
              lp = T.unwords freshArgs
              rp = nm <> "_tl"
              calls = [(n `elem` scDomain sc, n, x) | (n, x) <- zip args freshArgs]
              rhs = T.unwords [if inDom then "(" <> substName (sbName sb) n <> " " <> commonLhs <> " " <> x <> ")" else x | (inDom, n, x) <- calls]
              rhsDeps = reverse [substName (sbName sb) n | (True, n, _) <- calls]
          pure
            ( ident
            , [ IntFunc
                  { rFunId = ident
                  , rFunDep = ident : rhsDeps
                  , rFunType = suf
                  , rFunHeader = header
                  , rFunClauses =
                      [ ("", "Nil_" <> suf, "Nil_" <> suf)
                      , ("", "Cons_" <> suf <> " " <> lp <> " " <> rp, "Cons_" <> suf <> " " <> rhs <> " (" <> ident <> " " <> commonLhs <> " " <> rp <> ")")
                      ]
                  }
              ]
            )
      | otherwise -> pure ("", [])
    Caml -> pure ("", [])
    _ -> do
      let typ = makeNameElements env True els <> " list"
      splitSuffix <-
        if isIsa env && optIsaPrimrec (envOpts env)
          then do
            let pre = if scFlag sc then "_" <> prodName (scProd sc) else ""
            c <- bumpCounter "subst_split_inprod" (typ <> pre)
            pure (pre <> c)
          else pure ""
      let header = ident <> splitSuffix <> " :: \"" <> substHeaderOf env sb typ
          lp = hideIsaTrailingUnderscore env (nm <> "_")
          rp = hideIsaTrailingUnderscore env (nm <> "_list_")
          (depId, depFuncs)
            | T.any (== '*') (makeNameElements env True els) = (depId0 <> splitSuffix, makeAuxFuncsTuple env sc splitSuffix els commonLhs)
            | otherwise = (depId0, [])
          func =
            IntFunc
              { rFunId = ident <> splitSuffix
              , rFunDep = [depId, ident <> splitSuffix]
              , rFunType = typ <> splitSuffix
              , rFunHeader = (header, "", "")
              , rFunClauses =
                  [ ("", commonLhs <> " Nil", "Nil")
                  , ("", commonLhs <> " (" <> lp <> "#" <> rp <> ")", "(" <> depId <> " " <> commonLhs <> " " <> lp <> ") # (" <> ident <> splitSuffix <> " " <> commonLhs <> " " <> rp <> ")")
                  ]
              }
      pure (ident <> splitSuffix, func : depFuncs)

makeAuxFuncsTuple :: Env -> SubstCtx -> Text -> [Ste] -> Text -> [IntFunc]
makeAuxFuncsTuple env sc splitSuffix els commonLhs = case els of
  [] -> error "Haskott.Prover.Substs: make_aux_funcs_tuple of no elements"
  elHd : elTl ->
    let sb = scSubst sc
        domain = scDomain sc
        single = length elTl == 1
        nm = makeNameElements env False els
        nameTl = makeNameElements env False elTl <> (if single then "" else splitSuffix)
        ident = substName (sbName sb) nm
        depEl = if single then makeDepElements els else makeDepElements [elHd] ++ [nameTl]
        depId = map (substName (sbName sb)) (nameTl : filter (`elem` domain) depEl)
        typ
          | single = makeNameElements env True els
          | otherwise = makeNameElements env True [elHd] <> "*" <> makeNameElements env True elTl
        header = ident <> splitSuffix <> " :: \"" <> substHeaderOf env sb typ
        fresh = freshen depEl
        lhs = " (" <> T.intercalate "," fresh <> ")"
        (elsHd, elsTl) = case zip depEl fresh of
          [h, t] -> (h, t)
          _ -> error "internal: never happen in make_aux_funcs_tuple"
        makeCall (el, elf) = if el `elem` domain then substName (sbName sb) el <> " " <> commonLhs <> " " <> elf else elf
        comp1 = makeCall elsHd
        (comp2, aux2)
          | single = (makeCall elsTl, [])
          | otherwise = (substName (sbName sb) nameTl <> " " <> commonLhs <> " " <> snd elsTl, makeAuxFuncsTuple env sc splitSuffix elTl commonLhs)
     in IntFunc (ident <> splitSuffix) depId (typ <> splitSuffix) (header, "", "") [("", commonLhs <> lhs, comp1 <> " , " <> comp2)] : aux2

------------------------------------------------------------------------
-- Free variables

-- | Ott's @pp_freevars@.
ppFreevars :: Env -> [Freevar] -> P Collapsed
ppFreevars env fvs = concat <$> forM fvs (\fv -> collapse env <$> fooWithDependencies env (freevarNeeded fv) (ppFreevarRule env fv))

freevarNeeded :: Freevar -> Text -> Prod -> Bool
freevarNeeded fv ntr p
  | fvThis fv == ntr = case prodElements p of
      [Nonterm ntrp _ _] -> fvThat fv == Ntr ntrp
      [Metavar mvrp _ _] -> fvThat fv == Mvr mvrp
      _ -> False
  | otherwise = False

hasIsaSetHom :: Freevar -> Bool
hasIsaSetHom fv = any ((== "isa-set") . fst) (fvHoms fv)

fvName' :: Text -> Text -> Text
fvName' = substName

ppFreevarRule :: Env -> Freevar -> [Text] -> Rule -> P [IntFunc]
ppFreevarRule env fv domain r = do
  let flag = isaListNameFlag r
  fvProds <- mapM (ppFreevarProd env fv domain flag (ruleName r)) (nonMetaProds r)
  ln <- psCoqLocallyNameless <$> get
  let clauses = [c | (_, c, _) <- fvProds]
      funcs = concat [f | (_, _, f) <- fvProds]
      dep = concat [d | (d, _, _) <- fvProds]
      freshVar = freshNt (ntsOfSymterms (stsForLhss env r)) (secondaryNtr env (ruleName r), [])
      tyThat = ppNtOrMvRootTy env (fvThat fv)
      tyR = ppNontermrootTy env (ruleName r)
      header = case envTarget env of
        Coq ->
          ( fvName' (fvName fv) (ruleName r) <> " (" <> ppNonterm env freshVar <> ":" <> tyR <> ") "
          , ""
          , (if ln then ": vars" else ": list " <> tyThat) <> " :=\n  match " <> ppNonterm env freshVar <> " with\n"
          )
        Isa -> (fvName' (fvName fv) (ppNontermroot env (ruleName r)) <> " :: \"" <> tyR <> " => " <> tyThat <> (if hasIsaSetHom fv then " set" else " list") <> "\"\n", "", "")
        Hol -> ("", "", "")
        Twf -> (fvName' (fvName fv) (ruleName r) <> " : " <> tyR <> " -> " <> "natlist -> type.\n", "", "")
        _ ->
          ( fvName' (fvName fv) (ppNontermroot env (ruleName r)) <> " (" <> ppNonterm env freshVar <> ":" <> tyR <> ") "
          , ""
          , ": " <> (if isCaml env then tyThat <> " list" else " list " <> tyThat) <> " =\n  match " <> ppNonterm env freshVar <> " with\n"
          )
      ident = fvName' (fvName fv) (ppNontermroot env (ruleName r))
  pure (IntFunc ident (dep ++ map rFunId funcs) (ruleName r) header clauses : funcs)

ppFreevarProd :: Env -> Freevar -> [Text] -> Bool -> Text -> Prod -> P ([Text], (Text, Text, Text), [IntFunc])
ppFreevarProd env fv domain flag rnn p = do
  let lhsSt = canonicalNode rnn p
      lhsEs = case lhsSt of
        StNode _ _ es -> es
        _ -> []
  (de, _) <- boundExtraction' env [lhsSt]
  lhs <- ppSymterm env [] de lhsSt
  resetCounter "fv_list_split_inprod"
  ln <- psCoqLocallyNameless <$> get
  let singleton thingS =
        let rhs
              | isIsa env && hasIsaSetHom fv = "{" <> thingS <> "}"
              | isCoq env = if ln then "{{" <> thingS <> "}}" else "(cons " <> thingS <> " nil)"
              | isTwf env = "(natlist/cons " <> thingS <> " natlist/nil)"
              | otherwise = "[" <> thingS <> "]"
         in pure ([], (prodName p, lhs, rhs), [])
  case prodElements p of
    [Nonterm ntrp _ _]
      | rnn == fvThis fv && fvThat fv == Ntr ntrp -> case lhsEs of
          [SteSt (StNonterm _ nt0)] -> singleton (ppNonterm env nt0)
          _ -> error "internal error: lhs_stnb not of the right form"
    [Metavar mvrp _ _]
      | rnn == fvThis fv && fvThat fv == Mvr mvrp -> case lhsEs of
          [SteMetavar _ mv0] -> singleton (ppMetavar env mv0)
          _ -> error "internal error: lhs_stnb not of the right form"
    _ -> do
      (results, deps) <- runD (mapM (ppFvSte env fv domain rnn p [] de flag) lhsEs)
      let elements = catMaybes (map fst results)
          funcs = concatMap snd results
      rhs <- case elements of
        []
          | isIsa env && hasIsaSetHom fv -> pure "{}"
          | isCoq env -> pure (if ln then "{}" else "nil")
          | isTwf env -> pure "natlist/nil"
          | otherwise -> pure "[]"
        _ -> case envTarget env of
          Isa | hasIsaSetHom fv -> pure (T.intercalate " \\<union> " elements)
          Hol -> pure (T.intercalate " ++ " elements)
          Coq -> pure (if ln then T.intercalate " \\u " elements else insertAppend elements)
          Twf -> insertAppendTwf elements
          _ -> pure (T.intercalate (listAppend env) elements)
      pure (deps, (prodName p, lhs, rhs), funcs)

ppFvSte :: Env -> Freevar -> [Text] -> Text -> Prod -> Suffix -> De -> Bool -> Ste -> D (Maybe Text, [IntFunc])
ppFvSte env fv domain rnn p sie de flag ste = case ste of
  SteSt (StNonterm ntrp nt) -> (\s -> (s, [])) <$> ppFvNonterm env fv domain p sie de ntrp nt
  SteMetavar {} -> pure (Nothing, [])
  SteList [StliListform b es] -> ppFvListBody env fv domain rnn p sie de flag b es
  _ -> error "Haskott.Prover.Substs: not a canonical symterm element"

ppFvNonterm :: Env -> Freevar -> [Text] -> Prod -> Suffix -> De -> Text -> (Text, Suffix) -> D (Maybe Text)
ppFvNonterm env fv domain p sie de ntrp nt = do
  ntS <- liftP (ppNontermWithDeWithSie env sie de nt)
  recursive <-
    if ntrp `elem` domain
      then do
        let ident = ppNontermroot env ntrp
        addDep (fvName' (fvName fv) ident)
        let call = fvName' (fvName fv) ident <> " " <> ntS
        pure (Just (if isTwf env then call else "(" <> call <> ")"))
      else pure Nothing
  let bound = glommedBoundThings env p (fvThat fv) nt
  case (recursive, bound) of
    (Nothing, _) -> pure Nothing
    (Just s, Empty) -> pure (Just s)
    (Just s, _)
      | isTwf env -> do
          result <- liftP freshNl
          interm <- liftP freshNl
          m <- liftP (ppMseString env sie de bound)
          pure (Just (result <> " <- " <> s <> " " <> interm <> " <- " <> "list_minus/natlist " <> interm <> " " <> m <> " " <> result))
      | isIsa env && hasIsaSetHom fv -> (\m -> Just ("(" <> s <> " - set " <> m <> ")")) <$> liftP (ppMseString env sie de bound)
      | otherwise -> do
          liftP (ppListMinus env)
          m <- liftP (ppMseString env sie de bound)
          let eq = if isCoq env then "eq_" <> ppNtOrMvRootTy env (fvThat fv) <> " " else ""
          pure (Just ("(list_minus " <> eq <> s <> " " <> m <> ")"))

ppFvListBody :: Env -> Freevar -> [Text] -> Text -> Prod -> Suffix -> De -> Bool -> Bound -> [Ste] -> D (Maybe Text, [IntFunc])
ppFvListBody env _ _ _ _ _ _ _ _ _
  | isTwf env = liftP (failP "internal (Twelf): pp_fv_symterm_list_body")
ppFvListBody env fv domain rnn p sie de flag bound els = do
  let de1i = de1Lookup (fst de) bound
      sie' = SiVar "_" 0 : sie
  results <- mapM (ppFvSte env fv domain rnn p sie' de flag) els
  let bodyElements = catMaybes (map fst results)
      funcs = concatMap snd results
      bodyTmp = case envTarget env of
        Coq -> insertAppend bodyElements
        Isa | hasIsaSetHom fv -> T.intercalate " \\<union> " bodyElements
        _ -> T.intercalate (listAppend env) bodyElements
      body = if length bodyElements == 1 then bodyTmp else "(" <> bodyTmp <> ")"
      pat = de1Pattern de1i
      cid = de1CompoundId de1i
      opts = envOpts env
  case bodyElements of
    [] -> pure (Just (if isCoq env then "nil" else if isIsa env && hasIsaSetHom fv then "{}" else "[]"), funcs)
    _ -> case envTarget env of
      Twf -> error "Haskott.Prover.Substs: pp_fv_symterm_list_body"
      Isa
        | optIsaPrimrec opts -> do
            let args = T.intercalate "_" [ppNtOrMvWithSie env (SiVar "" 0 : sie) x | (x, _) <- de1Ntmvsns de1i]
                postName = makeNameElements env False els
                typList = makeNameElements env True els <> " list"
                idList = fvName' (fvName fv) postName <> "_list"
                idTuple = fvName' (fvName fv) postName
                pre = if flag then "_" <> prodName p else ""
                outputTyp = ppNtOrMvRootTy env (fvThat fv) <> " list"
                hide = hideIsaTrailingUnderscore env
            c <- liftP (bumpCounter "fv_list_split_inprod" (typList <> pre))
            let splitSuffix = pre <> c
            (rhsSc, tupleAux, listDeps) <-
              if length (de1Ntmvsns de1i) == 1
                then do
                  ds <- get
                  pure (body, [], ds)
                else do
                  let pattern = [ppNtOrMvWithSie env (SiPunct "" : sie) x | (x, _) <- de1Ntmvsns de1i]
                  aux <- makeAuxFuncsTupleFv env fv domain rnn p sie de flag splitSuffix els pattern
                  pure ("(" <> idTuple <> splitSuffix <> " " <> hide (args <> "_") <> ")", aux, [idTuple <> splitSuffix])
            let func =
                  IntFunc
                    { rFunId = idList <> splitSuffix
                    , rFunDep = (idList <> splitSuffix) : listDeps
                    , rFunType = typList <> splitSuffix
                    , rFunHeader = (idList <> splitSuffix <> " :: \"" <> typList <> " => " <> outputTyp <> "\"\n", "", "")
                    , rFunClauses =
                        [ ("", "Nil", "[]")
                        , ("", "(" <> hide (args <> "_") <> "#" <> hide (args <> "_list_") <> ")", rhsSc <> listAppend env <> "(" <> idList <> splitSuffix <> " " <> hide (args <> "_list_") <> ")")
                        ]
                    }
            pure (Just ("(" <> idList <> splitSuffix <> " " <> args <> "_list)"), func : tupleAux)
        | hasIsaSetHom fv -> pure (Just ("(\\<Union>" <> pat <> "\\<in> set " <> cid <> ". " <> T.intercalate " \\<union> " bodyElements <> ")"), funcs)
        | otherwise -> pure (Just ("(concat (map (%" <> pat <> ". " <> T.intercalate (listAppend env) bodyElements <> ") " <> cid <> "))"), funcs)
      Hol -> pure (Just ("(FLAT (MAP (\\" <> pat <> ". " <> T.intercalate " ++ " bodyElements <> ") " <> cid <> "))"), funcs)
      Caml -> pure (Just ("(List.flatten (List.map (fun " <> pat <> " -> " <> T.intercalate (listAppend env) bodyElements <> ") " <> cid <> "))"), funcs)
      Lem -> pure (Just ("(List.concat (List.map (fun " <> pat <> " -> " <> T.intercalate " ++ " bodyElements <> ") " <> cid <> "))"), funcs)
      Coq
        | optCoqExpandLists opts -> do
            ds <- get
            let varList = splitParensCommas pat
                args = T.intercalate "_" [ppNtOrMvWithSie env (SiVar "" 0 : sie) x | (x, _) <- de1Ntmvsns de1i]
                postName = makeNameElements env False els
                suf = "list_" <> postName
                idList = fvName' (fvName fv) postName <> "_list"
                outputTyp = "list " <> ppNtOrMvRootTy env (fvThat fv)
                header = (idList <> " (l:" <> suf <> ")", "", " : " <> outputTyp <> " :=\n" <> "  match l with\n")
            pure
              ( Just ("(" <> idList <> " " <> args <> "_list)")
              , [ IntFunc
                    { rFunId = idList
                    , rFunDep = idList : ds
                    , rFunType = suf
                    , rFunHeader = header
                    , rFunClauses =
                        [ ("", "Nil_" <> suf, "nil")
                        , ("", "Cons_" <> suf <> " " <> T.unwords varList <> " " <> args <> "_list_", "app " <> body <> " " <> "(" <> idList <> " " <> args <> "_list_)")
                        ]
                    }
                ]
              )
        | length (splitParensCommas pat) == 1 -> do
            ln <- liftP (psCoqLocallyNameless <$> get)
            pure (Just ("(" <> (if ln then "union_map" else "flat_map") <> " (fun (" <> pat <> ":" <> de1CoqTypeOfPattern de1i <> ") => " <> T.intercalate " ++ " bodyElements <> ") " <> cid <> ")"), funcs)
        | otherwise ->
            pure (Just ("(flat_map (fun (pat_:" <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> pat <> " => " <> T.intercalate " ++ " bodyElements <> " end) " <> cid <> ")"), funcs)

makeAuxFuncsTupleFv :: Env -> Freevar -> [Text] -> Text -> Prod -> Suffix -> De -> Bool -> Text -> [Ste] -> [Text] -> D [IntFunc]
makeAuxFuncsTupleFv env fv domain rnn p sie de flag splitSuffix els pattern = case (els, pattern) of
  (elHd : elTl, patHd : patTl) -> do
    let single = length elTl == 1
        nm = makeNameElements env False els
        nameTl = makeNameElements env False elTl
        ident = fvName' (fvName fv) nm
        idTl = fvName' (fvName fv) nameTl
        typ
          | single = makeNameElements env True els
          | otherwise = makeNameElements env True [elHd] <> "*" <> makeNameElements env True elTl
        outputTyp = ppNtOrMvRootTy env (fvThat fv) <> " list"
        hide = hideIsaTrailingUnderscore env
        lhs
          | single = "(" <> T.intercalate "," [hide (s <> "_") | s <- pattern] <> ")"
          | otherwise = "(" <> hide (patHd <> "_") <> "," <> hide (T.intercalate "_" patTl <> "_") <> ")"
        sie' = SiVar "_" 0 : sie
    (rhs, aux) <-
      if single
        then do
          rs <- mapM (ppFvSte env fv domain rnn p sie' de flag) els
          pure (T.intercalate (listAppend env) (catMaybes (map fst rs)), [])
        else do
          let argTl = hide (T.intercalate "_" patTl <> "_")
          addDep (idTl <> splitSuffix)
          -- the pair is evaluated right to left
          aux <- makeAuxFuncsTupleFv env fv domain rnn p sie de flag splitSuffix elTl patTl
          (h, _) <- ppFvSte env fv domain rnn p sie' de flag elHd
          pure (maybe " " (<> listAppend env) h <> "(" <> idTl <> splitSuffix <> " " <> argTl <> ")", aux)
    deps <- get
    pure (IntFunc (ident <> splitSuffix) deps (typ <> splitSuffix) (ident <> splitSuffix <> " :: \"" <> typ <> " => " <> outputTyp <> "\"\n", "", "") [("", lhs, rhs)] : aux)
  _ -> error "Haskott.Prover.Substs: make_aux_funcs_tuple_fv of no elements"
