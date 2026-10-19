{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @coq_induct.ml@: induction principles for Coq types with lists.
-- Coq's own induction principle for a type whose constructors take lists
-- of the type is too weak, so for each group of mutually recursive rules
-- with such a list (and no Coq hom) Ott prints a section with a predicate
-- per type and per list type, a hypothesis per production and per list
-- constructor, and the mutually recursive functions that prove the
-- predicates by structural recursion.
module Haskott.Prover.CoqInduct
  ( ppInduction
  ) where

import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Prover.Bounds
import Haskott.Prover.Dependency
import Haskott.Prover.Pp
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm (Symterm)

-- | The dependency group of a rule.
groupOf :: Env -> Text -> [RootRef]
groupOf env ntr = fromMaybe (error ("Haskott.Prover.CoqInduct: no dependency group for " ++ T.unpack ntr)) (find (Ntr ntr `elem`) (depTs (envDeps env)))

-- | Ott's @need_induction@: a non-meta rule with a list of a type of its
-- own group.
needInduction :: Env -> Rule -> Bool
needInduction env r =
  let recRules = groupOf env (ruleName r)
      elementUsesListNt e = case e of
        ListForm lb -> or [Ntr ntr `elem` recRules | Nonterm ntr _ _ <- lbElements lb]
        _ -> False
   in not (ruleMeta r) && any (any elementUsesListNt . prodElements) (ruleProds r)

-- | Ott's @rules_needing_induction@: the groups of mutually recursive rules
-- that need an induction principle.
rulesNeedingInduction :: Env -> [Rule] -> [[Text]]
rulesNeedingInduction env rs =
  let groups = removeDuplicates [[ntr | Ntr ntr <- groupOf env (ruleName r)] | r <- rs, needInduction env r]
   in filter (all (\ntr -> lookup "coq" (ruleHoms (ruleOfNtr env ntr)) == Nothing)) groups

-- | Ott's @make_index@: a counter per type, from 0.
nextIndex :: M.Map Text Int -> Text -> (Int, M.Map Text Int)
nextIndex m s = case M.lookup s m of
  Just i -> (i + 1, M.insert s (i + 1) m)
  Nothing -> (0, M.insert s 0 m)

-- | The variables of the types, each named by its type and its index.
indexed :: M.Map Text Int -> [Text] -> ([(Text, Text)], M.Map Text Int)
indexed m0 = go m0
  where
    go m ts = case ts of
      [] -> ([], m)
      t : more ->
        let (i, m') = nextIndex m t
            (rest, m'') = go m' more
         in ((t <> T.pack (show i), t) : rest, m'')

bounds :: Env -> [Symterm] -> P (De, De3)
bounds env sts = either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env sts)

-- | Ott's @generate_induction@ for a group of rules.
generateInduction :: Env -> [Text] -> P Text
generateInduction env ntrSet = do
  let ruleSet = map (ruleOfNtr env) ntrSet
      ruleNamesSet = map ruleName ruleSet
      ipName = T.intercalate "_" ntrSet <> "_rect"
      usedInTuple e = case e of
        Nonterm p _ _ -> let n = promoteNtr env p in [(n, n)]
        Metavar p _ _ -> [(p, p)]
        _ -> []
      inductiveTypesUsedInElement e = case e of
        Nonterm p _ _ ->
          let n = promoteNtr env p in [(n, n, Nothing) | n `elem` ruleNamesSet]
        ListForm lb ->
          let l = concatMap usedInTuple (lbElements lb)
           in if any ((`elem` ruleNamesSet) . fst) l
                then case l of
                  [] -> []
                  [(x, y)] -> [("list_" <> x, "list " <> y, Just y)]
                  _ ->
                    [ ( "list_" <> T.intercalate "_" (map fst l)
                      , "list (" <> T.intercalate "*" (map snd l) <> ")"
                      , Just (T.intercalate "*" (map snd l))
                      )
                    ]
                else []
        _ -> []
      inductiveTypesUsedInProd p
        | prodMeta p = []
        | otherwise = removeDuplicates (concatMap inductiveTypesUsedInElement (prodElements p))
      inductiveTypesUsedInRule r = removeDuplicates (concatMap inductiveTypesUsedInProd (ruleProds r))
      preDeclarations =
        removeDuplicates
          ( [(ruleName r, ppNontermrootTy env (ruleName r), Nothing) | r <- ruleSet]
              ++ concatMap inductiveTypesUsedInRule ruleSet
          )
      variablesAssoc = [(s, "P_" <> n) | (n, s, _) <- preDeclarations]
      listTypesUsed = [l | (_, _, Just l) <- preDeclarations]
      variablesDeclaration =
        "Variables\n  "
          <> T.intercalate "\n  " ["(P_" <> n <> " : " <> s <> " -> Prop)" | (n, s, _) <- preDeclarations]
          <> ".\n"
      predicateFor t v = maybe "" (\p -> p <> " " <> v <> " -> ") (lookup t variablesAssoc)
      makeHypothesis r p = do
        let concSt = canonicalNode (ruleName r) p
        (de@(de1, de2), de3) <- bounds env [concSt]
        conc <- ppSymterm env [] de concSt
        varList <- extractQuantifiedProofAssistantVars env de1 de2 de3
        let hyp = T.concat ["forall (" <> x <> ":" <> t <> "), " <> predicateFor t x | (x, _, (t, _)) <- varList]
            v = ppNontermrootTy env (ruleName r)
            concl = fromMaybe ("<<<" <> v <> ">>>") (lookup v variablesAssoc) <> " " <> conc
        pure (hyp <> concl)
  hypothesisFromRules <-
    T.intercalate "\n  " . concat
      <$> mapM
        ( \r ->
            mapM
              (\p -> (\s -> "(H_" <> prodName p <> " : " <> s <> ")") <$> makeHypothesis r p)
              (filter (not . prodMeta) (ruleProds r))
        )
        ruleSet
  let listHypothesis idx t =
        let types = splitParensStars t
            (varsTypes, idx') = indexed idx types
            n = T.intercalate "_" types
            xl = n <> "_l"
            tl = "list " <> (if length types == 1 then t else "(" <> t <> ")")
            consArg = case varsTypes of
              [(v, _)] -> v
              _ -> "(" <> T.intercalate "," (map fst varsTypes) <> ")"
         in ( "  (H_list_" <> n <> "_nil : P_list_" <> n <> " nil)\n"
                <> "  (H_list_" <> n <> "_cons : "
                <> T.concat ["forall (" <> v <> ":" <> ty <> "), " <> predicateFor ty v | (v, ty) <- varsTypes]
                <> "forall (" <> xl <> ":" <> tl <> "), "
                <> predicateFor tl xl
                <> maybe "<<>>" (\p -> p <> " (cons " <> consArg <> " " <> xl <> ")") (lookup tl variablesAssoc)
                <> ")"
            , idx'
            )
      (listHyps, index1) = foldl (\(acc, idx) t -> let (h, idx') = listHypothesis idx t in (acc ++ [h], idx')) ([], M.empty) listTypesUsed
      hypothesisDeclaration = "Hypothesis\n  " <> hypothesisFromRules <> "\n" <> T.intercalate "\n" listHyps <> ".\n"
      assocOrDie t = fromMaybe (error ("Haskott.Prover.CoqInduct: no predicate for " ++ T.unpack t)) (lookup t variablesAssoc)
      inductionCall idx (v, _, (t, l)) = case l of
        Just lt ->
          let types = splitParensStars lt
              (varsTypes, idx') = indexed idx types
           in if any (`elem` ruleNamesSet) types
                then
                  let nameL = v <> "_ott_ind"
                      n = T.intercalate "_" types
                      lArg = n <> "_l"
                      consArg = case varsTypes of
                        [(x, _)] -> x
                        _ -> "(" <> T.intercalate "," (map fst varsTypes) <> ")"
                   in ( Just
                          ( "(((fix " <> nameL <> " (" <> lArg <> ":" <> t <> ") : "
                              <> assocOrDie t <> " " <> lArg <> " := "
                              <> "match " <> lArg <> " as x return " <> assocOrDie t <> " x with "
                              <> "nil => H_list_" <> n <> "_nil"
                              <> (" | cons " <> consArg <> " xl" <> " =>")
                              <> " H_list_" <> n <> "_cons "
                              <> T.unwords [x <> (if ty `elem` ruleNamesSet then "(" <> ty <> "_ott_ind " <> x <> ")" else " ") | (x, ty) <- varsTypes]
                              <> "xl (" <> nameL <> " xl) "
                              <> "end)) " <> v <> ")"
                          )
                      , idx'
                      )
                else (Nothing, idx')
        Nothing -> (if t `elem` ruleNamesSet then Just ("(" <> t <> "_ott_ind " <> v <> ")") else Nothing, idx)
      clauseOf r (idx, acc) p = do
        let lhsSt = canonicalNode (ruleName r) p
        (de@(de1, de2), de3) <- bounds env [lhsSt]
        lhs <- ppSymterm env [] de lhsSt
        varList <- extractQuantifiedProofAssistantVars env de1 de2 de3
        let step (i, acc') var@(v, _, _) = let (call, i') = inductionCall i var in (i', acc' ++ [Just v, call])
            (idx', ext) = foldl step (idx, []) varList
            rhs = "H_" <> prodName p <> " " <> T.unwords (mapMaybe id ext)
        pure (idx', acc ++ [("", lhs, rhs)])
      functionOf (idx, acc) r = do
        let name = ppNontermrootTy env (ruleName r)
            indIp = assocOrDie name
        (idx', clauses) <- foldlM (clauseOf r) (idx, []) (filter (not . prodMeta) (ruleProds r))
        let func =
              IntFunc
                { rFunId = name <> "_ott_ind"
                , rFunDep = [ppNontermrootTy env (ruleName r') <> "_ott_ind" | r' <- ruleSet]
                , rFunType = name
                , rFunHeader = (name <> "_ott_ind (n:" <> ruleName r <> ") : " <> indIp <> " " <> "n :=\n", "", "  match n as x return " <> indIp <> " x with\n")
                , rFunClauses = clauses
                }
        pure (idx', acc ++ [func])
  (_, functionInt) <- foldlM functionOf (index1, []) ruleSet
  functionDefinition <- compute env (collapse env (IntFuncs functionInt Nothing))
  pure
    ( "Section " <> ipName <> ".\n\n"
        <> variablesDeclaration <> "\n"
        <> hypothesisDeclaration <> "\n"
        <> functionDefinition
        <> "End " <> ipName <> ".\n"
    )
  where
    foldlM f z xs = case xs of
      [] -> pure z
      x : more -> f z x >>= \z' -> foldlM f z' more

-- | Ott's @pp_induction@.
ppInduction :: Env -> [Rule] -> P Text
ppInduction env rs = T.intercalate "\n\n" <$> mapM (generateInduction env) (rulesNeedingInduction env rs)
