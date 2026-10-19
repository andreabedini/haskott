{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @transform.ml@: with @-coq_expand_list_types true@, each list
-- form of a Coq type becomes a type of its own (@list_t_u@ with
-- constructors @Nil_list_t_u@ and @Cons_list_t_u@), defined with the
-- rules that use it, together with functions to map, make, unmake, index
-- and append such lists.
module Haskott.Prover.ExpandLists
  ( Expanded (..)
  , expandLists
  , makeAuxListFuncs
  , ppListRule
  ) where

import Data.List (find)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Graft (TextRange)
import qualified Graft.Range as Range
import qualified Data.Set as Set
import Haskott.Prover.Dependency (computeDependencies)
import Haskott.Prover.Pp (ppElement, ppHomSpec, ppNtOrMvRootTy)
import Haskott.Prover.Types
import Haskott.Spec

-- | The expanded specification, the structure with the new list types
-- among the rules that introduce them, the list functions, the names of
-- the list types, the dependencies of the expanded rules and the
-- auxiliary functions extended over the list types; and the vertex
-- counter after the dependencies.
data Expanded a = Expanded
  { exSpec :: Spec
  , exStructure :: [(FilePath, Either [Text] a)]
  -- ^ groups of rules, and the other entries of the structure
  , exListAuxFuncs :: Text
  , exListTypes :: [Text]
  , exDeps :: Deps
  , exAuxfns :: [(Text, ([Text], RootRef))]
  , exVertex :: Int
  }

data IntCode
  = IcNone
  | IcAux Text Text RootRef
  | IcMetaVarListExp Text Text RootRef
  | IcNonTermListExp Text Text RootRef

dummyRetType :: RootRef
dummyRetType = Ntr "dummy_ret_type"

-- | Ott's @make_aux_list_funcs@.
makeAuxListFuncs :: Spec -> [Text] -> Text -> Text
makeAuxListFuncs spec t s =
  let used = map ruleName (specRules spec) ++ map mvdName (specMetavars spec)
      unused n = let ns = T.pack (show n) in if ("l" <> ns) `elem` used then unused (n + 1) else ns
      l = if "l" `elem` used then "l" <> unused (0 :: Int) else "l"
      hl = case t of
        [_] -> ["h"]
        _ -> ["h" <> T.pack (show i) | (i, _) <- zip [0 :: Int ..] t]
      h = T.unwords hl
      hComma = if length hl == 1 then h else "(" <> T.intercalate "," hl <> ")"
      tArrow = T.intercalate "->" t
      t' = if length t == 1 then tArrow else "(" <> T.intercalate " * " t <> ")"
   in T.concat
        [ "Fixpoint map_" <> s <> " (A:Type) (f:" <> tArrow <> "->A) (" <> l <> ":" <> s <> ") : list A :=\n"
        , "  match " <> l <> " with\n"
        , "  | Nil_" <> s <> " => nil\n"
        , "  | Cons_" <> s <> " " <> h <> " tl_ => cons (f " <> h <> ") (map_" <> s <> " A f tl_)\n  end.\n"
        , "Arguments map_" <> s <> " [A] _ _.\n\n"
        , "Fixpoint make_" <> s <> " (" <> l <> ": list " <> t' <> "): " <> s <> " :=\n"
        , "  match " <> l <> " with\n"
        , "  | nil  => Nil_" <> s <> "\n"
        , "  | cons " <> hComma <> " tl_ => Cons_" <> s <> " " <> h <> " (make_" <> s <> " tl_)\n  end.\n\n"
        , "Fixpoint unmake_" <> s <> " (" <> l <> ": " <> s <> "): list " <> t' <> " :=\n"
        , "  match " <> l <> " with\n"
        , "  | Nil_" <> s <> " => nil\n"
        , "  | Cons_" <> s <> " " <> h <> " tl_ => cons " <> hComma <> " (unmake_" <> s <> " tl_)\n  end.\n\n"
        , "Fixpoint nth_" <> s <> " (n:nat) (" <> l <> ": " <> s <> ") {struct n} : option " <> t' <> " :=\n"
        , "  match n," <> l <> " with\n"
        , "  | O, Cons_" <> s <> " " <> h <> " tl_ => Some " <> hComma <> "\n"
        , "  | O, _ => None\n"
        , "  | S m, Nil_" <> s <> " => None\n"
        , "  | S m, Cons_" <> s <> " " <> h <> " tl_ => nth_" <> s <> " m tl_\n"
        , "  end.\n\n"
        , "Fixpoint app_" <> s <> " (" <> l <> " m: " <> s <> "): " <> s <> " :=\n"
        , "  match " <> l <> " with\n"
        , "  | Nil_" <> s <> " => m\n"
        , "  | Cons_" <> s <> " " <> h <> " tl_ => Cons_" <> s <> " " <> h <> " (app_" <> s <> " tl_ m)\n"
        , "  end.\n\n"
        ]

-- | Ott's @pp_list_rule@: a list type a rule needs for its premises.
ppListRule :: Spec -> [RootRef] -> Text
ppListRule spec ss =
  let names = [case r of Ntr n -> n; Mvr n -> n | r <- ss]
      ident = "list_" <> T.intercalate "_" names
   in "Inductive " <> ident <> " : Set := Nil_" <> ident <> " | Cons_" <> ident
        <> T.concat [" (_:" <> n <> ")" | n <- names]
        <> " (tl_ : " <> ident <> ").\n\n"
        <> makeAuxListFuncs spec names ident

-- | Ott's @expand_element@.
expandElement :: Env -> [Bindspec] -> Element -> (Element, [Bindspec], [Rule], [(Text, ([Text], RootRef))])
expandElement env bs e = case e of
  ListForm lb ->
    let ss = mapMaybe root (lbElements lb)
        root x = case x of
          Nonterm ntr _ _ -> Just (Ntr (promoteNtr env ntr))
          Metavar mvr _ _ -> Just (Mvr mvr)
          Terminal _ -> Nothing
          ListForm _ -> error "Haskott.Prover.ExpandLists: expand element, cannot happen"
        ident = "list_" <> T.intercalate "_" (map (ppNtOrMvRootTy env) ss)
        idNt = (ident, [])
        idEl = Nonterm ident ident []
        universe =
          let us = [case r of Ntr n -> maybe "Set" (ppHomSpec env) (lookup "coq-universe" (ruleHoms (ruleOfNtr env n))); Mvr _ -> "Set" | r <- ss]
           in if all (== "Set") us then "Set" else "Type"
        primaryNtr n = primaryNtrOfNtr env n
        primaryMvr n = primaryMvrOfMvr env n
        update b = case b of
          AuxFnDef f (AuxList g (nt, s) bd) r
            | Ntr nt `elem` ss -> (AuxFnDef f (Aux g idNt) r, IcAux g nt dummyRetType)
            | otherwise -> (AuxFnDef f (AuxList g (nt, s) bd) r, IcNone)
          AuxFnDef f (NonTermListExp (ntr, s) bd) r
            | Ntr (primaryNtr ntr) `elem` ss -> (AuxFnDef f (Aux f idNt) r, IcNonTermListExp f ntr dummyRetType)
            | otherwise -> (AuxFnDef f (NonTermListExp (ntr, s) bd) r, IcNone)
          AuxFnDef f (MetaVarListExp (mvr, s) bd) r
            | Mvr (primaryMvr mvr) `elem` ss -> (AuxFnDef f (Aux f idNt) r, IcMetaVarListExp f mvr dummyRetType)
            | otherwise -> (AuxFnDef f (MetaVarListExp (mvr, s) bd) r, IcNone)
          Bind (NonTermListExp (ntr, s) bd) nt r ->
            let fname = "bind_" <> ident
             in if Ntr (primaryNtr ntr) `elem` ss
                  then (Bind (Aux fname idNt) nt r, IcNonTermListExp fname ntr (Ntr ntr))
                  else (Bind (NonTermListExp (ntr, s) bd) nt r, IcNone)
          Bind (MetaVarListExp (mvr, s) bd) nt r ->
            let fname = "bind_" <> ident
             in if Mvr (primaryMvr mvr) `elem` ss
                  then (Bind (Aux fname idNt) nt r, IcMetaVarListExp fname mvr (Mvr mvr))
                  else (Bind (MetaVarListExp (mvr, s) bd) nt r, IcNone)
          _ -> (b, IcNone)
        (bsN, auxToDef) = unzip (map update bs)
        nilBs = [AuxFnDef f Empty dummyRange | ic <- auxToDef, Just f <- [icName ic]]
        icName ic = case ic of
          IcNone -> Nothing
          IcAux f _ _ -> Just f
          IcMetaVarListExp f _ _ -> Just f
          IcNonTermListExp f _ _ -> Just f
        consBs =
          [ AuxFnDef f mse dummyRange
          | ic <- auxToDef
          , Just (f, mse) <- [case ic of
              IcNone -> Nothing
              IcAux f nt _ -> Just (f, Union (Aux f (nt, [])) (Aux f idNt))
              IcMetaVarListExp f mvr _ -> Just (f, Union (MetaVarExp (mvr, [])) (Aux f idNt))
              IcNonTermListExp f ntr _ -> Just (f, Union (NonTermExp (ntr, [])) (Aux f idNt))]
          ]
        removeSuffix x = case x of
          Nonterm ntr n _ -> Nonterm ntr n []
          Metavar mvr n _ -> Metavar mvr n []
          Terminal _ -> x
          ListForm _ -> error "Haskott.Prover.ExpandLists: remove suffix, cannot happen"
        prod nm es bspecs =
          Prod
            { prodName = nm
            , prodMeta = False
            , prodSugar = False
            , prodCategories = Set.empty
            , prodElements = es
            , prodHoms = []
            , prodDisambiguate = Nothing
            , prodBindspecs = bspecs
            , prodRange = dummyRange
            }
        auxRule =
          Rule
            { ruleName = ident
            , ruleNames = [(ident, [])]
            , rulePrefix = ""
            , ruleProds = [prod ("Nil_" <> ident) [] nilBs, prod ("Cons_" <> ident) (map removeSuffix (lbElements lb) ++ [idEl]) consBs]
            , ruleHoms = [("coq-universe", [HomString universe])]
            , ruleMeta = False
            , ruleSemiMeta = False
            , rulePhantom = False
            , ruleJudgement = False
            , ruleCategories = []
            , ruleRange = dummyRange
            }
        xtd = [(f, ([ident], rt)) | ic <- auxToDef, Just (f, rt) <- [case ic of
                IcNone -> Nothing
                IcAux f _ rt -> Just (f, rt)
                IcMetaVarListExp f _ rt -> Just (f, rt)
                IcNonTermListExp f _ rt -> Just (f, rt)]]
     in (idEl, bsN, [auxRule], xtd)
  _ -> (e, bs, [], [])

dummyRange :: TextRange
dummyRange = fromMaybe (error "range") (Range.fromEnds 0 0)

expandProd :: Env -> Prod -> (Prod, [Rule], [(Text, ([Text], RootRef))])
expandProd env p =
  let go bs els = case els of
        h : t ->
          let (e', bs', r', x') = expandElement env bs h
              (els'', bs'', rl'', x'') = go bs' t
           in (e' : els'', bs'', r' ++ rl'', x' ++ x'')
        [] -> ([], bs, [], [])
      (elsN, bsN, rlN, xN) = go (prodBindspecs p) (prodElements p)
   in (p {prodElements = elsN, prodBindspecs = bsN}, rlN, xN)

expandRule :: Env -> Rule -> ([Rule], [Text], [(Text, ([Text], RootRef))])
expandRule env r
  | ruleName r == "formula" || any ((== "coq") . fst) (ruleHoms r) = ([r], [], [])
  | otherwise =
      let (prods, newRules0, auxs) = unzip3 (map (expandProd env) (ruleProds r))
          newRules = [nr {ruleRange = ruleRange r} | nr <- concat newRules0]
       in (r {ruleProds = prods} : newRules, map ruleName newRules, concat auxs)

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicates more else x : removeDuplicates more

-- | Ott's @expand_lists_in_syntaxdefn@ for Coq with
-- @-coq_expand_list_types true@: the groups of rules of the structure
-- are expanded, in order.
expandLists :: Env -> (Text -> a) -> [(FilePath, Either [Text] a)] -> Int -> Expanded a
expandLists env embed structure vertex0 =
  let spec = envSpec env
      step (expandedNtrs, acc) (fn, entry) = case entry of
        Right other -> (expandedNtrs, acc ++ [((fn, Right other), Nothing)])
        Left br ->
          let (expandedNtrs', newstruct, expansions) = foldl expandOne (expandedNtrs, [], []) br
              expandOne (done, ns, ex) ntr =
                let (ers, nntrs, eauxfns) = expandRule env (ruleOfNtr env ntr)
                    newntrs = removeDuplicates [n | n <- nntrs, n `notElem` done]
                 in (newntrs ++ done, newntrs ++ ns, ex ++ [(ers, nntrs, eauxfns)])
              localRules = concat [ers | (ers, _, _) <- expansions]
              extractType x =
                let r = fromMaybe (error "Haskott.Prover.ExpandLists: no list rule") (find ((== x) . ruleName) localRules)
                    es = case ruleProds r of
                      (_ : p : _) -> prodElements p
                      _ -> error "Haskott.Prover.ExpandLists: list rule without Cons"
                 in mapMaybe (ppElement env [] True) (take (length es - 1) es)
              funcs = T.concat [makeAuxListFuncs spec (extractType x) x | x <- newstruct]
              rsEntry = ((fn, Left (newstruct ++ br)), Just expansions)
              entries = if T.null funcs then [rsEntry] else [rsEntry, ((fn, Right (embed funcs)), Nothing)]
           in (expandedNtrs', acc ++ entries)
      (_, expandedStructure) = foldl step ([], []) structure
      exps = concat [x | (_, Just x) <- expandedStructure]
      expandedRules = removeDupRules (concat [x | (x, _, _) <- exps])
      newRuleNames = removeDuplicates (concat [y | (_, y, _) <- exps])
      extendedAuxfns = removeDuplicates (concat [z | (_, _, z) <- exps])
      removeDupRules rs = case rs of
        [] -> []
        x : xs -> if any ((== ruleName x) . ruleName) xs then removeDupRules xs else x : removeDupRules xs
      listAuxFuncs = T.concat [makeAuxListFuncs spec (extractType' x) x | x <- newRuleNames]
      extractType' x =
        let r = fromMaybe (error "Haskott.Prover.ExpandLists: no list rule") (find ((== x) . ruleName) expandedRules)
            es = case ruleProds r of
              (_ : p : _) -> prodElements p
              _ -> error "Haskott.Prover.ExpandLists: list rule without Cons"
         in mapMaybe (ppElement env [] True) (take (length es - 1) es)
      merged = mergeAux (envAuxfnTypes env ++ extendedAuxfns)
      mergeAux axs = case axs of
        [] -> []
        (f, (ntl, ntmvr)) : tl ->
          let newTail = [x | x@(g, _) <- tl, g /= f]
              same = concat [ntl' | (g, (ntl', _)) <- tl, g == f]
           in (f, (same ++ ntl, ntmvr)) : mergeAux newTail
      spec' = spec {specRules = expandedRules}
      (deps, vertex1) = computeDependencies spec' "coq" vertex0
      structure' = map fst expandedStructure
   in Expanded spec' structure' listAuxFuncs newRuleNames deps merged vertex1
