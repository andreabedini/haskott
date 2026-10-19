{-# LANGUAGE OverloadedStrings #-}

-- | The prover half of Ott's @defns.ml@: each definition class as an
-- inductive relation, each rule as a clause quantified over its variables
-- (with the subrule predicates of the nonterminals it uses at non-free
-- types and, in Coq, the hypotheses of its projections from lists), and
-- each function class as mutually recursive functions sorted by their
-- dependencies.
module Haskott.Prover.Defns
  ( ppFunOrRelnDefnclassList
  , nonFreeNtrs
  ) where

import Control.Monad (forM)
import Control.Monad.Trans.State.Strict (get, modify)
import Data.List (find, partition)
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Defns
import Haskott.Prover.Bounds
import Haskott.Prover.Dependency
import Haskott.Prover.ExpandLists (ppListRule)
import Haskott.Prover.Pp
import Haskott.Prover.Types
import Haskott.SourceLoc (druleLoc)
import Haskott.Spec
import Haskott.Term.Symterm

-- | Ott's @non_free_ntrs@: the primary roots with non-free definitions,
-- those on the left of a subrule and those whose productions mention
-- one, each with the root of the free type it is carved out of.
nonFreeNtrs :: Env -> [Subrule] -> [(Text, Text)]
nonFreeNtrs env srs =
  let spec = envSpec env
      rs = [r | r <- specRules spec, not (ruleMeta r), homSpecForTarget env (ruleHoms r) == Nothing]
      mentions = [(ruleName r, primaryNtrsUsedInRule spec Nothing False r) | r <- rs]
      f xs = Set.union xs (Set.fromList [n | (n, ns) <- mentions, not (Set.null (Set.intersection xs ns))])
      ntrs0 = Set.fromList (map srLower srs)
      fixedpoint g x = let x' = g x in if x == x' then x' else g x'
      others = Set.toList (Set.difference (fixedpoint f ntrs0) ntrs0)
   in [(srLower sr, srTop sr) | sr <- srs] ++ [(x, x) | x <- others]

-- | Ott's @pp_subntr@.
ppSubntr :: Env -> (Text, Text, (Text, Suffix)) -> Text
ppSubntr env (ntrl, ntru, (ntr', suff)) =
  let ntr'' = if isTwf env then T.toUpper ntr' else ntr'
      s = ppIs ntrl ntru <> " " <> hideIsaTrailingUnderscore env (ntr'' <> ppSuffixWithSie sieProject suff)
   in if isCoq env && not (optCoqExpandLists (envOpts env)) then "Is_true (" <> s <> ")" else s

-- | Ott's @pp_listsubntr@.
ppListsubntr :: Env -> [([(Text, Text, (Text, Suffix))], Text, Text, Text)] -> [Text]
ppListsubntr env listsubntrs =
  [ clause
  | (subntrs, squished, pattern, coqType) <- listsubntrs
  , subntr <- subntrs
  , let sub = ppSubntr env subntr
        tyList = splitParensStars coqType
        listArg
          | optCoqExpandLists (envOpts env) = "(unmake_list_" <> T.intercalate "_" tyList <> " " <> squished <> ")"
          | otherwise = squished
        clause = case envTarget env of
          Isa -> "List.list_all " <> "(%" <> pattern <> ". " <> sub <> ") " <> squished
          Hol -> "EVERY " <> "(\\" <> pattern <> ". " <> sub <> ") " <> squished
          Lem -> "List.all " <> "(fun " <> pattern <> " -> " <> sub <> ") " <> squished
          Coq
            | T.any (== '*') coqType ->
                "(Forall (fun (tmp_:" <> coqType <> ") => match tmp_ with " <> pattern <> " => " <> sub <> " end) " <> listArg <> ")"
            | otherwise -> "(Forall (fun (" <> pattern <> ":" <> coqType <> ") => " <> sub <> ") " <> listArg <> ")"
          Caml -> error "Haskott.Prover.Defns: pp_listsubntr"
          Twf -> error "Haskott.Prover.Defns: pp_listsubntr"
  ]

-- | Ott's @collapse_quantifications@: @(e1:term) (e2:term)@ becomes
-- @(e1 e2:term)@.
collapseQuantifications :: [(Text, Maybe Text)] -> [([Text], Maybe Text)]
collapseQuantifications = collapseNone
  where
    collapseNone l = case l of
      [] -> []
      (v, Nothing) : tl -> ([v], Nothing) : collapseNone tl
      (v, Just t) : tl -> collapseSome [v] t tl
    collapseSome b t l = case l of
      [] -> [(b, Just t)]
      (v, Nothing) : tl -> (b, Just t) : ([v], Nothing) : collapseNone tl
      (v, Just t1) : tl
        | t == t1 -> collapseSome (b ++ [v]) t1 tl
        | otherwise -> (b, Just t) : collapseSome [v] t1 tl

bounds :: Env -> [Symterm] -> P (De, De3)
bounds env sts = either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env sts)

-- | Ott's @pp_drule@ for a prover.
ppDrule :: Env -> Drule -> P Text
ppDrule env dr = (located <>) <$> ppDruleBody env dr
  where
    located = case sourceLocation env 1 (druleLoc (envSources env) (druleRange dr)) of
      "" -> ""
      l -> "\n" <> l

ppDruleBody :: Env -> Drule -> P Text
ppDruleBody env dr = do
  (de@(de1, de2), de3) <- bounds env (druleConclusion dr : map snd (drulePremises dr))
  let coq = isCoq env
      expand = optCoqExpandLists (envOpts env)
  if coq && not expand
    then do
      q <- extractQuantifiedProofAssistantVars env de1 de2 de3
      modify (\s -> s {psCoqQuantifiedVarsFromDe = [x | (x, _, _) <- q]})
    else pure ()
  -- Coq: the pair (named, unnamed) is evaluated right to left
  (named, unnamed) <-
    if coq
      then do
        un <- forM [p | (Nothing, p) <- drulePremises dr] (ppSymterm env [] de)
        na <- forM [(hn, p) | (Just hn, p) <- drulePremises dr] $ \(hn, p) -> (\s -> "(" <> hn <> ": " <> s <> ")") <$> ppSymterm env [] de p
        pure (na, un)
      else (,) [] <$> mapM (ppSymterm env [] de . snd) (drulePremises dr)
  conclusion <- ppSymterm env [] de (druleConclusion dr)
  let nonFree = nonFreeNtrs env (specSubrules (envSpec env))
      subntrsOf ntmvsns =
        mapMaybe
          ( \x -> case x of
              ((Ntr ntr, suffix), Nothing) -> (\up -> (ntr, up, (ntr, suffix))) <$> lookup ntr nonFree
              ((Ntr ntr, suffix), Just (ntrl, ntru)) -> Just (ntrl, ntru, (ntr, suffix))
              ((Mvr _, _), _) -> Nothing
          )
          ntmvsns
      nonlistSubntrs = subntrsOf de3
      listSubntrs = [(subntrsOf (de1Ntmvsns i), de1CompoundId i, de1Pattern i, de1CoqTypeOfPattern i) | (_, i) <- de1]
      subntrs = map (ppSubntr env) nonlistSubntrs ++ ppListsubntr env listSubntrs
      hyps = subntrs ++ unnamed
  if isTwf env && any (\(xs, _, _, _) -> not (null xs)) listSubntrs
    then failP "internal (Twelf): pp_listsubntr"
    else pure ()
  quantified <- extractQuantifiedProofAssistantVars env de1 de2 de3
  let name = druleName dr
  case envTarget env of
    Isa ->
      pure $
        name <> "I: \""
          <> (if null hyps then "" else "\\<lbrakk>" <> T.intercalate " ;\n" hyps <> "\\<rbrakk> \\<Longrightarrow>\n")
          <> conclusion
          <> "\"\n"
    Hol ->
      pure $
        "[" <> name <> ":] ("
          <> (if null quantified then "" else "!" <> T.concat [" (" <> v <> ":" <> t <> ")" | (v, t, _) <- quantified] <> " .")
          <> "\n(clause_name \"" <> name <> "\")"
          <> (if null hyps then "" else " /\\\n(" <> T.intercalate " /\\\n" ["(" <> h <> ")" | h <- hyps] <> ")")
          <> "\n ==> \n(" <> conclusion <> "))\n"
    Lem ->
      pure $
        name <> ": "
          <> "forall" <> T.concat [" " <> v | (v, _, _) <- quantified] <> " .\n"
          <> (if null hyps then "true\n" else T.intercalate " &&\n" ["(" <> h <> ")" | h <- hyps] <> "\n")
          <> " ==> \n" <> conclusion <> "\n\n"
    Coq -> do
      s <- get
      let nlh = psCoqNonLocalHypDefn s
          nlhv = psCoqNonLocalHypDefnVars s
      modify (\st -> st {psCoqNonLocalHypDefn = "", psCoqNonLocalHypDefnVars = []})
      let vtl = [(x, Just t) | (x, _, (t, _)) <- quantified] ++ nlhv
          vtlr = if expand then removeDupl vtl else removeDuplicates vtl
          (t1, t2) = partition (\(_, t) -> t == Just "vars") vtlr
          qpavt = collapseQuantifications (t1 ++ t2)
          quant
            | null qpavt && null named = ""
            | otherwise =
                "forall"
                  <> T.concat [maybe (" " <> head' vs) (\t -> " (" <> T.unwords vs <> ":" <> t <> ")") mt | (vs, mt) <- qpavt]
                  <> T.concat ["\n     " <> x | x <- named]
                  <> ","
      pure ("\n | " <> name <> " : " <> quant <> "\n     " <> nlh <> T.concat [x <> " ->\n     " | x <- hyps] <> conclusion)
    Caml -> pure ""
    Twf -> do
      current <- psTwfCurrentDefn <$> get
      pure (current <> "/" <> name <> ": " <> conclusion <> T.concat [" <- " <> h | h <- hyps] <> ".\n")
  where
    removeDupl l = case l of
      [] -> []
      (v, t) : tl -> if any ((== v) . fst) tl then removeDupl tl else (v, t) : removeDupl tl
    head' vs = case vs of
      (v : _) -> v
      [] -> ""

-- | Ott's @pp_defn@ for a prover.
ppDefn :: Env -> Text -> Text -> ProcessedDefn -> P Text
ppDefn env wrapper universe d = do
  let rules = [dr | ItemRule dr <- pdRules d]
      sep = case envTarget env of
        Isa -> "\n| "
        Hol -> "\n"
        Lem -> "and\n"
        _ -> ""
  if isTwf env then modify (\s -> s {psTwfCurrentDefn = pdName d}) else pure ()
  printed <- mapM (ppDrule env) rules
  case envTarget env of
    Twf -> pure ("%% defn " <> pdName d <> "\n\n" <> T.concat printed)
    Coq -> do
      let es = prodElements (prodOfProdname env (wrapper <> pdName d))
          ss = mapMaybe (ppElement env [] True) es
          typeDefn = case ss of
            [] -> universe <> " :="
            [s] -> s <> " -> " <> universe <> " :="
            _ -> T.intercalate " -> " ss <> " -> " <> universe <> " :="
      pure (wrapper <> pdName d <> " : " <> typeDefn <> "    (* defn " <> pdName d <> " *)" <> T.concat printed)
    _ -> pure ("(* defn " <> pdName d <> " *)\n\n" <> T.intercalate sep printed)

defnClassOf :: Env -> Text -> DefnClass
defnClassOf env n = fromMaybe (error ("Haskott.Prover.Defns: no definition class " ++ T.unpack n)) (find ((== n) . dcName) (specDefnClasses (envSpec env)))

-- | Ott's @pp_defnclass@ for a prover.
ppDefnclass :: Env -> ProcessedClass -> P Text
ppDefnclass env pc = do
  let dc = defnClassOf env (pcName pc)
      universe = maybe "Prop" (ppHomSpec env) (lookup "coq-universe" (dcHoms dc))
      wrapper = pcWrapper pc
      defns = pcDefns pc
      typeSs d = let ss = mapMaybe (ppElement env [] True) (prodElements (prodOfProdname env (wrapper <> pdName d))) in if null ss then ["unit"] else ss
  case envTarget env of
    Isa -> do
      let opts = envOpts env
      fancy <- fmap concat $ forM defns $ \d -> maybe [] pure <$> isaFancySyntaxClauseForDefn env (pcName pc) wrapper (pdName d)
      bodies <- mapM (ppDefn env wrapper universe) defns
      let isaType d
            | optIsaInductive opts = T.intercalate " \\<Rightarrow> " (typeSs d) <> " \\<Rightarrow> bool"
            | otherwise = "(" <> T.intercalate "*" (typeSs d) <> ") set"
      pure $
        "(* defns " <> pcName pc <> " *)\n" <> (if optIsaInductive opts then "inductive" else "inductive_set") <> " "
          <> T.intercalate "\n and " [wrapper <> pdName d <> " :: \"" <> isaType d <> "\"" | d <- defns]
          <> T.concat ["\nand " <> fst x | x <- fancy]
          <> "\nwhere\n"
          <> (if null fancy then "" else T.intercalate "\n| " (map snd fancy) <> "\n\n| ")
          <> T.intercalate "\n| " bodies
    Hol -> do
      bodies <- mapM (ppDefn env wrapper universe) defns
      pure ("\n(* defns " <> pcName pc <> " *)\nInductive " <> pcName pc <> ":\n" <> T.intercalate "\n" bodies <> "End\n")
    Lem -> do
      bodies <- mapM (ppDefn env wrapper universe) defns
      let wcf d = maybe "" (\hs -> " " <> pseudoHomSpec hs) (lookup "lemwcf" (pdHoms d))
          lemType d = T.intercalate " -> " (typeSs d) <> " -> bool"
      pure $
        "(* defns " <> pcName pc <> " *)\nindreln\n"
          <> T.intercalate "\n and " ["[" <> wrapper <> pdName d <> " : " <> lemType d <> wcf d <> "]\n" | d <- defns]
          <> T.intercalate "\nand\n" bodies
          <> "\n"
    Coq -> do
      modify (\s -> s {psCoqListAuxNewlyDefined = []})
      bodies <- mapM (ppDefn env wrapper universe) defns
      newly <- psCoqListAuxNewlyDefined <$> get
      pure ("\n(* defns " <> pcName pc <> " *)\nInductive " <> T.intercalate "\nwith " bodies <> T.concat newly <> ".\n")
    Caml -> pure ""
    Twf -> do
      if any (any twfUnsupportedElement . prodElements . prodOfProdname env . (wrapper <>) . pdName) defns
        then twelfFail
        else pure ()
      let twfType d = case typeSs d of
            [t] -> t
            ts -> T.intercalate " -> " ts
      bodies <- mapM (ppDefn env wrapper universe) defns
      pure $
        "%% defns " <> pcName pc <> "\n\n"
          <> T.concat [wrapper <> pdName d <> " : " <> twfType d <> " -> type.\n" | d <- defns]
          <> T.concat bodies

------------------------------------------------------------------------
-- Functions

funDefnOf :: Env -> Text -> FunDefn
funDefnOf env n = fromMaybe (error ("Haskott.Prover.Defns: no function " ++ T.unpack n)) (find ((== n) . fdName) (concatMap fcDefns (specFunClasses (envSpec env))))

funClassOf :: Env -> Text -> FunClass
funClassOf env n = fromMaybe (error ("Haskott.Prover.Defns: no function class " ++ T.unpack n)) (find ((== n) . fcName) (specFunClasses (envSpec env)))

-- | Ott's @pp_symterm_node_lhs@: a clause's left-hand side, its elements
-- in the order of the production's @order@ hom.
ppSymtermNodeLhs :: Env -> De -> Symterm -> P Text
ppSymtermNodeLhs env de st = case st of
  StNode ntr pn es -> do
    let promoted = case [pps | (lower, (_, pps)) <- srdPromotion (specSubruleData (envSpec env)), lower == ntr] of
          (pps : _) -> fromMaybe (error "Haskott.Prover.Defns: ppd_lhs") (lookup pn pps)
          [] -> pn
        p = prodOfProdname env promoted
    pes <- ppSymtermElements env [] de False (prodElements p) es
    let hom0 = fromMaybe (error "Haskott.Prover.Defns: pp_symterm_node_lhs") (lookup "order" (prodHoms p))
        hom = if isCoq env || isCaml env || isLem env then insertCommas hom0 else hom0
    pure (T.unwords (applyHomSpec env hom pes))
  _ -> error "Haskott.Prover.Defns: pp_symterm_node_lhs"
  where
    insertCommas l = case l of
      [] -> []
      [h] -> [h]
      h : t -> h : HomString "," : insertCommas t

-- | Ott's @fundefn_to_int_func@.
fundefnToIntFunc :: Env -> [Text] -> ProcessedFun -> P (Maybe IntFunc)
fundefnToIntFunc env deps pf = do
  let fd = funDefnOf env (pfName pf)
      resultTypeName = ppNontermrootTy env (fdResult fd)
      prodEs = applyHomOrder (prodOfProdname env (fdResultPrefix fd <> fdName fd))
      ss = mapMaybe (ppElement env [] True) prodEs
      numbered = zip [1 :: Int ..] ss
      typeDefn sep = case ss of
        [] -> (sep, "")
        _ ->
          ( T.unwords ["(x" <> T.pack (show i) <> ":" <> s <> ")" | (i, s) <- numbered]
          , "  match " <> T.intercalate "," ["x" <> T.pack (show i) | (i, _) <- numbered] <> " with\n"
          )
  header <- case envTarget env of
    Hol -> pure (Just ("", "", ""))
    Lem -> failP "LemTODO: functions are not supported in the Lem back end"
    Twf -> pure Nothing
    Coq -> do
      let structOn = case lookup "coq-struct" (fdHoms fd) of
            Just [HomIndex i] -> "{struct x" <> T.pack (show (i + 1)) <> "} "
            Just _ -> "{struct <<<malformed term in coq-struct hom>>>}"
            Nothing -> ""
          (v, ms) = typeDefn " :="
      pure (Just (fdName fd <> " " <> v <> " " <> structOn <> ": " <> resultTypeName <> ":=\n", "", ms))
    Isa -> do
      let ty = (if null ss then "unit" else T.intercalate " => " ss) <> " => " <> resultTypeName
      pure (Just (fdName fd <> " :: \"" <> ty <> "\"\n", "", ""))
    Caml
      | fdResult fd == "formula" -> pure Nothing
      | otherwise -> do
          let (v, ms) = typeDefn " ="
          pure (Just (fdName fd <> " " <> v <> ": " <> resultTypeName <> "=\n", "", ms))
  case header of
    Nothing -> pure Nothing
    Just h -> do
      clauses <- forM (pfClauses pf) $ \fc -> do
        (de, _) <- bounds env [fcLhs fc, fcRhs fc]
        lhs <- ppSymtermNodeLhs env de (fcLhs fc)
        rhs <- ppSymterm env [] de (fcRhs fc)
        pure ("", lhs, rhs)
      pure (Just (IntFunc (fdName fd) deps "TODO" h clauses))

-- | Ott's @pp_fundefnclass@ for a prover.
ppFundefnclass :: Env -> ProcessedFunClass -> P Text
ppFundefnclass env pfc
 | isTwf env = pure ""
 | otherwise = do
  let fc = funClassOf env (pfcName pfc)
      proofOf hn = case lookup hn (fcHoms fc) of
        Just [HomString s] -> Just s
        Nothing -> Nothing
        _ -> Just "<<<malformed isa-proof/hol-proof hom>>>"
      proof = case envTarget env of
        Isa -> proofOf "isa-proof"
        Hol -> proofOf "hol-proof"
        _ -> Nothing
      deps = map pfName (pfcFuns pfc)
  funcs <- fmap concat (mapM (fmap (maybe [] pure) . fundefnToIntFunc env deps) (pfcFuns pfc))
  body <- compute env (collapse env (IntFuncs funcs proof))
  pure (printWithComment env "\n" ("funs " <> pfcName pfc) body)

-- | Ott's @pp_fun_or_reln_defnclass_list@ for a prover.
ppFunOrRelnDefnclassList :: Env -> [ProcessedItem] -> P Text
ppFunOrRelnDefnclassList env items = do
  listRules <- if isCoq env && optCoqExpandLists (envOpts env) then auxiliaryListRules env items else pure ""
  bodies <- forM items $ \it -> case it of
    PReln pc -> ppDefnclass env pc
    PFuns pfc -> ppFundefnclass env pfc
  let header
        | isCoq env = "(* definitions *)\n"
        | isTwf env = "%%% definitions %%%\n\n"
        | otherwise = "(** definitions *)\n"
  pure (listRules <> header <> T.concat bodies)

-- | Ott's @pp_auxiliary_list_rules@: with expanded list types, the list
-- types the dot forms of the rules need, each once.
auxiliaryListRules :: Env -> [ProcessedItem] -> P Text
auxiliaryListRules env items =
  fmap T.concat $ forM [dr | PReln pc <- items, d <- pcDefns pc, ItemRule dr <- pdRules d] $ \dr -> do
    ((de1, _), _) <- bounds env (druleConclusion dr : map snd (drulePremises dr))
    fmap T.concat $ forM de1 $ \(_, de1i) -> do
      let ntmvrl = [promoteNtmvr env (primaryNtmvr env r) | ((r, _), _) <- de1Ntmvsns de1i]
          name = "list" <> T.concat ["_" <> ppNtOrMvRoot env r | r <- ntmvrl]
      known <- psCoqListTypes <$> get
      if name `elem` known
        then pure ""
        else do
          modify (\st -> st {psCoqListTypes = name : psCoqListTypes st})
          pure (ppListRule (envSpec env) ntmvrl)
