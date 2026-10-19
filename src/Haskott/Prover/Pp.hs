{-# LANGUAGE OverloadedStrings #-}

-- | The prover half of Ott's @grammar_pp.ml@: the types of the grammar
-- (metavariable declarations, rules and their productions), and symbolic
-- terms as prover terms, for Coq, Isabelle, HOL, Lem and OCaml.
--
-- Printing a term can have effects in Coq (a projection from a list
-- becomes a hypothesis, named by a counter), so the term printers are in
-- 'P' and run their effects in the order OCaml evaluates them: the
-- operands of @^@, the components of a pair and the head and tail of
-- @::@ right to left, @List.map@ left to right.
module Haskott.Prover.Pp
  ( -- * Names and homs
    hideIsaTrailingUnderscore
  , capitalize
  , paren
  , splitParensStars
  , splitParensCommas
  , ppHomSpec
  , applyHomSpec
  , pseudoHomSpec
  , ppTerminal
  , ppPlainSuffixItem
  , ppSuffixWithSie
    -- * Nonterminals and metavariables
  , ppNontermWithSie
  , ppMetavarWithSie
  , ppNtOrMvWithSie
  , ppNonterm
  , ppMetavar
  , ppNontermroot
  , ppMetavarroot
  , ppNtOrMvRoot
  , ppNontermrootTy
  , ppMetavarrootTy
  , ppNtOrMvRootTy
  , ppNtOrMvWithDeWithSie
  , ppNontermWithDeWithSie
  , ppMetavarWithDeWithSie
    -- * The grammar
  , ppComEs
  , ppComStrings
  , ppElement
  , ppElements
  , applyHomOrder
  , ppMetavardefn
  , ppRuleList
  , canonicalNode
  , isaFancySyntaxHomForProd
  , isaFancySyntaxClauseForDefn
  , ppSymtermElementJudgeIsaPlain
  , ppSymtermElementJudgeIsaFancy
    -- * Terms
  , ppSymterm
  , ppSymtermElements
  , ppSymtermListBody
  , de1Lookup
  , ppMse
  , ppMseString
  , ppAuxfn
  , listAppend
  , extractQuantifiedProofAssistantVars
  , makeNameSymterm
  , makeNameElements
  , makeDepSymterm
  , ppTrue
  , ppFalse
  , ppAnd
  , ppOr
  , bigLineComment
  , printWithComment
  , auxfnName
  , ppIs
  , pseudoTerminalOfProdName
  , removeDuplicates
  ) where

import Control.Monad (forM)
import Control.Monad.Trans.State.Strict (get, modify)
import Data.Char (toUpper)
import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust)
import qualified Data.ByteString as B
import Data.Text (Text)
import qualified Data.Text.Encoding as TE
import qualified Data.Text as T
import Haskott.Prover.Dependency (IntFunc (..))
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

------------------------------------------------------------------------
-- Small things

oops :: String -> a
oops m = error ("Haskott.Prover.Pp: " ++ m)

-- | Ott's @remove_duplicates@: the last occurrence of each survives.
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicates more else x : removeDuplicates more

-- | OCaml's @String.escaped@, on the bytes of the UTF-8 encoding.
ocamlEscaped :: Text -> Text
ocamlEscaped = T.concat . map esc . B.unpack . TE.encodeUtf8
  where
    esc c = case c of
      34 -> "\\\""
      92 -> "\\\\"
      10 -> "\\n"
      9 -> "\\t"
      13 -> "\\r"
      8 -> "\\b"
      _
        | c >= 32 && c <= 126 -> T.singleton (toEnum (fromIntegral c))
        | otherwise -> "\\" <> T.justifyRight 3 '0' (T.pack (show c))

-- | Ott's @hide_isa_trailing_underscore@.
hideIsaTrailingUnderscore :: Env -> Text -> Text
hideIsaTrailingUnderscore env s
  | isIsa env, not (T.null s), T.last s == '_' = s <> "XXX"
  | otherwise = s

-- | @String.capitalize_ascii@.
capitalize :: Text -> Text
capitalize s = case T.uncons s of
  Just (c, rest) | c >= 'a' && c <= 'z' -> T.cons (toUpper c) rest
  _ -> s

-- | Ott's @Auxl.paren@.
paren :: Text -> Text
paren s = if T.any (== ' ') s then "(" <> s <> ")" else s

-- | @Str.split (Str.regexp "(\\|*\\|)")@.
splitParensStars :: Text -> [Text]
splitParensStars = filter (not . T.null) . T.split (`elem` ("(*)" :: String))

-- | @Str.split (Str.regexp "(\\|,\\|)")@.
splitParensCommas :: Text -> [Text]
splitParensCommas = filter (not . T.null) . T.split (`elem` ("(,)" :: String))

auxfnName :: Text -> Text -> Text -> Text
auxfnName s ntr typ = "aux_" <> s <> "_" <> ntr <> "_of_" <> typ

ppIs :: Text -> Text -> Text
ppIs ntr typ = "is_" <> ntr <> "_of_" <> typ

pseudoTerminalOfProdName :: Text -> Text
pseudoTerminalOfProdName pn = ":" <> pn <> ":"

listAppend :: Env -> Text
listAppend env = if isLem env || isHol env then " ++ " else " @ "

ppTrue, ppFalse, ppAnd, ppOr :: Env -> Bool -> Text
ppTrue env inProp = case envTarget env of
  Isa -> "True"
  Coq -> if optCoqExpandLists (envOpts env) || inProp then "True" else "true"
  Hol -> "T"
  _ -> "true"
ppFalse env inProp = case envTarget env of
  Isa -> "False"
  Coq -> if optCoqExpandLists (envOpts env) || inProp then "False" else "false"
  Hol -> "F"
  _ -> "false"
ppAnd env inProp = case envTarget env of
  Isa -> " & "
  Coq -> if optCoqExpandLists (envOpts env) || inProp then " /\\ " else " && "
  Hol -> " /\\ "
  _ -> " && "
ppOr env inProp = case envTarget env of
  Isa -> " | "
  Coq -> if optCoqExpandLists (envOpts env) || inProp then " \\/ " else " || "
  Hol -> " \\/ "
  _ -> " || "

bigLineComment :: Env -> Text -> Text
bigLineComment _ s = "(** " <> s <> " *)\n"

-- | Ott's @print_with_comment@: only when there is something to print.
printWithComment :: Env -> Text -> Text -> Text -> Text
printWithComment env s0 c s = if T.null s then "" else s0 <> bigLineComment env c <> s

------------------------------------------------------------------------
-- Homs

-- | Ott's @pp_hom_spec@ for a prover.
ppHomSpec :: Env -> [HomEl] -> Text
ppHomSpec env = T.concat . map el
  where
    el h = case h of
      HomString s -> s
      HomTerminal s
        | isIsa env || isHol env || isLem env -> s
        | otherwise -> oops "pp_hom_spec_el"
      HomIndex i
        | isIsa env || isHol env || isLem env -> "UNIMPLEMENTED[Hom_index" <> T.pack (show i) <> "]"
        | otherwise -> "UNIMPLEMENTED"
      HomLnFreeIndex _ _ -> oops "pp_hom_spec el"

applyHomSpec :: Env -> [HomEl] -> [Text] -> [Text]
applyHomSpec env hs ss = map el hs
  where
    el h = case h of
      HomString s -> s
      HomIndex i -> nth i
      HomTerminal tm -> ppTerminal env tm
      HomLnFreeIndex _ i -> nth i
    nth i = if i >= 0 && i < length ss then ss !! i else oops ("hom index " ++ show i ++ " out of range")

pseudoHomSpec :: [HomEl] -> Text
pseudoHomSpec = T.concat . map el
  where
    el h = case h of
      HomString s -> s
      HomTerminal tm -> tm
      _ -> oops "nontermroot hom contains a reference"

-- | Ott's @pp_terminal@ for a prover.
ppTerminal :: Env -> Text -> Text
ppTerminal env tm = case envTarget env of
  Isa ->
    case M.lookup "terminals" (envRuleByNtr env) of
      Just r
        | Just p <- find (\p -> take 1 (prodElements p) == [Terminal tm]) (ruleProds r)
        , Just hs <- lookup "isa" (prodHoms p) ->
            ppHomSpec env hs
      _ -> tm
  Caml -> "_"
  _ -> tm

------------------------------------------------------------------------
-- Suffixes

ppPlainSuffixItem :: SuffixItem -> Text
ppPlainSuffixItem si = case si of
  SiNum s -> s
  SiPunct s -> s
  SiVar s n -> s <> offset n
  SiIndex i -> "[" <> T.pack (show i) <> "]"
  SiIndexed s si' -> s <> ppPlainSuffixItem si'
  SiIndexShift i k -> "[" <> T.pack (show i) <> "]" <> offset k
  where
    offset n
      | n == 0 = ""
      | n > 0 = "+" <> T.pack (show n)
      | otherwise = T.pack (show n)

ppSuffixWithSie :: Suffix -> Suffix -> Text
ppSuffixWithSie sie = T.concat . map (ppSuffixItemWithSie sie)

ppSuffixItemWithSie :: Suffix -> SuffixItem -> Text
ppSuffixItemWithSie sie si = case si of
  SiNum s -> s
  SiPunct s -> s
  SiVar s n -> if n == 0 then s else oops "non-zero suffix offset in pp_suffix_item_with_sie"
  SiIndex i -> ppSuffixItemWithSie sie (nthOr999 i)
  SiIndexShift i k -> ppSuffixItemWithSie sie (if i >= 0 && i < length sie then shift k (sie !! i) else SiNum "999")
  SiIndexed s si' -> s <> ppSuffixItemWithSie sie si'
  where
    nthOr999 i = if i >= 0 && i < length sie then sie !! i else SiNum "999"
    shift k x = case x of
      SiNum n | Just v <- readInt n -> SiNum (T.pack (show (v + k)))
      SiVar v o -> SiVar v (o + k)
      _ -> x
    readInt t = if not (T.null t) && T.all (`elem` ['0' .. '9']) t then Just (read (T.unpack t) :: Int) else Nothing

------------------------------------------------------------------------
-- Nonterminals and metavariables

ppNontermWithSieInternal :: Bool -> Env -> Suffix -> (Text, Suffix) -> Text
ppNontermWithSieInternal asType env sie (ntr, suff) =
  let r = ruleOfNtr env (primaryNtrOfNtr env ntr)
      hr = homSpecForTarget env (ruleHoms r)
   in if rulePhantom r && isJust hr && asType
        then pseudoHomSpec (fromMaybe [] hr)
        else
          let homs = fromMaybe [] (lookup ntr (ruleNames r))
              ppNtr = maybe ntr pseudoHomSpec (homSpecForTarget env homs)
              auxparam = case lookup "auxparam" (ruleHoms r) of
                Just hs | asType, isCaml env || isLem env -> Just (T.concat [s | HomString s <- hs])
                _ -> Nothing
              s0 = ppNtr <> ppSuffixWithSie sie suff
              s1 = if asType then s0 else hideIsaTrailingUnderscore env s0
           in case envTarget env of
                Caml -> maybe s1 (\p -> p <> " " <> s1) auxparam
                Lem -> maybe s1 (\p -> "(" <> s1 <> " " <> p <> ")") auxparam
                _ -> s1

ppMetavarWithSieInternal :: Bool -> Env -> Suffix -> (Text, Suffix) -> Text
ppMetavarWithSieInternal asType env sie (mvr, suff) =
  let md = mvdOfMvrNonprimary env mvr
      hr = homSpecForTarget env (mvdHoms md)
   in if mvdPhantom md && isJust hr && asType
        then pseudoHomSpec (fromMaybe [] hr)
        else
          let homs = fromMaybe [] (lookup mvr (mvdNames md))
              ppMvr = maybe mvr pseudoHomSpec (homSpecForTarget env homs)
              s = ppMvr <> ppSuffixWithSie sie suff
           in if asType then s else hideIsaTrailingUnderscore env s

ppNontermWithSie :: Env -> Suffix -> (Text, Suffix) -> Text
ppNontermWithSie = ppNontermWithSieInternal False

ppMetavarWithSie :: Env -> Suffix -> (Text, Suffix) -> Text
ppMetavarWithSie = ppMetavarWithSieInternal False

ppNtOrMvWithSie :: Env -> Suffix -> NtMv -> Text
ppNtOrMvWithSie env sie (r, suff) = case r of
  Ntr n -> ppNontermWithSie env sie (n, suff)
  Mvr n -> ppMetavarWithSie env sie (n, suff)

ppNonterm :: Env -> (Text, Suffix) -> Text
ppNonterm env = ppNontermWithSie env []

ppMetavar :: Env -> (Text, Suffix) -> Text
ppMetavar env = ppMetavarWithSie env []

ppNontermroot :: Env -> Text -> Text
ppNontermroot env n = ppNonterm env (n, [])

ppMetavarroot :: Env -> Text -> Text
ppMetavarroot env n = ppMetavar env (n, [])

ppNtOrMvRoot :: Env -> RootRef -> Text
ppNtOrMvRoot env r = case r of
  Ntr n -> ppNontermroot env n
  Mvr n -> ppMetavarroot env n

ppNontermrootTy :: Env -> Text -> Text
ppNontermrootTy env n = ppNontermWithSieInternal True env [] (n, [])

ppMetavarrootTy :: Env -> Text -> Text
ppMetavarrootTy env n = ppMetavarWithSieInternal True env [] (n, [])

ppNtOrMvRootTy :: Env -> RootRef -> Text
ppNtOrMvRootTy env r = case r of
  Ntr n -> ppNontermrootTy env n
  Mvr n -> ppMetavarrootTy env n

-- | Ott's @pp_nt_or_mv_with_de_with_sie@: a projection from a list form
-- (@l'j@ of @l'1 .. l'n@) becomes an access to the list.
ppNtOrMvWithDeWithSie :: Env -> Suffix -> De -> NtMv -> P Text
ppNtOrMvWithDeWithSie env sie (de1, de2) ntmv@(ntmvr, _) = case lookup ntmv de2 of
  Nothing -> pure (ppNtOrMvWithSie env sie ntmv)
  Just (suff, suffi, bound) -> do
    let de1i = fromMaybe (oops "pp_nt_or_mv_with_de_with_sie: bound not in de1") (lookup bound de1)
        lower = case nonZeroLower bound of
          Nothing -> ""
          Just si -> " - " <> ppPlainSuffixItem si
        proj = ppNtOrMvWithSie env (SiVar "_" 0 : sie) (ntmvr, suff)
        index = ppPlainSuffixItem suffi <> lower
    case envTarget env of
      Isa -> pure ("((%" <> de1Pattern de1i <> " . " <> proj <> ")" <> " (List.nth " <> de1CompoundId de1i <> " " <> "(" <> index <> ")))")
      Hol -> pure (" ((\\ " <> de1Pattern de1i <> " . " <> proj <> ")" <> " (EL " <> " " <> "(" <> index <> ") " <> de1CompoundId de1i <> ")) ")
      Lem -> pure (" ((fun " <> de1Pattern de1i <> " -> " <> proj <> ")" <> " (List.nth " <> " " <> de1CompoundId de1i <> " " <> "(" <> index <> ") " <> ")) ")
      Coq -> do
        n <- freshC
        let hypVar = "t" <> T.pack (show n)
            tyList = splitParensStars (de1CoqTypeOfPattern de1i)
            nthPred
              | optCoqExpandLists (envOpts env) =
                  "     nth_list_" <> T.intercalate "_" tyList <> " " <> paren index <> " " <> de1CompoundId de1i
              | otherwise = "     nth_error " <> de1CompoundId de1i <> " " <> paren index
        modify $ \s ->
          s
            { psCoqNonLocalHypDefnVars = psCoqNonLocalHypDefnVars s ++ [(hypVar, Just (de1CoqTypeOfPattern de1i))]
            , psCoqNonLocalHypDefn = psCoqNonLocalHypDefn s <> nthPred <> " = Some " <> hypVar <> " ->\n"
            }
        pure $
          if de1Pattern de1i == proj
            then hypVar
            else "(match " <> hypVar <> " with " <> de1Pattern de1i <> " => " <> proj <> " end)"
      Caml -> pure (oops "pp_symterm for proper symterms not supported")
  where
    nonZeroLower b = case b of
      BoundDotform l _ _ -> if l == SiNum "0" then Nothing else Just l
      BoundCompLU _ l _ _ -> if l == SiNum "0" then Nothing else Just l
      _ -> Nothing

ppNontermWithDeWithSie :: Env -> Suffix -> De -> (Text, Suffix) -> P Text
ppNontermWithDeWithSie env sie de (n, s) = ppNtOrMvWithDeWithSie env sie de (Ntr n, s)

ppMetavarWithDeWithSie :: Env -> Suffix -> De -> (Text, Suffix) -> P Text
ppMetavarWithDeWithSie env sie de (n, s) = ppNtOrMvWithDeWithSie env sie de (Mvr n, s)

ppVariable :: Env -> Text -> Text -> Text
ppVariable env mvrp var =
  let homs = mvdHoms (mvdOfMvr env mvrp)
      via hn = maybe var (\hs -> T.concat (applyHomSpec env hs [var])) (lookup hn homs)
   in case envTarget env of
        Isa -> via "isavar"
        Hol -> via "holvar"
        Lem -> via "lemvar"
        Caml -> via "ocamlvar"
        Coq -> var

ppUninterpreted :: Text -> Text
ppUninterpreted s = "(*" <> s <> "*)"

------------------------------------------------------------------------
-- Comments

ppComEs :: Env -> [Hom] -> [Element] -> Text
ppComEs env homs es = case lookup "com" homs of
  Nothing -> ""
  Just hs ->
    let ss = [s | e <- es, isNtMvList e, Just s <- [ppElement env [] False e]]
     in comment env (T.concat (applyHomSpec env hs ss))
  where
    isNtMvList e = case e of
      Terminal _ -> False
      _ -> True

ppComStrings :: Env -> [Hom] -> [Text] -> Text
ppComStrings env homs ss = case lookup "com" homs of
  Nothing -> ""
  Just hs -> comment env (T.concat (applyHomSpec env hs ss))

comment :: Env -> Text -> Text
comment env s
  | isIsa env = " \\<comment> \\<open>" <> s <> "\\<close>"
  | otherwise = " (* " <> s <> " *)"

------------------------------------------------------------------------
-- Elements and productions

-- | Ott's @pp_element@ for a prover: the type of an element.
ppElement :: Env -> Suffix -> Bool -> Element -> Maybe Text
ppElement env sie inType e =
  let checkConflict v t = if v == t then (Nothing, t) else (Just v, t)
      opts = envOpts env
      vto = case e of
        Nonterm ntrp ntr suff ->
          Just (checkConflict (ppNonterm env (ntr, suff)) (ppNontermrootTy env (promoteNtr env ntrp)))
        Metavar mvrp mvr suff ->
          Just (checkConflict (ppMetavar env (mvr, suff)) (ppMetavarrootTy env mvrp))
        Terminal _
          | isCaml env && optCamlIncludeTerminals opts -> Just (Nothing, "terminal")
          | otherwise -> Nothing
        ListForm lb -> case envTarget env of
          Coq
            | optCoqExpandLists opts -> case ppElements env sie (lbElements lb) False False True True of
                Nothing -> Nothing
                Just s -> Just (Nothing, "(list_" <> s <> ")")
            | otherwise -> case ppElements env sie (lbElements lb) True False True True of
                Nothing -> Just (Nothing, "list unit")
                Just s -> Just (Nothing, "list " <> s)
          Isa -> isaHol lb
          Hol -> isaHol lb
          Lem -> case ppElements env sie (lbElements lb) True False True True of
            Nothing -> Just (Nothing, "list unit")
            Just s -> Just (Nothing, "list " <> s)
          Caml ->
            let tmt = case (optCamlIncludeTerminals opts, lbSeparator lb) of
                  (True, Just _) -> " * terminal"
                  _ -> ""
             in case ppElements env sie (lbElements lb) True False True True of
                  Nothing -> Just (Nothing, "(unit" <> tmt <> ") list")
                  Just s -> Just (Nothing, "(" <> s <> tmt <> ") list")
      isaHol lb = case ppElements env sie (lbElements lb) True False True True of
        Nothing -> Just (Nothing, "unit list")
        Just s -> Just (Nothing, s <> " list")
   in case vto of
        Nothing -> Nothing
        Just (v, t)
          | isCoq env && optCoqNamesInRules opts && not inType -> Just (maybe ("(_:" <> t <> ")") (\v' -> "(" <> v' <> ":" <> t <> ")") v)
          | otherwise -> Just t

-- | Ott's @pp_elements@ for a prover.
ppElements :: Env -> Suffix -> [Element] -> Bool -> Bool -> Bool -> Bool -> Maybe Text
ppElements env sie es parens toplevel inList inType =
  let ss = [s | e <- es, Just s <- [ppElement env sie inType e]]
      opts = envOpts env
   in case envTarget env of
        Isa -> case ss of
          [] -> Nothing
          _
            | toplevel -> Just (T.unwords ["\"" <> s <> "\"" | s <- ss])
            | parens && length ss > 1 -> Just ("(" <> T.intercalate "*" ss <> ")")
            | otherwise -> Just (T.intercalate "*" ss)
        Hol -> case ss of
          [] -> Nothing
          _
            | toplevel -> Just (T.intercalate " => " ss)
            | parens && length ss > 1 -> Just ("(" <> T.intercalate "#" ss <> ")")
            | otherwise -> Just (T.intercalate "#" ss)
        _ ->
          let sep
                | inList = case envTarget env of
                    Coq -> if optCoqExpandLists opts then "_" else "*"
                    _ -> " * "
                | isCoq env && optCoqNamesInRules opts = " "
                | otherwise = " -> "
              s = T.intercalate sep ss
           in case ss of
                [] -> Nothing
                [_] -> Just s
                _ -> if parens then Just ("(" <> s <> ")") else Just s

-- | Ott's @apply_hom_order@: the elements in the order of the @order@
-- hom.
applyHomOrder :: Prod -> [Element]
applyHomOrder p = case lookup "order" (prodHoms p) of
  Nothing -> prodElements p
  Just oh ->
    let pf = filter (\e -> case e of Terminal _ -> False; _ -> True) (prodElements p)
     in [pf !! i | HomIndex i <- oh]

canonicalNode :: Text -> Prod -> Symterm
canonicalNode ntr p = StNode ntr (prodName p) (canonicalElements (prodElements p))
  where
    canonicalElements = concatMap canonical
    canonical e = case e of
      Nonterm p' n s -> [SteSt (StNonterm p' (n, s))]
      Metavar p' n s -> [SteMetavar p' (n, s)]
      Terminal _ -> []
      ListForm lb ->
        let b = fromMaybe (BoundDotform (SiVar "" 0) (SiVar "" 0) 2) (lbBound lb)
         in [SteList [StliListform b (canonicalElements (lbElements lb))]]

-- | Ott's @coq_maybe_decide_equality@.
coqMaybeDecideEquality :: Env -> [Hom] -> RootRef -> Text
coqMaybeDecideEquality env homs ntmvr = case lookup "coq-equality" homs of
  Nothing -> ""
  Just eh ->
    let tn = ppNtOrMvRootTy env ntmvr
        sel x y = if x == tn then y else x
        v1 = sel "x" "x'"
        v2 = sel "y" "y'"
     in "Lemma eq_" <> tn <> ": forall (" <> v1 <> " " <> v2 <> " : " <> tn <> ")"
          <> ", {" <> v1 <> " = " <> v2 <> "} + {" <> v1 <> " <> " <> v2 <> "}.\n"
          <> "Proof.\n"
          <> ( case eh of
                 [] -> "  decide equality; auto with ott_coq_equality arith."
                 [HomString s] -> s
                 _ -> oops "malformed coq-equality homomorphism"
             )
          <> "\nDefined.\n"
          <> "#[export] Hint Resolve eq_" <> tn <> " : ott_coq_equality.\n"

-- | Ott's @pp_metavardefn@ for a prover.
ppMetavardefn :: Env -> MetavarDefn -> Text
ppMetavardefn env md
  | mvdPhantom md = ""
  | otherwise =
      let com = ppComStrings env (mvdHoms md) [ppMetavarWithSie env [] (mvdName md, [])]
          tn = ppMetavarrootTy env (mvdName md)
          rep = ppMetavarrep env md
       in case envTarget env of
            Coq ->
              let universe = maybe "Set" (ppHomSpec env) (lookup "coq-universe" (mvdHoms md))
                  sentence
                    | isJust (lookup "coq-notation" (mvdHoms md)) = "Notation " <> tn <> " := (" <> rep <> " : " <> universe <> ")."
                    | otherwise = "Definition " <> tn <> " : " <> universe <> " := " <> rep <> "."
               in sentence <> com <> "\n" <> coqMaybeDecideEquality env (mvdHoms md) (Mvr (mvdName md))
            Caml -> "type " <> tn <> " = " <> rep <> com <> "\n"
            Isa
              | isJust (lookup "repr-nominal" (mvdHoms md)) -> "atom_decl \"" <> tn <> "\"" <> com <> "\n"
              | otherwise -> "type_synonym \"" <> tn <> "\" = \"" <> rep <> "\"" <> com <> "\n"
            Hol -> "Type " <> tn <> " = ``:" <> rep <> "``" <> com <> "\n"
            Lem -> "type " <> tn <> " = " <> rep <> com <> "\n"

ppMetavarrep :: Env -> MetavarDefn -> Text
ppMetavarrep env md = maybe "UNDEFINED" (ppHomSpec env) (homSpecForTarget env (mvdHoms md))

-- | Ott's @pp_prod@ for a prover.
ppProd :: Env -> Text -> Prod -> Maybe Text
ppProd env rnn p
  | prodMeta p = Nothing
  | otherwise =
      let com = ppComEs env (prodHoms p) (prodElements p)
          els cam = ppElements env [] (applyHomOrder p) False True cam False
       in case envTarget env of
            Isa
              | prodRequireNominal env p -> Just (ppNominalProd env p)
              | otherwise ->
                  let dc = maybe (prodName p) (\s -> prodName p <> " " <> s) (els False)
                   in Just (dc <> "  " <> isaFancySyntaxClauseForProd env p <> com)
            Hol -> Just (maybe (prodName p <> com) (\s -> prodName p <> " of " <> s <> com) (els False))
            Coq -> Just $ case els False of
              Nothing -> " | " <> prodName p <> " : " <> ppNontermrootTy env rnn <> com
              Just s
                | optCoqNamesInRules (envOpts env) -> " | " <> prodName p <> " " <> s <> com
                | otherwise -> " | " <> prodName p <> " : " <> s <> " -> " <> ppNontermrootTy env rnn <> com
            _ -> Just (maybe (capitalize (prodName p) <> com) (\s -> capitalize (prodName p) <> " of " <> s <> com) (els True))

isNominalAtom :: MetavarDefn -> Bool
isNominalAtom md = isJust (lookup "repr-nominal" (mvdHoms md))

prodRequireNominal :: Env -> Prod -> Bool
prodRequireNominal env p = or [isNominalAtom (mvdOfMvr env (primaryMvrOfMvr env mvr)) | Bind (MetaVarExp (mvr, _)) _ _ <- prodBindspecs p]

ruleRequireNominal :: Env -> Rule -> Bool
ruleRequireNominal env r = any (prodRequireNominal env) (ruleProds r)

-- | Ott's @pp_nominal_prod@.
ppNominalProd :: Env -> Prod -> Text
ppNominalProd env p =
  let np = [([], e) | e <- prodElements p]
      arrange xs bs = case bs of
        [] -> xs
        Bind (MetaVarExp mv) nt _ : more ->
          let rnp = [x | x@(_, el) <- xs, not (isMv mv el)]
              mvr = primaryMvrOfMvr env (fst mv)
              unp = [if isNt nt el then (Metavar mvr mvr [] : bl, el) else (bl, el) | (bl, el) <- rnp]
           in arrange unp more
        _ : more -> arrange xs more
      isMv (m, s) el = case el of
        Metavar _ m' s' -> (m', s') == (m, s)
        _ -> False
      isNt (n, s) el = case el of
        Nonterm _ n' s' -> (n', s') == (n, s)
        _ -> False
      anp = arrange np (prodBindspecs p)
      printed = [mconcat ["\\<guillemotleft>" <> b <> "\\<guillemotright>" | Just b <- map (ppElement env [] False) bl] <> s | (bl, el) <- anp, Just s <- [ppElement env [] False el]]
   in T.unwords (prodName p : ["\"" <> s <> "\"" | s <- printed]) <> ppComEs env (prodHoms p) (prodElements p)

-- | Ott's @pp_rule@ for a prover; the Coq one also queues the rule's
-- decidable equality lemma.
ppRule :: Env -> Rule -> P (Maybe Text)
ppRule env r = do
  let com = ppComStrings env (ruleHoms r) [ppNontermWithSie env [] (ruleName r, [])]
      prods = [s | p <- ruleProds r, Just s <- [ppProd env (ruleName r) p]]
      hidden = ruleMeta r || rulePhantom r
  case envTarget env of
    Isa
      | hidden -> pure Nothing
      | otherwise -> pure (Just ("\"" <> ppNontermrootTy env (ruleName r) <> "\" = " <> com <> "\n   " <> T.intercalate " | " [s <> "\n" | s <- prods]))
    Coq -> do
      modify (\s -> s {psCoqBuffer = psCoqBuffer s <> coqMaybeDecideEquality env (ruleHoms r) (Ntr (ruleName r))})
      if hidden
        then pure Nothing
        else do
          let universe = maybe "Set" (ppHomSpec env) (lookup "coq-universe" (ruleHoms r))
          pure (Just (ppNontermrootTy env (ruleName r) <> " : " <> universe <> " := " <> com <> "\n" <> T.intercalate "\n" prods))
    _
      | hidden -> pure Nothing
      | otherwise ->
          pure
            ( Just
                ( stripSurroundingParens (ppNontermrootTy env (ruleName r)) <> " = " <> com <> "\n"
                    <> (if isLem env then " | " else "   ")
                    <> T.intercalate " | " [s <> "\n" | s <- prods]
                )
            )

stripSurroundingParens :: Text -> Text
stripSurroundingParens s
  | T.length s >= 2, T.head s == '(', T.last s == ')' = T.init (T.tail s)
  | otherwise = s

-- | Ott's @pp_rule_list@ for a prover: the rules in their dependency
-- groups, a group with a hom becoming a type abbreviation.
ppRuleList :: Env -> [Rule] -> P Text
ppRuleList env rs = do
  let ntrsRs = map ruleName rs
      groups = [rg | rg <- depTs (envDeps env), any (\n -> Ntr n `elem` rg) ntrsRs]
      (td, md, fd) = case envTarget env of
        Isa -> (\rs' -> if any (ruleRequireNominal env) rs' then "nominal_datatype " else "datatype ", "and ", "")
        Hol -> (const "val _ = Hol_datatype ` \n", ";\n", "`;")
        Coq -> (const "\nInductive ", "\nwith ", ".")
        Caml -> (const "\ntype \n", "\nand ", "")
        Lem -> (const "\ntype ", "\nand ", "")
      block b = case b of
        [Ntr ntr]
          | Just hs <- homSpecForTarget env (ruleHoms (ruleOfNtr env ntr)) ->
              let r = ruleOfNtr env ntr
               in pure $
                    if rulePhantom r
                      then ""
                      else case envTarget env of
                        Isa -> "type_synonym " <> "\"" <> ppNontermrootTy env ntr <> "\" = \"" <> ppHomSpec env hs <> "\"\n"
                        Hol -> "\nType " <> ppNontermrootTy env ntr <> " = ``:" <> ppHomSpec env hs <> "``\n"
                        Coq ->
                          let tn = ppNontermrootTy env ntr
                              universe = maybe "Set" (ppHomSpec env) (lookup "coq-universe" (ruleHoms r))
                              body = ppHomSpec env hs
                           in if isJust (lookup "coq-notation" (ruleHoms r))
                                then "\nNotation " <> tn <> " := (" <> body <> " : " <> universe <> ").\n"
                                else "\nDefinition " <> tn <> " : " <> universe <> " := " <> body <> ".\n"
                        Caml -> "\ntype\n" <> ppNontermrootTy env ntr <> " = " <> ppHomSpec env hs <> "\n\n"
                        Lem -> "\ntype " <> stripSurroundingParens (ppNontermrootTy env ntr) <> " = " <> ppHomSpec env hs <> "\n\n"
        _ -> do
          let b' = reverse b
          defs <- fmap concat $ forM b' $ \nm -> case nm of
            Mvr _ -> pure []
            Ntr ntr -> maybe [] pure <$> ppRule env (ruleOfNtr env ntr)
          let defString = T.intercalate md defs
          pure $
            if T.null defString
              then ""
              else td [ruleOfNtr env ntr | Ntr ntr <- b'] <> defString <> fd <> "\n"
  body <- T.concat <$> mapM block groups
  if isCoq env
    then do
      s <- get
      modify (\st -> st {psCoqBuffer = ""})
      pure (body <> psCoqBuffer s)
    else pure body

------------------------------------------------------------------------
-- Isabelle's fancy syntax

vanillaElement :: Element -> Bool
vanillaElement e = case e of
  ListForm _ -> False
  _ -> True

arityOfVanillaElements :: [Element] -> Int
arityOfVanillaElements = length . filter (\e -> case e of Terminal _ -> False; _ -> True)

homOfVanillaElements :: [Element] -> [HomEl]
homOfVanillaElements es = interleave (go es 0) (HomString " ")
  where
    go xs i = case xs of
      [] -> []
      Terminal s : more -> HomTerminal s : go more i
      _ : more -> HomIndex i : go more (i + 1)
    interleave ys y = case ys of
      a : b : more -> a : y : interleave (b : more) y
      _ -> ys

terminalSeparatedVanillaElements :: [Element] -> Bool
terminalSeparatedVanillaElements es = case es of
  [] -> False
  [Nonterm {}] -> False
  [Metavar {}] -> False
  [Terminal _] -> True
  _ -> go Nothing es
  where
    go lastTm xs = case xs of
      [] -> True
      Terminal _ : more -> go (Just True) more
      _ : more -> case lastTm of
        Just False -> False
        _ -> go (Just False) more

arityOfHomspec :: [HomEl] -> Int
arityOfHomspec hs = foldr (\h acc -> case h of HomIndex i -> max (1 + i) acc; _ -> acc) 0 hs

-- | Ott's @isa_fancy_syntax_hom_for_prod@.
isaFancySyntaxHomForProd :: Env -> Prod -> Maybe ([HomEl], Int, Text)
isaFancySyntaxHomForProd env p =
  let hso = lookup "isasyn" (prodHoms p)
      dflt = optIsaSyntax (envOpts env) && all vanillaElement (prodElements p) && terminalSeparatedVanillaElements (prodElements p)
      prec = maybe "50" (ppHomSpec env) (lookup "isaprec" (prodHoms p))
   in case (hso, dflt) of
        (Nothing, False) -> Nothing
        (Nothing, True) -> Just (homOfVanillaElements (prodElements p), arityOfVanillaElements (prodElements p), prec)
        (Just hs, _) -> Just (hs, arityOfHomspec hs, prec)

isaFancySyntaxClauseForProd :: Env -> Prod -> Text
isaFancySyntaxClauseForProd env p = case isaFancySyntaxHomForProd env p of
  Nothing -> ""
  Just (hs, arity, prec) -> "(\"" <> T.concat (applyHomSpec env hs (replicate arity "_")) <> "\" " <> prec <> ")"

-- | Ott's @isa_fancy_syntax_clause_for_defn@: the syntax and translation
-- clauses of a definition with fancy syntax.
isaFancySyntaxClauseForDefn :: Env -> Text -> Text -> Text -> P (Maybe (Text, Text))
isaFancySyntaxClauseForDefn env dcName dcWrapper dName = do
  let pn = dcWrapper <> dName
      p = prodOfProdname env pn
  case isaFancySyntaxHomForProd env p of
    Nothing -> pure Nothing
    Just (hs, arity, prec) -> do
      let ss = [s | Just s <- map (ppElement env [] False) (prodElements p)]
          ty = T.concat [s <> " => " | s <- ss] <> " bool"
          syntaxPart = "  \"" <> pn <> "'\"" <> " :: " <> "\"" <> ty <> "\" " <> "(\"" <> T.concat (applyHomSpec env hs (replicate arity "_")) <> "\" " <> prec <> ")"
          stnb = canonicalNode dcName p
      plain <- ppSymtermElementJudgeIsaPlain env [] deEmpty p stnb
      fancy <- ppSymtermElementJudgeIsaFancy env [] deEmpty hs p stnb
      pure (Just (syntaxPart, "  \"" <> fancy <> " == " <> plain <> "\""))

------------------------------------------------------------------------
-- Symbolic terms

ppSymterm :: Env -> Suffix -> De -> Symterm -> P Text
ppSymterm env sie de st = case st of
  StNode "fancy_formula" pn es -> ppFancyFormula env sie de pn es
  StNode ntr pn es -> ppNodeBody env sie de ntr pn es
  StNonterm _ nt -> ppNontermWithDeWithSie env sie de nt
  StNontermSub _ _ nt -> ppNontermWithDeWithSie env sie de nt
  StUninterpreted l s -> pure ("(PARSE_ERROR \"" <> envLoc env l <> "\" \"" <> ocamlEscaped s <> "\")")

ppFancyFormula :: Env -> Suffix -> De -> Text -> [Ste] -> P Text
ppFancyFormula env sie de embedding es = do
  -- the terms are printed left to right (List.map), then interleaved
  pps <- mapM (ppSymterm env sie de) [st | SteSt st <- es]
  let pieces = T.splitOn "-ARG-" embedding
      go ts ps = case (ts, ps) of
        ([t], []) -> t
        (t : more, p : ps') -> t <> p <> go more ps'
        _ -> "internal fold_in"
  pure (go pieces pps)

promotedProdName :: Env -> Text -> Text -> Text
promotedProdName env ntr pn = case M.lookup ntr (envPromotion env) of
  Just (_, pps) -> fromMaybe (oops ("pp_symterm_node_body " ++ T.unpack pn ++ " not found in the promotion")) (M.lookup pn pps)
  Nothing -> pn

ppNodeBody :: Env -> Suffix -> De -> Text -> Text -> [Ste] -> P Text
ppNodeBody env sie de ntr pn es = do
  let promoted = promotedProdName env ntr pn
      p = prodOfProdname env promoted
      prodEs = prodElements p
  case homSpecForTarget env (prodHoms p) of
    Just hses -> do
      ppEs <- ppSymtermElements env sie de False prodEs es
      pure (" " <> T.unwords (applyHomSpec env hses ppEs) <> " ")
    Nothing -> do
      let includeTerminals = isCaml env && optCamlIncludeTerminals (envOpts env)
          ppEs = ppSymtermElements env sie de includeTerminals prodEs es
      case pn of
        "formula_judgement" -> case es of
          [SteSt (StNode _ _ [SteSt (StNode _ pn'' es'')])] -> do
            let p'' = prodOfProdname env pn''
                stnb'' = StNode "" pn'' es''
            case envTarget env of
              Isa -> case isaFancySyntaxHomForProd env p'' of
                Nothing -> ppSymtermElementJudgeIsaPlain env sie de p'' stnb''
                Just (hs, _, _) -> ppSymtermElementJudgeIsaFancy env sie de hs p'' stnb''
              Coq -> do
                xs <- ppSymtermElements env sie de False (prodElements p'') es''
                pure (pn'' <> " " <> T.unwords xs)
              Hol -> do
                xs <- ppSymtermElements env sie de False (prodElements p'') es''
                pure (" ( " <> pn'' <> " " <> T.unwords xs <> " )")
              Lem -> do
                xs <- ppSymtermElements env sie de False (prodElements p'') es''
                pure (pn'' <> " " <> T.unwords xs)
              Caml -> pure (oops "Caml pp_symterm for proper symterms not supported")
          _ -> pure (oops "strange production in formula_judgement")
        _
          | ntr == "user_syntax" -> case es of
              [SteSt st] -> ppSymterm env sie de st
              [SteMetavar _ mv] -> ppMetavarWithDeWithSie env sie de mv
              _ -> pure (oops "strange production in user_syntax")
        "formula_dots" -> ppFormulaDots env sie de p es ppEs
        _ -> case envTarget env of
          Isa -> case isaFancySyntaxHomForProd env p of
            Nothing -> case es of
              [] -> pure promoted
              _ -> (\xs -> "(" <> promoted <> " " <> T.unwords xs <> ")") <$> ppEs
            Just (hs, _, _) -> (\xs -> "(" <> T.concat (applyHomSpec env hs xs) <> ")") <$> ppEs
          Caml -> case es of
            [] -> pure (capitalize promoted)
            _ -> (\xs -> "(" <> capitalize promoted <> " " <> (case xs of [x] -> x; _ -> "(" <> T.intercalate "," xs <> ")") <> ")") <$> ppEs
          Lem -> case es of
            [] -> pure (capitalize promoted)
            _ -> (\xs -> "(" <> capitalize promoted <> " " <> (case xs of [x] -> x; _ -> T.unwords xs) <> ")") <$> ppEs
          _ -> case es of
            [] -> pure promoted
            _ -> (\xs -> "(" <> promoted <> " " <> T.unwords xs <> ")") <$> ppEs

ppFormulaDots :: Env -> Suffix -> De -> Prod -> [Ste] -> P [Text] -> P Text
ppFormulaDots env sie de p es ppEs = case envTarget env of
  Isa -> case isaFancySyntaxHomForProd env p of
    Nothing -> case es of
      [] -> pure "formula_dots"
      _ -> (\xs -> "(" <> "List.list_all (% b . b)" <> " " <> T.unwords xs <> ")") <$> ppEs
    Just (hs, _, _) -> (\xs -> "(" <> T.concat (applyHomSpec env hs xs) <> ")") <$> ppEs
  Hol -> case es of
    [] -> pure "formula_dots"
    _ -> (\xs -> "(" <> "EVERY (\\ b . b)" <> " " <> T.unwords xs <> ")") <$> ppEs
  Lem -> case es of
    [] -> pure "formula_dots"
    _ -> (\xs -> "(" <> "List.all (fun b -> b)" <> " " <> T.unwords xs <> ")") <$> ppEs
  Caml -> pure (oops "Caml pp_symterm for proper symterms not supported")
  Coq -> case es of
    [SteList [StliListform bound [SteSt (StNode ntr0 pn0 es0)]]] -> do
      let (ntrB, pnB, esB) =
            if pn0 == "formula_judgement"
              then case es0 of
                [SteSt (StNode _ _ [SteSt (StNode ntr' pn' es')])] -> (ntr', pn', es')
                _ -> oops "formula_dots: formula_judgement"
              else (ntr0, pn0, es0)
          sie' = SiVar "_" 0 : sie
      ntStnb <- ppNodeBody env sie' de ntrB pnB esB
      let de1i = de1Lookup (fst de) bound
      collected0 <- mapM (ppNtOrMvWithDeWithSie env sie' de) (extractNontermsDeep esB)
      quantified <- psCoqQuantifiedVarsFromDe <$> get
      let collected = removeDuplicates collected0
          withoutToplevel = [v | v <- collected, v `notElem` quantified]
          sCollected = case collected of
            [_] -> case withoutToplevel of
              (v : _) -> v
              [] -> oops "formula_dots: hd"
            _ -> "(" <> T.intercalate "," withoutToplevel <> ")"
          body
            | optCoqExpandLists (envOpts env) =
                let types = [ppNtOrMvRoot env (promoteNtmvr env (primaryNtmvr env x)) | (((x, _), _)) <- de1Ntmvsns de1i]
                 in "(unmake_list_" <> T.intercalate "_" types <> " " <> de1CompoundId de1i <> ")"
            | otherwise = de1CompoundId de1i
          arg
            | T.any (== ',') (de1Pattern de1i) =
                "(map (fun (pat_: " <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> de1Pattern de1i <> " => " <> sCollected <> " end) " <> body <> ")"
            | otherwise =
                "(map (fun (" <> de1Pattern de1i <> " : " <> de1CoqTypeOfPattern de1i <> ") => " <> sCollected <> ") " <> body <> ")"
      pure ("(forall " <> T.unwords withoutToplevel <> ", " <> "In " <> sCollected <> " " <> arg <> " -> " <> ntStnb <> ")")
    [SteList [StliListform _ _]] -> pure " <<< multiple slti in formula_dots not implemented >>> "
    _ -> pure " <<< invalid symterm in formula_dots >>> "

-- | Ott's @extract_nonterms_deep@: the nonterminals and metavariables of
-- the elements, left to right.
extractNontermsDeep :: [Ste] -> [NtMv]
extractNontermsDeep = concatMap ste
  where
    ste e = case e of
      SteSt (StNonterm _ (n, s)) -> [(Ntr n, s)]
      SteSt (StNontermSub _ _ (n, s)) -> [(Ntr n, s)]
      SteSt (StNode _ _ es) -> extractNontermsDeep es
      SteSt (StUninterpreted _ _) -> []
      SteMetavar _ (m, s) -> [(Mvr m, s)]
      SteVar _ _ -> []
      SteList stlis -> concatMap stli stlis
    stli s = case s of
      StliSingle es -> extractNontermsDeep es
      StliListform _ es -> extractNontermsDeep es

ppSymtermElementJudgeIsaFancy :: Env -> Suffix -> De -> [HomEl] -> Prod -> Symterm -> P Text
ppSymtermElementJudgeIsaFancy env sie de hs p st = do
  xs <- ppSymtermElements env sie de False (prodElements p) (nodeEs st)
  pure ("(" <> T.concat (applyHomSpec env hs xs) <> ")")

ppSymtermElementJudgeIsaPlain :: Env -> Suffix -> De -> Prod -> Symterm -> P Text
ppSymtermElementJudgeIsaPlain env sie de p st = do
  xs <- ppSymtermElements env sie de False (prodElements p) (nodeEs st)
  pure $
    if optIsaInductive (envOpts env)
      then nodePn st <> " " <> "(" <> T.intercalate ") (" xs <> ")"
      else " ( " <> T.intercalate " , " xs <> " )" <> " : " <> nodePn st

nodeEs :: Symterm -> [Ste]
nodeEs st = case st of
  StNode _ _ es -> es
  _ -> []

nodePn :: Symterm -> Text
nodePn st = case st of
  StNode _ pn _ -> pn
  _ -> ""

-- | Ott's @pp_symterm_elements'@ without the token categories: the
-- elements of a node against those of its production. The tail is printed
-- before the head, as OCaml evaluates @::@.
ppSymtermElements :: Env -> Suffix -> De -> Bool -> [Element] -> [Ste] -> P [Text]
ppSymtermElements env sie de includeTerminals = go
  where
    go prodEs es = case (prodEs, es) of
      ([], []) -> pure []
      (Terminal tm : pes, _) ->
        if includeTerminals then (ppTerminal env tm :) <$> go pes es else go pes es
      (Nonterm {} : pes, SteSt (StNonterm _ nt) : es') -> cons (ppNontermWithDeWithSie env sie de nt) (go pes es')
      (Nonterm {} : pes, SteSt (StNontermSub _ _ nt) : es') -> cons (ppNontermWithDeWithSie env sie de nt) (go pes es')
      (Nonterm {} : pes, SteSt (StNode ntr pn es'') : es') -> cons (ppNodeBody env sie de ntr pn es'') (go pes es')
      (_, SteSt (StUninterpreted _ s) : es') -> (ppUninterpreted s :) <$> go prodEs es'
      (Metavar {} : pes, SteMetavar _ mv : es') -> cons (ppMetavarWithDeWithSie env sie de mv) (go pes es')
      (Metavar {} : pes, SteVar mvrp var : es') -> (ppVariable env mvrp var :) <$> go pes es'
      (ListForm lb : pes, SteList stlis : es') -> do
        -- (pp_symterm_list_items ...) @ (f ...): the right operand first
        rest <- go pes es'
        items <- ppSymtermListItems env sie de (lbSeparator lb) (lbElements lb) stlis
        pure (items ++ rest)
      _ -> pure (oops "pp_symterm_elements' inconsistent structure")
    cons hd tl = do
      t <- tl
      h <- hd
      pure (h : t)

-- | The type names of the nonterminals and metavariables of elements.
elementsToString :: [Element] -> [Text]
elementsToString = concatMap el
  where
    el e = case e of
      Nonterm ntr _ _ -> [ntr]
      Metavar mvr _ _ -> [mvr]
      _ -> []

ppSymtermListItems :: Env -> Suffix -> De -> Maybe Text -> [Element] -> [Stli] -> P [Text]
ppSymtermListItems env sie de _ prodEs stlis = case stlis of
  [] -> pure $ case envTarget env of
    Coq
      | optCoqExpandLists (envOpts env) -> ["Nil_list_" <> T.intercalate "_" (elementsToString prodEs)]
      | otherwise -> ["nil"]
    Hol -> ["NIL"]
    _ -> ["[]"]
  _ -> do
    let includeTerminals = isCaml env && optCamlIncludeTerminals (envOpts env)
    ppStlis <- mapM (ppSymtermListItem env sie de includeTerminals prodEs) stlis
    let joinWith op = ["(" <> T.unwords (listConcat [op] ppStlis) <> ")"]
    pure $ case envTarget env of
      Isa -> joinWith "@"
      Hol -> joinWith "++"
      Caml -> joinWith "@"
      Lem -> joinWith "++"
      Coq ->
        let l = concat ppStlis
         in if length l > 1
              then
                let (appF, nil)
                      | optCoqExpandLists (envOpts env) =
                          let t = T.intercalate "_" (elementsToString prodEs) in ("app_list_" <> t, "Nil_list_" <> t)
                      | otherwise = ("app", "nil")
                 in ["(" <> foldr (\x s -> "(" <> appF <> " " <> x <> " " <> s <> ")") nil l <> ")"]
              else take 1 l

listConcat :: [a] -> [[a]] -> [a]
listConcat sep xss = case xss of
  [] -> []
  [xs] -> xs
  xs : more -> xs ++ sep ++ listConcat sep more

ppSymtermListItem :: Env -> Suffix -> De -> Bool -> [Element] -> Stli -> P [Text]
ppSymtermListItem env sie de includeTerminals prodEs stli = case stli of
  StliSingle stes -> do
    ppEs <- ppSymtermElements env sie de includeTerminals prodEs stes
    pure $ case envTarget env of
      Coq
        | optCoqExpandLists (envOpts env) ->
            let nm = T.intercalate "_" (elementsToString prodEs)
             in ["(Cons_list_" <> nm <> " " <> T.unwords ppEs <> " Nil_list_" <> nm <> ")"]
        | otherwise -> case ppEs of
            [x] -> ["(cons " <> x <> " nil)"]
            _ -> ["(cons " <> "(" <> T.intercalate "," ppEs <> ") nil)"]
      _ -> ["[(" <> T.intercalate "," ppEs <> ")]"]
  StliListform bound es -> ppSymtermListBody env sie de includeTerminals prodEs bound es

-- | Ott's @de1_lookup@.
de1Lookup :: De1 -> Bound -> De1i
de1Lookup de1 bound = fromMaybe bogus (lookup bound de1)
  where
    bogus =
      De1i
        { de1Ntmvsns = []
        , de1CompoundId = "<<< de1_lookup not found: bound " <> ppPlainBound bound <> " >>>"
        , de1Pattern = "[[[ de1_lookup not found: in de " <> "]]]"
        , de1CoqTypeOfPattern = "<<< de1_lookup not found >>>"
        , de1HolTypeOfCompoundId = "<<< de1_lookup not found >>>"
        }

-- | Ott's @pp_symterm_list_body@ for a prover: a list form is a map over
-- the compound list variable of its bound.
ppSymtermListBody :: Env -> Suffix -> De -> Bool -> [Element] -> Bound -> [Ste] -> P [Text]
ppSymtermListBody env sie de includeTerminals prodEs bound es = do
  let de1i = de1Lookup (fst de) bound
  tmp <- T.intercalate "," <$> ppSymtermElements env (SiVar "_" 0 : sie) de includeTerminals prodEs es
  let ppBody = if length es > 1 then "(" <> tmp <> ")" else tmp
      cid = de1CompoundId de1i
  if de1Pattern de1i == ppBody
    then pure [cid]
    else pure $ case envTarget env of
      Isa ->
        let vars = [ppNtOrMvWithSie env [SiPunct "_"] ntmv | (ntmv, _) <- de1Ntmvsns de1i]
            types = [ppNtOrMvRoot env (promoteNtmvr env (primaryNtmvr env r)) | ((r, _), _) <- de1Ntmvsns de1i]
            tmp' = T.intercalate "," (zipWith (\v t -> "(" <> v <> "::" <> t <> ")") vars types)
            pat = if length vars == 1 then tmp' else "(" <> tmp' <> ")"
         in ["(List.map (%" <> pat <> "." <> ppBody <> ") " <> cid <> ")"]
      Hol -> ["(MAP (\\" <> de1Pattern de1i <> " . " <> ppBody <> ") " <> cid <> ")"]
      Caml -> ["(List.map (fun " <> de1Pattern de1i <> " -> " <> ppBody <> ") " <> cid <> ")"]
      Lem -> ["(List.map (fun " <> de1Pattern de1i <> " -> " <> ppBody <> ") " <> cid <> ")"]
      Coq ->
        let expand = optCoqExpandLists (envOpts env)
            tyList = splitParensStars (de1CoqTypeOfPattern de1i)
            varList = splitParensCommas (de1Pattern de1i)
            mapFun = if expand then "map_list_" <> T.intercalate "_" tyList else "map"
            converted = concatMap convert prodEs
            convert e = case e of
              Nonterm ntr _ _ -> [(promoteNtr env ntr, isJust (lookup "coq" (ruleHoms (ruleOfNtr env ntr))))]
              Metavar mvr _ _ -> [(mvr, False)]
              _ -> []
            (header, footer)
              | not expand || any snd converted = ("", "")
              | otherwise = ("(make_list_" <> T.intercalate "_" (map fst converted) <> " ", ")")
            (patFun, patFunEnd)
              | expand = (T.unwords (zipWith (\x y -> "(" <> x <> ":" <> y <> ")") varList tyList), "")
              | length varList == 1 = ("(" <> de1Pattern de1i <> ":" <> de1CoqTypeOfPattern de1i <> ")", "")
              | otherwise = ("(pat_:" <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> de1Pattern de1i, " end ")
         in [header <> "(" <> mapFun <> " (fun " <> patFun <> " => " <> ppBody <> patFunEnd <> ") " <> cid <> ")" <> footer]

------------------------------------------------------------------------
-- Metavariable set expressions

ppAuxfn :: Text -> Text
ppAuxfn f = f

ppMseString :: Env -> Suffix -> De -> Mse -> P Text
ppMseString env sie de mse = (\(s, _, _) -> s) <$> ppMse env sie de False "" Nothing mse

-- | Ott's @pp_mse@ for a prover: the list of names an expression denotes,
-- with the functions it needs (in Isabelle with primrec, a function over
-- each list type) and their names.
ppMse :: Env -> Suffix -> De -> Bool -> Text -> Maybe RootRef -> Mse -> P (Text, [Text], [IntFunc])
ppMse env sie de isaListNameFlag prodNm ntmvro mse = case mse of
  MetaVarExp mv -> pure (single (ppMetavarWithSie env sie mv), [], [])
  NonTermExp nt -> pure (single (ppNontermWithSie env sie nt), [], [])
  MetaVarListExp mv b -> do
    let p = primaryMvrOfMvr env (fst mv)
    fake <- T.concat <$> ppSymtermListBody env sie de False [Metavar p (fst mv) (snd mv)] b [SteMetavar p mv]
    pure (unmake fake (fst mv), [], [])
  NonTermListExp nt b -> do
    let p = primaryNtrOfNtr env (fst nt)
    fake <- T.concat <$> ppSymtermListBody env sie de False [Nonterm p (fst nt) (snd nt)] b [SteSt (StNonterm p nt)]
    pure (unmake fake (fst nt), [], [])
  Aux f nt -> do
    let ntrp = ppNontermrootTy env (promoteNtr env (primaryNtrOfNtr env (fst nt)))
    pure ("(" <> auxfnName f ntrp ntrp <> " " <> ppNontermWithSie env sie nt <> ")", [], [])
  AuxList f nt b -> ppMseAuxList env sie de isaListNameFlag prodNm ntmvro f nt b
  Union m1 m2 -> case envTarget env of
    Isa -> do
      (s1, d1, f1) <- ppMse env sie de isaListNameFlag prodNm ntmvro m1
      (s2, d2, f2) <- ppMse env sie de isaListNameFlag prodNm ntmvro m2
      pure (s1 <> listAppend env <> s2, d1 ++ d2, f1 ++ f2)
    Coq -> do
      (s1, d1, f1) <- ppMse env sie de isaListNameFlag prodNm ntmvro m1
      (s2, d2, f2) <- ppMse env sie de isaListNameFlag prodNm ntmvro m2
      pure ("(app " <> s1 <> " " <> s2 <> ")", d1 ++ d2, f1 ++ f2)
    Hol -> do
      s2 <- ppMseString env sie de m2
      s1 <- ppMseString env sie de m1
      pure ("(" <> s1 <> listAppend env <> s2 <> ")", [], [])
    _ -> do
      s2 <- ppMseString env sie de m2
      s1 <- ppMseString env sie de m1
      pure (s1 <> listAppend env <> s2, [], [])
  Empty -> pure (if isCoq env then "nil" else "[]", [], [])
  where
    single s = if isCoq env then "(cons " <> s <> " nil)" else "[" <> s <> "]"
    unmake fake root
      | isCoq env && optCoqExpandLists (envOpts env) = case ntmvro of
          Just r -> "(unmake_list_" <> ppNtOrMvRootTy env r <> " " <> fake <> ")"
          Nothing -> "(unmake_list_" <> root <> " " <> fake <> ")"
      | otherwise = fake

ppMseAuxList :: Env -> Suffix -> De -> Bool -> Text -> Maybe RootRef -> Text -> (Text, Suffix) -> Bound -> P (Text, [Text], [IntFunc])
ppMseAuxList env sie de isaListNameFlag prodNm ntmvro f nt b = do
  let ntrp0 = primaryNtrOfNtr env (fst nt)
      (ntrp, st, dummyE) = case promoteNtr' env ntrp0 of
        Just (_, srt) -> (srt, StNontermSub ntrp0 srt nt, Nonterm srt (fst nt) (snd nt))
        Nothing -> (ntrp0, StNonterm ntrp0 nt, Nonterm ntrp0 (fst nt) (snd nt))
  ppNtlist <- T.concat <$> ppSymtermListBody env sie de False [dummyE] b [SteSt st]
  let de1i = de1Lookup (fst de) b
  case envTarget env of
    Isa
      | optIsaPrimrec (envOpts env) -> isaPrimrecAuxList env isaListNameFlag prodNm ntmvro f ntrp de1i
      | otherwise ->
          let s = ppNontermroot env ntrp in pure ("(concat (map " <> auxfnName f s s <> " (" <> ppNtlist <> ")))", [], [])
    Hol -> pure ("(FLAT (MAP " <> auxfnName f ntrp ntrp <> " (" <> ppNtlist <> ")))", [], [])
    Caml -> pure ("(List.flatten (List.map " <> auxfnName f ntrp ntrp <> " (" <> ppNtlist <> ")))", [], [])
    Lem -> let s = ppNontermroot env ntrp in pure (" (List.concat (List.map " <> auxfnName f s s <> " (" <> ppNtlist <> ")))", [], [])
    Coq
      | optCoqExpandLists (envOpts env) -> do
          let tyList = splitParensStars (de1CoqTypeOfPattern de1i)
              varList = splitParensCommas (de1Pattern de1i)
              suf = "list_" <> T.intercalate "_" tyList
              outputTyp = maybe "<<<None_in_nmtvro_pp_mse>>>" (\r -> "list " <> ppNtOrMvRootTy env r) ntmvro
              args = T.intercalate "_" [ppNtOrMvRoot env (promoteNtmvr env (primaryNtmvr env x)) | ((x, _), _) <- de1Ntmvsns de1i]
              idList = auxfnName f ntrp (args <> "_list")
              ntrs = [(y, s) | ((Ntr y, s), _) <- de1Ntmvsns de1i]
              defTypes = maybe [] fst (lookup f (envAuxfnTypes env))
              interesting = [(n, s) | (n, s) <- ntrs, primaryNtrOfNtr env n `elem` defTypes]
              fname n = let pn = primaryNtrOfNtr env n in auxfnName f pn pn
              rhs
                | null interesting = "nil"
                | otherwise = insertAppend ["(" <> fname n <> " " <> n <> ppSuffixWithSie (SiVar "_" 0 : sie) s <> ")" | (n, s) <- interesting]
              func =
                IntFunc
                  { rFunId = idList
                  , rFunDep = idList : map (fname . fst) interesting
                  , rFunType = suf
                  , rFunHeader = (idList <> " (l:" <> suf <> ")", "", ": " <> outputTyp <> " :=\n  match l with\n")
                  , rFunClauses =
                      [ ("", "Nil_" <> suf, "nil")
                      , ("", "Cons_" <> suf <> " " <> T.unwords varList <> " " <> args <> "_list_", "app (" <> rhs <> ") (" <> idList <> " " <> args <> "_list_)")
                      ]
                  }
          pure ("(" <> idList <> " " <> de1CompoundId de1i <> ")", [idList], [func])
      | otherwise -> do
          let expand = optCoqExpandLists (envOpts env)
              tyList = splitParensStars (de1CoqTypeOfPattern de1i)
              varList = splitParensCommas (de1Pattern de1i)
              (patFun, patFunEnd)
                | expand = (T.unwords (zipWith (\x y -> "(" <> x <> ":" <> y <> ")") varList tyList), "")
                | length varList == 1 = ("(" <> de1Pattern de1i <> ":" <> de1CoqTypeOfPattern de1i <> ")", "")
                | otherwise = ("(pat_:" <> de1CoqTypeOfPattern de1i <> ") => match pat_ with " <> de1Pattern de1i, " end ")
              calls = [auxfnName f n n | Nonterm n _ _ <- [dummyE]]
          se <- ppSymtermElements env (SiVar "_" 0 : sie) de False [dummyE] [SteSt st]
          let tmp = T.intercalate "," (zipWith (\x y -> x <> " " <> y) calls se)
              ppBody = tmp
          if de1Pattern de1i == ppBody
            then pure (de1CompoundId de1i, [], [])
            else pure ("(flat_map (fun " <> patFun <> " => " <> ppBody <> patFunEnd <> ") " <> de1CompoundId de1i <> ")", [], [])
  where
    insertAppend l = case l of
      [] -> "nil"
      [x] -> "(" <> x <> ")"
      _ -> foldr (\x s -> "(app " <> x <> " " <> s <> ")") (last l) (init l)

-- | Ott's Isabelle primrec case of an auxiliary function over a list
-- form: a function over the list type and one over the tuples.
isaPrimrecAuxList :: Env -> Bool -> Text -> Maybe RootRef -> Text -> Text -> De1i -> P (Text, [Text], [IntFunc])
isaPrimrecAuxList env isaListNameFlag prodNm ntmvro f ntrp de1i = do
  let tyOf ((x, _), _) = ppNtOrMvRootTy env (promoteNtmvr env (primaryNtmvr env x))
      typList = map tyOf (de1Ntmvsns de1i)
      typTuple = let tmp = T.intercalate "*" typList in if length (de1Ntmvsns de1i) > 1 then "(" <> tmp <> ")" else tmp
      typ = typTuple <> " list"
      outputTyp = maybe "<<<None_in_nmtvro_pp_mse>>>" (\r -> ppNtOrMvRootTy env r <> " list") ntmvro
      args = T.intercalate "_" typList
  preSplit <-
    if isaListNameFlag
      then do
        prodCounter <- counterNames "mse_split_prod"
        if typ `elem` prodCounter
          then pure ("_" <> prodNm)
          else addCounterName "mse_split_prod" typ >> pure ""
      else pure ""
  counterSuffix <-
    if isaListNameFlag
      then bumpCounter "mse_split_inprod" (typ <> preSplit)
      else pure ""
  let splitSuffix = preSplit <> counterSuffix
      ntrpn = ppNontermrootTy env ntrp
      idList = auxfnName f ntrpn (args <> "_list") <> splitSuffix
      listPatterns = splitParensCommas (de1Pattern de1i)
      makeTuple tl pattern ntmvsns =
        let argsList = map tyOf ntmvsns
            idTuple
              | length argsList == 1 = auxfnName f ntrpn (T.intercalate "_" argsList)
              | otherwise = auxfnName f ntrpn (T.intercalate "_" argsList) <> splitSuffix
            funcTuple
              | length ntmvsns == 1 = []
              | otherwise =
                  let tt = if length tl == 2 then "(" <> T.intercalate "*" tl <> ")" else "(" <> head tl <> "*(" <> T.intercalate "*" (tail tl) <> "))"
                      lhsTl = T.concat (tail pattern)
                      lhs = if length pattern == 2 then "(" <> T.intercalate "," pattern <> ")" else "(" <> head pattern <> "," <> lhsTl <> ")"
                      ntrs = [(y, p) | (((Ntr y, _), _), p) <- if length ntmvsns == 2 then zip ntmvsns pattern else [(head ntmvsns, head pattern)]]
                      defTypes = maybe [] fst (lookup f (envAuxfnTypes env))
                      interesting = [(n, p) | (n, p) <- ntrs, primaryNtrOfNtr env n `elem` defTypes]
                      tupleDeps = [auxfnName f n n | (n, _) <- interesting]
                      tmp = T.intercalate (listAppend env) ["(" <> auxfnName f n n <> " " <> p <> ")" | (n, p) <- interesting]
                      calc = if length ntrs == 1 then tmp else "(" <> tmp <> ")"
                      (rhs, auxTupleFuncs, deps)
                        | length tl == 2 = (calc, [], tupleDeps)
                        | otherwise =
                            let (idAux, aux) = makeTuple (tail tl) (tail pattern) (tail ntmvsns)
                             in ("(" <> calc <> ")" <> listAppend env <> "(" <> idAux <> " " <> lhsTl <> ")", aux, idAux : tupleDeps)
                   in IntFunc
                        { rFunId = idTuple
                        , rFunDep = deps
                        , rFunType = tt <> splitSuffix
                        , rFunHeader = (idTuple <> " :: \"" <> tt <> " => " <> outputTyp <> "\"\n", "", "")
                        , rFunClauses = [("", lhs, rhs)]
                        }
                        : auxTupleFuncs
         in (idTuple, funcTuple)
      (idTuple, funcTuple) = makeTuple typList listPatterns (de1Ntmvsns de1i)
      hide = hideIsaTrailingUnderscore env
      listFunc =
        IntFunc
          { rFunId = idList
          , rFunDep = [idList, idTuple]
          , rFunType = typ <> splitSuffix
          , rFunHeader = (idList <> " :: \"" <> typ <> " => " <> outputTyp <> "\"\n", "", "")
          , rFunClauses =
              [ ("", "Nil", "[]")
              , ("", "(" <> hide (args <> "_") <> "#" <> hide (args <> "_list_") <> ")", "(" <> idTuple <> " " <> hide (args <> "_") <> ")" <> listAppend env <> "(" <> idList <> " " <> hide (args <> "_list_") <> ")")
              ]
          }
  pure ("(" <> idList <> " " <> de1CompoundId de1i <> ")", [idList], listFunc : funcTuple)

counterNames :: Text -> P [Text]
counterNames k = maybe [] M.keys . M.lookup k . psCounters <$> get

addCounterName :: Text -> Text -> P ()
addCounterName k n = modify (\s -> s {psCounters = M.insertWith M.union k (M.singleton n 0) (psCounters s)})

-- | A split counter: empty the first time a name is seen, then 1, 2, ...
bumpCounter :: Text -> Text -> P Text
bumpCounter k n = do
  s <- get
  let m = M.findWithDefault M.empty k (psCounters s)
  case M.lookup n m of
    Nothing -> do
      modify (\st -> st {psCounters = M.insert k (M.insert n 0 m) (psCounters st)})
      pure ""
    Just c -> do
      modify (\st -> st {psCounters = M.insert k (M.insert n (c + 1) m) (psCounters st)})
      pure (T.pack (show (c + 1)))

------------------------------------------------------------------------
-- Quantified variables and names

-- | Ott's @extract_quantified_proof_assistant_vars@: the variables a rule
-- quantifies over, with their HOL and Coq types.
extractQuantifiedProofAssistantVars :: Env -> De1 -> De2 -> De3 -> P [(Text, Text, (Text, Maybe Text))]
extractQuantifiedProofAssistantVars env de1 de2 de3 = do
  let expand = isCoq env && optCoqExpandLists (envOpts env)
      fromDe1 =
        [ (de1CompoundId de1i, de1HolTypeOfCompoundId de1i, (coqTypeVar, Just tmp))
        | (_, de1i) <- de1
        , let pp1 = [ppNtOrMvRootTy env (promoteNtmvr env (primaryNtmvr env r)) | ((r, _), _) <- de1Ntmvsns de1i]
              tmp = if expand then T.intercalate "_" pp1 else T.intercalate "*" pp1
              coqTypeVar = if expand then "list_" <> tmp else "list " <> (if length pp1 > 1 then "(" <> tmp <> ")" else tmp)
        ]
      fromDe2 =
        [ case i of
            SiVar s _ -> let t = ppMetavarrootTy env (primaryMvrOfMvr env s) in (s, t, (t, Nothing))
            SiNum s -> ("UNK: NUM " <> s, "UNK_HTP", ("UNK_CTP", Nothing))
            SiPunct s -> ("UNK: PUNCT " <> s, "UNK_HTP", ("UNK_CTP", Nothing))
            SiIndex n -> ("UNK: PUNCT " <> T.pack (show n), "UNK_HTP", ("UNK_CTP", Nothing))
            SiIndexed s _ -> ("UNK: INDEXED " <> s, "UNK_HTP", ("UNK_CTP", Nothing))
            SiIndexShift n _ -> ("UNK: SHIFT " <> T.pack (show n), "UNK_HTP", ("UNK_CTP", Nothing))
        | (_, (_, i, _)) <- de2
        ]
      judgement ntmv = case fst ntmv of
        Ntr n -> ruleJudgement (ruleOfNtr env (primaryNtrOfNtr env n))
        Mvr _ -> False
  fromDe3 <- fmap concat $ forM de3 $ \(ntmv, _) ->
    if judgement ntmv
      then pure []
      else do
        let typ = ppNtOrMvRootTy env (promoteNtmvr env (primaryNtmvr env (fst ntmv)))
        v <- ppNtOrMvWithDeWithSie env [] deEmpty ntmv
        pure [(v, typ, (typ, Nothing))]
  pure (removeDuplicates (fromDe1 ++ fromDe2 ++ fromDe3))

makeNameSymterm :: Env -> Bool -> Symterm -> Text
makeNameSymterm env typ st = case st of
  StNode _ _ es -> makeNameElements env typ es
  StNonterm ntr _ -> if typ then ppNontermrootTy env ntr else ppNontermroot env ntr
  StNontermSub l t (ntr, _) -> l <> "-" <> t <> (if typ then ppNontermrootTy env ntr else ppNontermroot env ntr)
  StUninterpreted _ s -> s

makeNameElements :: Env -> Bool -> [Ste] -> Text
makeNameElements env typ es =
  let lst = map el es
      body = T.intercalate (if typ then "*" else "_") lst
   in if length lst > 1 && typ then "(" <> body <> ")" else body
  where
    el e = case e of
      SteSt st -> makeNameSymterm env typ st
      SteMetavar mvr _ -> if typ then ppMetavarrootTy env mvr else ppMetavarroot env mvr
      _ -> oops "Ste_var or Ste_list in make_name_element"

makeDepSymterm :: Symterm -> [Text]
makeDepSymterm st = case st of
  StNode _ _ es -> concatMap el es
  StNonterm ntr _ -> [ntr]
  StNontermSub l t (ntr, _) -> [l <> "-" <> t <> ntr]
  StUninterpreted _ s -> [s]
  where
    el e = case e of
      SteSt s -> makeDepSymterm s
      SteMetavar mvr _ -> [mvr]
      SteVar mvr _ -> [mvr]
      SteList _ -> oops "Ste_list in make_dep_element"
