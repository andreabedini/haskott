{-# LANGUAGE OverloadedStrings #-}

-- | The Typst back end: Ott's TeX back end in its Typst dialect, as the
-- andreabedini/ott fork prints it (@grammar_pp.ml@, @defns.ml@,
-- @system_pp.ml@, @embed_pp.ml@). The output is a Typst file defining one
-- function per rule, definition and definition rule, with a runtime of
-- defaults that @typst-preamble@ embeds may shadow.
module Haskott.Typst
  ( TypstOptions (..)
  , defaultTypstOptions
  , Env
  , makeEnv
  , makeTypst
  , typstDocument
  , ppSymterm
  , renderSymterm
  , filterDocument
  , countsString
  ) where

import Data.Char (isDigit)
import Data.List (find, sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as B
import Haskott.Defns
import Haskott.Spec hiding (ppSuffix, ppSuffixItem)
import Haskott.Term.Parse
import Haskott.Term.Symterm

data TypstOptions = TypstOptions
  { optPrefix :: Text
  , optShowMeta :: Bool
  , optShowCategories :: Bool
  , optColour :: Bool
  , optWrap :: Bool
  , optSuppressedCategories :: [Text]
  , optSuppressedNtrs :: [Text]
  }

defaultTypstOptions :: TypstOptions
defaultTypstOptions = TypstOptions "ott" True False True True [] []

-- | What the printers need from the specification, indexed.
data Env = Env
  { envOpts :: TypstOptions
  , envSpec :: Spec
  , envRuleByNtr :: M.Map Text Rule
  -- ^ every rule by every one of its names
  , envProdByName :: M.Map Text (Text, Prod)
  -- ^ every production by name, with its rule's primary root
  , envMvdByMvr :: M.Map Text MetavarDefn
  -- ^ every metavariable declaration by every one of its names
  , envPromotion :: M.Map Text (Text, M.Map Text Text)
  -- ^ a sub-rule root to its top root and its productions' promotion
  , envTerminalHom :: M.Map Text (Maybe [HomEl])
  -- ^ the @typst@ hom of the first production of the @terminals@ rule
  -- starting with each terminal
  , envParseQuotation :: Text -> Symterm
  -- ^ the parser of @[[ ]]@ quotations, supplied by the driver, which
  -- owns the term parser and the parse policy
  }

makeEnv :: TypstOptions -> Spec -> (Text -> Symterm) -> Env
makeEnv opts spec quotation =
  Env
    { envParseQuotation = quotation
    , envOpts = opts
    , envSpec = spec
    , envRuleByNtr = M.fromList [(n, r) | r <- specRules spec, (n, _) <- ruleNames r]
    , envProdByName = M.fromList [(prodName p, (ruleName r, p)) | r <- specRules spec, p <- ruleProds r]
    , envMvdByMvr = M.fromList [(n, md) | md <- specMetavars spec, (n, _) <- mvdNames md]
    , envPromotion = M.fromList [(lower, (top, M.fromList pps)) | (lower, (top, pps)) <- srdPromotion (specSubruleData spec)]
    , envTerminalHom =
        case find ((== "terminals") . ruleName) (specRules spec) of
          Nothing -> M.empty
          Just r ->
            M.fromListWith (\_ first -> first)
              [ (tm, lookup "typst" (prodHoms p))
              | p <- ruleProds r
              , (Terminal tm : _) <- [prodElements p]
              ]
    }

-- | Everything the Typst output needs from a checked specification: the
-- parse policy (several parses of a term are accepted when they print the
-- same in Typst, unless picky), the term parser, the processed
-- definitions with their diagnostics, and the environment whose quotation
-- parser follows the same policy.
makeTypst :: TypstOptions -> Bool -> Spec -> (Env, ParsePolicy, TermParser, Processed, [Diagnostic])
makeTypst opts picky spec =
  let tp = makeTermParser spec
      -- Ott compares the parses of a term only under its TeX and prover
      -- modes, so a Typst target alone takes the first parse
      policy = if picky then Picky else FirstIfSame []
      (processed, diags) = processDefns policy tp spec
      quotation s = case justOneParse policy userSyntaxTransform tp "user_syntax" False s of
        Parsed p -> parseTerm p
        NoParses -> StUninterpreted (noParsesErrorString tp "user_syntax" False s)
        MultipleParses _ -> StUninterpreted "multiple parses"
   in (makeEnv opts spec quotation, policy, tp, processed, diags)

------------------------------------------------------------------------
-- Dialect leaves

typstString :: Text -> Text
typstString s = "\"" <> T.concatMap esc s <> "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      _ -> T.singleton c

-- | Inline math: Typst reads @$ x $@, with surrounding spaces, as display
-- math.
typstMath :: Text -> Text
typstMath s = "$" <> ocamlTrim s <> "$"

-- | OCaml's @String.trim@: spaces, tabs, newlines, carriage returns and
-- form feeds at both ends.
ocamlTrim :: Text -> Text
ocamlTrim = T.dropAround (`elem` (" \t\n\r\x0c" :: String))

typstComMath :: Text -> Text
typstComMath s = "#(" <> typstMath s <> ")"

app :: Text -> [Text] -> Text
app cmd args = cmd <> "(" <> T.intercalate ", " args <> ")"

sans :: Text -> Text
sans s = "sans(" <> typstString s <> ")"

-- | Ott's @is_alpha@ on the bytes of the string: letters of ISO 8859-1
-- and underscore; true of the empty string.
isAlpha :: Text -> Bool
isAlpha = B.all ok . TE.encodeUtf8
  where
    ok c =
      (c >= 65 && c <= 90)
        || (c >= 192 && c <= 214)
        || (c >= 216 && c <= 222)
        || (c >= 97 && c <= 122)
        || (c >= 224 && c <= 246)
        || (c >= 248 && c <= 254)
        || c == 95

byteLength :: Text -> Int
byteLength = B.length . TE.encodeUtf8

-- | Ott's @tex_command_escape@.
commandEscape :: Text -> Text
commandEscape = T.concatMap esc
  where
    esc c = case c of
      '_' -> "XX"
      '#' -> "YY"
      '\'' -> "PP"
      '0' -> "Zero"
      '1' -> "One"
      '2' -> "Two"
      '3' -> "Three"
      '4' -> "Four"
      '5' -> "Five"
      '6' -> "Six"
      '7' -> "Seven"
      '8' -> "Eight"
      '9' -> "Nine"
      _ -> T.singleton c

name :: Env -> Text -> Text
name env s = optPrefix (envOpts env) <> s

-- | Ott's @remove_duplicates@: the last occurrence of each survives.
removeDuplicatesLast :: Eq a => [a] -> [a]
removeDuplicatesLast xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicatesLast more else x : removeDuplicatesLast more

------------------------------------------------------------------------
-- Token categories and spacing

data Ttc = TtcAlpha | TtcSymb | TtcNt | TtcSpace | TtcDots | TtcComp
  deriving (Eq, Show)

classifyTerminal :: Text -> Ttc
classifyTerminal s = if isAlpha s then TtcAlpha else TtcSymb

spacing :: Ttc -> Ttc -> Text
spacing l r = case (l, r) of
  (TtcSpace, _) -> ""
  (_, TtcSpace) -> ""
  (TtcSymb, TtcSymb) -> ""
  (TtcSymb, TtcNt) -> ""
  (TtcNt, TtcSymb) -> ""
  _ -> "thin"

insertSpacing :: [(Text, Ttc)] -> Text
insertSpacing es = case es of
  [] -> ""
  [(s, _)] -> s
  (s, c) : rest@((_, c') : _) -> s <> " " <> spacing c c' <> " " <> insertSpacing rest

------------------------------------------------------------------------
-- Homs

-- | A hom with its references already resolved to strings.
applyHomSpec :: Env -> [HomEl] -> [Text] -> [Text]
applyHomSpec env hs ss = map el hs
  where
    el h = case h of
      HomString s -> s
      HomIndex i -> nth i
      HomTerminal tm -> ppTerminal env tm
      HomLnFreeIndex _ i -> nth i
    nth i = if i >= 0 && i < length ss then ss !! i else "UNIMPLEMENTED"

-- | A hom printed as text: strings only (Ott's @pp_hom_spec@ for TeX).
ppHomSpec :: [HomEl] -> Text
ppHomSpec = T.concat . map el
  where
    el h = case h of
      HomString s -> s
      HomTerminal tm -> tm
      _ -> "UNIMPLEMENTED"

pseudoHomSpec :: [HomEl] -> Text
pseudoHomSpec = T.concat . map el
  where
    el h = case h of
      HomString s -> s
      HomTerminal tm -> tm
      _ -> error "Haskott.Typst: nontermroot hom contains a reference"

comHom :: [Hom] -> Maybe [HomEl]
comHom = lookup "com"

-- | A comment hom over the nonterminals and metavariables of elements.
ppComEs :: Env -> [Hom] -> [Element] -> Text
ppComEs env homs es = case comHom homs of
  Nothing -> ""
  Just hs ->
    let ss = mapMaybe ppElementForCom es
     in name env "com" <> "[" <> T.concat (applyHomSpec env hs (map typstComMath ss)) <> "]"
  where
    ppElementForCom e = case e of
      Nonterm _ n suff -> Just (ppNonterm env [] (n, suff))
      Metavar _ m suff -> Just (ppMetavar env [] (m, suff))
      Terminal _ -> Nothing
      ListForm _ -> Just "pp element refactoring in progress"

ppComStrings :: Env -> [Hom] -> [Text] -> Text
ppComStrings env homs ss = case comHom homs of
  Nothing -> ""
  Just hs -> name env "com" <> "[" <> T.concat (applyHomSpec env hs (map typstComMath ss)) <> "]"

------------------------------------------------------------------------
-- Terminals, nonterminals, metavariables, variables

ppTerminal :: Env -> Text -> Text
ppTerminal env tm = case M.lookup tm (envTerminalHom env) of
  Just (Just hom) -> ppHomSpec hom
  _ ->
    let es = typstString tm
     in if isAlpha tm then app (name env "kw") [es] else app (name env "sym") [es]

ppDots :: Int -> Text
ppDots _ = " dots.h "

ppUninterpreted :: Text -> Text
ppUninterpreted s = if byteLength s > 1 || isAlpha s then "bold(" <> typstString s <> ")" else typstString s

ruleOf :: Env -> Text -> Rule
ruleOf env ntr = fromMaybe (error ("Haskott.Typst: no rule " ++ T.unpack ntr)) (M.lookup ntr (envRuleByNtr env))

mvdOf :: Env -> Text -> MetavarDefn
mvdOf env mvr = fromMaybe (error ("Haskott.Typst: no metavar " ++ T.unpack mvr)) (M.lookup mvr (envMvdByMvr env))

ppNonterm :: Env -> Suffix -> (Text, Suffix) -> Text
ppNonterm env sie (ntr, suff) =
  let r = ruleOf env ntr
      perName = lookup "typst" (fromMaybe [] (lookup ntr (ruleNames r)))
      perRule = lookup "typst" (ruleHoms r)
      suffixText = ppSuffix env sie suff
   in case (perName, perRule) of
        (Nothing, Nothing) -> app (name env "nt") [typstString ntr <> suffixText]
        (Just hs, _) -> pseudoHomSpec hs <> suffixText
        (Nothing, Just hs) -> T.concat (applyHomSpec env hs [typstString ntr <> suffixText])

ppMetavar :: Env -> Suffix -> (Text, Suffix) -> Text
ppMetavar env sie (mvr, suff) =
  let md = mvdOf env mvr
      perName = lookup "typst" (fromMaybe [] (lookup mvr (mvdNames md)))
      perDecl = lookup "typst" (mvdHoms md)
      suffixText = ppSuffix env sie suff
   in case (perName, perDecl) of
        (Nothing, Nothing) -> app (name env "mv") [typstString mvr <> suffixText]
        (Just hs, _) -> pseudoHomSpec hs <> suffixText
        (Nothing, Just hs) -> T.concat (applyHomSpec env hs [typstString mvr <> suffixText])

ppMetavarroot :: Env -> Text -> Text
ppMetavarroot env mvr = ppMetavar env [] (mvr, [])

ppNontermroot :: Env -> Text -> Text
ppNontermroot env ntr = ppNonterm env [] (ntr, [])

ppVariable :: Env -> Text -> Text -> Text
ppVariable env mvrp var = case lookup "typstvar" (mvdHoms (mvdOf env mvrp)) of
  Nothing -> "italic(" <> typstString var <> ")"
  Just hs -> T.concat (applyHomSpec env hs [typstString var])

------------------------------------------------------------------------
-- Suffixes

ppSuffix :: Env -> Suffix -> Suffix -> Text
ppSuffix env sie suff =
  let subscript = filter isSub suff
      nosubscript = filter (== SiPunct "'") suff
   in T.concat (map (ppSuffixItem env sie True) nosubscript)
        <> ( if null subscript
               then ""
               else "_(" <> T.intercalate " thin " (map (ppSuffixItem env sie True) subscript) <> ")"
           )
  where
    isSub si = case si of
      SiNum _ -> True
      SiVar _ _ -> True
      SiIndex _ -> True
      SiIndexed _ _ -> True
      SiIndexShift _ _ -> True
      SiPunct _ -> False

ppSuffixItem :: Env -> Suffix -> Bool -> SuffixItem -> Text
ppSuffixItem env sie nosub si = case si of
  SiNum s -> if nosub then s else "_(" <> s <> ")"
  SiPunct s -> s
  SiVar s n -> let v = ppSuffixvar env (s, n) in if nosub then v else "_(" <> v <> ")"
  SiIndex i -> ppSuffixItem env sie nosub (nthSie sie i)
  SiIndexShift i k -> ppSuffixItem env sie nosub (shiftedSieItem sie i k)
  SiIndexed s inner ->
    let s' = ppSuffixvar env (s, 0) <> "_(" <> ppSuffixItem env sie True inner <> ")"
     in if nosub then s' else "_(" <> s' <> ")"

nthSie :: Suffix -> Int -> SuffixItem
nthSie sie i = if i >= 0 && i < length sie then sie !! i else SiNum "999"

shiftedSieItem :: Suffix -> Int -> Int -> SuffixItem
shiftedSieItem sie i k =
  let si = nthSie sie i
   in case si of
        SiNum s | T.all isDigit s, not (T.null s) -> SiNum (T.pack (show (read (T.unpack s) + k :: Int)))
        SiVar v o -> SiVar v (o + k)
        _ -> si

-- | The de Bruijn indices inside a bound refer to the enclosing list
-- forms; resolve them before the bound is pushed onto the environment.
resolveSuffixItem :: Suffix -> SuffixItem -> SuffixItem
resolveSuffixItem sie si = case si of
  SiIndexed s (SiIndex i) | i >= 0 && i < length sie -> SiIndexed s (sie !! i)
  _ -> si

ppSuffixvar :: Env -> (Text, Int) -> Text
ppSuffixvar env (s, n) =
  let md = mvdOf env s
      hso = lookup "typst" (fromMaybe [] (lookup s (mvdNames md)))
      ppMvr = case hso of
        Nothing -> typstString s
        Just hs -> pseudoHomSpec hs
   in app (name env "mv") [ppMvr] <> (if n == 0 then "" else offsetText n)

offsetText :: Int -> Text
offsetText n
  | n == 0 = ""
  | n > 0 = "+" <> T.pack (show n)
  | otherwise = T.pack (show n)

------------------------------------------------------------------------
-- Symbolic terms

-- | A term, with no enclosing list forms.
renderSymterm :: Env -> Symterm -> Text
renderSymterm env = ppSymterm env []

ppSymterm :: Env -> Suffix -> Symterm -> Text
ppSymterm env sie st = case st of
  StNode "fancy_formula" pn es -> ppFancyFormula env sie pn es
  StNode ntr pn es -> ppNodeBody env sie ntr pn es
  StNonterm _ nt -> ppNonterm env sie nt
  StNontermSub _ _ nt -> ppNonterm env sie nt
  StUninterpreted s ->
    let s' = "mono(" <> typstString ("<<" <> s <> ">>") <> ")"
     in if optColour (envOpts env) then "#text(fill: red, $" <> s' <> "$)" else s'

ppFancyFormula :: Env -> Suffix -> Text -> [Ste] -> Text
ppFancyFormula env sie embedding es =
  let sts = [st | SteSt st <- es]
      pieces = T.splitOn "-ARG-" embedding
      ppString s = "mono(" <> typstString s <> ")"
      -- Str.full_split yields texts and delimiters alternately, without
      -- empty texts
      go ts ps = case (ts, ps) of
        ([t], []) -> text t
        (t : more, p : ps') -> text t <> ppSymterm env sie p <> go more ps'
        _ -> "internal fold_in"
      text t = if T.null t then "" else ppString t
   in go pieces sts

-- | The production a node is printed with: a sub-rule's node is promoted
-- to the top rule's production.
promotedProd :: Env -> Text -> Text -> (Text, Prod)
promotedProd env ntr pn =
  let pn' = case M.lookup ntr (envPromotion env) of
        Just (_, pps) -> fromMaybe (error ("Haskott.Typst: production " ++ T.unpack pn ++ " not found in the promotion of " ++ T.unpack ntr)) (M.lookup pn pps)
        Nothing -> pn
   in fromMaybe (error ("Haskott.Typst: no production " ++ T.unpack pn')) (M.lookup pn' (envProdByName env))

ppNodeBody :: Env -> Suffix -> Text -> Text -> [Ste] -> Text
ppNodeBody env sie ntr pn es =
  let (_, p) = promotedProd env ntr pn
      prodEs = prodElements p
   in case lookup "typst" (prodHoms p) of
        Just hs ->
          let ppEs = map fst (ppElements env sie False prodEs es)
           in " " <> T.intercalate " " (applyHomSpec env hs ppEs) <> " "
        Nothing ->
          if pn == "formula_dots"
            then T.intercalate " quad " (map fst (ppElements env sie True prodEs es))
            else insertSpacing (ppElements env sie True prodEs es)

-- | The elements of a node against the elements of its production.
ppElements :: Env -> Suffix -> Bool -> [Element] -> [Ste] -> [(Text, Ttc)]
ppElements env sie includeTerminals = go
  where
    go prodEs es = case (prodEs, es) of
      ([], []) -> []
      (Terminal tm : pes, _) ->
        if includeTerminals then (ppTerminal env tm, classifyTerminal tm) : go pes es else go pes es
      (_, SteSt (StUninterpreted s) : es') -> (ppUninterpreted s, classifyTerminal s) : go prodEs es'
      (Nonterm {} : pes, SteSt (StNonterm _ nt) : es') -> (ppNonterm env sie nt, TtcNt) : go pes es'
      (Nonterm {} : pes, SteSt (StNontermSub _ _ nt) : es') -> (ppNonterm env sie nt, TtcNt) : go pes es'
      (Nonterm {} : pes, SteSt (StNode ntr pn es'') : es') -> (ppNodeBody env sie ntr pn es'', TtcNt) : go pes es'
      (Metavar {} : pes, SteMetavar _ mv : es') -> (ppMetavar env sie mv, TtcNt) : go pes es'
      (Metavar {} : pes, SteVar mvrp var : es') -> (ppVariable env mvrp var, TtcNt) : go pes es'
      (ListForm lb : pes, SteList stlis : es') ->
        ppListItems env sie (lbSeparator lb) (lbElements lb) stlis ++ go pes es'
      _ -> error ("Haskott.Typst: inconsistent structure in " ++ show (map ppPlainSte es))
    ppPlainSte ste = case ste of
      SteSt st -> ppPlainSymterm st
      SteMetavar _ (m, s) -> m <> ppSuffixPlain s
      SteVar _ v -> v
      SteList _ -> "list"
    ppSuffixPlain = T.concat . map ppSuffixItemPlain
    ppSuffixItemPlain si = case si of
      SiNum s -> s
      SiPunct s -> s
      SiVar v n -> v <> offsetText n
      SiIndex i -> "[" <> T.pack (show i) <> "]"
      SiIndexed s inner -> s <> ppSuffixItemPlain inner
      SiIndexShift i k -> "[" <> T.pack (show i) <> "]" <> offsetText k

ppListItems :: Env -> Suffix -> Maybe Text -> [Element] -> [Stli] -> [(Text, Ttc)]
ppListItems env sie tmopt prodEs stlis =
  let sep = case tmopt of
        Nothing -> []
        Just tm -> [(ppTerminal env tm, classifyTerminal tm)]
      item stli = case stli of
        StliSingle stes -> ppElements env sie True prodEs stes
        StliListform bound es -> ppListBody env sie tmopt prodEs bound es
   in case stlis of
        [] -> [("thin", TtcSpace)]
        _ -> listConcat sep (map item stlis)

listConcat :: [a] -> [[a]] -> [a]
listConcat sep xss = case xss of
  [] -> []
  [xs] -> xs
  xs : more -> xs ++ sep ++ listConcat sep more

ppListBody :: Env -> Suffix -> Maybe Text -> [Element] -> Bound -> [Ste] -> [(Text, Ttc)]
ppListBody env sie tmopt prodEs bound es = case bound of
  BoundDotform lower upper n ->
    let sep = case tmopt of
          Nothing -> []
          Just tm -> [(ppTerminal env tm, classifyTerminal tm)]
     in ppElements env (resolveSuffixItem sie lower : sie) True prodEs es
          ++ sep
          ++ [(ppDots n, TtcDots)]
          ++ sep
          ++ ppElements env (resolveSuffixItem sie upper : sie) True prodEs es
  BoundComp v ->
    [(app (name env "comp") [body v, ppMetavarroot env v], TtcComp)]
  BoundCompU v u ->
    [(app (name env "compu") [body v, ppMetavarroot env v, ppSuffixItem env [] True u], TtcComp)]
  BoundCompLU v l u n ->
    [(app (name env "complu") [body v, ppMetavarroot env v, ppSuffixItem env [] True l, ppDots n, ppSuffixItem env [] True u], TtcComp)]
  where
    body v = insertSpacing (ppElements env (SiVar v 0 : sie) True prodEs es)

------------------------------------------------------------------------
-- Binding specifications

ppBindspec :: Env -> Bindspec -> Text
ppBindspec env bs = case bs of
  Bind mse nt _ -> sans "bind" <> " thick " <> ppMse env mse <> " thick " <> sans "in" <> " thick " <> ppNonterm env [] nt
  AuxFnDef f mse _ -> ppAuxfn f <> "=" <> ppMse env mse
  NamesEqual m m' _ -> sans "names" <> "(" <> ppMse env m <> ")" <> " thin " <> "=" <> " thin " <> sans "names" <> "(" <> ppMse env m' <> ")"
  NamesDistinct m m' _ -> sans "names" <> "(" <> ppMse env m <> ")" <> " thin " <> "\"#\"" <> " thin " <> sans "names" <> "(" <> ppMse env m' <> ")"
  AllNamesDistinct m _ -> sans "distinctnames" <> "(" <> ppMse env m <> ")"

ppAuxfn :: Text -> Text
ppAuxfn f = "upright(" <> typstString f <> ")"

ppMse :: Env -> Mse -> Text
ppMse env mse = case mse of
  MetaVarExp mv -> ppMetavar env [] mv
  NonTermExp nt -> ppNonterm env [] nt
  MetaVarListExp mv@(mvr, _) b ->
    let md = mvdOf env mvr
     in T.concat (map fst (ppListBody env [] Nothing [Metavar (mvdName md) mvr []] b [SteMetavar (mvdName md) mv]))
  NonTermListExp nt@(ntr, _) b ->
    let r = ruleOf env ntr
     in T.concat (map fst (ppListBody env [] Nothing [Nonterm (ruleName r) ntr []] b [SteSt (StNonterm (ruleName r) nt)]))
  Aux f nt -> ppAuxfn f <> "(" <> ppNonterm env [] nt <> ")"
  AuxList f nt@(ntr, _) b ->
    let r = ruleOf env ntr
        ntlist = T.concat (map fst (ppListBody env [] Nothing [Nonterm (ruleName r) ntr []] b [SteSt (StNonterm (ruleName r) nt)]))
     in ppAuxfn f <> "(" <> ntlist <> ")"
  Union m m' -> ppMse env m <> " " <> "union " <> " " <> ppMse env m'
  Empty -> "\"{}\""

------------------------------------------------------------------------
-- The grammar

canonicalNode :: Text -> Prod -> Symterm
canonicalNode ntr p = StNode ntr (prodName p) (canonicalElements (prodElements p))

ppMetavardefn :: Env -> MetavarDefn -> Text
ppMetavardefn env md =
  let com = ppComStrings env (mvdHoms md) [ppMetavar env [] (mvdName md, [])]
      names = T.intercalate " , " [ppMetavarroot env mvr | (mvr, _) <- mvdNames md]
   in name env "metavarline" <> "(" <> typstMath names <> ", " <> (if T.null com then "[]" else com) <> "),"

ppProd :: Env -> Text -> Prod -> Maybe Text
ppProd env rnn p =
  let opts = envOpts env
      suppressed = any (`elem` optSuppressedCategories opts) (Set.toList (prodCategories p))
   in if suppressed || (not (optShowMeta opts) && prodMeta p && not (prodSugar p))
        then Nothing
        else
          Just $
            let pp = ppSymterm env [] (canonicalNode rnn p)
                com0 = ppComEs env (prodHoms p) (prodElements p)
                empty = "[]"
                com = if T.null com0 then empty else com0
                (meta, bindspec, remaining)
                  | prodSugar p = (typstMath (sans "S"), empty, [])
                  | prodMeta p = (typstMath (sans "M"), empty, [])
                  | otherwise = case map (ppBindspec env) (prodBindspecs p) of
                      [] -> (empty, empty, [])
                      hd : tl -> (empty, typstMath hd, tl)
                categories =
                  let cats = reverse (sortOn id [c | c <- Set.toList (prodCategories p), c /= "M", c /= "S"])
                   in if optShowCategories opts && not (null cats)
                        then typstMath (sans ("[" <> T.unwords cats <> "]"))
                        else empty
                texlong = any ((== "texlong") . fst) (prodHoms p)
                line n args = n <> "(" <> T.intercalate ", " args <> ")"
                bar = typstMath "|"
             in T.intercalate ",\n" $
                  ( if not texlong
                      then [line (name env "prodline") [bar, typstMath pp, meta, bindspec, categories, com]]
                      else
                        [ line (name env "longprodline") [bar, typstMath pp]
                        , line (name env "prodline") [empty, empty, meta, bindspec, categories, com]
                        ]
                  )
                    ++ [line (name env "bindspecprodline") [empty, empty, empty, typstMath bs, empty, empty] | bs <- remaining]

ruleSuppressed :: Env -> Rule -> Bool
ruleSuppressed env r =
  ruleName r `elem` optSuppressedNtrs (envOpts env) || (not (optShowMeta (envOpts env)) && ruleSemiMeta r)

ppRule :: Env -> Rule -> Maybe Text
ppRule env r
  | ruleSuppressed env r = Nothing
  | otherwise =
      let com0 = ppComStrings env (ruleHoms r) [ppNonterm env [] (ruleName r, [])]
          com = if T.null com0 then "[]" else com0
          names = T.intercalate " , " (removeDuplicatesLast [ppNontermroot env ntr | (ntr, _) <- ruleNames r])
          headLine = name env "rulehead" <> "(" <> typstMath names <> ", $::=$, " <> com <> ")"
          body = "#let " <> name env (commandEscape (ruleName r)) <> " = (\n"
            <> T.intercalate ",\n" (headLine : mapMaybe (ppProd env (ruleName r)) (ruleProds r))
            <> ",\n)\n"
       in Just (replaceFirst (name env "prodline" <> "(") (name env "firstprodline" <> "(") body)

replaceFirst :: Text -> Text -> Text -> Text
replaceFirst old new s = case T.breakOn old s of
  (before, rest)
    | T.null rest -> s
    | otherwise -> before <> new <> T.drop (T.length old) rest

ppRuleList :: Env -> [Rule] -> Text
ppRuleList env rs =
  T.intercalate "\n" (mapMaybe (ppRule env) rs)
    <> "\n"
    <> "#let " <> name env "grammar" <> " = " <> name env "grammartabular" <> "(\n"
    <> T.intercalate (", " <> name env "interrule" <> ",\n") [name env (commandEscape (ruleName r)) | r <- rs, not (ruleSuppressed env r)]
    <> (if null rs then "" else ", " <> name env "afterlastrule")
    <> "\n)\n\n"

ppSyntaxdefn :: Env -> Text
ppSyntaxdefn env =
  "#let " <> name env "metavars" <> " = " <> name env "metavartabular" <> "(\n"
    <> T.intercalate "\n" (map (ppMetavardefn env) (specMetavars (envSpec env)))
    <> "\n)\n\n"
    <> ppRuleList env (specRules (envSpec env))

------------------------------------------------------------------------
-- Definitions

ppDrule :: Env -> Drule -> Text
ppDrule env dr =
  let com = case comHom (druleHoms dr) of
        Nothing -> "[]"
        Just hs -> "[" <> T.concat (applyHomSpec env hs []) <> "]"
   in "#let " <> name env ("drule" <> commandEscape (druleName dr)) <> "(..args) = " <> name env "drule" <> "(..args,\n  premises: (\n"
        <> T.concat ["    " <> name env "premise" <> "(" <> typstMath (ppSymterm env [] p) <> "),\n" | (_, p) <- drulePremises dr]
        <> "  ),\n  conclusion: " <> typstMath (ppSymterm env [] (druleConclusion dr))
        <> ",\n  name: " <> name env "drulename" <> "(" <> typstString (druleName dr) <> ")"
        <> ",\n  com: " <> com <> ")\n"

ppDefn :: Env -> ProcessedClass -> ProcessedDefn -> Text
ppDefn env pc d =
  let prodName' = pcWrapper pc <> pdName d
      (_, p) = fromMaybe (error ("Haskott.Typst: no production " ++ T.unpack prodName')) (M.lookup prodName' (envProdByName env))
      com0 = ppComEs env (pdHoms d) (prodElements p)
      com = if T.null com0 then "[]" else com0
      rules = [dr | ItemRule dr <- pdRules d]
      ruleTexts = case rules of
        [] -> ""
        _ -> T.intercalate "\n" (map (ppDrule env) rules)
      use item = case item of
        ItemRule dr ->
          "    " <> name env "usedrule" <> "(" <> name env ("drule" <> commandEscape (druleName dr)) <> "()"
            <> ( if optShowCategories (envOpts env) && not (Set.null (druleCategories dr))
                   then ", categories: (" <> T.intercalate ", " (map typstString (Set.toList (druleCategories dr))) <> ",)"
                   else ""
               )
            <> "),\n"
        ItemComment es _ -> "    " <> name env "defncom" <> "[" <> ppEmbedSpec env es <> "],\n"
   in "// defn " <> pdName d <> "\n"
        <> ruleTexts
        <> "\n#let " <> name env ("defn" <> commandEscape (pcWrapper pc <> pdName d)) <> "(..args) = " <> name env "defnblock" <> "(..args,\n  judgement: "
        <> typstMath (ppSymterm env [] (pdForm d))
        <> ",\n  com: " <> com <> ",\n  rules: (\n"
        <> T.concat (map use (pdRules d))
        <> "  ))\n\n"

ppDefnClass :: Env -> ProcessedClass -> Text
ppDefnClass env pc =
  "// defns " <> pcName pc <> "\n"
    <> T.concat (map (ppDefn env pc) (pcDefns pc))
    <> "\n#let " <> name env ("defns" <> commandEscape (pcName pc)) <> " = {\n"
    <> T.concat ["  " <> name env ("defn" <> commandEscape (pcWrapper pc <> pdName d)) <> "()\n" | d <- pcDefns pc]
    <> "}\n\n"

ppFunclause :: Env -> Funclause -> Text
ppFunclause env fc =
  "    " <> name env "funclause" <> "(" <> typstMath (ppSymterm env [] (fcLhs fc)) <> ", " <> typstMath (ppSymterm env [] (fcRhs fc)) <> "),\n"

ppFundefn :: Env -> ProcessedFun -> Text
ppFundefn env pf =
  let com0 = ppComEs env (pfHoms pf) (pfElements pf)
      com = if T.null com0 then "[]" else com0
   in "// fundefn " <> pfName pf <> "\n"
        <> "\n#let " <> name env ("fundefn" <> commandEscape (pfName pf)) <> "(..args) = " <> name env "fundefnblock" <> "(..args,\n  form: "
        <> typstMath (ppSymterm env [] (pfForm pf))
        <> ",\n  com: " <> com <> ",\n  clauses: (\n"
        <> T.concat (map (ppFunclause env) (pfClauses pf))
        <> "  ))\n\n"

ppFunClass :: Env -> ProcessedFunClass -> Text
ppFunClass env pfc =
  "// fundefns " <> pfcName pfc <> "\n"
    <> T.intercalate "\n" (map (ppFundefn env) (pfcFuns pfc))
    <> "\n"
    <> "#let " <> name env ("fundefns" <> commandEscape (pfcName pfc)) <> " = {\n"
    <> T.concat ["  " <> name env ("fundefn" <> commandEscape (pfName pf)) <> "()\n" | pf <- pfcFuns pfc]
    <> "}\n\n"

ppDefnss :: Env -> Processed -> Text
ppDefnss env processed =
  "// defnss\n"
    <> T.concat (map item (processedItems processed))
    <> "#let " <> name env "defnss" <> " = {\n"
    <> T.concat (map entry (processedItems processed))
    <> "}\n\n"
  where
    item it = case it of
      PReln pc -> ppDefnClass env pc
      PFuns pfc -> ppFunClass env pfc
    entry it = case it of
      PReln pc -> "  " <> name env ("defns" <> commandEscape (pcName pc)) <> "\n"
      PFuns pfc -> "  " <> name env ("fundefns" <> commandEscape (pfcName pfc)) <> "\n"

------------------------------------------------------------------------
-- Embeds and quotations

-- | The quotations of an embed are terms of user syntax. A quotation that
-- does not parse is reported through the parser's policy and printed as
-- uninterpreted, as Ott does.
ppEmbedSpec :: Env -> [EmbedEl] -> Text
ppEmbedSpec env = T.concat . map el
  where
    el e = case e of
      EmbedString s -> s
      EmbedInner "TEX_NAME_PREFIX" -> optPrefix (envOpts env)
      EmbedInner s -> ocamlTrim (ppSymterm env [] (envQuotation env s))

envQuotation :: Env -> Text -> Symterm
envQuotation = envParseQuotation

------------------------------------------------------------------------
-- The whole document

countsString :: Processed -> Text
countsString processed =
  let drules = [dr | PReln pc <- processedItems processed, d <- pcDefns pc, ItemRule dr <- pdRules d]
      clausesOf dr = druleConclusion dr : map snd (drulePremises dr)
      good st = not (hasUninterpreted st)
      clauseCounts = [(length (filter good cs), length (filter (not . good) cs)) | dr <- drules, let cs = clausesOf dr]
      ruleGood = length [() | (_, bad) <- clauseCounts, bad == 0]
      ruleBad = length clauseCounts - ruleGood
      clauseGood = sum (map fst clauseCounts)
      clauseBad = sum (map snd clauseCounts)
      n = T.pack . show
   in if ruleGood + ruleBad == 0
        then ""
        else
          "Definition rules:        " <> n ruleGood <> " good    " <> n ruleBad <> " bad\n"
            <> "Definition rule clauses: " <> n clauseGood <> " good    " <> n clauseBad <> " bad\n"

hasUninterpreted :: Symterm -> Bool
hasUninterpreted st = case st of
  StUninterpreted _ -> True
  StNode _ _ es -> any ste es
  _ -> False
  where
    ste e = case e of
      SteSt s -> hasUninterpreted s
      SteList stlis -> any stli stlis
      _ -> False
    stli s = case s of
      StliSingle es -> any ste es
      StliListform _ es -> any ste es

runtime :: Text -> Text
runtime p =
  T.unlines
    [ "#let " <> p <> "nt(x) = math.italic(x)"
    , "#let " <> p <> "mv(x) = math.italic(x)"
    , "#let " <> p <> "kw(x) = math.bold(math.upright(x))"
    , "#let " <> p <> "sym(x) = x"
    , "#let " <> p <> "com(x) = x"
    , "#let " <> p <> "drulename(x) = smallcaps(x)"
    , "#let " <> p <> "comp(body, var) = math.attach(math.overline(body), t: var)"
    , "#let " <> p <> "compu(body, var, upper) = math.attach(math.overline(body), t: $var < upper$)"
    , "#let " <> p <> "complu(body, var, lower, ellipsis, upper) = math.attach(math.overline(body), t: $var in lower ellipsis upper$)"
    , ""
    , "#let " <> p <> "premise(x) = x"
    , "#let " <> p <> "drule(premises: (), conclusion: none, name: none, com: none, ..args) = {"
    , "  let top = stack(dir: ttb, spacing: 0.65em, ..premises)"
    , "  $ display(frac(#top, conclusion)) quad #name $"
    , "}"
    , "#let " <> p <> "usedrule(r, categories: ()) = block(r)"
    , "#let " <> p <> "defncom(x) = x"
    , "#let " <> p <> "defnblock(judgement: none, com: none, rules: (), ..args) = block(width: 100%)["
    , "  #box(stroke: 0.5pt, inset: 3pt, judgement) #h(1em) #com"
    , "  #for r in rules { r }"
    , "]"
    , "#let " <> p <> "funclause(lhs, rhs) = (lhs, $equiv$, rhs)"
    , "#let " <> p <> "fundefnblock(form: none, com: none, clauses: (), ..args) = block(width: 100%)["
    , "  #box(stroke: 0.5pt, inset: 3pt, form) #h(1em) #com"
    , "  #align(center, grid(columns: 3, column-gutter: 0.5em, row-gutter: 0.65em, ..clauses.flatten()))"
    , "]"
    , ""
    , "#let " <> p <> "rulehead(names, cce, com) = (names, [], cce, [], [], grid.cell(colspan: 2, com))"
    , "#let " <> p <> "prodline(bar, prod, meta, bindspec, categories, com) = ([], [], bar, prod, [#meta #bindspec], categories, com)"
    , "#let " <> p <> "firstprodline = " <> p <> "prodline"
    , "#let " <> p <> "longprodline(bar, prod) = ([], [], bar, grid.cell(colspan: 4, prod))"
    , "#let " <> p <> "firstlongprodline = " <> p <> "longprodline"
    , "#let " <> p <> "bindspecprodline = " <> p <> "prodline"
    , "#let " <> p <> "interrule = (grid.cell(colspan: 7, inset: (top: 0.5em))[],)"
    , "#let " <> p <> "afterlastrule = ()"
    , "#let " <> p <> "grammartabular(..rules) = grid(columns: 7, column-gutter: 0.4em, row-gutter: 0.5em, align: left + horizon, ..rules.pos().flatten())"
    , "#let " <> p <> "metavarline(names, com) = (names, com)"
    , "#let " <> p <> "metavartabular(..lines) = grid(columns: 2, column-gutter: 1em, row-gutter: 0.5em, ..lines.pos().flatten())"
    ]
    <> "\n"

-- | The Typst file for a specification: the header names the sources as
-- Ott prints them.
typstDocument :: Env -> Text -> Processed -> Text
typstDocument env sources processed =
  let p = optPrefix (envOpts env)
      embeds which = T.concat [ppEmbedSpec env (embedSpec e) <> "\n" | e <- specEmbeds (envSpec env), embedName e == which]
   in "// generated by Ott 0.34 from: " <> sources <> "\n\n"
        <> runtime p
        <> embeds "typst-preamble"
        <> ppSyntaxdefn env
        <> ppDefnss env processed
        <> "#let " <> p <> "all = [\n#" <> p <> "metavars\n\n#" <> p <> "grammar\n\n"
        <> embeds "typst"
        <> "\n#" <> p <> "defnss\n]\n\n"
        <> ( if optWrap (envOpts env)
               then "#" <> p <> "all\n\n#raw(block: true, " <> typstString (countsString processed) <> ")\n"
               else ""
           )

------------------------------------------------------------------------
-- The document filter

-- | Ott's @-typst_filter@: every @[[ ... ]]@ of a document is parsed as
-- user syntax and replaced by its Typst form; the rest is copied. A @[[@
-- without its @]]@ is an error.
filterDocument :: Env -> Text -> Either Text Text
filterDocument env src = do
  els <- parseFiltered (lexFiltered src)
  pure (ppEmbedSpec env els)

data FTok = FBlanks Text | FString Text | FOpen | FClose

lexFiltered :: Text -> [FTok]
lexFiltered t
  | T.null t = []
  | isWs c =
      let (w, rest) = T.span isWs t
       in FBlanks w : lexFiltered rest
  | "[[" `T.isPrefixOf` t =
      let (brackets, rest) = T.span (== '[') t
       in if T.length brackets > 2
            then FString (T.init brackets) : lexFiltered rest
            else FOpen : lexFiltered (T.drop 2 t)
  | "]]" `T.isPrefixOf` t =
      let (brackets, rest) = T.span (== ']') t
       in if T.length brackets > 2
            then FString (T.init brackets) : lexFiltered rest
            else FClose : lexFiltered (T.drop 2 t)
  | c == '[' || c == ']' = FString (T.singleton c) : lexFiltered (T.drop 1 t)
  | otherwise =
      let (s, rest) = T.break (\x -> isWs x || x == '[' || x == ']') t
       in FString s : lexFiltered rest
  where
    c = T.head t
    isWs x = x `elem` (" \t\n\r\x0b\x0c" :: String)

parseFiltered :: [FTok] -> Either Text [EmbedEl]
parseFiltered toks = case toks of
  [] -> Right []
  FBlanks s : rest -> (EmbedString s :) <$> parseFiltered rest
  FString s : rest -> (EmbedString s :) <$> parseFiltered rest
  FClose : _ -> Left "unfiltered document cannot be parsed"
  FOpen : rest ->
    let (inner, after) = break isClose rest
     in case after of
          FClose : more
            | all notOpen inner -> (EmbedInner (T.concat (map tokText inner)) :) <$> parseFiltered more
          _ -> Left "unfiltered document cannot be parsed"
  where
    isClose tok = case tok of FClose -> True; _ -> False
    notOpen tok = case tok of FOpen -> False; _ -> True
    tokText tok = case tok of
      FBlanks s -> s
      FString s -> s
      _ -> ""
