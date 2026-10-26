{-# LANGUAGE OverloadedStrings #-}

-- | The TeX back end, in Ott's two dialects, LaTeX and Typst
-- (@grammar_pp.ml@, @defns.ml@, @system_pp.ml@, @embed_pp.ml@). The two
-- share the structure of the output and differ in its leaves. The LaTeX
-- output defines one command per rule, definition and definition rule,
-- after a preamble of default commands that @tex-preamble@ embeds may
-- redefine; the Typst output defines one function per rule, definition
-- and definition rule, after a runtime of defaults that @typst-preamble@
-- embeds may shadow.
--
-- Ott checks the bounds of dot forms while it prints, and stops at
-- inconsistent ones; here the driver makes those checks before printing
-- ('Haskott.Prover.Bounds.boundsConsistency').
module Haskott.Tex
  ( Dialect (..)
  , TexOptions (..)
  , defaultTexOptions
  , Env
  , makeEnv
  , withSources
  , makeTex
  , quotationParser
  , texDocument
  , ppSymterm
  , renderSymterm
  , filterDocument
  , filteredDocument
  , documentQuotations
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
import Haskott.SourceLoc
import Haskott.Spec hiding (ppSuffix, ppSuffixItem)
import Haskott.Term.Parse
import Haskott.Term.Symterm

-- | Ott's @tex_dialect@.
data Dialect = Latex | Typst
  deriving (Eq, Show)

data TexOptions = TexOptions
  { optDialect :: Dialect
  , optPrefix :: Text
  , optShowMeta :: Bool
  , optShowCategories :: Bool
  , optColour :: Bool
  , optWrap :: Bool
  , optSuppressedCategories :: [Text]
  , optSuppressedNtrs :: [Text]
  , optTexSourceLocations :: Int
  -- ^ @-output_source_locations@: 1 for the rules of the definitions, 2
  -- for the grammar and the embeds too
  }

defaultTexOptions :: Dialect -> TexOptions
defaultTexOptions d = TexOptions d "ott" True False True True [] [] 0

-- | What the printers need from the specification, indexed.
data Env = Env
  { envOpts :: TexOptions
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
  -- ^ the dialect's hom of the first production of the @terminals@ rule
  -- starting with each terminal
  , envParseQuotation :: Text -> Symterm
  -- ^ the parser of @[[ ]]@ quotations, supplied by the driver, which
  -- owns the term parser and the parse policy
  , envSources :: Sources
  -- ^ the sources, for @-output_source_locations@
  }

makeEnv :: TexOptions -> Spec -> (Text -> Symterm) -> Env
makeEnv opts spec quotation =
  Env
    { envParseQuotation = quotation
    , envSources = noSources
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
              [ (tm, lookup (homName (optDialect opts)) (prodHoms p))
              | p <- ruleProds r
              , (Terminal tm : _) <- [prodElements p]
              ]
    }

-- | The environment with the sources the specification was loaded from.
withSources :: Sources -> Env -> Env
withSources sources env = env {envSources = sources}

-- | Ott's @pp_source_location@ as the first line of a construct (after a
-- blank line), when @-output_source_locations@ is at least the level.
sourceLocation :: Env -> Int -> SourceLoc -> Text
sourceLocation env level l
  | optTexSourceLocations (envOpts env) < level = ""
  | typst env = "// " <> ppSourceLoc l <> "\n"
  | otherwise = "% " <> ppSourceLoc l <> "\n"

-- | Everything the output of one dialect needs from a checked
-- specification, when it is the only target: the parse policy (several
-- parses of a term are accepted when they print the same, unless picky),
-- the term parser, the processed definitions with their diagnostics, and
-- the environment whose quotation parser follows the same policy.
makeTex :: TexOptions -> Bool -> Spec -> (Env, ParsePolicy, TermParser, Processed, [Diagnostic])
makeTex opts picky spec =
  let tp = makeTermParser spec
      env = makeEnv opts spec (quotationParser policy tp)
      -- Ott compares the parses of a term under its TeX and prover modes
      -- only, so a Typst target alone takes the first parse
      policy
        | picky = Picky
        | optDialect opts == Latex = FirstIfSame [renderSymterm env]
        | otherwise = FirstIfSame []
      (processed, diags) = processDefns policy tp spec
   in (env, policy, tp, processed, diags)

-- | The parser of @[[ ]]@ quotations under a policy: a quotation that
-- does not parse, or has several parses the policy rejects, is
-- uninterpreted.
quotationParser :: ParsePolicy -> TermParser -> Text -> Symterm
quotationParser policy tp s = case justOneParse policy userSyntaxTransform tp "user_syntax" False s of
  Parsed p -> parseTerm p
  NoParses -> StUninterpreted Nothing (noParsesErrorString tp "user_syntax" False s)
  MultipleParses _ -> StUninterpreted Nothing "multiple parses"

------------------------------------------------------------------------
-- Dialect leaves

dialect :: Env -> Dialect
dialect = optDialect . envOpts

typst :: Env -> Bool
typst env = dialect env == Typst

-- | Ott's @hom_name_for_pp_mode@.
homName :: Dialect -> Text
homName d = case d of
  Latex -> "tex"
  Typst -> "typst"

typstString :: Text -> Text
typstString s = "\"" <> T.concatMap esc s <> "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      _ -> T.singleton c

-- | Ott's @pp_tex_escape@.
texEscape :: Text -> Text
texEscape = T.concatMap esc
  where
    esc c = case c of
      '_' -> "\\_"
      '%' -> "\\%"
      '$' -> "\\$"
      '#' -> "\\#"
      '?' -> "\\mbox{?}"
      '^' -> "\\mbox{$\\uparrow$}"
      '{' -> "\\{"
      '}' -> "\\}"
      '&' -> "\\&"
      '\\' -> "\\mbox{$\\backslash{}$}"
      '|' -> "\\mbox{$\\mid$}"
      _ -> T.singleton c

escape :: Env -> Text -> Text
escape env = if typst env then typstString else texEscape

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

-- | A LaTeX math spacing command, or its Typst equivalent.
texSpace :: Env -> Text -> Text
texSpace env s
  | not (typst env) = s
  | otherwise = case s of
      "\\," -> "thin"
      "\\:" -> "med"
      "\\;" -> "thick"
      "\\ " -> "space"
      "\\quad" -> "quad"
      _ -> s

-- | A command applied to arguments, in math.
app :: Env -> Text -> [Text] -> Text
app env c args
  | typst env = c <> "(" <> T.intercalate ", " args <> ")"
  | otherwise = c <> T.concat ["{" <> a <> "}" | a <- args]

sans :: Env -> Text -> Text
sans env s = if typst env then "sans(" <> typstString s <> ")" else "\\textsf{" <> s <> "}"

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

-- | A name with the prefix.
name :: Env -> Text -> Text
name env s = optPrefix (envOpts env) <> s

-- | A command: a name with the backslash LaTeX introduces commands with.
cmd :: Env -> Text -> Text
cmd env s = (if typst env then "" else "\\") <> name env s

-- | Ott's @tex_com@: LaTeX @\\ottcom{...}@, Typst @ottcom[...]@ (markup).
texCom :: Env -> Text -> Text
texCom env s
  | typst env = cmd env "com" <> "[" <> s <> "]"
  | otherwise = cmd env "com" <> "{" <> s <> "}"

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
  _ -> "\\,"

insertSpacing :: Env -> [(Text, Ttc)] -> Text
insertSpacing env es = case es of
  [] -> ""
  [(s, _)] -> s
  (s, c) : rest@((_, c') : _) -> s <> " " <> texSpace env (spacing c c') <> " " <> insertSpacing env rest

------------------------------------------------------------------------
-- Homs

-- | A hom with its references already resolved to strings; a reference
-- past them prints as @UNIMPLEMENTED@, as in Ott.
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
      _ -> error "Haskott.Tex: nontermroot hom contains a reference"

comHom :: [Hom] -> Maybe [HomEl]
comHom = lookup "com"

-- | A comment hom over the nonterminals and metavariables of elements.
ppComEs :: Env -> [Hom] -> [Element] -> Text
ppComEs env homs es = case comHom homs of
  Nothing -> ""
  Just hs ->
    let ss = mapMaybe ppElementForCom es
     in texCom env (T.concat (applyHomSpec env hs (if typst env then map typstComMath ss else ss)))
  where
    ppElementForCom e = case e of
      Nonterm _ n suff -> Just (ppNonterm env [] (n, suff))
      Metavar _ m suff -> Just (ppMetavar env [] (m, suff))
      Terminal _ -> Nothing
      -- Ott's own placeholder for a list form in a comment hom
      ListForm _ -> Just "pp element refactoring in progress"

ppComStrings :: Env -> [Hom] -> [Text] -> Text
ppComStrings env homs ss = case comHom homs of
  Nothing -> ""
  Just hs -> texCom env (T.concat (applyHomSpec env hs (map math ss)))
  where
    math s = if typst env then typstComMath s else "$" <> s <> "$"

------------------------------------------------------------------------
-- Terminals, nonterminals, metavariables, variables

ppTerminal :: Env -> Text -> Text
ppTerminal env tm = case M.lookup tm (envTerminalHom env) of
  Just (Just hom) -> ppHomSpec hom
  _ ->
    let es = escape env tm
     in if isAlpha tm then app env (cmd env "kw") [es] else app env (cmd env "sym") [es]

ppDots :: Env -> Int -> Text
ppDots env n
  | typst env = " dots.h "
  | otherwise = case n of
      0 -> ".."
      1 -> "..."
      _ -> "...."

ppUninterpreted :: Env -> Text -> Text
ppUninterpreted env s
  | typst env = if byteLength s > 1 || isAlpha s then "bold(" <> typstString s <> ")" else typstString s
  | otherwise =
      let es = texEscape s
       in if byteLength es > 1 || isAlpha es then "\\mathbf{" <> es <> "}" else es

ruleOf :: Env -> Text -> Rule
ruleOf env ntr = fromMaybe (error ("Haskott.Tex: no rule " ++ T.unpack ntr)) (M.lookup ntr (envRuleByNtr env))

mvdOf :: Env -> Text -> MetavarDefn
mvdOf env mvr = fromMaybe (error ("Haskott.Tex: no metavar " ++ T.unpack mvr)) (M.lookup mvr (envMvdByMvr env))

ppNonterm :: Env -> Suffix -> (Text, Suffix) -> Text
ppNonterm env sie (ntr, suff) =
  let r = ruleOf env ntr
      hn = homName (dialect env)
      perName = lookup hn (fromMaybe [] (lookup ntr (ruleNames r)))
      perRule = lookup hn (ruleHoms r)
      suffixText = ppSuffix env sie suff
   in case (perName, perRule) of
        (Nothing, Nothing) -> app env (cmd env "nt") [escape env ntr <> suffixText]
        (Just hs, _) -> pseudoHomSpec hs <> suffixText
        (Nothing, Just hs) -> T.concat (applyHomSpec env hs [escape env ntr <> suffixText])

ppMetavar :: Env -> Suffix -> (Text, Suffix) -> Text
ppMetavar env sie (mvr, suff) =
  let md = mvdOf env mvr
      hn = homName (dialect env)
      perName = lookup hn (fromMaybe [] (lookup mvr (mvdNames md)))
      perDecl = lookup hn (mvdHoms md)
      suffixText = ppSuffix env sie suff
   in case (perName, perDecl) of
        (Nothing, Nothing) -> app env (cmd env "mv") [escape env mvr <> suffixText]
        (Just hs, _) -> pseudoHomSpec hs <> suffixText
        (Nothing, Just hs) -> T.concat (applyHomSpec env hs [escape env mvr <> suffixText])

ppMetavarroot :: Env -> Text -> Text
ppMetavarroot env mvr = ppMetavar env [] (mvr, [])

ppNontermroot :: Env -> Text -> Text
ppNontermroot env ntr = ppNonterm env [] (ntr, [])

ppVariable :: Env -> Text -> Text -> Text
ppVariable env mvrp var
  | typst env = case lookup "typstvar" homs of
      Nothing -> "italic(" <> typstString var <> ")"
      Just hs -> T.concat (applyHomSpec env hs [typstString var])
  | otherwise = case lookup "texvar" homs of
      Nothing -> var
      Just hs -> T.concat (applyHomSpec env hs [var])
  where
    homs = mvdHoms (mvdOf env mvrp)

------------------------------------------------------------------------
-- Suffixes

ppSuffix :: Env -> Suffix -> Suffix -> Text
ppSuffix env sie suff =
  let subscript = filter isSub suff
      nosubscript = filter (== SiPunct "'") suff
   in T.concat (map (ppSuffixItem env sie True) nosubscript)
        <> ( if null subscript
               then ""
               else
                 if typst env
                   then "_(" <> T.intercalate " thin " (map (ppSuffixItem env sie True) subscript) <> ")"
                   else "_{" <> T.intercalate "\\," (map (ppSuffixItem env sie True) subscript) <> "}"
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
ppSuffixItem env sie nosub si
  | typst env = case si of
      SiNum s -> if nosub then s else "_(" <> s <> ")"
      SiPunct s -> s
      SiVar s n -> let v = ppSuffixvar env (s, n) in if nosub then v else "_(" <> v <> ")"
      SiIndex i -> ppSuffixItem env sie nosub (nthSie sie i)
      SiIndexShift i k -> ppSuffixItem env sie nosub (shiftedSieItem sie i k)
      SiIndexed s inner ->
        let s' = ppSuffixvar env (s, 0) <> "_(" <> ppSuffixItem env sie True inner <> ")"
         in if nosub then s' else "_(" <> s' <> ")"
  | otherwise = case si of
      SiNum s -> sub <> "{\\mathrm{" <> s <> "}}"
      SiPunct s -> s
      SiVar s n -> sub <> ppSuffixvar env (s, n)
      SiIndex i -> ppSuffixItem env sie nosub (nthSie sie i)
      SiIndexShift i k -> ppSuffixItem env sie nosub (shiftedSieItem sie i k)
      SiIndexed s inner -> sub <> "{" <> ppSuffixvar env (s, 0) <> "_{" <> ppSuffixItem env sie True inner <> "}}"
  where
    sub = if nosub then "" else "_"

-- | The item a de Bruijn index stands for; Ott prints @999@ for an index
-- with no enclosing list form.
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

-- | Ott's @pp_tex_suffixvar@: the metavariable's name is not escaped in
-- LaTeX.
ppSuffixvar :: Env -> (Text, Int) -> Text
ppSuffixvar env (s, n) =
  let md = mvdOf env s
      hso = lookup (homName (dialect env)) (fromMaybe [] (lookup s (mvdNames md)))
      ppMvr = case hso of
        Nothing -> if typst env then typstString s else s
        Just hs -> pseudoHomSpec hs
   in if typst env
        then app env (cmd env "mv") [ppMvr] <> offsetText n
        else
          if n == 0
            then cmd env "mv" <> "{" <> ppMvr <> "}"
            else "{" <> cmd env "mv" <> "{" <> ppMvr <> "}" <> offsetText n <> "}"

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
  StUninterpreted _ s
    | typst env ->
        let s' = "mono(" <> typstString ("<<" <> s <> ">>") <> ")"
         in if colour then "#text(fill: red, $" <> s' <> "$)" else s'
    | otherwise ->
        "\\texttt{"
          <> (if colour then "\\textcolor{red}{" else "")
          <> "<<" <> texEscape s <> ">>"
          <> (if colour then "}" else "")
          <> "}"
  where
    colour = optColour (envOpts env)

ppFancyFormula :: Env -> Suffix -> Text -> [Ste] -> Text
ppFancyFormula env sie embedding es =
  let sts = [st | SteSt st <- es]
      pieces = T.splitOn "-ARG-" embedding
      ppString s = if typst env then "mono(" <> typstString s <> ")" else "\\texttt{" <> texEscape s <> "}"
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
        Just (_, pps) -> fromMaybe (error ("Haskott.Tex: production " ++ T.unpack pn ++ " not found in the promotion of " ++ T.unpack ntr)) (M.lookup pn pps)
        Nothing -> pn
   in fromMaybe (error ("Haskott.Tex: no production " ++ T.unpack pn')) (M.lookup pn' (envProdByName env))

ppNodeBody :: Env -> Suffix -> Text -> Text -> [Ste] -> Text
ppNodeBody env sie ntr pn es =
  let (_, p) = promotedProd env ntr pn
      prodEs = prodElements p
   in case lookup (homName (dialect env)) (prodHoms p) of
        Just hs ->
          let ppEs = map fst (ppElements env sie False prodEs es)
           in " " <> T.intercalate " " (applyHomSpec env hs ppEs) <> " "
        Nothing ->
          if pn == "formula_dots"
            then T.intercalate (" " <> texSpace env "\\quad" <> " ") (map fst (ppElements env sie True prodEs es))
            else insertSpacing env (ppElements env sie True prodEs es)

-- | The elements of a node against the elements of its production.
ppElements :: Env -> Suffix -> Bool -> [Element] -> [Ste] -> [(Text, Ttc)]
ppElements env sie includeTerminals = go
  where
    go prodEs es = case (prodEs, es) of
      ([], []) -> []
      (Terminal tm : pes, _) ->
        if includeTerminals then (ppTerminal env tm, classifyTerminal tm) : go pes es else go pes es
      (_, SteSt (StUninterpreted _ s) : es') -> (ppUninterpreted env s, classifyTerminal s) : go prodEs es'
      (Nonterm {} : pes, SteSt (StNonterm _ nt) : es') -> (ppNonterm env sie nt, TtcNt) : go pes es'
      (Nonterm {} : pes, SteSt (StNontermSub _ _ nt) : es') -> (ppNonterm env sie nt, TtcNt) : go pes es'
      (Nonterm {} : pes, SteSt (StNode ntr pn es'') : es') -> (ppNodeBody env sie ntr pn es'', TtcNt) : go pes es'
      (Metavar {} : pes, SteMetavar _ mv : es') -> (ppMetavar env sie mv, TtcNt) : go pes es'
      (Metavar {} : pes, SteVar mvrp var : es') -> (ppVariable env mvrp var, TtcNt) : go pes es'
      (ListForm lb : pes, SteList stlis : es') ->
        ppListItems env sie (lbSeparator lb) (lbElements lb) stlis ++ go pes es'
      _ -> error ("Haskott.Tex: inconsistent structure in " ++ show (map ppPlainSte es))
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
        [] -> [(texSpace env "\\,", TtcSpace)]
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
          ++ [(ppDots env n, TtcDots)]
          ++ sep
          ++ ppElements env (resolveSuffixItem sie upper : sie) True prodEs es
  BoundComp v ->
    [(app env (cmd env "comp") [body v, ppMetavarroot env v], TtcComp)]
  BoundCompU v u ->
    [(app env (cmd env "compu") [body v, ppMetavarroot env v, ppSuffixItem env [] True u], TtcComp)]
  BoundCompLU v l u n ->
    [(app env (cmd env "complu") [body v, ppMetavarroot env v, ppSuffixItem env [] True l, ppDots env n, ppSuffixItem env [] True u], TtcComp)]
  where
    body v = insertSpacing env (ppElements env (SiVar v 0 : sie) True prodEs es)

------------------------------------------------------------------------
-- Binding specifications

ppBindspec :: Env -> Bindspec -> Text
ppBindspec env bs = case bs of
  Bind mse nt _ ->
    let sp = if typst env then " thick " else "\\; "
     in sans env "bind" <> sp <> ppMse env mse <> sp <> sans env "in" <> sp <> ppNonterm env [] nt
  AuxFnDef f mse _ -> ppAuxfn env f <> "=" <> ppMse env mse
  NamesEqual m m' _ -> names m <> thin <> "=" <> thin <> names m'
  NamesDistinct m m' _ -> names m <> thin <> hash <> thin <> names m'
  AllNamesDistinct m _ -> sans env "distinctnames" <> "(" <> ppMse env m <> ")"
  where
    names m = sans env "names" <> "(" <> ppMse env m <> ")"
    thin = if typst env then " thin " else "\\,"
    hash = if typst env then "\"#\"" else "\\#"

ppAuxfn :: Env -> Text -> Text
ppAuxfn env f
  | typst env = "upright(" <> typstString f <> ")"
  | otherwise = "\\textrm{" <> texEscape f <> "}"

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
  Aux f nt -> ppAuxfn env f <> "(" <> ppNonterm env [] nt <> ")"
  AuxList f nt@(ntr, _) b ->
    let r = ruleOf env ntr
        ntlist = T.concat (map fst (ppListBody env [] Nothing [Nonterm (ruleName r) ntr []] b [SteSt (StNonterm (ruleName r) nt)]))
     in ppAuxfn env f <> "(" <> ntlist <> ")"
  Union m m' -> ppMse env m <> " " <> (if typst env then "union " else "\\cup ") <> " " <> ppMse env m'
  Empty -> if typst env then "\"{}\"" else "\\{\\}"

------------------------------------------------------------------------
-- The grammar

canonicalNode :: Text -> Prod -> Symterm
canonicalNode ntr p = StNode ntr (prodName p) (canonicalElements (prodElements p))

ppMetavardefn :: Env -> MetavarDefn -> Text
ppMetavardefn env md =
  let com = ppComStrings env (mvdHoms md) [ppMetavar env [] (mvdName md, [])]
      roots = [ppMetavarroot env mvr | (mvr, _) <- mvdNames md]
   in if typst env
        then name env "metavarline" <> "(" <> typstMath (T.intercalate " , " roots) <> ", " <> (if T.null com then "[]" else com) <> "),"
        else " $ " <> T.intercalate " ,\\, " roots <> " $ & " <> com <> " \\\\"

ppProd :: Env -> Text -> Prod -> Maybe Text
ppProd env rnn p =
  let suppressed = any (`elem` optSuppressedCategories opts) (Set.toList (prodCategories p))
   in if suppressed || (not (optShowMeta opts) && prodMeta p && not (prodSugar p))
        then Nothing
        else Just (if typst env then typstProd else latexProd)
  where
    opts = envOpts env
    pp = ppSymterm env [] (canonicalNode rnn p)
    com = ppComEs env (prodHoms p) (prodElements p)
    bindspecs = map (ppBindspec env) (prodBindspecs p)
    -- StringSet.fold conses the categories in increasing order
    categories = reverse (sortOn id [c | c <- Set.toList (prodCategories p), c /= "M", c /= "S"])
    texlong = any ((== "texlong") . fst) (prodHoms p)
    typstProd =
      let empty = "[]"
          com' = if T.null com then empty else com
          (meta, bindspec, remaining)
            | prodSugar p = (typstMath (sans env "S"), empty, [])
            | prodMeta p = (typstMath (sans env "M"), empty, [])
            | otherwise = case bindspecs of
                [] -> (empty, empty, [])
                hd : tl -> (empty, typstMath hd, tl)
          cats =
            if optShowCategories opts && not (null categories)
              then typstMath (sans env ("[" <> T.unwords categories <> "]"))
              else empty
          line n args = n <> "(" <> T.intercalate ", " args <> ")"
          bar = typstMath "|"
       in T.intercalate ",\n" $
            ( if not texlong
                then [line (name env "prodline") [bar, typstMath pp, meta, bindspec, cats, com']]
                else
                  [ line (name env "longprodline") [bar, typstMath pp]
                  , line (name env "prodline") [empty, empty, meta, bindspec, cats, com']
                  ]
            )
              ++ [line (name env "bindspecprodline") [empty, empty, empty, typstMath bs, empty, empty] | bs <- remaining]
    latexProd =
      let (metaOrBindspec, remaining)
            | prodSugar p = (" {\\textsf{S}}{}", [])
            | prodMeta p = (" {\\textsf{M}}{}", [])
            | otherwise = case bindspecs of
                [] -> ("{}{}", [])
                hd : tl -> ("{}{" <> hd <> "}", tl)
          cats
            | optShowCategories opts = if null categories then "{}" else "{\\textsf{[" <> T.unwords categories <> "]}}"
            | otherwise = "{}"
       in T.intercalate (cmd env "prodnewline" <> "\n") $
            ( if not texlong
                then [T.concat [cmd env "prodline", "{|}", "{", pp, "}", metaOrBindspec, cats, "{", com, "}"]]
                else
                  [ T.concat [cmd env "longprodline", "{|}", "{", pp, "}"]
                  , T.concat [cmd env "prodline", "{}", "{}", metaOrBindspec, cats, "{", com, "}"]
                  ]
            )
              ++ [cmd env "bindspecprodline" <> "{}{}{}{" <> bs <> "}{}{}" | bs <- remaining]

ruleSuppressed :: Env -> Rule -> Bool
ruleSuppressed env r =
  ruleName r `elem` optSuppressedNtrs (envOpts env) || (not (optShowMeta (envOpts env)) && ruleSemiMeta r)

ppRule :: Env -> Rule -> Maybe Text
ppRule env r = (located <>) <$> ppRuleBody env r
  where
    located = case sourceLocation env 2 (ruleLoc (envSources env) r) of
      "" -> ""
      l -> "\n" <> l

ppRuleBody :: Env -> Rule -> Maybe Text
ppRuleBody env r
  | ruleSuppressed env r = Nothing
  | typst env =
      let com' = if T.null com then "[]" else com
          headLine = name env "rulehead" <> "(" <> typstMath (T.intercalate " , " names) <> ", $::=$, " <> com' <> ")"
          body = "#let " <> cmd env (commandEscape (ruleName r)) <> " = (\n"
            <> T.intercalate ",\n" (headLine : prods)
            <> ",\n)\n"
       in Just (replaceFirst (name env "prodline" <> "(") (name env "firstprodline" <> "(") body)
  | otherwise =
      let headLine = cmd env "rulehead" <> "{" <> T.intercalate "  ,\\ " names <> "}{::=}{" <> com <> "}"
          body = "\\newcommand{" <> cmd env (commandEscape (ruleName r)) <> "}{\n"
            <> T.intercalate (cmd env "prodnewline" <> "\n") (headLine : prods)
            <> "}\n"
       in Just (replaceFirst (cmd env "prodline") (cmd env "firstprodline") body)
  where
    com = ppComStrings env (ruleHoms r) [ppNonterm env [] (ruleName r, [])]
    names = removeDuplicatesLast [ppNontermroot env ntr | (ntr, _) <- ruleNames r]
    prods = mapMaybe (ppProd env (ruleName r)) (ruleProds r)

replaceFirst :: Text -> Text -> Text -> Text
replaceFirst old new s = case T.breakOn old s of
  (before, rest)
    | T.null rest -> s
    | otherwise -> before <> new <> T.drop (T.length old) rest

ppRuleList :: Env -> [Rule] -> Text
ppRuleList env rs
  | typst env =
      rules
        <> "#let " <> cmd env "grammar" <> " = " <> name env "grammartabular" <> "(\n"
        <> T.intercalate (", " <> cmd env "interrule" <> ",\n") shown
        <> (if null rs then "" else ", " <> cmd env "afterlastrule")
        <> "\n)\n\n"
  | otherwise =
      rules
        <> "\\newcommand{" <> cmd env "grammar" <> "}{" <> cmd env "grammartabular{\n"
        <> T.intercalate (cmd env "interrule" <> "\n") shown
        <> (if null rs then "" else cmd env "afterlastrule")
        <> "\n}}\n\n"
  where
    rules = T.intercalate "\n" (mapMaybe (ppRule env) rs) <> "\n"
    shown = [cmd env (commandEscape (ruleName r)) | r <- rs, not (ruleSuppressed env r)]

ppSyntaxdefn :: Env -> Text
ppSyntaxdefn env
  | typst env =
      "#let " <> cmd env "metavars" <> " = " <> name env "metavartabular" <> "(\n"
        <> mvds
        <> "\n)\n\n"
        <> ppRuleList env (specRules (envSpec env))
  | otherwise =
      "\\newcommand{" <> cmd env "metavars" <> "}{\n" <> cmd env "metavartabular{\n"
        <> mvds
        <> "\n}}\n\n"
        <> ppRuleList env (specRules (envSpec env))
  where
    mvds = T.intercalate "\n" (map (ppMetavardefn env) (specMetavars (envSpec env)))

------------------------------------------------------------------------
-- Definitions

ppDrule :: Env -> Drule -> Text
ppDrule env dr = located <> ppDruleBody env dr
  where
    located = case sourceLocation env 1 (druleLoc (envSources env) (druleRange dr)) of
      "" -> ""
      l -> "\n" <> l

ppDruleBody :: Env -> Drule -> Text
ppDruleBody env dr
  | typst env =
      let com = case comHom (druleHoms dr) of
            Nothing -> "[]"
            Just hs -> "[" <> T.concat (applyHomSpec env hs []) <> "]"
       in "#let " <> cmd env ("drule" <> commandEscape (druleName dr)) <> "(..args) = " <> cmd env "drule" <> "(..args,\n  premises: (\n"
            <> T.concat ["    " <> cmd env "premise" <> "(" <> typstMath p <> "),\n" | p <- premises]
            <> "  ),\n  conclusion: " <> typstMath conclusion
            <> ",\n  name: " <> cmd env "drulename" <> "(" <> typstString (druleName dr) <> ")"
            <> ",\n  com: " <> com <> ")\n"
  | otherwise =
      let com = case comHom (druleHoms dr) of
            Nothing -> ""
            Just hs -> "\\text{" <> T.concat (applyHomSpec env hs []) <> "}"
       in "\\newcommand{" <> cmd env ("drule" <> commandEscape (druleName dr)) <> "}[1]{" <> cmd env "drule" <> "[#1]{%\n"
            <> T.concat [cmd env "premise" <> "{" <> p <> "}%\n" | p <- premises]
            <> "}{\n"
            <> conclusion
            <> "}{%\n{" <> cmd env "drulename" <> "{" <> texEscape (druleName dr) <> "}}{" <> com <> "}%\n}}\n"
  where
    premises = [ppSymterm env [] p | (_, p) <- drulePremises dr]
    conclusion = ppSymterm env [] (druleConclusion dr)

ppDefn :: Env -> ProcessedClass -> ProcessedDefn -> Text
ppDefn env pc d
  | typst env =
      let com' = if T.null com then "[]" else com
          use item = case item of
            ItemRule dr ->
              "    " <> cmd env "usedrule" <> "(" <> cmd env ("drule" <> commandEscape (druleName dr)) <> "()"
                <> ( if optShowCategories (envOpts env) && not (Set.null (druleCategories dr))
                       then ", categories: (" <> T.intercalate ", " (map typstString (Set.toList (druleCategories dr))) <> ",)"
                       else ""
                   )
                <> "),\n"
            ItemComment es _ -> "    " <> name env "defncom" <> "[" <> ppEmbedSpec env es <> "],\n"
       in "// defn " <> pdName d <> "\n"
            <> T.intercalate "\n" (map (ppDrule env) rules)
            <> "\n#let " <> defnName <> "(..args) = " <> name env "defnblock" <> "(..args,\n  judgement: "
            <> typstMath (ppSymterm env [] (pdForm d))
            <> ",\n  com: " <> com' <> ",\n  rules: (\n"
            <> T.concat (map use (pdRules d))
            <> "  ))\n\n"
  | otherwise =
      let use item = case item of
            ItemRule dr ->
              cmd env "usedrule" <> "{" <> cmd env ("drule" <> commandEscape (druleName dr)) <> "{}"
                <> ( if optShowCategories (envOpts env) && not (Set.null (druleCategories dr))
                       then "\\quad\\textsf{[" <> T.concat [c <> " " | c <- Set.toList (druleCategories dr)] <> "]}"
                       else ""
                   )
                <> "}\n"
            ItemComment es _ -> ppEmbedSpec env es
       in "%% defn " <> pdName d <> "\n"
            <> T.intercalate "\n\n" (map (ppDrule env) rules)
            <> "\n\\newcommand{" <> defnName <> "}[1]{\\begin{" <> name env "defnblock" <> "}[#1]{$"
            <> ppSymterm env [] (pdForm d)
            <> "$}{" <> com <> "}\n"
            <> T.concat (map use (pdRules d))
            <> "\\end{" <> name env "defnblock" <> "}}\n\n"
  where
    prodName' = pcWrapper pc <> pdName d
    (_, p) = fromMaybe (error ("Haskott.Tex: no production " ++ T.unpack prodName')) (M.lookup prodName' (envProdByName env))
    com = ppComEs env (pdHoms d) (prodElements p)
    rules = [dr | ItemRule dr <- pdRules d]
    defnName = cmd env ("defn" <> commandEscape prodName')

ppDefnClass :: Env -> ProcessedClass -> Text
ppDefnClass env pc
  | typst env =
      "// defns " <> pcName pc <> "\n"
        <> T.concat (map (ppDefn env pc) (pcDefns pc))
        <> "\n#let " <> className <> " = {\n"
        <> T.concat ["  " <> defnName d <> "()\n" | d <- pcDefns pc]
        <> "}\n\n"
  | otherwise =
      "% defns " <> pcName pc <> "\n"
        <> T.concat (map (ppDefn env pc) (pcDefns pc))
        <> "\n\\newcommand{" <> className <> "}{\n"
        <> T.concat [defnName d <> "{}" | d <- pcDefns pc]
        <> "}\n\n"
  where
    className = cmd env ("defns" <> commandEscape (pcName pc))
    defnName d = cmd env ("defn" <> commandEscape (pcWrapper pc <> pdName d))

ppFunclause :: Env -> Funclause -> Text
ppFunclause env fc
  | typst env = "    " <> cmd env "funclause" <> "(" <> typstMath lhs <> ", " <> typstMath rhs <> "),\n"
  | otherwise = cmd env "funclause" <> "{" <> lhs <> "}{" <> rhs <> "}%\n"
  where
    lhs = ppSymterm env [] (fcLhs fc)
    rhs = ppSymterm env [] (fcRhs fc)

ppFundefn :: Env -> ProcessedFun -> Text
ppFundefn env pf
  | typst env =
      "// fundefn " <> pfName pf <> "\n"
        <> "\n#let " <> funName <> "(..args) = " <> name env "fundefnblock" <> "(..args,\n  form: "
        <> typstMath form
        <> ",\n  com: " <> (if T.null com then "[]" else com) <> ",\n  clauses: (\n"
        <> clauses
        <> "  ))\n\n"
  | otherwise =
      "% fundefn " <> pfName pf <> "\n"
        <> "\n\\newcommand{" <> funName <> "}[1]{\\begin{" <> name env "fundefnblock" <> "}[#1]{$"
        <> form
        <> "$}{" <> com <> "}\n"
        <> clauses
        <> "\\end{" <> name env "fundefnblock" <> "}}\n\n"
  where
    com = ppComEs env (pfHoms pf) (pfElements pf)
    funName = cmd env ("fundefn" <> commandEscape (pfName pf))
    form = ppSymterm env [] (pfForm pf)
    clauses = T.concat (map (ppFunclause env) (pfClauses pf))

ppFunClass :: Env -> ProcessedFunClass -> Text
ppFunClass env pfc
  | typst env =
      "// fundefns " <> pfcName pfc <> "\n"
        <> T.intercalate "\n" (map (ppFundefn env) (pfcFuns pfc))
        <> "\n"
        <> "#let " <> className <> " = {\n"
        <> T.concat ["  " <> funName pf <> "()\n" | pf <- pfcFuns pfc]
        <> "}\n\n"
  | otherwise =
      "% fundefns " <> pfcName pfc <> "\n"
        <> T.intercalate "\n" (map (ppFundefn env) (pfcFuns pfc))
        <> "\n"
        <> "\\newcommand{" <> className <> "}{\n"
        <> T.intercalate "\n" [funName pf <> "{}" | pf <- pfcFuns pfc]
        <> "}\n\n"
  where
    className = cmd env ("fundefns" <> commandEscape (pfcName pfc))
    funName pf = cmd env ("fundefn" <> commandEscape (pfName pf))

ppDefnss :: Env -> Processed -> Text
ppDefnss env processed
  | typst env =
      "// defnss\n"
        <> T.concat (map item (processedItems processed))
        <> "#let " <> cmd env "defnss" <> " = {\n"
        <> T.concat ["  " <> entry it <> "\n" | it <- processedItems processed]
        <> "}\n\n"
  | otherwise =
      "% defnss\n"
        <> T.concat (map item (processedItems processed))
        <> "\\newcommand{" <> cmd env "defnss" <> "}{\n"
        <> T.concat [entry it <> "\n" | it <- processedItems processed]
        <> "}\n\n"
  where
    item it = case it of
      PReln pc -> ppDefnClass env pc
      PFuns pfc -> ppFunClass env pfc
    entry it = case it of
      PReln pc -> cmd env ("defns" <> commandEscape (pcName pc))
      PFuns pfc -> cmd env ("fundefns" <> commandEscape (pfcName pfc))

------------------------------------------------------------------------
-- Embeds and quotations

-- | The quotations of an embed are terms of user syntax, read by the
-- driver's quotation parser; one that does not parse, or whose parses the
-- policy does not resolve, prints as uninterpreted, as in Ott. As in Ott,
-- the quotation @[[TEX_NAME_PREFIX]]@ is the command prefix, and a Typst
-- quotation is trimmed.
ppEmbedSpec :: Env -> [EmbedEl] -> Text
ppEmbedSpec env = T.concat . map el
  where
    el e = case e of
      EmbedString s -> s
      EmbedInner "TEX_NAME_PREFIX" -> optPrefix (envOpts env)
      EmbedInner s ->
        let pp = ppSymterm env [] (envParseQuotation env s)
         in if typst env then ocamlTrim pp else pp

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
  StUninterpreted _ _ -> True
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

-- | The Typst runtime: one definition per LaTeX @\\newcommand@ of the TeX
-- preamble.
typstRuntime :: Text -> Text
typstRuntime p =
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

-- | The LaTeX preamble of default commands.
latexPreamble :: Env -> Text
latexPreamble env =
  T.concat
    [ "\\newcommand{" <> c "drule" <> "}[4][]{{\\displaystyle\\frac{\\begin{array}{l}#2\\end{array}}{#3}\\quad" <> c "drulename" <> "{#4}}}\n"
    , "\\newcommand{" <> c "usedrule" <> "}[1]{\\[#1\\]}\n"
    , "\\newcommand{" <> c "premise" <> "}[1]{ #1 \\\\}\n"
    , "\\newenvironment{" <> n "defnblock" <> "}[3][]{ \\framebox{\\mbox{#2}} \\quad #3 \\\\[0pt]}{}\n"
    , "\\newenvironment{" <> n "fundefnblock" <> "}[3][]{ \\framebox{\\mbox{#2}} \\quad #3 \\\\[0pt]\\begin{displaymath}\\begin{array}{l}}{\\end{array}\\end{displaymath}}\n"
    , "\\newcommand{" <> c "funclause" <> "}[2]{ #1 \\equiv #2 \\\\}\n"
    , "\\newcommand{" <> c "nt" <> "}[1]{\\mathit{#1}}\n"
    , "\\newcommand{" <> c "mv" <> "}[1]{\\mathit{#1}}\n"
    , "\\newcommand{" <> c "kw" <> "}[1]{\\mathbf{#1}}\n"
    , "\\newcommand{" <> c "sym" <> "}[1]{#1}\n"
    , "\\newcommand{" <> c "com" <> "}[1]{\\text{#1}}\n"
    , "\\newcommand{" <> c "drulename" <> "}[1]{\\textsc{#1}}\n"
    , "\\newcommand{" <> c "complu" <> "}[5]{\\overline{#1}^{\\,#2\\in #3 #4 #5}}\n"
    , "\\newcommand{" <> c "compu" <> "}[3]{\\overline{#1}^{\\,#2<#3}}\n"
    , "\\newcommand{" <> c "comp" <> "}[2]{\\overline{#1}^{\\,#2}}\n"
    , "\\newcommand{" <> c "grammartabular" <> "}[1]{\\begin{supertabular}{llcllllll}#1\\end{supertabular}}\n"
    , "\\newcommand{" <> c "metavartabular" <> "}[1]{\\begin{supertabular}{ll}#1\\end{supertabular}}\n"
    , "\\newcommand{" <> c "rulehead" <> "}[3]{$#1$ & & $#2$ & & & \\multicolumn{2}{l}{#3}}\n"
    , "\\newcommand{" <> c "prodline" <> "}[6]{& & $#1$ & $#2$ & $#3 #4$ & $#5$ & $#6$}\n"
    , "\\newcommand{" <> c "firstprodline" <> "}[6]{" <> c "prodline" <> "{#1}{#2}{#3}{#4}{#5}{#6}}\n"
    , "\\newcommand{" <> c "longprodline" <> "}[2]{& & $#1$ & \\multicolumn{4}{l}{$#2$}}\n"
    , "\\newcommand{" <> c "firstlongprodline" <> "}[2]{" <> c "longprodline" <> "{#1}{#2}}\n"
    , "\\newcommand{" <> c "bindspecprodline" <> "}[6]{" <> c "prodline" <> "{#1}{#2}{#3}{#4}{#5}{#6}}\n"
    , "\\newcommand{" <> c "prodnewline" <> "}{\\\\}\n"
    , "\\newcommand{" <> c "interrule" <> "}{\\\\[5.0mm]}\n"
    , "\\newcommand{" <> c "afterlastrule" <> "}{\\\\}\n"
    ]
  where
    c = cmd env
    n = name env

-- | The output file for a specification: the header names the sources as
-- Ott prints them.
texDocument :: Env -> Text -> Processed -> Text
texDocument env sources processed
  | typst env =
      "// generated by Ott 0.34 from: " <> sources <> "\n\n"
        <> typstRuntime p
        <> preambleEmbedsFor "typst"
        <> ppSyntaxdefn env
        <> ppDefnss env processed
        <> "#let " <> p <> "all = [\n#" <> p <> "metavars\n\n#" <> p <> "grammar\n\n"
        <> laterEmbedsFor "typst"
        <> "\n#" <> p <> "defnss\n]\n\n"
        <> ( if optWrap (envOpts env)
               then "#" <> p <> "all\n\n#raw(block: true, " <> typstString (countsString processed) <> ")\n"
               else ""
           )
  | otherwise =
      "% generated by Ott 0.34 from: " <> sources <> "\n"
        <> ( if not (optWrap (envOpts env))
               then ""
               else case named "tex-wrap-pre" of
                 [] ->
                   "\\documentclass[11pt]{article}\n\\usepackage{amsmath,amssymb}\n\\usepackage{supertabular}\n"
                     <> "\\usepackage{geometry}\n\\usepackage{ifthen}\n\\usepackage{alltt}%hack\n"
                     <> "\\geometry{a4paper,dvips,twoside,left=22.5mm,right=22.5mm,top=20mm,bottom=30mm}\n"
                     <> (if optColour (envOpts env) then "\\usepackage{color}\n" else "")
                 pre -> T.concat [embed e | e <- pre]
           )
        <> latexPreamble env
        <> preambleEmbedsFor "tex"
        <> ppSyntaxdefn env
        <> ppDefnss env processed
        <> "\\newcommand{" <> cmd env "all" <> "}{" <> cmd env "metavars" <> "\\\\[0pt]\n" <> cmd env "grammar" <> "\\\\[5.0mm]\n"
        <> laterEmbedsFor "tex"
        <> cmd env "defnss" <> "}\n\n"
        <> ( if not (optWrap (envOpts env))
               then ""
               else case named "tex-wrap-post" of
                 [] -> "\\begin{document}\n" <> cmd env "all" <> "\n\n\\begin{verbatim}\n" <> countsString processed <> "\\end{verbatim}\n\\end{document}\n"
                 post -> T.concat [embed e | e <- post]
           )
  where
    p = optPrefix (envOpts env)
    named which = [e | e <- specEmbeds (envSpec env), embedName e == which]
    located e = sourceLocation env 2 (itemLoc (envSources env) (embedRange e))
    embed e = located e <> ppEmbedSpec env (embedSpec e) <> "\n"
    -- Ott's passes over the preamble embeds, then over all of them: each
    -- prints its location, and the dialect's its body
    preambleEmbedsFor h =
      T.concat [if embedName e == h then embed e else located e | e <- preambleEmbeds (envSpec env)]
    laterEmbedsFor h = T.concat [if embedName e == h then embed e else located e | e <- specEmbeds (envSpec env)]

------------------------------------------------------------------------
-- The document filter

-- | Ott's @-tex_filter@ and @-typst_filter@: every @[[ ... ]]@ of a
-- document is parsed as user syntax and replaced by its form in the
-- dialect; the rest is copied. A @[[@ without its @]]@ is an error.
filterDocument :: Env -> Text -> Either Text Text
filterDocument env src = do
  els <- parseFiltered (map fst (lexFiltered src))
  pure (ppEmbedSpec env els)

-- | A document as Ott's @filter@ lexer sees it: text and @[[ ]]@
-- quotations.
filteredDocument :: Text -> Either Text [EmbedEl]
filteredDocument src = parseFiltered (map fst (lexFiltered src))

-- | The @[[ ... ]]@ quotations of a document, as the filter sees them:
-- the byte offset of each quotation's text, the text as written, and the
-- text the filter parses (they differ only where @[[[@ or @]]]@, the
-- escapes for brackets, occur inside a quotation).
documentQuotations :: Text -> Either Text [(Int, Text, Text)]
documentQuotations src = go 0 (lexFiltered src)
  where
    go off toks = case toks of
      [] -> Right []
      (FOpen, n) : rest ->
        let (inner, after) = break (isClose . fst) rest
            innerLen = sum (map snd inner)
            start = off + n
         in case after of
              (FClose, m) : more
                | all (notOpen . fst) inner ->
                    let written = TE.decodeUtf8 (B.take innerLen (B.drop start bytes))
                        parsed = T.concat (map (tokText . fst) inner)
                     in ((start, written, parsed) :) <$> go (start + innerLen + m) more
              _ -> Left "unfiltered document cannot be parsed"
      (FClose, _) : _ -> Left "unfiltered document cannot be parsed"
      (_, n) : rest -> go (off + n) rest
    bytes = TE.encodeUtf8 src

data FTok = FBlanks Text | FString Text | FOpen | FClose

isClose, notOpen :: FTok -> Bool
isClose tok = case tok of FClose -> True; _ -> False
notOpen tok = case tok of FOpen -> False; _ -> True

tokText :: FTok -> Text
tokText tok = case tok of
  FBlanks s -> s
  FString s -> s
  _ -> ""

-- | Ott's @filter@ lexer mode, with the number of bytes each token
-- consumes.
lexFiltered :: Text -> [(FTok, Int)]
lexFiltered t
  | T.null t = []
  | isWs c =
      let (w, rest) = T.span isWs t
       in (FBlanks w, byteLength w) : lexFiltered rest
  | "[[" `T.isPrefixOf` t =
      let (brackets, rest) = T.span (== '[') t
       in if T.length brackets > 2
            then (FString (T.init brackets), T.length brackets) : lexFiltered rest
            else (FOpen, 2) : lexFiltered (T.drop 2 t)
  | "]]" `T.isPrefixOf` t =
      let (brackets, rest) = T.span (== ']') t
       in if T.length brackets > 2
            then (FString (T.init brackets), T.length brackets) : lexFiltered rest
            else (FClose, 2) : lexFiltered (T.drop 2 t)
  | c == '[' || c == ']' = (FString (T.singleton c), 1) : lexFiltered (T.drop 1 t)
  | otherwise =
      let (s, rest) = T.break (\x -> isWs x || x == '[' || x == ']') t
       in (FString s, byteLength s) : lexFiltered rest
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
