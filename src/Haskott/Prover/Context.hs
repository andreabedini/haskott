{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @context_pp.ml@: for each context rule, a function applying a
-- context to a term. For each production of the context's rule, the
-- production is printed in Ott's ASCII form with the hole @__@ replaced
-- by a variable, parsed back as a term of the target rule, and the parse
-- printed for the prover.
module Haskott.Prover.Context
  ( ppContext
  ) where

import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Prover.Bounds
import Haskott.Prover.Dependency
import Haskott.Prover.Pp
import Haskott.Prover.Transform (freshNt)
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

-- | Ott's @pp_context@.
ppContext :: Env -> [Contextrule] -> P Collapsed
ppContext env crs = do
  funcs <- mapM (ppRuleContext env) crs
  pure (collapse env (IntFuncs funcs Nothing))

ppRuleContext :: Env -> Contextrule -> P IntFunc
ppRuleContext env cr = do
  let eRule = ruleOfNtr env (crNtr cr)
      ntsUsed0 = ntsUsedInLhss eRule
      ctx = freshNt ntsUsed0 (crNtr cr, [])
      ctxVar = ppNonterm env ctx
      ntsUsed = ctx : ntsUsed0
      fakeHole = freshNt ntsUsed (crHole cr, [])
      fakeHoleVar = ppNonterm env fakeHole
      ident = "appctx_" <> crNtr cr <> "_" <> crHole cr
      ty = ppNontermrootTy env
  clauses <- mapM (ppProdContext env fakeHole (crTarget cr) eRule) (ruleProds eRule)
  header <- case envTarget env of
    Coq ->
      pure
        ( ident <> " (" <> ctxVar <> ":" <> ty (crNtr cr) <> ") (" <> fakeHoleVar <> ":" <> ty (crHole cr) <> ")"
        , ""
        , " : " <> ty (crTarget cr) <> " :=\n  match " <> ctxVar <> " with\n"
        )
    Isa -> pure (ident <> " :: \"" <> ty (crNtr cr) <> " => " <> ty (crHole cr) <> " => " <> ty (crTarget cr) <> "\"\n", "", "")
    Hol -> pure ("", "", "")
    Lem -> failP "LemTODO: context rules are not supported in the Lem back end"
    Twf -> failP "internal (Twelf): pp_rule_context"
    Caml ->
      pure
        ( ident <> " (" <> ctxVar <> ":" <> ty (crNtr cr) <> ") (" <> fakeHoleVar <> ":" <> ty (crHole cr) <> ")"
        , ""
        , " : " <> ty (crTarget cr) <> " =\n  match " <> ctxVar <> " with\n"
        )
  pure (IntFunc ident [] (crNtr cr) header clauses)

-- | Ott's @pp_prod_context@: the production as a pattern, and the term
-- of the target rule it becomes with the hole filled.
ppProdContext :: Env -> (Text, Suffix) -> Text -> Rule -> Prod -> P (Text, Text, Text)
ppProdContext env hole target r p = do
  let lhsSt = canonicalNode (ruleName r) p
  (de, _) <- bounds [lhsSt]
  lhsPat <- ppSymterm env [] de lhsSt
  let lhs = case envTarget env of
        Coq -> lhsPat
        Caml -> lhsPat
        _ -> lhsPat <> " " <> ppNonterm env hole
  rhs <- contextAppRhs env hole target r p
  pure (prodName p, lhs, rhs)
  where
    bounds sts = either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env sts)

-- | Ott's @context_app_rhs@, which a production of a checked context rule
-- always satisfies.
contextAppRhs :: Env -> (Text, Suffix) -> Text -> Rule -> Prod -> P Text
contextAppRhs env hole target r p = do
  let withHole = asciiSymterm env [] (canonicalNode (ruleName r) p)
      fake = replaceFirst "__" (ppNonterm env hole) withHole
  case envParse env target fake of
    [] -> failP "internal: cannot parse context fake rhs"
    st0 : _ -> do
      let st = if isCaml env then capitalizeProdnames st0 else st0
      (de, _) <- either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env [st])
      ppSymterm env [] de st

replaceFirst :: Text -> Text -> Text -> Text
replaceFirst old new s = case T.breakOn old s of
  (before, rest)
    | T.null rest -> s
    | otherwise -> before <> new <> T.drop (T.length old) rest

capitalizeProdnames :: Symterm -> Symterm
capitalizeProdnames st = case st of
  StNode ntr pn es -> StNode ntr (capitalize pn) (map ste es)
  _ -> st
  where
    ste e = case e of
      SteSt s -> SteSt (capitalizeProdnames s)
      SteList stlis -> SteList (map stli stlis)
      _ -> e
    stli s = case s of
      StliSingle es -> StliSingle (map ste es)
      StliListform b es -> StliListform b (map ste es)

-- | The nonterminals of the canonical terms of a rule's productions
-- (Ott's @nts_used_in_lhss@).
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

------------------------------------------------------------------------
-- Ott's ASCII printing (without colour), of canonical terms

-- | Ott's @quote_ident@.
quoteIdent :: Text -> Text
quoteIdent s
  | s `elem` quoted = "'" <> s <> "'"
  | otherwise = s
  where
    quoted = ["::=", "|", "{{", "}}", "::", "..", "...", "....", "metavar", "grammar", "by", "Defn", "Defns", "<::", "_::", "subrules", "substitutions", "freevars", "embed", "homs", "(+", ""]

asciiSuffixItem :: Suffix -> SuffixItem -> Text
asciiSuffixItem sie si = case si of
  SiNum s -> s
  SiPunct s -> s
  SiVar s n -> s <> offset n
  SiIndex i -> asciiSuffixItem sie (nth i)
  SiIndexShift i k -> asciiSuffixItem sie (shiftItem k (nth i))
  SiIndexed s si' -> s <> asciiSuffixItem sie si'
  where
    nth i = if i >= 0 && i < length sie then sie !! i else SiNum "999"
    offset n
      | n == 0 = ""
      | n > 0 = "+" <> T.pack (show n)
      | otherwise = T.pack (show n)
    shiftItem k x = case x of
      SiVar v o -> SiVar v (o + k)
      _ -> x

asciiSuffix :: Suffix -> Suffix -> Text
asciiSuffix sie = T.concat . map (asciiSuffixItem sie)

asciiNonterm :: Env -> Suffix -> (Text, Suffix) -> Text
asciiNonterm env sie (ntr, suff) =
  let r = ruleOfNtrNonprimary env ntr
      ppNtr = maybe ntr pseudoHomSpec (lookup "ascii" (fromMaybe [] (lookup ntr (ruleNames r))))
   in quoteIdent (ppNtr <> asciiSuffix sie suff)

asciiMetavar :: Env -> Suffix -> (Text, Suffix) -> Text
asciiMetavar env sie (mvr, suff) =
  let md = mvdOfMvrNonprimary env mvr
      ppMvr = maybe mvr pseudoHomSpec (lookup "ascii" (fromMaybe [] (lookup mvr (mvdNames md))))
   in ppMvr <> asciiSuffix sie suff

asciiSymterm :: Env -> Suffix -> Symterm -> Text
asciiSymterm env sie st = case st of
  StNode ntr pn es -> asciiNodeBody env sie ntr pn es
  StNonterm _ nt -> asciiNonterm env sie nt
  StNontermSub _ _ nt -> asciiNonterm env sie nt
  StUninterpreted _ s -> "(*" <> s <> "*)"

asciiNodeBody :: Env -> Suffix -> Text -> Text -> [Ste] -> Text
asciiNodeBody env sie ntr pn es =
  let promoted = case M.lookup ntr (envPromotion env) of
        Just (_, pps) -> fromMaybe pn (M.lookup pn pps)
        Nothing -> pn
      p = prodOfProdname env promoted
   in case lookup "ascii" (prodHoms p) of
        Just hs -> " " <> T.unwords (asciiApplyHom env hs (asciiElements env sie False (prodElements p) es)) <> " "
        Nothing -> T.unwords (asciiElements env sie True (prodElements p) es)

asciiApplyHom :: Env -> [HomEl] -> [Text] -> [Text]
asciiApplyHom _ hs ss = map el hs
  where
    el h = case h of
      HomString s -> s
      HomIndex i -> if i >= 0 && i < length ss then ss !! i else ""
      HomTerminal tm -> quoteIdent tm
      HomLnFreeIndex _ i -> if i >= 0 && i < length ss then ss !! i else ""

asciiElements :: Env -> Suffix -> Bool -> [Element] -> [Ste] -> [Text]
asciiElements env sie includeTerminals = go
  where
    go prodEs es = case (prodEs, es) of
      ([], []) -> []
      (Terminal tm : pes, _) -> if includeTerminals then tm : go pes es else go pes es
      (Nonterm {} : pes, SteSt (StNonterm _ nt) : es') -> asciiNonterm env sie nt : go pes es'
      (Nonterm {} : pes, SteSt (StNontermSub _ _ nt) : es') -> asciiNonterm env sie nt : go pes es'
      (Nonterm {} : pes, SteSt (StNode ntr pn es'') : es') -> asciiNodeBody env sie ntr pn es'' : go pes es'
      (_, SteSt (StUninterpreted _ s) : es') -> ("(*" <> s <> "*)") : go prodEs es'
      (Metavar {} : pes, SteMetavar _ mv : es') -> asciiMetavar env sie mv : go pes es'
      (Metavar {} : pes, SteVar _ v : es') -> v : go pes es'
      (ListForm lb : pes, SteList stlis : es') -> asciiListItems env sie (lbSeparator lb) (lbElements lb) stlis ++ go pes es'
      _ -> error "Haskott.Prover.Context: inconsistent structure"

asciiListItems :: Env -> Suffix -> Maybe Text -> [Element] -> [Stli] -> [Text]
asciiListItems env sie tmopt prodEs stlis = case stlis of
  [] -> [""]
  _ -> listConcat sep (map item stlis)
  where
    sep = maybe [] (\tm -> [quoteIdent tm]) tmopt
    item stli = case stli of
      StliSingle stes -> asciiElements env sie True prodEs stes
      StliListform b es -> asciiListBody env sie sep prodEs b es
    listConcat s xss = case xss of
      [] -> []
      [xs] -> xs
      xs : more -> xs ++ s ++ listConcat s more

asciiListBody :: Env -> Suffix -> [Text] -> [Element] -> Bound -> [Ste] -> [Text]
asciiListBody env sie sep prodEs b es = case b of
  BoundDotform lo up n ->
    asciiElements env (resolve lo : sie) True prodEs es ++ sep ++ [dots n] ++ sep ++ asciiElements env (resolve up : sie) True prodEs es
  BoundComp v -> ["</"] ++ asciiElements env (SiVar v 0 : sie) True prodEs es ++ ["//", asciiMetavar env [] (v, []), "/>"]
  BoundCompU v u -> ["</"] ++ asciiElements env (SiVar v 0 : sie) True prodEs es ++ ["//", asciiMetavar env [] (v, []), "IN", asciiSuffixItem [] u, "/>"]
  BoundCompLU v l u n -> ["</"] ++ asciiElements env (SiVar v 0 : sie) True prodEs es ++ ["//", asciiMetavar env [] (v, []), "IN", asciiSuffixItem [] l, dots n, asciiSuffixItem [] u, "/>"]
  where
    dots n = case n of
      0 -> ".."
      1 -> "..."
      _ -> "...."
    resolve si = case si of
      SiIndexed s (SiIndex i) | i >= 0 && i < length sie -> SiIndexed s (sie !! i)
      _ -> si
