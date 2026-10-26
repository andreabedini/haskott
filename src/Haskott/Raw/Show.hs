{-# LANGUAGE OverloadedStrings #-}

-- | The raw specification in the format of Ott's @-showraw true@ output
-- (@pp_raw_*@ in Ott's @grammar_pp.ml@), down to its padding and its
-- missing newlines, so that the projection can be compared with Ott's
-- parse byte for byte.
module Haskott.Raw.Show
  ( showRaw
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Foreign as TF
import Haskott.Raw

showRaw :: Document -> Text
showRaw = T.concat . map item

-- | The "TODO: ..." texts for parsing annotations, hom sections and Coq
-- items are not unfinished work here: Ott's @pp_raw_item@ prints exactly
-- these placeholders, and they are kept so the output still matches Ott's.
item :: Item -> Text
item it = case it of
  ItemMetavar d -> metavardefn d
  ItemGrammar rs -> "grammar\n" <> T.intercalate "\n" (map rule rs)
  ItemSubrules ss -> "subrules\n" <> T.intercalate "\n" (map subrule ss)
  ItemContextrules cs -> "contextrules\n" <> T.intercalate "\n" (map contextrule cs)
  ItemSubstitutions ss -> "substitutions\n" <> T.intercalate "\n" (map substitution ss)
  ItemFreevars fs -> "freevars\n" <> T.intercalate "\n" (map freevar fs)
  ItemEmbed es -> "embed\n" <> T.intercalate "\n" (map embedmorphism es) <> "\n"
  ItemParsing _ -> "TODO: raw parsing annotation"
  ItemHomSection _ -> "TODO: raw hom section"
  ItemDefns dc -> defnclass dc
  ItemFuns fc -> funclass fc
  ItemCoqSection _ _ -> "TODO: coq section"
  ItemCoqVariable _ -> "TODO: coq variable"

-- | Ott's @pad@: pad with spaces to a width counted in bytes.
pad :: Int -> Text -> Text
pad n s =
  let m = n - TF.lengthWord8 s
   in if m >= 1 then s <> T.replicate m " " else s

homs :: [Hom] -> Text
homs = T.intercalate " " . map hom

hom :: Hom -> Text
hom (Hom hn hs _) = "{{ " <> hn <> " " <> T.intercalate " " (map homSpecEl hs) <> " }}"

homSpecEl :: HomSpecEl -> Text
homSpecEl e = case e of
  HomString s -> s
  HomBlanks s -> s
  HomIdent ris -> "[[" <> T.intercalate " " ris <> "]]"
  HomIdentDots ris n ris' -> "[[" <> T.intercalate " " ris <> dots n <> T.intercalate " " ris' <> "]]"
  HomIdentComp ris b -> "[[ </" <> T.intercalate " " ris <> "//" <> compBound b <> "/> ]]"

dots :: Int -> Text
dots n = T.replicate (n + 2) "."

compBound :: CompBound -> Text
compBound b = case b of
  Bound i -> i
  BoundU i u -> i <> " IN " <> u <> " "
  BoundLU i l n u -> i <> " IN " <> l <> " " <> dots n <> " " <> u <> " "

embedmorphism :: Embed -> Text
embedmorphism (Embed hn es _) = "{{ " <> hn <> " " <> embedSpecText es <> " }}"

embedSpecText :: [EmbedEl] -> Text
embedSpecText = T.concat . map el
  where
    el e = case e of
      EmbedString s -> s
      EmbedInner s -> "[[" <> s <> "]]"

namesWithHoms :: [(Text, [Hom])] -> Text
namesWithHoms = T.intercalate " , " . map (\(n, hs) -> n <> homs hs)

metavardefn :: MetavarDefn -> Text
metavardefn d = "metavar " <> namesWithHoms (mvdNames d) <> " ::= " <> homs (mvdHoms d) <> "\n"

rule :: Rule -> Text
rule r =
  namesWithHoms (ruleNames r)
    <> " :: " <> rulePrefix r
    <> " ::=" <> homs (ruleHoms r)
    <> "\n  "
    <> T.intercalate "  " (map (\p -> prod p <> "\n") (ruleProds r))

prod :: Prod -> Text
prod p =
  pad 60 ("| " <> T.intercalate " " (map element (prodElements p)))
    <> " :: " <> pad 1 (T.intercalate " " (prodCategories p))
    <> " :: " <> prodName p
    <> "  " <> bindspecList (prodBindspecs p)
    <> "  " <> homs (prodHoms p)

element :: Element -> Text
element e = case e of
  EIdent s -> s
  EQuoted s -> "'" <> s <> "'"
  EDots n -> " " <> dots n <> " "
  EComp es mi b ->
    "</ " <> T.intercalate " " (map element es) <> "// "
      <> maybe "" (\i -> i <> "// ") mi
      <> compBound b <> " />"

bindspecList :: [Bindspec] -> Text
bindspecList bs = case bs of
  [] -> ""
  [b] -> "(+ " <> bindspec b <> " +)"
  _ -> "(+ " <> T.intercalate " " (map bindspec bs) <> " +)"

bindspec :: Bindspec -> Text
bindspec b = case b of
  Bind m x _ -> "bind " <> mse m <> " in " <> x
  AuxFnDef f m _ -> f <> "=" <> mse m
  NamesEqual m m' _ -> "names(" <> mse m <> ")=names(" <> mse m' <> ")"
  NamesDistinct m m' _ -> "names(" <> mse m <> ")#names(" <> mse m' <> ")"
  AllNamesDistinct m _ -> "distinctnames(" <> mse m <> ")"

mse :: Mse -> Text
mse m = case m of
  MseVar x -> x
  MseDots x n y -> x <> dots n <> y
  MseComp x b -> "</" <> x <> "//" <> compBound b <> "/>"
  MseAux f x -> f <> "(" <> x <> ")"
  MseAuxDots f x n y -> f <> "(" <> x <> dots n <> y <> ")"
  MseAuxComp f x b -> f <> "(</" <> x <> "//" <> compBound b <> "/>)"
  MseUnion a b -> mse a <> " union " <> mse b
  MseEmpty -> "{}"

subrule :: Subrule -> Text
subrule s = srLower s <> " <:: " <> srUpper s <> " " <> homs (srHoms s)

contextrule :: Contextrule -> Text
contextrule c = crNtr c <> " _:: " <> crTarget c <> "  :: " <> crHole c <> " "

substitution :: Substitution -> Text
substitution s = sbName s <> " " <> sbThis s <> " " <> sbThat s <> homs (sbHoms s)

freevar :: Freevar -> Text
freevar f = fvName f <> " " <> fvThis f <> " " <> fvThat f <> homs (fvHoms f)

defnclass :: DefnClass -> Text
defnclass dc =
  "Defns\n" <> dcName dc <> " :: " <> dcWrapper dc <> " ::=" <> "\n\n"
    <> T.intercalate "\n" (map defn (dcDefns dc))

defn :: Defn -> Text
defn d =
  "Defn\n"
    <> T.intercalate " " (map element (dElements d))
    <> " :: " <> pad 1 (T.intercalate " " (dCategories d))
    <> " :: " <> dName d <> " "
    <> " :: " <> dWrapper d <> " "
    <> homs (dHoms d)
    <> "by" <> "\n\n"
    <> T.intercalate "\n" (map semirawRule (dBody d))

semirawRule :: SemirawRule -> Text
semirawRule r = case r of
  LinelessRule ls _ -> "[[\n" <> T.concat (map bar ls) <> "]]\n"
  LinedRule ps annot _ cs _ _ _ -> "[[\n" <> T.concat (map bar ps) <> "---------------" <> annot <> T.concat (map bar cs) <> "]]\n"
  DefnComRule es _ -> "[[\n" <> embedSpecText es <> "]]\n"
  where
    bar s = "| " <> s <> "\n"

funclass :: FunClass -> Text
funclass fc = "funs\n" <> fcName fc <> " ::=" <> "\n\n " <> T.intercalate "\n" (map fundefn (fcDefns fc))

fundefn :: FunDefn -> Text
fundefn f =
  "fun\n"
    <> T.intercalate " " (map element (fdElements f))
    <> " :: " <> fdResult f
    -- the placeholder Ott's parser leaves in raw_fd_pn_wrapper for the
    -- checker to fill, which -showraw prints
    <> " // dummy, to be replaced by grammar_typecheck "
    <> " :: " <> fdName f <> " "
    <> homs (fdHoms f)
    <> "by" <> "\n\n"
    <> T.intercalate "\n" (fdClauses f)
