{-# LANGUAGE OverloadedStrings #-}

-- | The checked specification as text, in the shape of Ott's
-- @-show_sort true@ printout, and as classified tokens for comparison with
-- that printout.
module Haskott.Spec.Show
  ( Class (..)
  , Tok (..)
  , prodTokens
  , homsText
  , showSpec
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Spec

-- | How Ott colours a token: nonterminal (yellow), metavariable (red),
-- terminal (green), or plain for the punctuation of list forms.
data Class = CN | CM | CT | CP
  deriving (Eq, Show)

data Tok = Tok Class Text
  deriving (Eq, Show)

-- | The elements of a production as Ott prints them, with list forms
-- expanded to their written form: a dot form shows its two ends, a
-- comprehension its body under its index.
prodTokens :: Prod -> [Tok]
prodTokens = concatMap (elementTokens []) . prodElements

elementTokens :: [SuffixItem] -> Element -> [Tok]
elementTokens sie e = case e of
  Nonterm _ n suff -> [Tok CN (n <> suffixWith sie suff)]
  Metavar _ m suff -> [Tok CM (m <> suffixWith sie suff)]
  Terminal t -> [Tok CT t]
  ListForm lb ->
    -- Ott's printout shows a dot form with its separator on both sides of
    -- the dots, and a comprehension without its separator, with the parts
    -- of its bound as plain tokens.
    let body sie' = concatMap (elementTokens sie') (lbElements lb)
        sep = maybe [] (\t -> [Tok CT t]) (lbSeparator lb)
     in case lbBound lb of
          Just (BoundDotform lo up n) -> body (lo : sie) ++ sep ++ [Tok CP (dots n)] ++ sep ++ body (up : sie)
          Just (BoundComp v) -> comp (body (SiVar v 0 : sie)) [Tok CM v]
          Just (BoundCompU v u) -> comp (body (SiVar v 0 : sie)) [Tok CM v, Tok CP "IN", Tok CP (ppSuffixItem u)]
          Just (BoundCompLU v l u n) -> comp (body (SiVar v 0 : sie)) [Tok CM v, Tok CP "IN", Tok CP (ppSuffixItem l), Tok CP (dots n), Tok CP (ppSuffixItem u)]
          Nothing -> body sie
  where
    comp inner bound = [Tok CP "</"] ++ inner ++ [Tok CP "//"] ++ bound ++ [Tok CP "/>"]
    dots n = T.replicate (n + 2) "."

-- | A suffix with its de Bruijn indices replaced from the environment.
suffixWith :: [SuffixItem] -> Suffix -> Text
suffixWith sie = T.concat . map item
  where
    item si = case si of
      SiIndex i | i < length sie -> ppSuffixItem (sie !! i)
      SiIndexed v (SiIndex i) | i < length sie -> v <> ppSuffixItem (sie !! i)
      _ -> ppSuffixItem si

homsText :: [Hom] -> Text
homsText = T.intercalate " " . map hom
  where
    hom (hn, els) = "{{ " <> hn <> " " <> T.concat (map el els) <> " }}"
    el x = case x of
      HomString s -> s
      HomIndex i -> "[[" <> T.pack (show i) <> "]]"
      HomTerminal s -> "[[" <> s <> "]]"
      HomLnFreeIndex is i -> "[[" <> T.concat (map (\k -> "(" <> T.pack (show k) <> ")") is) <> T.pack (show i) <> "]]"

showSpec :: Spec -> Text
showSpec spec =
  T.unlines
    ( map metavar (specMetavars spec)
        ++ ["grammar"]
        ++ concatMap rule (specRules spec)
        ++ ["subrules"]
        ++ [srLower s <> " <:: " <> srUpper s <> " (top " <> srTop s <> ")" | s <- specSubrules spec]
        ++ ["substitutions"]
        ++ [sbName s <> " " <> sbThis s <> " " <> rootRef (sbThat s) | s <- specSubstitutions spec]
        ++ ["freevars"]
        ++ [fvName f <> " " <> fvThis f <> " " <> rootRef (fvThat f) | f <- specFreevars spec]
    )
  where
    metavar md = "metavar " <> T.intercalate " , " (map fst (mvdNames md)) <> " ::= " <> homsText (mvdHoms md)
    rule r =
      [""
      , T.intercalate " , " (map fst (ruleNames r)) <> " :: '' ::= " <> homsText (ruleHoms r)
          <> (if ruleMeta r then "   % meta" else "")
      ]
        ++ ["  | " <> pad 60 (T.unwords [t | Tok _ t <- prodTokens p]) <> " :: " <> prodName p <> " " <> homsText (prodHoms p) | p <- ruleProds r]
    rootRef r = case r of
      Mvr m -> m
      Ntr n -> n
    pad n s = if T.length s < n then s <> T.replicate (n - T.length s) " " else s
