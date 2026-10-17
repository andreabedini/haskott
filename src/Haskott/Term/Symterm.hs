{-# LANGUAGE OverloadedStrings #-}

-- | Symbolic terms: the parse trees of rule premises, conclusions and
-- function clauses (Ott's @symterm@), and their plain printing in the
-- format of Ott's @pp_plain_symterm@, which @ott -parse@ prints and the
-- differential compares.
module Haskott.Term.Symterm
  ( Symterm (..)
  , Ste (..)
  , Stli (..)
  , ppPlainSymterm
  , ppPlainBound
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Spec.Suffix

data Symterm
  = StNode Text Text [Ste]
  -- ^ rule root, production name, elements
  | StNonterm Text (Text, Suffix)
  -- ^ primary root; root as written and suffix
  | StNontermSub Text Text (Text, Suffix)
  -- ^ the subrule's root, the top root, the nonterminal as written
  | StUninterpreted Text
  deriving (Eq, Ord, Show)

data Ste
  = SteSt Symterm
  | SteMetavar Text (Text, Suffix)
  -- ^ primary root; root as written and suffix
  | SteVar Text Text
  -- ^ metavariable root, concrete variable
  | SteList [Stli]
  deriving (Eq, Ord, Show)

data Stli
  = StliSingle [Ste]
  | StliListform Bound [Ste]
  deriving (Eq, Ord, Show)

ppPlainSymterm :: Symterm -> Text
ppPlainSymterm st = case st of
  StNode ntr pn es -> "(St_node :" <> ntr <> ":" <> pn <> ": " <> T.unwords (map ppPlainSte es) <> ")"
  StNonterm _ (n, suff) -> "(St_nonterm " <> n <> ppSuffix suff <> ")"
  StNontermSub _ _ (n, suff) -> "(St_nontermsub " <> n <> ppSuffix suff <> ")"
  StUninterpreted s -> "(St_uninterpreted " <> s <> ")"

ppPlainSte :: Ste -> Text
ppPlainSte ste = case ste of
  SteSt st -> "(Ste_st " <> ppPlainSymterm st <> ")"
  SteMetavar _ (m, suff) -> "(Ste_metavar " <> m <> ppSuffix suff <> ")"
  SteVar _ v -> "(Ste_var " <> v <> ")"
  SteList items -> "(Ste_list [" <> T.intercalate "," (map ppPlainStli items) <> "])"

ppPlainStli :: Stli -> Text
ppPlainStli stli = case stli of
  StliSingle es -> "Stli_single " <> T.unwords (map ppPlainSte es)
  StliListform b es -> "Stli_listform " <> T.unwords (ppPlainBound b : " : " : map ppPlainSte es)

ppPlainBound :: Bound -> Text
ppPlainBound b = case b of
  BoundDotform lo up n -> "(" <> ppSuffixItem lo <> dots n <> ppSuffixItem up <> ")"
  BoundComp v -> "(" <> v <> ")"
  BoundCompU v u -> "(" <> v <> " IN " <> ppSuffixItem u <> ")"
  BoundCompLU v l u n -> "(" <> v <> " IN " <> ppSuffixItem l <> dots n <> ppSuffixItem u <> ")"
  where
    dots n = T.replicate (n + 2) "."
