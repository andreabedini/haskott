{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @substs_pp.ml@: auxiliary functions, substitutions, free
-- variables, and the library lemmas about lists they use.
module Haskott.Prover.Substs
  ( ppAuxfns
  , ppSubsts
  , ppFreevars
  , ppListAllCongLemma
  , ppListSimpLemmas
  ) where

import Data.Text (Text)
import Haskott.Prover.Dependency
import Haskott.Prover.Types
import Haskott.Spec

ppAuxfns :: Env -> [(Text, ([Text], RootRef))] -> P Collapsed
ppAuxfns _ _ = pure []

ppSubsts :: Env -> [Substitution] -> P Collapsed
ppSubsts _ _ = pure []

ppFreevars :: Env -> [Freevar] -> P Collapsed
ppFreevars _ _ = pure []

ppListAllCongLemma :: Env -> P ()
ppListAllCongLemma _ = pure ()

ppListSimpLemmas :: Env -> P ()
ppListSimpLemmas _ = pure ()
