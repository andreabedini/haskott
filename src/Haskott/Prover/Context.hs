{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @context_pp.ml@: the functions applying a context to a term.
module Haskott.Prover.Context
  ( ppContext
  ) where

import Haskott.Prover.Dependency
import Haskott.Prover.Types
import Haskott.Spec

ppContext :: Env -> [Contextrule] -> P Collapsed
ppContext _ _ = pure []
