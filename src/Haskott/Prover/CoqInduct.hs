{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @coq_induct.ml@: induction principles for Coq types with lists.
module Haskott.Prover.CoqInduct
  ( ppInduction
  ) where

import Data.Text (Text)
import Haskott.Prover.Types
import Haskott.Spec

ppInduction :: Env -> [Rule] -> P Text
ppInduction _ _ = pure ""
