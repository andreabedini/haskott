{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @subrules_pp.ml@: the predicates that carve each subrule out of
-- the type of its top rule.
module Haskott.Prover.Subrules
  ( ppSubrules
  ) where

import Haskott.Prover.Dependency
import Haskott.Prover.Types
import Haskott.Spec

ppSubrules :: Env -> [Subrule] -> P Collapsed
ppSubrules _ _ = pure []
