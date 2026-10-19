{-# LANGUAGE OverloadedStrings #-}

-- | The prover back ends: Ott's output for Coq, Isabelle, HOL, Lem and
-- OCaml.
module Haskott.Prover
  ( Target (..)
  , targetName
  , ProverOptions (..)
  , defaultProverOptions
  , targetOfOutput
  , renderProverSymterm
  , module Haskott.Prover.System
  ) where

import Data.List (isSuffixOf)
import Data.Text (Text)
import Haskott.Prover.Pp (ppSymterm)
import Haskott.Prover.System
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

-- | The target of an output file, by Ott's table of extensions.
targetOfOutput :: FilePath -> Maybe Target
targetOfOutput f
  | ".v" `isSuffixOf` f = Just Coq
  | ".thy" `isSuffixOf` f = Just Isa
  | ".sml" `isSuffixOf` f = Just Hol
  | ".lem" `isSuffixOf` f = Just Lem
  | ".ml" `isSuffixOf` f = Just Caml
  | otherwise = Nothing

-- | A term as the target prints it outside any rule, as Ott does to
-- compare the parses of an ambiguous term.
renderProverSymterm :: Target -> ProverOptions -> Spec -> Symterm -> Text
renderProverSymterm t opts spec st =
  let env = makeEnv t opts (Deps [] [] []) [] (const (StUninterpreted "")) spec
   in case runP (initialPState 0) (ppSymterm env [] deEmpty st) of
        Right (s, _) -> s
        Left e -> e
