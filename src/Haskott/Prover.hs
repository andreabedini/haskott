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
  , proverFilter
  , module Haskott.Prover.System
  ) where

import Data.List (isSuffixOf)
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Prover.Bounds (boundExtraction)
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
  | ".twf" `isSuffixOf` f = Just Twf
  | ".ml" `isSuffixOf` f = Just Caml
  | otherwise = Nothing

-- | A term as the target prints it outside any rule, as Ott does to
-- compare the parses of an ambiguous term.
renderProverSymterm :: Target -> ProverOptions -> Spec -> Symterm -> Text
renderProverSymterm t opts spec st =
  let env = makeEnv t opts (Deps [] [] []) [] (const (StUninterpreted Nothing "")) spec
   in case runP (initialPState 0) (ppSymterm env [] deEmpty st) of
        Right (s, _) -> s
        Left e -> e

-- | Ott's @-coq_filter@ and the like: the @[[ ]]@ quotations of a
-- document, already split by "Haskott.Tex.filteredDocument", printed as
-- prover terms.
proverFilter :: Target -> ProverOptions -> Spec -> (Text -> Symterm) -> [EmbedEl] -> Either Text Text
proverFilter t opts spec quotation els =
  let env = makeEnv t opts (Deps [] [] []) [] quotation spec
      el e = case e of
        EmbedString s -> pure s
        EmbedInner s -> do
          let st = quotation s
          (de, _) <- either (\m -> failP ("\nError in generating output:\n" <> m <> "\n")) pure (boundExtraction env [st])
          ppSymterm env [] de st
   in fst <$> runP (initialPState 0) (T.concat <$> mapM el els)
