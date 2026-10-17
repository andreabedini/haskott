{-# LANGUAGE OverloadedStrings #-}

-- | Parsing symbolic terms against a checked specification: Ott's
-- @parse_complete@ and @just_one_parse@.
module Haskott.Term.Parse
  ( TermParser
  , makeTermParser
  , termGrammar
  , parseComplete
  , Outcome (..)
  , justOneParse
  , Transform
  , userSyntaxTransform
  , defnTransform
  , stripTrailingWhitespace
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Spec (Spec)
import Haskott.Term.Earley (parseAll)
import Haskott.Term.Grammar
import Haskott.Term.Symterm

newtype TermParser = TermParser Grammar

makeTermParser :: Spec -> TermParser
makeTermParser = TermParser . buildGrammar

termGrammar :: TermParser -> Grammar
termGrammar (TermParser g) = g

-- | Every parse of the text as a term of the root, with trailing
-- whitespace removed first as Ott does. An unknown root has no parses.
parseComplete :: TermParser -> Text -> Bool -> Text -> [Symterm]
parseComplete (TermParser g) ntr concrete s = case startSymbol g ntr concrete of
  Nothing -> []
  Just start -> [st | ResSt st <- parseAll g start (stripTrailingWhitespace s)]

stripTrailingWhitespace :: Text -> Text
stripTrailingWhitespace = T.dropWhileEnd (`elem` (" \n\t\r\f" :: String))

type Transform = [Symterm] -> [Symterm]

-- | For user syntax, metavariable parses take precedence over all others.
userSyntaxTransform :: Transform
userSyntaxTransform sts = case filter isMetavar sts of
  [] -> sts
  mvs -> mvs
  where
    isMetavar st = case st of
      StNode "user_syntax" _ [SteMetavar _ _] -> True
      _ -> False

-- | Keep only the parses that are the judgement form being defined.
defnTransform :: Text -> Transform
defnTransform prodName = filter isDefnFormula
  where
    isDefnFormula st = case st of
      StNode _ "formula_judgement" [SteSt (StNode _ _ [SteSt (StNode _ pn _)])] -> pn == prodName
      _ -> False

data Outcome
  = Parsed Symterm
  | NoParses
  | MultipleParses [Symterm]
  deriving (Eq, Show)

-- | Ott's @just_one_parse@. With @picky@ off, several parses yield the
-- first, as Ott does when no output target is requested.
justOneParse :: Bool -> Transform -> TermParser -> Text -> Bool -> Text -> Outcome
justOneParse picky transform tp ntr concrete s =
  case transform (parseComplete tp ntr concrete s) of
    [st] -> Parsed st
    [] -> NoParses
    sts@(st : _) -> if picky then MultipleParses sts else Parsed st
