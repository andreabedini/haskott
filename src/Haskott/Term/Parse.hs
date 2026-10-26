{-# LANGUAGE OverloadedStrings #-}

-- | Parsing symbolic terms against a checked specification: Ott's
-- @parse_complete@ and @just_one_parse@.
module Haskott.Term.Parse
  ( TermParser
  , makeTermParser
  , termGrammar
  , ParseCache
  , withCache
  , Parse (..)
  , parseComplete
  , parseTerms
  , noParsesErrorString
  , ParsePolicy (..)
  , selectParse
  , Outcome (..)
  , justOneParse
  , Transform
  , userSyntaxTransform
  , defnTransform
  , stripTrailingWhitespace
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Spec (Spec)
import Haskott.Term.Earley (DTree, parseAll, parseAllFurthest)
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as B
import Haskott.Term.Grammar
import Haskott.Term.Symterm

-- | Parses already made, by root and text, so that the tree splice and
-- the processing of the definitions parse each term once.
type ParseCache = M.Map (Text, Text) [Parse]

data TermParser = TermParser
  { termGrammar :: Grammar
  , tpCache :: ParseCache
  }

makeTermParser :: Spec -> TermParser
makeTermParser spec = TermParser (buildGrammar spec) M.empty

withCache :: ParseCache -> TermParser -> TermParser
withCache cache tp = tp {tpCache = M.union cache (tpCache tp)}

-- | One parse of a term: the symbolic term and its derivation, from which
-- "Haskott.Term.Tree" builds the lossless subtree.
data Parse = Parse
  { parseTerm :: Symterm
  , parseTree :: DTree
  }

-- | Every parse of the text as a term of the root, with trailing
-- whitespace removed first as Ott does. An unknown root has no parses.
parseComplete :: TermParser -> Text -> Bool -> Text -> [Parse]
parseComplete tp ntr concrete s
  | not concrete, Just ps <- M.lookup (ntr, s') (tpCache tp) = ps
  | otherwise = case startSymbol (termGrammar tp) ntr concrete of
      Nothing -> []
      Just start -> [Parse st t | (ResSt st, t) <- parseAll (termGrammar tp) start s']
  where
    s' = stripTrailingWhitespace s

-- | Ott's message for a term with no parses: the text split after the
-- character the parser failed on, with that position printed in bytes,
-- as Ott's byte-level parser counts it.
noParsesErrorString :: TermParser -> Text -> Bool -> Text -> Text
noParsesErrorString tp ntr concrete s =
  let s' = stripTrailingWhitespace s
      furthest = case startSymbol (termGrammar tp) ntr concrete of
        Nothing -> 0
        Just start -> snd (parseAllFurthest (termGrammar tp) start s')
      -- Ott counts the character it failed on
      pos = min (furthest + 1) (T.length s')
      c = B.length (TE.encodeUtf8 (T.take pos s'))
   in "no parses (char " <> T.pack (show c) <> "): " <> T.take pos s <> "***" <> T.drop pos s <> " "

parseTerms :: TermParser -> Text -> Bool -> Text -> [Symterm]
parseTerms tp ntr concrete s = map parseTerm (parseComplete tp ntr concrete s)

stripTrailingWhitespace :: Text -> Text
stripTrailingWhitespace = T.dropWhileEnd (`elem` (" \n\t\r\f" :: String))

type Transform = [Parse] -> [Parse]

-- | For user syntax, metavariable parses take precedence over all others.
userSyntaxTransform :: Transform
userSyntaxTransform ps = case filter (isMetavar . parseTerm) ps of
  [] -> ps
  mvs -> mvs
  where
    isMetavar st = case st of
      StNode "user_syntax" _ [SteMetavar _ _] -> True
      _ -> False

-- | Keep only the parses that are the judgement form being defined.
defnTransform :: Text -> Transform
defnTransform prodName = filter (isDefnFormula . parseTerm)
  where
    isDefnFormula st = case st of
      StNode _ "formula_judgement" [SteSt (StNode _ _ [SteSt (StNode _ pn _)])] -> pn == prodName
      _ -> False

data Outcome
  = Parsed Parse
  | NoParses
  | MultipleParses [Parse]

-- | What to do with several parses of a term: Ott's
-- @-picky_multiple_parses@ makes them an error; otherwise the first is
-- taken when every output target prints all of them the same way, so
-- with no targets the first is always taken.
data ParsePolicy
  = Picky
  | FirstIfSame [Symterm -> Text]

-- | The parse to use among several, under the policy.
selectParse :: ParsePolicy -> [Parse] -> Maybe Parse
selectParse policy ps = case ps of
  [p] -> Just p
  [] -> Nothing
  p : rest -> case policy of
    Picky -> Nothing
    FirstIfSame renderers
      | all (\render -> all (\q -> render (parseTerm q) == render (parseTerm p)) rest) renderers -> Just p
      | otherwise -> Nothing

-- | Ott's @just_one_parse@.
justOneParse :: ParsePolicy -> Transform -> TermParser -> Text -> Bool -> Text -> Outcome
justOneParse policy transform tp ntr concrete s =
  case transform (parseComplete tp ntr concrete s) of
    [] -> NoParses
    ps -> maybe (MultipleParses ps) Parsed (selectParse policy ps)
