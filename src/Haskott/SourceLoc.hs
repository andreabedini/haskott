{-# LANGUAGE OverloadedStrings #-}

-- | Ott's source locations (@-output_source_locations@): the files and
-- lines of the constructs an output was printed from, as comments.
--
-- Ott's parser gives a construct the span of its tokens. In the grammar
-- the tokens are words and symbols, so a construct runs from its first to
-- its last syntax token and its lines are theirs. In the body of a
-- definition the tokens are whole lines with their newlines (comment lines
-- among them), so a rule runs from its first line, comment lines before it
-- included, to the start of the line after its last, and a definition
-- class with its definitions to the start of the next keyword line.
module Haskott.SourceLoc
  ( Sources
  , SourceLoc
  , noSources
  , makeSources
  , itemLoc
  , druleLoc
  , ruleLoc
  , ppSourceLoc
  ) where

import qualified Data.ByteString as B
import qualified Data.IntMap.Strict as IM
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Graft (GreenElement (..), TextRange)
import qualified Graft.Cursor as Cursor
import qualified Graft.Range as Range
import Haskott.Load (Source (..))
import Haskott.Spec (Rule (..))
import Haskott.Syntax.Kind (isTrivia)

-- | A source file, indexed by offsets in the concatenation of the sources.
data SourceFile = SourceFile
  { sfPath :: FilePath
  , sfBase :: Int
  , sfBytes :: B.ByteString
  , sfLineOf :: IM.IntMap Int
  -- ^ the offset of each line's start to the line's number
  , sfLineStart :: IM.IntMap Int
  -- ^ each line's number to the offset of its start
  , sfTokens :: IM.IntMap Int
  -- ^ the start of each syntax token to its end
  }

newtype Sources = Sources [SourceFile]

-- | For each span, its file and its first and last lines; none for what
-- Ott synthesises.
type SourceLoc = [(FilePath, Int, Int)]

noSources :: Sources
noSources = Sources []

makeSources :: [Source] -> Sources
makeSources = Sources . map file
  where
    file s =
      let bytes = TE.encodeUtf8 (srcText s)
          base = srcBase s
          starts = base : [base + i + 1 | i <- B.elemIndices 10 bytes]
          tokens =
            [ (base + fromIntegral (Range.start r), base + fromIntegral (Range.end r))
            | t <- Cursor.descendantTokens (Cursor.fromGreen (Node (srcTree s)))
            , not (isTrivia (Cursor.kind t))
            , let r = Cursor.range t
            ]
       in SourceFile
            { sfPath = srcPath s
            , sfBase = base
            , sfBytes = bytes
            , sfLineOf = IM.fromList (zip starts [1 ..])
            , sfLineStart = IM.fromList (zip [1 ..] starts)
            , sfTokens = IM.fromList tokens
            }

fileAt :: Sources -> Int -> Maybe SourceFile
fileAt (Sources fs) off = case [f | f <- fs, sfBase f <= off] of
  [] -> Nothing
  xs -> Just (last xs)

lineAt :: SourceFile -> Int -> Int
lineAt f off = maybe 1 snd (IM.lookupLE off (sfLineOf f))

fileEnd :: SourceFile -> Int
fileEnd f = sfBase f + B.length (sfBytes f)

-- | The line's text, without its newline, if it has one.
lineText :: SourceFile -> Int -> Maybe B.ByteString
lineText f n = do
  s <- IM.lookup n (sfLineStart f)
  e <- IM.lookup (n + 1) (sfLineStart f)
  pure (B.take (e - s - 1) (B.drop (s - sfBase f) (sfBytes f)))

-- | Ott's @COMMENTLINE@ of a definition body.
isCommentLine :: SourceFile -> Int -> Bool
isCommentLine f n = case lineText f n of
  Just l -> B.take 1 (B.dropWhile (`elem` [32, 9, 12]) l) == "%"
  Nothing -> False

-- | The syntax tokens of a range: the start of the first and the end of
-- the last.
tokenSpan :: SourceFile -> TextRange -> Maybe (Int, Int)
tokenSpan f r = do
  let s = fromIntegral (Range.start r)
      e = fromIntegral (Range.end r)
  (ts, _) <- IM.lookupGE s (sfTokens f)
  (_, te) <- IM.lookupLT e (sfTokens f)
  if ts < e && te > ts then Just (ts, te) else Nothing

located :: Sources -> TextRange -> (SourceFile -> (Int, Int) -> (Int, Int)) -> SourceLoc
located sources r spanLines
  | Range.start r == Range.end r = []
  | otherwise = case fileAt sources (fromIntegral (Range.start r)) of
      Nothing -> []
      Just f -> case tokenSpan f r of
        Nothing -> []
        Just sp -> let (l1, l2) = spanLines f sp in [(sfPath f, l1, l2)]

-- | A construct of the grammar: from its first to its last token.
itemLoc :: Sources -> TextRange -> SourceLoc
itemLoc sources r = located sources r (\f (ts, te) -> (lineAt f ts, lineAt f te))

-- | A definition or function class, from its name (after the keyword
-- that introduces it); with definitions, to the line of the next token
-- after it, or to the end of its file.
classLoc :: Sources -> Bool -> TextRange -> SourceLoc
classLoc sources withBody r = located sources r $ \f (ts, te) ->
  let e = fromIntegral (Range.end r)
      tokenText (s, t) = B.take (t - s) (B.drop (s - sfBase f) (sfBytes f))
      start = case IM.lookupGE ts (sfTokens f) of
        Just k@(s, _)
          | tokenText k `elem` ["defns", "funs"] -> maybe s fst (IM.lookupGT s (sfTokens f))
        _ -> ts
      end
        | not withBody = lineAt f te
        | otherwise = case IM.lookupGE e (sfTokens f) of
            Just (t, _) | t < fileEnd f -> lineAt f t
            _ -> eofLine f
   in (lineAt f start, end)

-- | The line Ott's lexer is on at the end of a file: a last line without
-- a newline is counted as if it had one, unless it is a comment.
eofLine :: SourceFile -> Int
eofLine f =
  let n = lineAt f (fileEnd f)
      lastLine = B.takeWhileEnd (/= 10) (sfBytes f)
   in if B.null lastLine || B.take 1 (B.dropWhile (`elem` [32, 9, 12]) lastLine) == "%" then n else n + 1

-- | A rule of a definition body: its lines with the comment lines around
-- them, to the start of the line after the last.
druleLoc :: Sources -> TextRange -> SourceLoc
druleLoc sources r = located sources r $ \f (ts, te) ->
  let up n = if n > 1 && isCommentLine f (n - 1) then up (n - 1) else n
      down n = if isCommentLine f (n + 1) then down (n + 1) else n
   in (up (lineAt f ts), down (lineAt f te) + 1)

-- | A rule of the grammar. The rules Ott synthesises have none; those of
-- the definition and function classes span the classes.
ruleLoc :: Sources -> Rule -> SourceLoc
ruleLoc sources r
  | any (`elem` ruleCategories r) ["formula", "judgement", "user_syntax"] = []
  | any (`elem` ruleCategories r) ["defnclass", "fundefnclass"] = classLoc sources (not (null (ruleProds r))) (ruleRange r)
  | otherwise = itemLoc sources (ruleRange r)

-- | Ott's @Location.pp_t_source@.
ppSourceLoc :: SourceLoc -> Text
ppSourceLoc l = "#source " <> T.intercalate " and " [span' p l1 l2 | (p, l1, l2) <- l]
  where
    span' p l1 l2 = "file " <> (if null p then "?" else T.pack p) <> "  lines " <> n l1 <> " - " <> n l2
    n = T.pack . show
