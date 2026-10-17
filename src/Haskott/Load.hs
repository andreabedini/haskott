-- | Loading a specification from several files, as Ott does with several
-- @-i@ options: each file is parsed into its own lossless tree, and the
-- raw documents are concatenated and checked as one. Offsets of later
-- files are shifted past the earlier ones for the check, and shifted back
-- when a diagnostic is reported, so that it names its own file.
module Haskott.Load
  ( Source (..)
  , Loaded (..)
  , LoadError (..)
  , loadSpec
  , Checked (..)
  , loadSpecRecovering
  , locateDiagnostic
  , shiftRange
  ) where

import qualified Data.ByteString as B
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Graft.Green (GreenElement (..), GreenNode, greenNode, greenToken, nodeChildren, nodeKind)
import Graft.Range (TextRange, rangeEnd, rangeStart, textRange)
import Haskott.Raw (rawDocument)
import Haskott.Spec (Diagnostic (..), Spec)
import Haskott.Spec.Check (checkDocument, checkDocumentRecovering)
import Haskott.Syntax (ParseError (..), parseDocument, parseDocumentRecovering)
import Haskott.Syntax.Kind (Kind (..))

data Source = Source
  { srcPath :: FilePath
  , srcText :: Text
  , srcTree :: GreenNode Kind
  , srcBase :: Int
  -- ^ the byte offset of this file in the concatenation
  }

data Loaded = Loaded
  { ldSources :: [Source]
  , ldSpec :: Spec
  }

data LoadError
  = LoadParse FilePath Text ParseError
  | LoadCheck FilePath Text Diagnostic
  -- ^ with the diagnostic's range in its own file

loadSpec :: [(FilePath, Text)] -> Either LoadError Loaded
loadSpec files = do
  trees <- mapM (\(f, src) -> either (Left . LoadParse f src) (\t -> Right (f, src, t)) (parseDocument src)) files
  let bases = scanl (+) 0 [B.length (TE.encodeUtf8 src) | (_, src, _) <- trees]
      sources = [Source f src t b | ((f, src, t), b) <- zip trees bases]
      raw = concat [rawDocument (shiftTree (srcBase s) (srcTree s)) | s <- sources]
  case checkDocument raw of
    Left d -> let (f, src, d') = locateDiagnostic sources d in Left (LoadCheck f src d')
    Right spec -> Right (Loaded sources spec)

-- | A specification loaded with recovery: every file parses into a tree
-- (with error nodes where it did not), the checker records every error,
-- and the specification is there when the early steps of the check
-- succeeded. The diagnostics are those of the parser, then those of the
-- checker, each with its file.
data Checked = Checked
  { ckSources :: [Source]
  , ckSpec :: Maybe Spec
  , ckDiagnostics :: [(FilePath, Text, Diagnostic)]
  }

loadSpecRecovering :: [(FilePath, Text)] -> Checked
loadSpecRecovering files =
  let parsed = [(f, src, parseDocumentRecovering src) | (f, src) <- files]
      bases = scanl (+) 0 [B.length (TE.encodeUtf8 src) | (_, src, _) <- parsed]
      sources = [Source f src t b | ((f, src, (t, _)), b) <- zip parsed bases]
      parseDiags =
        [ (f, src, Diagnostic (lineRange src (parseErrorOffset e)) (parseErrorMessage e))
        | (f, src, (_, es)) <- parsed
        , e <- es
        ]
      raw = concat [rawDocument (shiftTree (srcBase s) (srcTree s)) | s <- sources]
      (spec, checkDiags) = checkDocumentRecovering raw
   in Checked sources spec (parseDiags ++ map (locateDiagnostic sources) checkDiags)

-- | From an offset to the end of its line.
lineRange :: Text -> Int -> TextRange
lineRange src off =
  let bytes = TE.encodeUtf8 src
      lineEnd = maybe (B.length bytes) (+ off) (B.elemIndex 10 (B.drop off bytes))
   in fromMaybe (error "lineRange") (textRange (fromIntegral off) (fromIntegral (max off lineEnd)))

-- | The file a diagnostic of the concatenation belongs to, and the
-- diagnostic with its range in that file.
locateDiagnostic :: [Source] -> Diagnostic -> (FilePath, Text, Diagnostic)
locateDiagnostic sources d =
  let off = fromIntegral (rangeStart (diagRange d))
   in case [s | s <- sources, srcBase s <= off] of
        [] -> case sources of
          (s : _) -> (srcPath s, srcText s, d)
          [] -> ("", T.empty, d)
        xs ->
          let s = last xs
           in (srcPath s, srcText s, d {diagRange = shiftRange (negate (srcBase s)) (diagRange d)})

-- | A document tree whose offsets start at the base: the real children
-- behind a space token of that length.
shiftTree :: Int -> GreenNode Kind -> GreenNode Kind
shiftTree base tree
  | base == 0 = tree
  | otherwise = greenNode (nodeKind tree) (Token (greenToken Space (T.replicate base (T.singleton ' '))) : nodeChildren tree)

shiftRange :: Int -> TextRange -> TextRange
shiftRange n r = fromMaybe r (textRange (rangeStart r + fromIntegral n) (rangeEnd r + fromIntegral n))
