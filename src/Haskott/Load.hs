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
import Haskott.Spec.Check (checkDocument)
import Haskott.Syntax (ParseError, parseDocument)
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

-- | The file a diagnostic of the concatenation belongs to, and the
-- diagnostic with its range in that file.
locateDiagnostic :: [Source] -> Diagnostic -> (FilePath, Text, Diagnostic)
locateDiagnostic sources d =
  let off = rangeStart (diagRange d)
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
shiftRange n r = fromMaybe r (textRange (rangeStart r + n) (rangeEnd r + n))
