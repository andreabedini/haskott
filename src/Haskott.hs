-- | haskott: a Haskell reimplementation of Ott.
--
-- The package is at its first milestone: the specification of the Ott source
-- language in @GRAMMAR.md@. The parser that builds the lossless tree comes
-- next. This module exists so that the package, and its dependency on the
-- sibling @graft@ checkout, build.
module Haskott
  ( -- * Syntax kinds
    Kind (..)
  ) where

-- | The syntax kinds of haskott's lossless tree, as far as they are fixed by
-- @GRAMMAR.md@ §7. Trivia kinds first, because every mode has them; the
-- syntax kinds follow in later milestones.
data Kind
  = Space
    -- ^ a run of non-newline whitespace: space, tab, form feed
  | Newline
    -- ^ one line terminator: @\\n@, @\\r@ or @\\r\\n@
  | LineComment
    -- ^ from @%@ to the end of the line, terminator excluded
  | BlockComment
    -- ^ from @>>@ to its matching @<<@, nesting included
  deriving (Eq, Ord, Show)
