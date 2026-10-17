{-# LANGUAGE OverloadedStrings #-}
-- | The lossless syntax tree of an Ott source file.
--
-- 'parseDocument' builds a graft green tree that holds every character of
-- the input; 'render' gives the input back. @GRAMMAR.md@ specifies the
-- language and the placement of trivia in the tree.
module Haskott.Syntax
  ( -- * Kinds
    Kind (..)
  , isTrivia
  , isTokenKind

    -- * Parsing
  , parseDocument
  , parseDocumentRecovering
  , ParseError (..)
  , parseErrorPosition

    -- * Rendering and inspection
  , render
  , dumpTree
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Graft.Green (GreenElement (..), GreenNode, nodeChildren, nodeKind, renderNode, tokenKind, tokenText)
import Haskott.Syntax.Kind
import Haskott.Syntax.Parser

-- | The source text of a tree: the concatenation of its tokens.
render :: GreenNode Kind -> Text
render = renderNode

-- | A readable listing of a tree, one element per line, indented by depth.
dumpTree :: GreenNode Kind -> Text
dumpTree = T.unlines . go 0
  where
    go d n =
      (indent d <> T.pack (show (nodeKind n)))
        : concatMap (element (d + 1)) (nodeChildren n)
    element d e = case e of
      Node n -> go d n
      Token t -> [indent d <> T.pack (show (tokenKind t)) <> " " <> T.pack (show (tokenText t))]
    indent d = T.replicate d "  "
