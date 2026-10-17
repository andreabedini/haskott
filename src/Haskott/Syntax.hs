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
import Graft
import qualified Graft.Green as Green
import Haskott.Syntax.Kind
import Haskott.Syntax.Parser

-- | The source text of a tree: the concatenation of its tokens.
render :: GreenNode Kind -> Text
render = Green.renderNode

-- | A readable listing of a tree, one element per line, indented by depth.
dumpTree :: GreenNode Kind -> Text
dumpTree = T.unlines . go 0
  where
    go d n =
      (indent d <> T.pack (show (Green.nodeKind n)))
        : concatMap (element (d + 1)) (Green.children n)
    element d e = case e of
      Node n -> go d n
      Token t -> [indent d <> T.pack (show (Green.tokenKind t)) <> " " <> T.pack (show (Green.text t))]
    indent d = T.replicate d "  "
