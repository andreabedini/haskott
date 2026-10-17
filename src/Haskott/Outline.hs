{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | The outline of one file, for an editor: its declarations, grammar
-- rules with their productions, definitions with their rules, and
-- functions, each with the bytes it spans and those of its name.
--
-- It reads the tree of the file alone, so it needs no specification and
-- shows what parsed even in a file with errors.
module Haskott.Outline
  ( Symbol (..)
  , SymbolKind (..)
  , outline
  ) where

import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Graft
import qualified Graft.Cursor as Cursor
import qualified Graft.Green as Green
import qualified Graft.Range as Range
import qualified Haskott.Syntax.Ast as A
import Haskott.Syntax.Kind (Kind)

data SymbolKind
  = SymMetavar
  | SymIndexvar
  | SymRule
  | SymProduction
  | SymDefns
  | SymDefn
  | SymDRule
  | SymFuns
  | SymFundefn
  deriving (Eq, Show)

data Symbol = Symbol
  { symName :: Text
  , symKind :: SymbolKind
  , symRange :: (Int, Int)
  -- ^ the bytes of the whole construct
  , symSelection :: (Int, Int)
  -- ^ the bytes of its name
  , symChildren :: [Symbol]
  }
  deriving (Eq, Show)

type C = Cursor Kind

outline :: GreenNode Kind -> [Symbol]
outline tree = concatMap item (mapMaybe A.castItem (Cursor.children (A.documentCursor tree)))

item :: A.Item -> [Symbol]
item it = case it of
  A.ItemMetavar d ->
    let kind = if A.metavarKeyword d == T.pack "indexvar" then SymIndexvar else SymMetavar
     in [symbol n kind d (A.nameIdent n) [] | n <- A.metavarNames d]
  A.ItemGrammar g -> map rule (A.grammarRules g)
  A.ItemDefns ds -> [named (A.defnsName ds) SymDefns ds (map defn (A.defnsDefns ds))]
  A.ItemFuns fs -> [named (A.funsName fs) SymFuns fs [named (A.fundefnName f) SymFundefn f [] | f <- A.funsDefns fs]]
  _ -> []
  where
    rule r = case A.ruleNames r of
      [] -> symbol r SymRule r (T.pack "") (prods r)
      n : _ -> (symbol n SymRule r (A.nameIdent n) (prods r)) {symName = T.intercalate (T.pack ", ") (map A.nameIdent (A.ruleNames r))}
    prods r = [(named (A.prodName p) SymProduction p []) {symName = A.rulePrefix r <> A.prodName p} | p <- A.ruleProds r]
    defn d =
      named (A.defnName d) SymDefn d
        [ symbol l SymDRule dr (A.ruleLineName l) []
        | A.BodyRule dr <- A.defnBodyItems d
        , Just l <- [A.druleRuleLine dr]
        ]
    named name kind n = symbol n kind n name

-- | A symbol spanning one node, whose name is the first token under
-- another node that spells it (or that whole node, when none does).
symbol :: (AstNode a, AstNodeKind a ~ Kind, AstNode b, AstNodeKind b ~ Kind) => a -> SymbolKind -> b -> Text -> [Symbol] -> Symbol
symbol nameNode kind whole name =
  Symbol name kind (bytes (nodeSyntax whole)) (maybe (bytes (nodeSyntax nameNode)) bytes spelled)
  where
    spelled =
      listToMaybe
        [ c
        | c <- Cursor.descendants (nodeSyntax nameNode)
        , Token t <- [Cursor.green c]
        , not (T.null name)
        , A.identValue (Green.text t) == name
        ]

bytes :: C -> (Int, Int)
bytes c = let r = Cursor.range c in (fromIntegral (Range.start r), fromIntegral (Range.end r))
