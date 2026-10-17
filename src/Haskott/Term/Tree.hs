-- | The lossless subtree of a parsed term.
--
-- A derivation of the character-level grammar is turned into green
-- elements by the productions' tags: user productions become 'TNode'
-- nodes, list forms 'TList', 'TEntry' and 'TListForm' nodes, and the
-- terminals, nonterminals, metavariables, variables, pseudo-terminals and
-- bound items single tokens, with the whitespace between them as 'Space'
-- tokens. Nodes are tight: the whitespace before a node's first token
-- belongs to its parent. Rendering the elements gives the parsed text back.
module Haskott.Term.Tree
  ( termElements
  ) where

import Data.Array (Array, listArray, (!))
import qualified Data.IntMap.Strict as IM
import Data.Text (Text)
import qualified Data.Text as T
import Graft
import qualified Graft.Green as Green
import Haskott.Syntax.Kind (Kind (..))
import Haskott.Term.Earley (DTree (..))
import Haskott.Term.Grammar

termElements :: Grammar -> Text -> DTree -> [GreenElement Kind]
termElements g input = build
  where
    chars = T.unpack input
    n = length chars
    arr :: Array Int Char
    arr = listArray (0, max 0 (n - 1)) (if null chars then ['\0'] else chars)
    slice a b = T.pack [arr ! i | i <- [a .. b - 1]]
    prod i = gProds g IM.! i
    tagOf = prodTag . prod
    isSpace t = tagOf (dtProd t) == TagLeaf Space

    token k a b = [Token (Green.token k (slice a b)) | b > a]

    build :: DTree -> [GreenElement Kind]
    build t@(DTree p a b kids) = case tagOf p of
      TagLeaf Space -> token Space a b
      TagLeaf k -> case kids of
        (w : _) | isSpace w && dtStart w == a -> token Space a (dtEnd w) ++ token k (dtEnd w) b
        _ -> token k a b
      TagPass k -> walk k t
      TagNode k -> wrap k (walk k t)
      TagProd ntr pn k -> wrap (TNode ntr pn) (walk k t)

    -- the elements of a production's children, with its literal
    -- characters as tokens of the kind (or, in a list form, of the kind
    -- the delimiter denotes)
    walk :: Kind -> DTree -> [GreenElement Kind]
    walk k (DTree p a _ kids) = go (prodRight (prod p)) kids a a
      where
        go syms ks runStart pos = case syms of
          [] -> literal runStart pos
          T _ : more -> go more ks runStart (pos + 1)
          N _ : more -> case ks of
            (c : cs) -> literal runStart pos ++ build c ++ go more cs (dtEnd c) (dtEnd c)
            [] -> literal runStart pos
        literal a' b'
          | b' > a' = let s = slice a' b' in [Token (Green.token (kindFor s) s)]
          | otherwise = []
        kindFor s = case k of
          TListForm -> case T.unpack s of
            "</" -> CompOpen
            "//" -> CompMiddle
            "/>" -> CompClose
            "IN" -> CompIn
            _ -> TTerminal
          _ -> k

    -- a node around the elements, with a leading space left outside
    wrap :: Kind -> [GreenElement Kind] -> [GreenElement Kind]
    wrap k els = case els of
      (Token t : rest) | Green.tokenKind t == Space -> Token t : [Node (Green.node k rest)]
      _ -> [Node (Green.node k els)]
