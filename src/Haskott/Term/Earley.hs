-- | An Earley parser for the character-level term grammar.
--
-- Recognition is standard Earley, with nullable completions handled at the
-- point of prediction, and the single-character follow restrictions of the
-- grammar applied when a nonterminal completes. Derivations are then
-- enumerated from the completed spans with the productions' semantic
-- actions, honouring reject productions (a rejected span of a nonterminal
-- has no derivations), the priority table (Visser-style: a child
-- production may be forbidden under a parent anywhere, or only at its
-- leftmost or rightmost non-empty position, with injection chains visible
-- to the check), and Ott's exclusion of a nonterminal recurring in an
-- injection chain over the same span.
module Haskott.Term.Earley
  ( parseAll
  ) where

import Data.Array.Unboxed (UArray, listArray, (!))
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Lazy as ML
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Term.Grammar

-- | Every result of parsing the whole input from the start nonterminal.
parseAll :: Grammar -> NtId -> Text -> [Res]
parseAll g start input =
  let s = T.unpack input
      n = length s
      chars = listArray (0, max 0 (n - 1)) (if null s then ['\0'] else s) :: UArray Int Char
      done = recognise g start chars n
      table = derivations g chars n done
   in [v | Deriv v _ <- fromMaybe [] (ML.lookup (start, 0, n) table)]

------------------------------------------------------------------------
-- Recognition

-- | Items are triples of production, dot position and origin. For each
-- input position, the completed (production, origin) pairs that
-- passed their follow restriction.
type Done = IM.IntMap (Set.Set (Int, Int))

recognise :: Grammar -> NtId -> UArray Int Char -> Int -> Done
recognise g start chars n = go 0 IM.empty IM.empty initial
  where
    prodsOf x = fromMaybe [] (IM.lookup x (gByLeft g))
    prod i = gProds g IM.! i
    rhsLength i = length (prodRight (prod i))
    initial = Set.fromList [(p, 0, 0) | p <- prodsOf start]
    nextSym (p, d, _) = case drop d (prodRight (prod p)) of
      (s : _) -> Just s
      [] -> Nothing
    followOk x j = case IM.lookup x (gFollow g) of
      Nothing -> True
      Just fs
        | j >= n -> True
        | otherwise -> not (any ($ (chars ! j)) fs)

    -- sets: the item sets of the positions before j
    go j sets done seed
      | j > n = done
      | otherwise =
          let items = closure j sets seed
              doneJ = Set.fromList [(p, o) | (p, d, o) <- Set.toList items, d == rhsLength p, followOk (prodLeft (prod p)) j]
              nextSeed
                | j >= n = Set.empty
                | otherwise =
                    Set.fromList
                      [ (p, d + 1, o)
                      | it@(p, d, o) <- Set.toList items
                      , Just (T c) <- [nextSym it]
                      , c == chars ! j
                      ]
           in go (j + 1) (IM.insert j items sets) (IM.insert j doneJ done) nextSeed

    -- the closure of a set of items at position j under prediction and
    -- completion; a completion with origin j is a nullable completion and
    -- must also advance items added afterwards
    closure j sets seed = loop seed (Set.toList seed) Set.empty
      where
        loop items work nullDone = case work of
          [] -> items
          it@(p, d, o) : rest -> case nextSym it of
            Just (N y) ->
              let predicted = [(q, 0, j) | q <- prodsOf y]
                  advanced = [(p, d + 1, o) | Set.member y nullDone]
               in add items rest nullDone (predicted ++ advanced)
            Just (T _) -> loop items rest nullDone
            Nothing ->
              let x = prodLeft (prod p)
               in if not (followOk x j)
                    then loop items rest nullDone
                    else
                      if o == j
                        then
                          let nullDone' = Set.insert x nullDone
                              advanced = [(q, e + 1, oq) | it'@(q, e, oq) <- Set.toList items, nextSym it' == Just (N x)]
                           in add items rest nullDone' advanced
                        else
                          let parents = maybe [] Set.toList (IM.lookup o sets)
                              advanced = [(q, e + 1, oq) | it'@(q, e, oq) <- parents, nextSym it' == Just (N x)]
                           in add items rest nullDone advanced
        add items rest nullDone new =
          let fresh = [i | i <- new, not (Set.member i items)]
              items' = foldr Set.insert items fresh
           in loop items' (rest ++ fresh) nullDone

------------------------------------------------------------------------
-- Derivations

-- | A value and the production indices visible to a priority check.
data Deriv = Deriv Res [Int]

-- | A child of a derivation: the symbol, its span, and its derivation when
-- it is a nonterminal.
type Child = (Sym, Int, Int, Maybe Deriv)

derivations :: Grammar -> UArray Int Char -> Int -> Done -> ML.Map (NtId, Int, Int) [Deriv]
derivations g chars _ done = table
  where
    prod i = gProds g IM.! i
    -- the productions completing each (nonterminal, start, end)
    spans :: M.Map (NtId, Int, Int) [Int]
    spans =
      M.fromListWith (++)
        [ ((prodLeft (prod p), o, j), [p])
        | (j, s) <- IM.toList done
        , (p, o) <- Set.toList s
        ]
    endsFrom :: M.Map (NtId, Int) [Int]
    endsFrom = M.fromListWith (++) [((x, o), [j]) | ((x, o, j), _) <- M.toList spans]
    rejected key = any (prodReject . prod) (fromMaybe [] (M.lookup key spans))
    -- lazily memoised derivations of every completed span
    table = ML.fromList [(key, compute (Set.singleton x) key) | key@(x, _, _) <- M.keys spans]

    -- derivations of a nonterminal over a span; anc holds the nonterminals
    -- of the injection chain leading here over this same span
    compute :: Set.Set NtId -> (NtId, Int, Int) -> [Deriv]
    compute anc key@(_, i, j)
      | rejected key = []
      | otherwise =
          [ Deriv v (visibleIndices p children)
          | p <- fromMaybe [] (M.lookup key spans)
          , not (prodReject (prod p))
          , children <- splits anc (i, j) (prodRight (prod p)) i j
          , conflictsOk p children
          , Just v <- [prodAction (prod p) [r | (N _, _, _, Just (Deriv r _)) <- children]]
          ]

    -- ways to lay a right-hand side over [a, j]
    splits :: Set.Set NtId -> (Int, Int) -> [Sym] -> Int -> Int -> [[Child]]
    splits anc parent syms a j = case syms of
      []
        | a == j -> [[]]
        | otherwise -> []
      T c : more
        | a < j && chars ! a == c -> map ((T c, a, a + 1, Nothing) :) (splits anc parent more (a + 1) j)
        | otherwise -> []
      [N y] -> [[(N y, a, j, Just d)] | d <- childDerivs anc parent y a j]
      N y : more ->
        [ (N y, a, b, Just d) : rest
        | b <- fromMaybe [] (M.lookup (y, a) endsFrom)
        , b <= j
        , rest <- splits anc parent more b j
        , d <- childDerivs anc parent y a b
        ]

    childDerivs :: Set.Set NtId -> (Int, Int) -> NtId -> Int -> Int -> [Deriv]
    childDerivs anc (pi', pj) y a b
      | (a, b) == (pi', pj) = if Set.member y anc then [] else compute (Set.insert y anc) (y, a, b)
      | otherwise = fromMaybe [] (ML.lookup (y, a, b) table)

    -- the production indices a priority check at the parent sees: the
    -- production itself, plus the child's when the production is an
    -- injection (one non-empty nonterminal child, no terminals), or all
    -- children's when it is transparent
    visibleIndices :: Int -> [Child] -> [Int]
    visibleIndices p children =
      let allChildren = [vs | (N _, _, _, Just (Deriv _ vs)) <- children]
          nonEmpty = [vs | (N _, a, b, Just (Deriv _ vs)) <- children, b > a]
          hasTerminal = not (null [() | (T _, _, _, _) <- children])
       in if prodTransparent (prod p)
            then p : concat allChildren
            else
              if hasTerminal
                then [p]
                else case nonEmpty of
                  [vs] -> p : vs
                  [] -> p : concat allChildren
                  _ -> [p]

    conflictsOk :: Int -> [Child] -> Bool
    conflictsOk p children = and (zipWith ok [0 :: Int ..] children)
      where
        eps = [case c of (T _, _, _, _) -> False; (N _, a, b, _) -> b == a | c <- children]
        ok k child = case child of
          (N _, _, _, Just (Deriv _ vs)) ->
            let leftEps = and (take k eps)
                rightEps = and (drop (k + 1) eps)
             in all (allowed leftEps rightEps) vs
          _ -> True
        allowed leftEps rightEps v = case M.lookup (p, v) (gPriority g) of
          Nothing -> True
          Just (gr, l, r, na) ->
            not (gr || ((r || na) && not rightEps && leftEps) || ((l || na) && not leftEps && rightEps))
