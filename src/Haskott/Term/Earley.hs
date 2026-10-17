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
  ( DTree (..)
  , parseAll
  ) where

import Data.Array (Array)
import Data.Array.Unboxed (UArray, listArray, (!))
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Lazy as ML
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Term.Grammar

-- | A derivation: the production, its span in characters, and the
-- derivations of the nonterminals of its right-hand side, in order.
data DTree = DTree
  { dtProd :: !Int
  , dtStart :: !Int
  , dtEnd :: !Int
  , dtChildren :: [DTree]
  }

-- | Every result of parsing the whole input from the start nonterminal,
-- with its derivation.
parseAll :: Grammar -> NtId -> Text -> [(Res, DTree)]
parseAll g start input =
  let s = T.unpack input
      n = length s
      chars = listArray (0, max 0 (n - 1)) (if null s then ['\0'] else s) :: UArray Int Char
      done = recognise g start chars n
      table = derivations g chars n done
   in [(v, t) | Deriv v _ t <- fromMaybe [] (ML.lookup (start, 0, n) table)]

------------------------------------------------------------------------
-- Recognition

-- | Items are triples of production, dot position and origin. For each
-- input position, the completed (production, origin) pairs that
-- passed their follow restriction.
type Done = IM.IntMap (Set.Set (Int, Int))

recognise :: Grammar -> NtId -> UArray Int Char -> Int -> Done
recognise g start chars n = go 0 IM.empty IM.empty [(dotId p 0, 0) | p <- prodsOf start]
  where
    prodsOf x = fromMaybe [] (IM.lookup x (gByLeft g))
    numProds = maybe 0 ((+ 1) . fst) (IM.lookupMax (gProds g))
    -- a dotted production is one Int: production times stride plus dot
    stride = 1 + maximum (0 : [length (prodRight p) | p <- IM.elems (gProds g)])
    dotId p d = p * stride + d
    dotProd dot = dot `quot` stride
    -- the symbol after each dot, or 'Nothing' at the end
    nextArr :: Array Int (Maybe Sym)
    nextArr =
      listArray (0, numProds * stride - 1)
        [ case IM.lookup p (gProds g) of
            Just pr -> case drop d (prodRight pr) of
              (sy : _) -> Just sy
              [] -> Nothing
            Nothing -> Nothing
        | p <- [0 .. numProds - 1]
        , d <- [0 .. stride - 1]
        ]
    leftArr :: UArray Int Int
    leftArr = listArray (0, max 0 (numProds - 1)) [maybe 0 prodLeft (IM.lookup p (gProds g)) | p <- [0 .. max 0 (numProds - 1)]]
    followOk x j = case IM.lookup x (gFollow g) of
      Nothing -> True
      Just fs
        | j >= n -> True
        | otherwise -> not (any ($ (chars ! j)) fs)

    -- waitings: for each earlier position, the items waiting on each
    -- nonterminal; done: the completed items per position
    go j waitings done seed
      | j > n = done
      | otherwise =
          let st = closure j waitings seed
              done' = IM.insert j (Set.fromList (psDone st)) done
              nextSeed = [(dot + 1, o) | (dot, o) <- psScan st]
           in go (j + 1) (IM.insert j (psWaiting st) waitings) done' nextSeed

    closure j waitings seed = loop emptyPS seed
      where
        loop st work = case work of
          [] -> st
          (dot, o) : rest
            | IS.member o (IM.findWithDefault IS.empty dot (psSeen st)) -> loop st rest
            | otherwise ->
                let st1 = st {psSeen = IM.insertWith IS.union dot (IS.singleton o) (psSeen st)}
                 in case nextArr ! dot of
                      Just (N y) ->
                        let predicted = IS.member y (psPredicted st1)
                            st2 = st1 {psWaiting = IM.insertWith (++) y [(dot, o)] (psWaiting st1), psPredicted = IS.insert y (psPredicted st1)}
                            new = [(dotId q 0, j) | not predicted, q <- prodsOf y] ++ [(dot + 1, o) | IS.member y (psNull st1)]
                         in loop st2 (new ++ rest)
                      Just (T c)
                        | j < n && c == chars ! j -> loop st1 {psScan = (dot, o) : psScan st1} rest
                        | otherwise -> loop st1 rest
                      Nothing ->
                        let p = dotProd dot
                            x = leftArr ! p
                         in if not (followOk x j)
                              then loop st1 rest
                              else
                                let st2 = st1 {psDone = (p, o) : psDone st1}
                                 in if o == j
                                      then
                                        let st3 = st2 {psNull = IS.insert x (psNull st2)}
                                            advanced = [(d + 1, o') | (d, o') <- IM.findWithDefault [] x (psWaiting st2)]
                                         in loop st3 (advanced ++ rest)
                                      else
                                        let parents = IM.findWithDefault [] x (IM.findWithDefault IM.empty o waitings)
                                            advanced = [(d + 1, o') | (d, o') <- parents]
                                         in loop st2 (advanced ++ rest)

-- | The state of one position's item set.
data PS = PS
  { psSeen :: !(IM.IntMap IS.IntSet)
  -- ^ dotted production to its origins
  , psWaiting :: !(IM.IntMap [(Int, Int)])
  -- ^ nonterminal to the items waiting on it
  , psPredicted :: !IS.IntSet
  , psNull :: !IS.IntSet
  -- ^ nonterminals completed over the empty span here
  , psDone :: [(Int, Int)]
  -- ^ completed (production, origin) pairs that passed their follow restriction
  , psScan :: [(Int, Int)]
  -- ^ items whose next symbol is the character here
  }

emptyPS :: PS
emptyPS = PS IM.empty IM.empty IS.empty IS.empty [] []

------------------------------------------------------------------------
-- Derivations

-- | A value, the production indices visible to a priority check, and the
-- derivation.
data Deriv = Deriv Res [Int] DTree

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
          [ Deriv v (visibleIndices p children) (DTree p i j [t | (N _, _, _, Just (Deriv _ _ t)) <- children])
          | p <- fromMaybe [] (M.lookup key spans)
          , not (prodReject (prod p))
          , children <- splits anc (i, j) (prodRight (prod p)) i j
          , conflictsOk p children
          , Just v <- [prodAction (prod p) [r | (N _, _, _, Just (Deriv r _ _)) <- children]]
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
      let allChildren = [vs | (N _, _, _, Just (Deriv _ vs _)) <- children]
          nonEmpty = [vs | (N _, a, b, Just (Deriv _ vs _)) <- children, b > a]
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
          (N _, _, _, Just (Deriv _ vs _)) ->
            let leftEps = and (take k eps)
                rightEps = and (drop (k + 1) eps)
             in all (allowed leftEps rightEps) vs
          _ -> True
        allowed leftEps rightEps v = case M.lookup (p, v) (gPriority g) of
          Nothing -> True
          Just (gr, l, r, na) ->
            not (gr || ((r || na) && not rightEps && leftEps) || ((l || na) && not leftEps && rightEps))
