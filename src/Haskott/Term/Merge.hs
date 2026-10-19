-- | Anti-unification of symbolic terms, behind dot forms in terms:
-- @e1 : t1 , .. , en : tn@ is accepted when the two sides merge into one
-- body @e[0] : t[0]@ with a single varying pair of suffix items, the bound
-- @1..n@. Ott's @merge.ml@ for symterms, including the fork's shifted
-- indices (@e_1 = f e_0 .. e_n = f e_n-1@, where the pairs @(0,n-1)@ are
-- the canonical pair @(1,n)@ shifted by one).
module Haskott.Term.Merge
  ( mergeSteListShifts
  , abstractIndexvarSte
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Haskott.Spec.Suffix
import Haskott.Term.Symterm

type Pair = (SuffixItem, SuffixItem)

-- | How a differing pair of suffix items is treated.
data Mode
  = Plain
  | Canonical Pair
  -- ^ pairs that are shifts of this one become shifted indices

-- | Merge two element lists, trying shifted indices when the plain merge
-- fails. 'Nothing' when they do not merge; otherwise the varying pair, if
-- any, and the merged elements.
mergeSteListShifts :: [Ste] -> [Ste] -> Maybe (Maybe Pair, [Ste])
mergeSteListShifts es es' = case mergeSteList Plain 0 es es' of
  Just r -> Just r
  Nothing ->
    let pairs = collectSteList es es'
        unshifted (a, b) = all (\si -> case si of SiVar _ o -> o == 0; _ -> True) [a, b]
        -- Ott's remove_duplicates keeps the last occurrence of each pair
        candidates = removeDuplicatesLast (filter unshifted pairs ++ pairs)
        try cs = case cs of
          [] -> Nothing
          c : more -> case mergeSteList (Canonical c) 0 es es' of
            Just r -> Just r
            Nothing -> try more
     in try candidates

-- | Ott's @remove_duplicates@: an element that occurs again later is
-- dropped, so the last occurrence survives.
removeDuplicatesLast :: Eq a => [a] -> [a]
removeDuplicatesLast xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicatesLast more else x : removeDuplicatesLast more

------------------------------------------------------------------------
-- Collecting the varying pairs (Ott's collected_pbos)

collectSteList :: [Ste] -> [Ste] -> [Pair]
collectSteList es es'
  | length es /= length es' = []
  | otherwise = concat (zipWith collectSte es es')

collectSte :: Ste -> Ste -> [Pair]
collectSte a b = case (a, b) of
  (SteSt s, SteSt s') -> collectSt s s'
  (SteMetavar m (r, suff), SteMetavar _ (r', suff')) | m == m' && r == r' -> collectSuffix suff suff'
    where
      m' = m
  (SteList xs, SteList ys) | length xs == length ys -> concat (zipWith collectStli xs ys)
  _ -> []

collectStli :: Stli -> Stli -> [Pair]
collectStli a b = case (a, b) of
  (StliSingle xs, StliSingle ys) -> collectSteList xs ys
  (StliListform _ xs, StliListform _ ys) -> collectSteList xs ys
  _ -> []

collectSt :: Symterm -> Symterm -> [Pair]
collectSt a b = case (a, b) of
  (StNode n p es, StNode n' p' es') | n == n' && p == p' -> collectSteList es es'
  (StNonterm _ (r, s), StNonterm _ (r', s')) | r == r' -> collectSuffix s s'
  (StNontermSub _ _ (r, s), StNontermSub _ _ (r', s')) | r == r' -> collectSuffix s s'
  _ -> []

collectSuffix :: Suffix -> Suffix -> [Pair]
collectSuffix s s'
  | length s /= length s' = []
  | otherwise = [(a, b) | (a, b) <- zip s s', a /= b, isNumOrVar a, isNumOrVar b]

------------------------------------------------------------------------
-- Merging

mergeSteList :: Mode -> Int -> [Ste] -> [Ste] -> Maybe (Maybe Pair, [Ste])
mergeSteList mode depth es es' = do
  if length es /= length es' then Nothing else Just ()
  xs <- sequence (zipWith (mergeSte mode depth) es es')
  pbo <- combinePairs (map fst xs)
  Just (pbo, map snd xs)

combinePairs :: [Maybe Pair] -> Maybe (Maybe Pair)
combinePairs pbos = case [p | Just p <- pbos] of
  [] -> Just Nothing
  p : more -> if all (== p) more then Just (Just p) else Nothing

mergeSte :: Mode -> Int -> Ste -> Ste -> Maybe (Maybe Pair, Ste)
mergeSte mode depth a b = case (a, b) of
  (SteSt s, SteSt s') -> do
    (pbo, s'') <- mergeSt mode depth s s'
    Just (pbo, SteSt s'')
  (SteMetavar m (r, suff), SteMetavar _ (r', suff')) | r == r' -> do
    (pbo, suff'') <- mergeSuffixMode mode depth suff suff'
    Just (pbo, SteMetavar m (r, suff''))
  (SteVar m v, SteVar m' v') | m == m' && v == v' -> Just (Nothing, a)
  (SteList xs, SteList ys) -> do
    if length xs /= length ys then Nothing else Just ()
    items <- sequence (zipWith (mergeStli mode depth) xs ys)
    pbo <- combinePairs (map fst items)
    Just (pbo, SteList (map snd items))
  _ -> Nothing

mergeStli :: Mode -> Int -> Stli -> Stli -> Maybe (Maybe Pair, Stli)
mergeStli mode depth a b = case (a, b) of
  (StliSingle xs, StliSingle ys) -> do
    (pbo, zs) <- mergeSteList mode depth xs ys
    Just (pbo, StliSingle zs)
  (StliListform bd xs, StliListform bd' ys) -> do
    (pboB, bd'') <- mergeBound depth bd bd'
    (pboE, zs) <- mergeSteList mode (depth + 1) xs ys
    pbo <- case (pboB, pboE) of
      (Nothing, p) -> Just p
      (p, Nothing) -> Just p
      (Just y, Just y') | y == y' -> Just pboB
      _ -> Nothing
    Just (pbo, StliListform bd'' zs)
  _ -> Nothing

-- | The bounds of the inner lists of a nested dot form may vary with the
-- outer index, as in @(1..k1)@ and @(1..kn)@.
mergeBound :: Int -> Bound -> Bound -> Maybe (Maybe Pair, Bound)
mergeBound depth b b'
  | b == b' = Just (Nothing, b)
  | otherwise = case (b, b') of
      (BoundDotform lo up n, BoundDotform lo' up' n') | n == n' -> do
        (pl, lower) <- item lo lo'
        (pu, upper) <- item up up'
        pbo <- case (pl, pu) of
          (Nothing, p) -> Just p
          (p, Nothing) -> Just p
          (Just y, Just y') | y == y' -> Just pl
          _ -> Nothing
        Just (pbo, BoundDotform lower upper n)
      _ -> Nothing
  where
    item si si'
      | si == si' = Just (Nothing, si)
      | otherwise = case (si, si') of
          (SiIndexed v x, SiIndexed v' x') | v == v' && isNumOrVar x && isNumOrVar x' -> Just (Just (x, x'), SiIndexed v (SiIndex depth))
          _ -> Nothing

mergeSt :: Mode -> Int -> Symterm -> Symterm -> Maybe (Maybe Pair, Symterm)
mergeSt mode depth a b = case (a, b) of
  (StNode n p es, StNode n' p' es') | n == n' && p == p' -> do
    (pbo, es'') <- mergeSteList mode depth es es'
    Just (pbo, StNode n p es'')
  (StNonterm p (r, s), StNonterm _ (r', s')) | r == r' -> do
    (pbo, s'') <- mergeSuffixMode mode depth s s'
    Just (pbo, StNonterm p (r, s''))
  (StNontermSub lo top (r, s), StNontermSub lo' top' (r', s')) | lo == lo' && top == top' && r == r' -> do
    (pbo, s'') <- mergeSuffixMode mode depth s s'
    Just (pbo, StNontermSub lo top (r, s''))
  (StUninterpreted _ s, StUninterpreted _ s') | s == s' -> Just (Nothing, a)
  _ -> Nothing

-- | 'mergeSuffix' with the canonical-pair treatment of differing items.
mergeSuffixMode :: Mode -> Int -> Suffix -> Suffix -> Maybe (Maybe Pair, Suffix)
mergeSuffixMode mode depth suff suff' = case mode of
  Plain -> mergeSuffix depth suff suff'
  Canonical c
    | length suff /= length suff' -> mergeSuffix depth suff suff'
    | otherwise -> do
        items <- mapM (mergeItem c) (zip suff suff')
        pbo <- combinePairs (map fst items)
        Just (pbo, map snd items)
  where
    mergeItem c (x, y)
      | x == y = Just (Nothing, x)
      | isNumOrVar x && isNumOrVar y =
          if c /= (x, y)
            then case shiftAgainst c (x, y) of
              Just k -> Just (Just c, SiIndexShift depth k)
              Nothing -> Just (Just (x, y), SiIndex depth)
            else Just (Just (x, y), SiIndex depth)
      | otherwise = Nothing

-- | The non-zero @k@ such that the pair is the canonical pair shifted by
-- @k@, if any.
shiftAgainst :: Pair -> Pair -> Maybe Int
shiftAgainst (c, c') (x, x') = do
  k <- case (c, x) of
    (SiNum s, SiNum s') -> (-) <$> readInt s' <*> readInt s
    (SiVar v o, SiVar v' o') | v == v' -> Just (o' - o)
    _ -> Nothing
  if k == 0 then Nothing else Just ()
  sc <- shiftItem k c
  sc' <- shiftItem k c'
  if sc == x && sc' == x' then Just k else Nothing

readInt :: Text -> Maybe Int
readInt t = case TR.signed TR.decimal t of
  Right (n, rest) | T.null rest -> Just n
  _ -> Nothing

shiftItem :: Int -> SuffixItem -> Maybe SuffixItem
shiftItem k si = case si of
  SiNum s -> (\n -> SiNum (T.pack (show (n + k)))) <$> readInt s
  SiVar v o -> Just (SiVar v (o + k))
  _ -> Nothing

-- | Replace every occurrence of an index variable in a symterm element by
-- the de Bruijn index of the enclosing comprehension (Ott's
-- @abstract_indexvar_symterm_element@, which does not require linearity).
abstractIndexvarSte :: Text -> Int -> Ste -> Ste
abstractIndexvarSte ivr depth ste = case ste of
  SteSt st -> SteSt (abstractSt st)
  SteMetavar m (r, suff) -> SteMetavar m (r, abstractSuffix suff)
  SteVar _ _ -> ste
  SteList items -> SteList (map abstractStli items)
  where
    abstractSuffix = map item
    item si = case si of
      SiVar v 0 | v == ivr -> SiIndex depth
      _ -> si
    abstractSt st = case st of
      StNode n p es -> StNode n p (map (abstractIndexvarSte ivr depth) es)
      StNonterm p (r, suff) -> StNonterm p (r, abstractSuffix suff)
      StNontermSub lo top (r, suff) -> StNontermSub lo top (r, abstractSuffix suff)
      StUninterpreted _ _ -> st
    abstractStli stli = case stli of
      StliSingle es -> StliSingle (map (abstractIndexvarSte ivr depth) es)
      StliListform b es -> StliListform b (map (abstractIndexvarSte ivr (depth + 1)) es)
