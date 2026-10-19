{-# LANGUAGE OverloadedStrings #-}

-- | Ott's @bounds.ml@: the bounds of the dot forms and comprehensions of a
-- rule or clause, and from them the dot environment its terms are printed
-- in. Each bound gets a compound list variable (@l_p_list@ for the
-- elements @l@ and @p@ of @l1 p1 .. ln pn@) and a pattern, and a
-- nonterminal written with an index variable of a bound (@lj@) is a
-- projection from that list.
module Haskott.Prover.Bounds
  ( boundExtraction
  , boundsConsistency
  , sieProject
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Prover.Pp
import Haskott.Prover.Types
import Haskott.Spec
import Haskott.Term.Symterm

sieProject, sieNull :: Suffix
sieProject = [SiPunct "_"]
sieNull = [SiPunct ""]

type Item = ((NtMv, SubntrData), Maybe Bound)

-- | Ott's @findbounds@: the bound a suffix refers to; with several, the
-- innermost.
findBounds :: [Bound] -> Suffix -> Maybe Bound
findBounds be suff = case [i | si <- suff, Just i <- [index si]] of
  [] -> Nothing
  is -> Just (be !! minimum' is)
  where
    index si = case si of
      SiIndex i -> Just i
      SiIndexShift i _ -> Just i
      _ -> Nothing
    minimum' is = case is of
      i : more -> foldl' min i more
      [] -> 0

ntOrMvOfSymterm :: [Bound] -> Symterm -> [Item]
ntOrMvOfSymterm be st = case st of
  StNode _ _ es -> concatMap (ntOrMvOfSte be) es
  StNonterm _ (ntr, sf) -> [(((Ntr ntr, sf), Nothing), findBounds be sf)]
  StNontermSub ntrl ntrt (ntr, sf) -> [(((Ntr ntr, sf), Just (ntrl, ntrt)), findBounds be sf)]
  StUninterpreted _ -> []

ntOrMvOfSte :: [Bound] -> Ste -> [Item]
ntOrMvOfSte be ste = case ste of
  SteSt st -> ntOrMvOfSymterm be st
  SteMetavar _ (mvr, sf) -> [(((Mvr mvr, sf), Nothing), findBounds be sf)]
  SteVar _ _ -> []
  SteList stlis -> concatMap stli stlis
  where
    stli s = case s of
      StliSingle es -> concatMap (ntOrMvOfSte be) es
      StliListform b es -> concatMap (ntOrMvOfSte (b : be)) es

-- | Ott's @check_length_consistency@: the bounds, each once.
checkLengthConsistency :: [Item] -> Either Text [Bound]
checkLengthConsistency xys =
  let bounds = removeDuplicates [b | (_, Just b) <- xys]
      f acc bs = case bs of
        [] -> Right ()
        b@(BoundDotform lo up n) : more -> case lookup (lo, up) acc of
          Just i
            | i == n -> f acc more
            | otherwise -> Left ("bound " <> ppPlainBound b <> " has inconsistent length constraints, \"" <> dots i <> "\" and \"" <> dots n <> "\"")
          Nothing -> f (((lo, up), n) : acc) more
        _ : more -> f acc more
      dots n = T.replicate (n + 2) "."
   in bounds <$ f [] bounds

-- | Ott's @check_bounds_consistency@: each nonterminal or metavariable
-- once, with its bound, most recent first.
checkBoundsConsistency :: [Item] -> Either Text [Item]
checkBoundsConsistency = go []
  where
    go acc xbos = case xbos of
      [] -> Right acc
      (x, bo) : more -> case lookup x acc of
        Nothing -> go ((x, bo) : acc) more
        Just bo'
          | bo == bo' -> go acc more
          | otherwise -> Left ("inconsistent bounds for " <> plainNtMv (fst x) <> ": " <> plainBo bo <> " and " <> plainBo bo')
    plainBo bo = maybe "None: " (\b -> ppPlainBound b <> ": ") bo

plainNtMv :: NtMv -> Text
plainNtMv (r, suff) = (case r of Ntr n -> n; Mvr n -> n) <> T.concat (map ppPlainSuffixItem suff)

-- | Ott's @split_bounded@.
splitBounded :: [Item] -> ([(NtMv, SubntrData)], [((NtMv, SubntrData), Bound)])
splitBounded = foldl' step ([], [])
  where
    step (a1, a2) (x, bo) = case bo of
      Nothing -> (x : a1, a2)
      Just b -> (a1, (x, b) : a2)

-- | Ott's @nt_or_mv_per_bound@.
ntOrMvPerBound :: [((NtMv, SubntrData), Bound)] -> [(Bound, [(NtMv, SubntrData)])]
ntOrMvPerBound = foldl' step []
  where
    step acc (x, y) = case lookup y acc of
      Just xs0 -> (y, xs0 ++ [x]) : removeAssoc y acc
      Nothing -> (y, [x]) : acc
    removeAssoc y acc = case acc of
      [] -> []
      (k, v) : more -> if k == y then more else (k, v) : removeAssoc y more

-- | Ott's @sie_for_suffix@: the environment repeated to cover every
-- index of the suffix.
sieForSuffix :: Suffix -> Suffix -> Suffix
sieForSuffix sie suff =
  let depth = foldl' (\d si -> case si of SiIndex i -> max d (i + 1); SiIndexShift i _ -> max d (i + 1); _ -> d) 1 suff
   in concat (replicate depth sie)

dotenv1 :: Env -> [(Bound, [(NtMv, SubntrData)])] -> De1
dotenv1 env = map one
  where
    one (bound, ntmvsns) =
      let pp1 = [ppNtOrMvWithSie env (sieForSuffix sieProject (snd ntmv)) ntmv | (ntmv, _) <- ntmvsns]
          pp1Null = [ppNtOrMvWithSie env (sieForSuffix sieNull (snd ntmv)) ntmv | (ntmv, _) <- ntmvsns]
          rootTy ((r, _), _) = ppNtOrMvRootTy env (promoteNtmvr env (primaryNtmvr env r))
          coqTypePp1 = if isCoq env then map rootTy ntmvsns else ["dummy"]
          holTypePp1 = if isHol env || isLem env then map rootTy ntmvsns else ["dummy"]
          many = length pp1 > 1
          wrap t = if many then "(" <> t <> ")" else t
       in ( bound
          , De1i
              { de1Ntmvsns = ntmvsns
              , de1CompoundId = T.intercalate "_" pp1Null <> "_list"
              , de1Pattern = wrap (T.intercalate "," pp1)
              , de1CoqTypeOfPattern = wrap (T.intercalate "*" coqTypePp1)
              , de1HolTypeOfCompoundId = wrap (T.intercalate "#" holTypePp1) <> " list"
              }
          )

-- | Ott's @merge_nobound@: a nonterminal without a bound written with an
-- index variable of one with a bound (@xj@ of @x1 .. xn@).
mergeNobound :: [((NtMv, SubntrData), Bound)] -> (NtMv, SubntrData) -> ((NtMv, SubntrData), Maybe (Suffix, SuffixItem, Bound))
mergeNobound xbs x@((ntmvr, suff), sd) = case xbs of
  [] -> (x, Nothing)
  (((ntmvr', suff'), sd'), bound) : more
    | ntmvr == ntmvr' && sd == sd' -> case mergeSuffixAgainstIndex suff suff' of
        Just (Just (si, _), suff'') -> (x, Just (suff'', si, bound))
        Just (Nothing, _) -> error "Haskott.Prover.Bounds: cannot happen"
        Nothing -> mergeNobound more x
    | otherwise -> mergeNobound more x

-- | Ott's @merge_suffix_against_index 0@.
mergeSuffixAgainstIndex :: Suffix -> Suffix -> Maybe (Maybe (SuffixItem, SuffixItem), Suffix)
mergeSuffixAgainstIndex suff suff'
  | length suff /= length suff' = Nothing
  | otherwise = do
      xs <- mapM item (zip suff suff')
      case [p | (Just p, _) <- xs] of
        [] -> Just (Nothing, map snd xs)
        [p] -> Just (Just p, map snd xs)
        _ -> Nothing
  where
    item (a, b)
      | a == b = Just (Nothing, a)
      | isNumOrVar a && isIndex b = Just (Just (a, b), SiIndex 0)
      | otherwise = Nothing
    isIndex si = case si of
      SiIndex _ -> True
      _ -> False

-- | Nested dot forms and shifted indices are only typeset.
isNestedDotForm :: Item -> Bool
isNestedDotForm (((_, suff), _), bo) =
  length [() | si <- suff, isIdx si] > 1
    || any isShift suff
    || ( case bo of
           Just (BoundDotform lo up _) -> any isIndexed [lo, up]
           _ -> False
       )
  where
    isIdx si = case si of
      SiIndex _ -> True
      SiIndexShift _ _ -> True
      _ -> False
    isShift si = case si of
      SiIndexShift _ _ -> True
      _ -> False
    isIndexed si = case si of
      SiIndexed _ _ -> True
      _ -> False

-- | Ott's @bound_extraction@ for a prover: the dot environment of the
-- terms and the nonterminals and metavariables that are not projections,
-- or why the bounds are inconsistent.
boundExtraction :: Env -> [Symterm] -> Either Text (De, De3)
boundExtraction env sts = do
  let x = concatMap (ntOrMvOfSymterm []) sts
  if any isNestedDotForm x
    then Left "nested dot forms and shifted indices are only supported in TeX, Typst and ASCII output"
    else pure ()
  _ <- checkLengthConsistency x
  withBoundopts <- checkBoundsConsistency x
  let (without, with) = splitBounded withBoundopts
      de1 = dotenv1 env (ntOrMvPerBound with)
      y = map (mergeNobound with) without
      de2 = [(ntmv, z) | ((ntmv, _), Just z) <- y]
      de3 = [(ntmv, sd) | ((ntmv, sd), Nothing) <- y]
  pure ((de1, de2), de3)

-- | The checks of Ott's @bound_extraction@ that do not depend on the
-- target, which it makes for TeX output too: each dot form's bound has
-- one length, and each nonterminal or metavariable one bound.
boundsConsistency :: [Symterm] -> Either Text ()
boundsConsistency sts = do
  let x = concatMap (ntOrMvOfSymterm []) sts
  _ <- checkLengthConsistency x
  _ <- checkBoundsConsistency x
  pure ()
