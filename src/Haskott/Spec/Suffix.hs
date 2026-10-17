{-# LANGUAGE OverloadedStrings #-}

-- | Identifiers, suffixes and the merging of suffixes behind dot forms.
--
-- An identifier in a production or a term is a declared root followed by a
-- suffix of numbers, primes, underscores and index variables (Ott manual,
-- "Reference: The language of symbolic terms"). This module reproduces
-- Ott's @make_ident_lexer@ (@term_parser.ml@): every way of splitting an
-- identifier into a root and a suffix is a parse, and an identifier with
-- several parses is an error, with none a terminal. It also reproduces the
-- part of @merge.ml@ that anti-unifies the two sides of a dot form such as
-- @x1 .. xn@ into one element @x[0]@ with the bound @1..n@.
module Haskott.Spec.Suffix
  ( SuffixItem (..)
  , Suffix
  , Bound (..)
  , ppSuffix
  , ppSuffixItem
  , Roots (..)
  , IdentTok (..)
  , lexIdent
  , parseUpperBound
  , isNumOrVar
  , mergeSuffix
  , abstractIndexvarSuffix
  , AbstractResult (..)
  ) where

import Data.Char (isDigit)
import Data.Text (Text)
import qualified Data.Text as T

data SuffixItem
  = SiNum Text
  | SiPunct Text
  | SiVar Text Int
  -- ^ an index variable and an offset, 0 or -1
  | SiIndex Int
  -- ^ a de Bruijn index to the enclosing list form
  | SiIndexed Text SuffixItem
  -- ^ the fork's nested dot forms: an index variable with a subscript
  | SiIndexShift Int Int
  deriving (Eq, Ord, Show)

type Suffix = [SuffixItem]

data Bound
  = BoundDotform SuffixItem SuffixItem Int
  -- ^ lower, upper, dot length (0, 1 or 2)
  | BoundComp Text
  | BoundCompU Text SuffixItem
  | BoundCompLU Text SuffixItem SuffixItem Int
  deriving (Eq, Ord, Show)

ppSuffix :: Suffix -> Text
ppSuffix = T.concat . map ppSuffixItem

ppSuffixItem :: SuffixItem -> Text
ppSuffixItem si = case si of
  SiNum s -> s
  SiPunct s -> s
  SiVar s n -> s <> offset n
  SiIndex i -> "[" <> T.pack (show i) <> "]"
  SiIndexed s si' -> s <> ppSuffixItem si'
  SiIndexShift i k -> "[" <> T.pack (show i) <> "]" <> offset k
  where
    offset n
      | n == 0 = ""
      | n > 0 = "+" <> T.pack (show n)
      | otherwise = T.pack (show n)

-- | The declared roots a lexer is built from.
data Roots = Roots
  { rootsNonindexMetavars :: [Text]
  , rootsIndexvars :: [Text]
  , rootsNonterms :: [Text]
  }

data IdentTok
  = TokMetavar Text Suffix
  | TokNonterm Text Suffix
  deriving (Eq, Show)

-- | All parses of an identifier as a root and a suffix. An index variable
-- parses only on its own, without a suffix.
lexIdent :: Roots -> Text -> [IdentTok]
lexIdent roots s =
  [TokMetavar s [] | s `elem` rootsIndexvars roots]
    ++ [TokMetavar r suff | r <- rootsNonindexMetavars roots, Just rest <- [T.stripPrefix r s], suff <- parseSuffix (rootsIndexvars roots) rest]
    ++ [TokNonterm r suff | r <- rootsNonterms roots, Just rest <- [T.stripPrefix r s], suff <- parseSuffix (rootsIndexvars roots) rest]

-- | All parses of a suffix: runs of digits, @'@, @_@, and index variables
-- with an optional @-1@. Each digit is an item of its own in the grammar
-- and runs are joined afterwards, as Ott does.
parseSuffix :: [Text] -> Text -> [Suffix]
parseSuffix indexvars = map agglomerate . go
  where
    go t
      | T.null t = [[]]
      | otherwise = concat [map (si :) (go rest) | (si, rest) <- item t]
    item t =
      [(SiNum (T.singleton c), T.drop 1 t) | Just (c, _) <- [T.uncons t], isDigit c]
        ++ [(SiPunct (T.singleton c), T.drop 1 t) | Just (c, _) <- [T.uncons t], c == '\'' || c == '_']
        ++ concat
          [ (SiVar v 0, rest) : [(SiVar v (-1), rest') | Just rest' <- [T.stripPrefix "-1" rest]]
          | v <- indexvars
          , Just rest <- [T.stripPrefix v t]
          ]
    agglomerate sis = case sis of
      SiNum a : SiNum b : more -> agglomerate (SiNum (a <> b) : more)
      si : more -> si : agglomerate more
      [] -> []

-- | The upper bound of a comprehension @i IN 1..n@: an index variable with
-- an optional @-1@. All parses.
parseUpperBound :: [Text] -> Text -> [SuffixItem]
parseUpperBound indexvars s =
  [SiVar v 0 | v <- indexvars, v == s]
    ++ [SiVar v (-1) | v <- indexvars, s == v <> "-1"]

isNumOrVar :: SuffixItem -> Bool
isNumOrVar si = case si of
  SiNum _ -> True
  SiVar _ _ -> True
  _ -> False

-- | Anti-unify two suffixes at a depth: equal items stay, exactly one pair
-- of differing numbers or index variables becomes the de Bruijn index and
-- is returned as the varying pair. 'Nothing' when the suffixes cannot be
-- merged. Ott's @merge_suffix@ without the shifted-index case, which only
-- arises inside symbolic terms.
mergeSuffix :: Int -> Suffix -> Suffix -> Maybe (Maybe (SuffixItem, SuffixItem), Suffix)
mergeSuffix depth suff suff'
  | length suff' == length suff + 1 = indexedUpper
  | length suff /= length suff' = Nothing
  | otherwise = do
      items <- mapM mergeItem (zip suff suff')
      let varying = [p | (Just p, _) <- items]
      pbo <- case varying of
        [] -> Just Nothing
        [p] -> Just (Just p)
        _ -> Nothing
      Just (pbo, map snd items)
  where
    mergeItem (a, b)
      | a == b = Just (Nothing, a)
      | isNumOrVar a && isNumOrVar b = Just (Just (a, b), SiIndex depth)
      | otherwise = Nothing
    -- p_1_1 .. p_1_k1: the upper suffix has an index variable with a
    -- subscript where the lower has a single varying item
    indexedUpper =
      let n = length suff
          candidates =
            [ ((si, SiIndexed v si'), pre ++ [SiIndex depth] ++ post)
            | k <- [0 .. n]
            , let (pre, rest) = splitAt k suff
            , let (pre', rest') = splitAt k suff'
            , pre == pre'
            , (si : post) <- [rest]
            , (SiVar v 0 : si' : post') <- [rest']
            , post == post'
            , isNumOrVar si
            , isNumOrVar si'
            ]
       in case candidates of
            [(pb, s'')] -> Just (Just pb, s'')
            _ -> Nothing

data AbstractResult = Abstracted Suffix | NotLinear

-- | Replace the one occurrence of an index variable in a suffix by the de
-- Bruijn index of the enclosing comprehension; an error when it does not
-- occur exactly once (Ott's @abstract_indexvar_suffix_linear@).
abstractIndexvarSuffix :: Text -> Int -> Suffix -> AbstractResult
abstractIndexvarSuffix ivr depth suff =
  let (suff', n) = foldr step ([], 0 :: Int) suff
      step si (acc, c) = case si of
        SiVar v 0 | v == ivr -> (SiIndex depth : acc, c + 1)
        _ -> (si : acc, c)
   in if n == 1 then Abstracted suff' else NotLinear
