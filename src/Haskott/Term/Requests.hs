{-# LANGUAGE OverloadedStrings #-}

-- | The terms a specification asks the term parser to parse: the
-- premises, conclusions and formulas of its rules, the quotations in its
-- embedded premises and comment blocks, and its function clauses, each
-- with the root it is parsed from (Ott's @defns.ml@).
module Haskott.Term.Requests
  ( TermRequest (..)
  , Role (..)
  , termRequests
  , ruleNameParse
  , embeddedQuotations
  , embeddedSplit
  ) where

import Data.Char (isAlpha, isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import Graft
import Haskott.Spec

data Role = Premise | Conclusion | Formula | Quotation | Clause
  deriving (Eq, Show)

data TermRequest = TermRequest
  { trRoot :: Text
  , trText :: Text
  , trRole :: Role
  , trProd :: Text
  -- ^ for a conclusion, the production name of the definition
  , trRange :: TextRange
  }
  deriving (Eq, Show)

termRequests :: Spec -> [TermRequest]
termRequests spec = concatMap fromClass (specDefnClasses spec) ++ concatMap fromFunClass (specFunClasses spec)
  where
    fromClass dc = concatMap (fromDefn dc) (dcDefns dc)
    fromDefn dc d = concatMap (fromRule (dcWrapper dc <> dName d)) (dBody d)
    fromRule pn r = case r of
      LinedRule premises _ _ conclusions range _ _ ->
        concatMap (premise range) premises ++ [TermRequest "formula" c Conclusion pn range | c <- conclusions]
      LinelessRule ls range -> [TermRequest "formula" (T.intercalate " " ls) Formula pn range | not (null ls)]
      DefnComRule es range -> [TermRequest "user_syntax" q Quotation pn range | q <- [s | EmbedInner s <- es]]
    premise range s =
      let (s', _) = ruleNameParse s
       in case embeddedQuotations s' of
            Just qs -> [TermRequest "user_syntax" q Quotation "" range | q <- qs]
            Nothing -> [TermRequest "formula" s' Premise "" range]
    fromFunClass fc = [TermRequest (fcName fc) c Clause (fdName fd) (fdRange fd) | fd <- fcDefns fc, c <- fdClauses fd]

-- | A premise may end with @[[:name]]@, naming it for the Coq back end.
-- Returns the premise without it, and the name.
ruleNameParse :: Text -> (Text, Maybe Text)
ruleNameParse s =
  let trimmed = T.dropWhileEnd (== ' ') s
   in case T.stripSuffix "]]" trimmed of
        Nothing -> (s, Nothing)
        Just beforeClose ->
          let name = T.takeWhileEnd isAlphaNum beforeClose
              beforeName = T.dropEnd (T.length name) beforeClose
           in if not (T.null name) && isAlpha (T.head name) && "[[:" `T.isSuffixOf` beforeName
                then (T.dropEnd 3 beforeName, Just name)
                else (s, Nothing)

-- | Ott recognises an embedded premise by matching @ *{{ *\(.*\)}} *@ at
-- the start of the line only: after spaces the text begins with @{{@ and
-- contains @}}@; the body runs to the last @}}@ and whatever follows is
-- dropped. Returns the body (between the braces) and the text after the
-- closing braces.
embeddedSplit :: Text -> Maybe (Text, Text)
embeddedSplit s = case T.stripPrefix "{{" (T.dropWhile (== ' ') s) of
  Nothing -> Nothing
  Just rest -> case T.breakOnEnd "}}" rest of
    (body, after) | "}}" `T.isSuffixOf` body -> Just (T.dropEnd 2 body, after)
    _ -> Nothing

-- | A premise of the shape @{{ ... }}@ is embedded prover code; its
-- @[[ ... ]]@ quotations are the terms to parse.
embeddedQuotations :: Text -> Maybe [Text]
embeddedQuotations s = quotations . fst <$> embeddedSplit s
  where
    quotations t = case T.breakOn "[[" t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let (q, after) = T.breakOn "]]" (T.drop 2 rest)
             in q : quotations (T.drop 2 after)
