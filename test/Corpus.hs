{-# LANGUAGE OverloadedStrings #-}
-- | The acceptance corpus (GRAMMAR.md §8).
--
-- @test/ott-acceptance.tsv@ records, for every @.ott@ file in Ott's
-- @tests/@ and @examples/@ directories and for the Haskell report's
-- @expressions.ott@, what Ott 0.34 (fork) did with it: @accepted@,
-- @other-error@ (parsed, then failed later), or @parse-error@. It is
-- produced by @scripts/ott-acceptance.zsh@. This suite checks that haskott
-- parses exactly the files Ott parses, and that rendering a parsed file
-- gives the input back, before and after the rule lines are parsed as
-- terms.
--
-- Paths in the table start with @ott/@ or @haskell-report-ott/@. Those
-- prefixes name the checkouts of ott and haskell-report-ott, found next to
-- this repository by default, or where @HASKOTT_OTT@ and
-- @HASKOTT_REPORT_OTT@ point.
module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.ByteString as B
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Haskott.Raw (rawDocument)
import Haskott.Spec.Check (checkDocument)
import Haskott.Syntax
import Haskott.Term.Parse (ParsePolicy (..), makeTermParser)
import Haskott.Term.Splice (spliceTerms)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (splitDirectories, joinPath, (</>))

data Expectation = ShouldParse | ShouldFail
  deriving (Eq, Show)

main :: IO ()
main = do
  ottDir <- fromMaybe "../ott" <$> lookupEnv "HASKOTT_OTT"
  reportDir <- fromMaybe "../haskell-report-ott" <$> lookupEnv "HASKOTT_REPORT_OTT"
  let resolve rel = case splitDirectories rel of
        ("ott" : more) -> ottDir </> joinPath more
        ("haskell-report-ott" : more) -> reportDir </> joinPath more
        _ -> rel
  table <- TIO.readFile "test/ott-acceptance.tsv"
  let entries =
        [ (expectation cls, T.unpack path)
        | line <- T.lines table
        , not (T.null line)
        , not ("#" `T.isPrefixOf` line)
        , let (cls, rest) = T.breakOn "\t" line
        , let path = T.drop 1 rest
        ]
  results <- forM entries $ \(expected, rel) -> do
    bytes <- B.readFile (resolve rel)
    case TE.decodeUtf8' bytes of
      -- GRAMMAR.md §2.1: haskott rejects what is not UTF-8. That agrees with
      -- Ott only when Ott rejects the file too.
      Left err
        | expected == ShouldFail -> pure Nothing
        | otherwise -> pure (Just (rel ++ ": not valid UTF-8: " ++ show err))
      Right src -> pure (check rel expected src)
  let failures = [f | Just f <- results]
  putStrLn (show (length entries) ++ " files, " ++ show (length failures) ++ " disagreements")
  mapM_ putStrLn failures
  unless (null failures) exitFailure
  where
    expectation cls
      | cls == "parse-error" = ShouldFail
      | otherwise = ShouldParse

check :: FilePath -> Expectation -> T.Text -> Maybe String
check rel expected src = case (expected, parseDocument src) of
  (ShouldParse, Left e) ->
    let (l, c) = parseErrorPosition src e
     in Just (rel ++ ":" ++ show l ++ ":" ++ show c ++ ": rejected, Ott accepts: " ++ T.unpack (parseErrorMessage e))
  (ShouldParse, Right tree)
    | render tree /= src -> Just (rel ++ ": does not round-trip")
    | otherwise -> case checkDocument (rawDocument tree) of
        Left _ -> Nothing
        Right spec ->
          -- stage two: the tree with its rule lines parsed still renders
          -- to the source
          let (tree', _, _) = spliceTerms (FirstIfSame []) (makeTermParser spec) tree
           in if render tree' /= src then Just (rel ++ ": does not round-trip after the term splice") else Nothing
  (ShouldFail, Right _) -> Just (rel ++ ": accepted, Ott rejects")
  (ShouldFail, Left _) -> Nothing
