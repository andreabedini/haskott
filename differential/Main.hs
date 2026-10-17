{-# LANGUAGE OverloadedStrings #-}

-- | Compare haskott with the Ott binary over the acceptance corpus.
--
-- For every corpus file Ott parses, this runs @ott -i FILE -showraw true@
-- and checks that Ott's printout of its raw parse starts with haskott's
-- rendering of the same parse ('Haskott.Raw.Show.showRaw'). Ott prints
-- the raw parse before anything else, so a prefix match means the two
-- parses agree; the first differing line is reported otherwise.
--
-- Usage: haskott-differential [--ott DIR] [--report-ott DIR]
module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.ByteString as B
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Haskott.Raw (rawDocument)
import Haskott.Raw.Show (showRaw)
import Haskott.Syntax (parseDocument)
import System.Environment (getArgs, lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (joinPath, splitDirectories, (</>))
import System.Process (readProcessWithExitCode)

main :: IO ()
main = do
  args <- getArgs
  envOtt <- lookupEnv "HASKOTT_OTT"
  envReport <- lookupEnv "HASKOTT_REPORT_OTT"
  let opt flag def = fromMaybe def (lookup flag (pairs args))
      ottDir = opt "--ott" (fromMaybe "../ott" envOtt)
      reportDir = opt "--report-ott" (fromMaybe "../haskell-report-ott" envReport)
      ott = ottDir </> "bin" </> "ott"
      resolve rel = case splitDirectories rel of
        ("ott" : more) -> ottDir </> joinPath more
        ("haskell-report-ott" : more) -> reportDir </> joinPath more
        _ -> rel
  table <- TIO.readFile "test/ott-acceptance.tsv"
  let entries =
        [ T.unpack path
        | line <- T.lines table
        , not (T.null line)
        , not ("#" `T.isPrefixOf` line)
        , let (cls, rest) = T.breakOn "\t" line
        , cls /= "parse-error"
        , let path = T.drop 1 rest
        ]
  results <- forM entries $ \rel -> do
    let file = resolve rel
    bytes <- B.readFile file
    case TE.decodeUtf8' bytes of
      Left err -> pure (Just (rel ++ ": not valid UTF-8: " ++ show err))
      Right src -> case parseDocument src of
        Left e -> pure (Just (rel ++ ": haskott rejects: " ++ T.unpack (show' e)))
        Right tree -> do
          let mine = showRaw (rawDocument tree)
          (_, out, _) <- readProcessWithExitCode ott ["-i", file, "-showraw", "true"] ""
          let theirs = dropVersionLine (T.pack out)
          pure (compareRaw rel mine theirs)
  let failures = [f | Just f <- results]
  putStrLn (show (length entries) ++ " files compared with ott -showraw, " ++ show (length failures) ++ " disagreements")
  mapM_ putStrLn failures
  unless (null failures) exitFailure
  where
    pairs (k : v : more) = (k, v) : pairs more
    pairs _ = []
    show' e = T.pack (show e)

dropVersionLine :: T.Text -> T.Text
dropVersionLine t = case T.lines t of
  (first : _) | "Ott version" `T.isPrefixOf` first -> T.drop (T.length first + 1) t
  _ -> t

compareRaw :: FilePath -> T.Text -> T.Text -> Maybe String
compareRaw rel mine theirs
  | mine `T.isPrefixOf` theirs = Nothing
  | otherwise =
      let common = length (takeWhile id (zipWith (==) (T.unpack mine) (T.unpack theirs)))
          lineNo = T.count "\n" (T.take common mine) + 1
          mineLine = lineAt lineNo mine
          theirLine = lineAt lineNo theirs
       in Just (rel ++ ": differs at raw line " ++ show lineNo ++ "\n  haskott: " ++ show mineLine ++ "\n  ott:     " ++ show theirLine)
  where
    lineAt n t = case drop (n - 1) (T.lines t) of
      (l : _) -> T.unpack l
      [] -> "<end>"
