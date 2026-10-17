-- | A development front end for the parser.
--
-- @haskott check FILE...@ parses each file and reports success or the first
-- error. @haskott dump FILE@ prints the lossless tree.
module Main (main) where

import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Haskott.Syntax
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("check" : files@(_ : _)) -> do
      results <- mapM checkFile files
      if and results then pure () else exitFailure
    ["dump", file] -> do
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> TIO.putStr (dumpTree tree)
    _ -> do
      hPutStrLn stderr "usage: haskott check FILE...\n       haskott dump FILE"
      exitFailure

readSource :: FilePath -> IO T.Text
readSource file = do
  bytes <- B.readFile file
  case TE.decodeUtf8' bytes of
    Left err -> do
      hPutStrLn stderr (file ++ ": not valid UTF-8: " ++ show err)
      exitFailure
    Right t -> pure t

checkFile :: FilePath -> IO Bool
checkFile file = do
  src <- readSource file
  case parseDocument src of
    Left e -> reportError file src e >> pure False
    Right tree
      | render tree == src -> putStrLn (file ++ ": ok") >> pure True
      | otherwise -> putStrLn (file ++ ": PARSED BUT DOES NOT ROUND-TRIP") >> pure False

reportError :: FilePath -> T.Text -> ParseError -> IO ()
reportError file src e =
  let (l, c) = parseErrorPosition src e
   in putStrLn (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (parseErrorMessage e))
