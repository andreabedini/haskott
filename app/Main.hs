{-# LANGUAGE OverloadedStrings #-}
-- | A development front end for the parser.
--
-- @haskott check FILE...@ parses each file and reports success or the first
-- error. @haskott dump FILE@ prints the lossless tree.
module Main (main) where

import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Graft.Range (rangeStart)
import Haskott.Defns (processDefns)
import Haskott.Raw (rawDocument)
import Haskott.Raw.Show (showRaw)
import Haskott.Spec (Diagnostic (..))
import Haskott.Spec.Check (checkDocument)
import Haskott.Spec.Show (showSpec)
import Haskott.Syntax
import Haskott.Term.Parse (makeTermParser, parseTerms)
import Haskott.Term.Splice (spliceTerms)
import Haskott.Term.Symterm (ppPlainSymterm)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("check" : files@(_ : _)) -> do
      let (picky, files') = (any (== "--picky") files, filter (/= "--picky") files)
      results <- mapM (checkFile picky) files'
      if and results then pure () else exitFailure
    ["showraw", file] -> do
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> TIO.putStr (showRaw (rawDocument tree))
    ["spec", file] -> do
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> case checkDocument (rawDocument tree) of
          Left d -> reportDiagnostic file src d >> exitFailure
          Right spec -> TIO.putStr (showSpec spec)
    ["parse", file, request] -> do
      -- like ott -parse ':root: text': every parse, in plain form
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> case checkDocument (rawDocument tree) of
          Left d -> putStrLn (T.unpack (diagMessage d)) >> exitFailure
          Right spec -> do
            let tp = makeTermParser spec
                (root, rest) = T.breakOn ":" (T.drop 1 (T.pack request))
                text = T.drop 1 rest
                parses = parseTerms tp root False text
            if null parses
              then putStrLn "no parses"
              else mapM_ (TIO.putStrLn . ppPlainSymterm) parses
    ["dump", file] -> do
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> TIO.putStr (dumpTree tree)
    ["dump", "--terms", file] -> do
      -- the tree after stage two
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> case checkDocument (rawDocument tree) of
          Left d -> reportDiagnostic file src d >> exitFailure
          Right spec -> do
            let (tree', _, _) = spliceTerms False (makeTermParser spec) tree
            TIO.putStr (dumpTree tree')
    _ -> do
      hPutStrLn stderr "usage: haskott check [--picky] FILE...\n       haskott dump [--terms] FILE\n       haskott showraw FILE\n       haskott spec FILE\n       haskott parse FILE \":root: text\""
      exitFailure

readSource :: FilePath -> IO T.Text
readSource file = do
  bytes <- B.readFile file
  case TE.decodeUtf8' bytes of
    Left err -> do
      hPutStrLn stderr (file ++ ": not valid UTF-8: " ++ show err)
      exitFailure
    Right t -> pure t

-- | The whole pipeline on one file: parse, check, process the definitions.
checkFile :: Bool -> FilePath -> IO Bool
checkFile picky file = do
  src <- readSource file
  case parseDocument src of
    Left e -> reportError file src e >> pure False
    Right tree
      | render tree /= src -> putStrLn (file ++ ": PARSED BUT DOES NOT ROUND-TRIP") >> pure False
      | otherwise -> case checkDocument (rawDocument tree) of
          Left d -> reportDiagnostic file src d >> pure False
          Right spec -> do
            let (tree', tp, warnings) = spliceTerms picky (makeTermParser spec) tree
                (_, diags) = processDefns picky tp spec
            mapM_ (reportDiagnostic file src) diags
            mapM_ (\d -> reportDiagnostic file src d {diagMessage = "warning: " <> diagMessage d}) warnings
            if render tree' /= src
              then putStrLn (file ++ ": TERMS DO NOT ROUND-TRIP") >> pure False
              else if null diags then putStrLn (file ++ ": ok") >> pure True else pure False

reportDiagnostic :: FilePath -> T.Text -> Diagnostic -> IO ()
reportDiagnostic file src d =
  let (l, c) = offsetPosition src (rangeStart (diagRange d))
   in putStrLn (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (diagMessage d))

reportError :: FilePath -> T.Text -> ParseError -> IO ()
reportError file src e =
  let (l, c) = parseErrorPosition src e
   in putStrLn (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (parseErrorMessage e))

-- | Line and column of a byte offset.
offsetPosition :: T.Text -> Int -> (Int, Int)
offsetPosition src off = parseErrorPosition src (ParseError off T.empty)
