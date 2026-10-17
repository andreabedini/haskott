{-# LANGUAGE OverloadedStrings #-}

-- | The command line.
--
-- With Ott's options (@-i FILE@, @-o FILE.typ@, @-typst_filter SRC DST@,
-- @-picky_multiple_parses BOOL@, @-tex_name_prefix P@, ...) haskott runs
-- the whole pipeline and writes Typst output, so that it can stand in for
-- @ott@ in a Makefile. The development subcommands @check@, @dump@,
-- @showraw@, @spec@ and @parse@ look at one stage each.
module Main (main) where

import Control.Monad (forM, forM_, unless, when)
import qualified Data.ByteString as B
import Data.List (isSuffixOf)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Graft.Green (GreenElement (..), GreenNode, greenNode, greenToken, nodeChildren, nodeKind)
import Graft.Range (TextRange, rangeEnd, rangeStart, textRange)
import Haskott.Defns (processDefns)
import Haskott.Raw (rawDocument)
import Haskott.Raw.Show (showRaw)
import Haskott.Spec (Diagnostic (..))
import Haskott.Spec.Check (checkDocument)
import Haskott.Spec.Show (showSpec)
import Haskott.Syntax
import Haskott.Term.Parse
import Haskott.Term.Splice (spliceTerms)
import Haskott.Term.Symterm (ppPlainSymterm)
import Haskott.Typst
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
            let (tree', _, _) = spliceTerms (FirstIfSame []) (makeTermParser spec) tree
            TIO.putStr (dumpTree tree')
    (('-' : _) : _) -> ottMain args
    _ -> do
      hPutStrLn stderr "usage: haskott [-i FILE]... [-o FILE.typ]... [-typst_filter SRC DST]... [OPTION]...\n       haskott check [--picky] FILE...\n       haskott dump [--terms] FILE\n       haskott showraw FILE\n       haskott spec FILE\n       haskott parse FILE \":root: text\""
      exitFailure

------------------------------------------------------------------------
-- Ott's command line

data Options = Options
  { oInputs :: [FilePath]
  , oOutputs :: [FilePath]
  , oFilters :: [(FilePath, FilePath)]
  , oPicky :: Bool
  , oTypst :: TypstOptions
  }

parseOptions :: [String] -> Either String Options
parseOptions = go (Options [] [] [] False defaultTypstOptions)
  where
    go o args = case args of
      [] -> Right o {oInputs = reverse (oInputs o), oOutputs = reverse (oOutputs o), oFilters = reverse (oFilters o)}
      "-i" : f : rest -> go o {oInputs = f : oInputs o} rest
      "-o" : f : rest -> go o {oOutputs = f : oOutputs o} rest
      "-typst_filter" : s : d : rest -> go o {oFilters = (s, d) : oFilters o} rest
      "-picky_multiple_parses" : b : rest -> bool b >>= \v -> go o {oPicky = v} rest
      "-tex_name_prefix" : p : rest -> go (typst o (\t -> t {optPrefix = T.pack p})) rest
      "-tex_show_meta" : b : rest -> bool b >>= \v -> go (typst o (\t -> t {optShowMeta = v})) rest
      "-tex_show_categories" : b : rest -> bool b >>= \v -> go (typst o (\t -> t {optShowCategories = v})) rest
      "-tex_colour" : b : rest -> bool b >>= \v -> go (typst o (\t -> t {optColour = v})) rest
      "-tex_wrap" : b : rest -> bool b >>= \v -> go (typst o (\t -> t {optWrap = v})) rest
      "-tex_suppress_category" : c : rest -> go (typst o (\t -> t {optSuppressedCategories = optSuppressedCategories t ++ [T.pack c]})) rest
      "-tex_suppress_ntr" : n : rest -> go (typst o (\t -> t {optSuppressedNtrs = optSuppressedNtrs t ++ [T.pack n]})) rest
      f : rest | ".ott" `isSuffixOf` f -> go o {oInputs = f : oInputs o} rest
      opt : _ -> Left ("unknown option or argument " ++ show opt)
    bool b = case b of
      "true" -> Right True
      "false" -> Right False
      _ -> Left ("expected true or false, found " ++ show b)
    typst o f = o {oTypst = f (oTypst o)}

ottMain :: [String] -> IO ()
ottMain args = do
  opts <- either (\m -> hPutStrLn stderr m >> exitFailure) pure (parseOptions args)
  when (null (oInputs opts)) $ hPutStrLn stderr "no input files" >> exitFailure
  forM_ (oOutputs opts) $ \o ->
    unless (".typ" `isSuffixOf` o) $ hPutStrLn stderr ("only Typst output is implemented; cannot write " ++ o) >> exitFailure
  -- parse every file; the raw documents are concatenated, with the
  -- offsets of later files shifted past the earlier ones so that a
  -- diagnostic finds its file
  inputs <- forM (oInputs opts) $ \f -> do
    src <- readSource f
    case parseDocument src of
      Left e -> reportError f src e >> exitFailure
      Right tree -> pure (f, src, tree)
  let bases = scanl (+) 0 [B.length (TE.encodeUtf8 src) | (_, src, _) <- inputs]
      files = zip bases inputs
      raw = concat [rawDocument (shiftTree base tree) | (base, (_, _, tree)) <- files]
      sources = T.pack (unwords (oInputs opts))
      locate d =
        let off = rangeStart (diagRange d)
            (base, (f, src, _)) = case [x | x@(b, _) <- files, b <= off] of
              [] -> (0, headInput)
              xs -> last xs
         in (f, src, d {diagRange = shiftRange (negate base) (diagRange d)})
      headInput = case inputs of
        (x : _) -> x
        [] -> error "no inputs"
      report d = let (f, src, d') = locate d in reportDiagnostic f src d'
  spec <- case checkDocument raw of
    Left d -> report d >> exitFailure
    Right spec -> pure spec
  let typstWanted = not (null (oOutputs opts)) || not (null (oFilters opts))
      (env, policy0, tp0, processed0, diags0) = makeTypst (oTypst opts) (oPicky opts) spec
      -- without a Typst target, several parses of a term are no error
      (policy, processed, diags)
        | typstWanted || oPicky opts = (policy0, processed0, diags0)
        | otherwise = let (pr, ds) = processDefns (FirstIfSame []) tp0 spec in (FirstIfSame [], pr, ds)
      -- stage two on every tree, for its warnings about quotations
      warnings = concat [map (shiftDiag base) ws | (base, (_, _, tree)) <- files, let (_, _, ws) = spliceTerms policy tp0 tree]
  mapM_ report diags
  mapM_ (\d -> report d {diagMessage = "warning: " <> diagMessage d}) warnings
  forM_ (oOutputs opts) $ \o -> writeText o (typstDocument env sources processed)
  forM_ (oFilters opts) $ \(s, d) -> do
    src <- readSource s
    case filterDocument env src of
      Left m -> hPutStrLn stderr (s ++ ": " ++ T.unpack m) >> exitFailure
      Right out -> writeText d out
  let counts = countsString processed
  unless (T.null counts) (TIO.putStr counts)
  unless (null diags) exitFailure
  where
    shiftDiag base d = d {diagRange = shiftRange base (diagRange d)}

-- | A document tree whose offsets start at the base: the real children
-- behind a space token of that length.
shiftTree :: Int -> GreenNode Kind -> GreenNode Kind
shiftTree base tree
  | base == 0 = tree
  | otherwise = greenNode (nodeKind tree) (Token (greenToken Space (T.replicate base " ")) : nodeChildren tree)

shiftRange :: Int -> TextRange -> TextRange
shiftRange n r = fromMaybe r (textRange (rangeStart r + n) (rangeEnd r + n))

writeText :: FilePath -> T.Text -> IO ()
writeText f = B.writeFile f . TE.encodeUtf8

------------------------------------------------------------------------
-- Development subcommands

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
            let policy = if picky then Picky else FirstIfSame []
                (tree', tp, warnings) = spliceTerms policy (makeTermParser spec) tree
                (_, diags) = processDefns policy tp spec
            mapM_ (reportDiagnostic file src) diags
            mapM_ (\d -> reportDiagnostic file src d {diagMessage = "warning: " <> diagMessage d}) warnings
            if render tree' /= src
              then putStrLn (file ++ ": TERMS DO NOT ROUND-TRIP") >> pure False
              else if null diags then putStrLn (file ++ ": ok") >> pure True else pure False

reportDiagnostic :: FilePath -> T.Text -> Diagnostic -> IO ()
reportDiagnostic file src d =
  let (l, c) = offsetPosition src (rangeStart (diagRange d))
   in hPutStrLn stderr (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (diagMessage d))

reportError :: FilePath -> T.Text -> ParseError -> IO ()
reportError file src e =
  let (l, c) = parseErrorPosition src e
   in hPutStrLn stderr (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (parseErrorMessage e))

-- | Line and column of a byte offset.
offsetPosition :: T.Text -> Int -> (Int, Int)
offsetPosition src off = parseErrorPosition src (ParseError off T.empty)
