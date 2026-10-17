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
import qualified Data.Map.Strict as M
import Haskott.Raw (rawDocument)
import Haskott.Raw.Show (showRaw)
import Haskott.Spec (Spec (..), Rule (..), Prod (..), Diagnostic (..))
import Haskott.Spec.Check (checkDocument)
import Haskott.Spec.Show (Class (..), Tok (..), homsText, prodTokens)
import Haskott.Syntax (parseDocument)
import Haskott.Defns (processDefns)
import Haskott.Term.Parse (ParsePolicy (..), makeTermParser, parseTerms)
import Haskott.Term.Requests (TermRequest (..), termRequests)
import Haskott.Term.Symterm (ppPlainSymterm)
import Haskott.Typst (defaultTypstOptions, makeTypst, typstDocument)
import Control.Exception (IOException, try)
import qualified Data.Text.Encoding.Error as TEE
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile)
import Data.List (isInfixOf, nub, sort)
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
      only = [s | ("--only", s) <- pairs args]
      ottDir = opt "--ott" (fromMaybe "../ott" envOtt)
      reportDir = opt "--report-ott" (fromMaybe "../haskell-2010-revised-report/formalisation" envReport)
      ott = ottDir </> "bin" </> "ott"
      resolve rel = case splitDirectories rel of
        ("ott" : more) -> ottDir </> joinPath more
        ("haskell-report-ott" : more) -> reportDir </> joinPath more
        _ -> rel
  table <- TIO.readFile "test/ott-acceptance.tsv"
  let entries =
        [ (T.unpack path, cls == "accepted")
        | line <- T.lines table
        , not (T.null line)
        , not ("#" `T.isPrefixOf` line)
        , let (cls, rest) = T.breakOn "\t" line
        , cls /= "parse-error"
        , let path = T.drop 1 rest
        , null only || any (`isInfixOf` T.unpack path) only
        ]
  results <- forM entries $ \(rel, ottAccepted) -> do
    let file = resolve rel
    bytes <- B.readFile file
    case TE.decodeUtf8' bytes of
      Left err -> pure (Just (rel ++ ": not valid UTF-8: " ++ show err))
      Right src -> case parseDocument src of
        Left e -> pure (Just (rel ++ ": haskott rejects: " ++ T.unpack (show' e)))
        Right tree -> do
          let raw = rawDocument tree
              mine = showRaw raw
          (_, out, _) <- readProcessWithExitCode ott ["-i", file, "-showraw", "true"] ""
          let theirs = dropVersionLine (T.pack out)
          case compareRaw rel mine theirs of
            Just failure -> pure (Just failure)
            Nothing -> do
              (_, sorted, _) <- readProcessWithExitCode ott ["-i", file, "-show_sort", "true"] ""
              let checked = checkDocument raw
              case compareChecked rel checked (T.pack sorted) of
                Just failure -> pure (Just failure)
                Nothing -> case checked of
                  Right spec | "AFTER CHECK, DISAMBIGUATE AND SORT" `T.isInfixOf` T.pack sorted -> do
                    termsResult <- compareTerms ott rel file spec
                    case termsResult of
                      Left failure -> pure (Just failure)
                      Right firstDiffers -> case compareAcceptance rel ottAccepted spec of
                        Just failure -> pure (Just failure)
                        Nothing
                          | firstDiffers -> do
                              putStrLn (rel ++ ": note: an ambiguous term's first parse differs from Ott's; Typst output not compared")
                              pure Nothing
                          | otherwise -> compareTypst ott rel file spec
                  _ -> pure Nothing
  let failures = [f | Just f <- results]
  putStrLn (show (length entries) ++ " files compared with ott -showraw, -show_sort, -parse and Typst output, " ++ show (length failures) ++ " disagreements")
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

-- | Compare the Typst output with Ott's, byte for byte. Ott is run on the
-- same path, so the header naming the sources agrees. When Ott fails to
-- produce output (it rejects some specifications only at output time),
-- the file is reported but not counted as a disagreement.
compareTypst :: FilePath -> FilePath -> FilePath -> Spec -> IO (Maybe String)
compareTypst ott rel file spec = do
  tmp <- getTemporaryDirectory
  let out = tmp </> "haskott-differential.typ"
  _ <- try (removeFile out) :: IO (Either IOException ())
  (code, _, err) <- readProcessWithExitCode ott ["-i", file, "-o", out] ""
  exists <- doesFileExist out
  if not exists
    then do
      putStrLn (rel ++ ": note: ott produced no Typst output (" ++ show code ++ "): " ++ take 200 (lastLine err))
      pure Nothing
    else do
      theirs <- B.readFile out
      let (env, _, _, processed, _) = makeTypst defaultTypstOptions False spec
          mine = TE.encodeUtf8 (typstDocument env (T.pack file) processed)
      if mine == theirs
        then pure Nothing
        else do
          let diffAt = length (takeWhile id (B.zipWith (==) mine theirs))
              context bs = T.unpack (TE.decodeUtf8With TEE.lenientDecode (B.take 160 (B.drop (max 0 (diffAt - 60)) bs)))
          pure (Just (rel ++ ": Typst output differs at byte " ++ show diffAt ++ "\n    haskott: " ++ show (context mine) ++ "\n    ott:     " ++ show (context theirs)))
  where
    lastLine s = case reverse (filter (not . null) (lines s)) of
      (l : _) -> l
      [] -> ""

-- | Ott accepts a file when, after the checks, every rule and clause
-- parses; haskott must agree, processing the definitions as Ott does
-- without a picky-parses option.
compareAcceptance :: FilePath -> Bool -> Spec -> Maybe String
compareAcceptance rel ottAccepted spec =
  let (_, diags) = processDefns (FirstIfSame []) (makeTermParser spec) spec
   in case (ottAccepted, diags) of
        (True, d : _) -> Just (rel ++ ": haskott reports a problem in the definitions of a file Ott accepts: " ++ T.unpack (diagMessage d))
        (False, []) -> Just (rel ++ ": haskott accepts the definitions of a file Ott rejects")
        _ -> Nothing

-- | Compare the parses of every term of the specification with Ott's: one
-- @ott -parse ':root: text'@ per term, in a single process, each printing
-- all parses in plain form.
-- Returns a disagreement, or whether some ambiguous term's first parse
-- differs from Ott's: Ott orders parses by OCaml's structural comparison
-- of its parse-forest nodes, which haskott does not reproduce, so such
-- files are noted and their Typst output is not compared.
compareTerms :: FilePath -> FilePath -> FilePath -> Spec -> IO (Either String Bool)
compareTerms ott rel file spec = do
  let requests = [r | r <- termRequests spec, not (T.null (T.strip (trText r)))]
  if null requests
    then pure (Right False)
    else do
      let args = ["-i", file] ++ concat [["-parse", ":" ++ T.unpack (trRoot r) ++ ": " ++ T.unpack (trText r)] | r <- requests]
      (_, out, _) <- readProcessWithExitCode ott args ""
      let blocks = ottParseBlocks (T.pack out)
          tp = makeTermParser spec
          mineOrdered = [map ppPlainSymterm (parseTerms tp (trRoot r) False (trText r)) | r <- requests]
          mine = map (nub . sort) mineOrdered
          theirs = map (nub . sort) blocks
          problems =
            [ T.unpack (trRoot r) ++ " " ++ show (trText r) ++ "\n    haskott: " ++ showParses a ++ "\n    ott:     " ++ showParses b
            | (r, a, b) <- zip3 requests mine (theirs ++ repeat ["<missing>"])
            , a /= b
            ]
          -- the first parse is the one taken when a term is ambiguous
          firstProblems =
            [ T.unpack (trRoot r) ++ " " ++ show (trText r) ++ " (first of " ++ show (length a) ++ " parses)\n    haskott: " ++ T.unpack a1 ++ "\n    ott:     " ++ T.unpack b1
            | (r, a1 : a, b1 : _) <- zip3 requests mineOrdered (blocks ++ repeat [])
            , a1 /= b1
            ]
      pure $
        if null blocks && "Error" `T.isInfixOf` T.pack out
          then Right False -- Ott stopped in its definitions before the test parses
          else if length blocks /= length requests
          then Left (rel ++ ": ott printed " ++ show (length blocks) ++ " parse blocks for " ++ show (length requests) ++ " terms")
          else
            if not (null problems)
              then Left (rel ++ ": " ++ show (length problems) ++ " of " ++ show (length requests) ++ " terms differ\n  " ++ unlines' (take 6 problems))
              else Right (not (null firstProblems))
  where
    showParses ps = case ps of
      [] -> "no parses"
      _ -> unwords' ps
    unwords' = foldr1 (\a b -> a ++ " | " ++ b) . map T.unpack
    unlines' = foldr1 (\a b -> a ++ "\n  " ++ b)

-- | The plain parses Ott printed for each @-parse@ request, in order.
ottParseBlocks :: T.Text -> [[T.Text]]
ottParseBlocks out = map plains (drop 1 (splitOn' (T.lines out)))
  where
    splitOn' ls = case break ("test parse: string " `T.isPrefixOf`) ls of
      (before, []) -> [before]
      (before, h : rest) -> before : splitOn' (h : rest `seq` restAfter rest)
    restAfter rest = rest
    plains = filter ("(St_" `T.isPrefixOf`)

-- | Compare the checked specification with Ott's @-show_sort@ printout:
-- Ott and haskott must agree on whether the file checks, and for every
-- production on its elements (by text and class) and its homs.
compareChecked :: FilePath -> Either Diagnostic Spec -> T.Text -> Maybe String
compareChecked rel result sorted =
  let ottAccepts = "AFTER CHECK, DISAMBIGUATE AND SORT" `T.isInfixOf` sorted
   in case (result, ottAccepts) of
        (Left d, True) -> Just (rel ++ ": haskott rejects a specification Ott checks: " ++ T.unpack (diagMessage d))
        (Right _, False) -> Just (rel ++ ": haskott checks a specification Ott rejects: " ++ firstError sorted)
        (Left _, False) -> Nothing
        (Right spec, True) ->
          let mine = M.fromList [(prodName p, (prodTokens p, normalise (homsText (prodHoms p)))) | r <- specRules spec, p <- ruleProds r]
              theirs = M.fromList (map parseProdLine (prodLines (T.lines sorted)))
              missing = M.keys (M.difference theirs mine)
              extra = M.keys (M.difference mine theirs)
              differing =
                [ T.unpack pn ++ "\n    haskott: " ++ showToks a ++ "  " ++ T.unpack ha ++ "\n    ott:     " ++ showToks b ++ "  " ++ T.unpack hb
                | (pn, ((a, ha), (b, hb))) <- M.toList (M.intersectionWith (,) mine theirs)
                , a /= b || ha /= hb
                ]
              problems =
                ["production " ++ T.unpack pn ++ " only in ott" | pn <- missing]
                  ++ ["production " ++ T.unpack pn ++ " only in haskott" | pn <- extra]
                  ++ differing
           in if null problems then Nothing else Just (rel ++ ":\n  " ++ unlines' (take 8 problems) ++ (if length problems > 8 then "\n  ... and " ++ show (length problems - 8) ++ " more" else ""))
  where
    unlines' = foldr1 (\a b -> a ++ "\n  " ++ b)
    firstError s = case filter ("Error" `T.isInfixOf`) (T.lines (stripAnsi s)) of
      (l : _) -> T.unpack l
      [] -> "(no error line found)"
    showToks = unwords . map (\(Tok c t) -> T.unpack t ++ "/" ++ cls c)
    cls c = case c of
      CN -> "n"
      CM -> "m"
      CT -> "t"
      CP -> "p"
    normalise = T.unwords . T.words

-- | The production lines of @-show_sort@, each joined with the lines a
-- multi-line hom spills onto.
prodLines :: [T.Text] -> [T.Text]
prodLines ls = case ls of
  [] -> []
  l : more
    | "  | " `T.isPrefixOf` l ->
        let (cont, rest) = span continuation more
         in T.unwords (l : cont) : prodLines rest
    | otherwise -> prodLines more
  where
    continuation x =
      not (T.null x) && not ("  | " `T.isPrefixOf` x) && not (":: '' ::=" `T.isInfixOf` x)
        && not ("metavar " `T.isPrefixOf` x) && x /= "grammar"

-- | A production line of @-show_sort@: elements with their colours, the
-- first plain @::@, the production name, then the homs. Ott quotes a
-- terminal that spells one of its own tokens; the quotes are dropped here.
parseProdLine :: T.Text -> (T.Text, ([Tok], T.Text))
parseProdLine line =
  let toks = map classify (T.words (T.drop 4 line))
      (els, rest) = break (== Tok CP "::") toks
   in case rest of
        (_ : Tok _ pn : homs) -> (pn, (els, T.unwords [t | Tok _ t <- homs]))
        _ -> ("?", (els, ""))
  where
    classify w
      | Just r <- T.stripPrefix "\ESC[0;33m" w = Tok CN (unquote (stripAnsi r))
      | Just r <- T.stripPrefix "\ESC[0;31m" w = Tok CM (unquote (stripAnsi r))
      | Just r <- T.stripPrefix "\ESC[0;32m" w = Tok CT (unquote (stripAnsi r))
      | otherwise = Tok CP (stripAnsi w)
    unquote x
      | T.length x >= 3 && T.head x == '\'' && T.last x == '\'' = T.init (T.tail x)
      | otherwise = x

stripAnsi :: T.Text -> T.Text
stripAnsi t = case T.breakOn "\ESC[" t of
  (before, after)
    | T.null after -> before
    | otherwise -> before <> stripAnsi (T.drop 1 (T.dropWhile (/= 'm') after))

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
