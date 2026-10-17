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
          let raw = rawDocument tree
              mine = showRaw raw
          (_, out, _) <- readProcessWithExitCode ott ["-i", file, "-showraw", "true"] ""
          let theirs = dropVersionLine (T.pack out)
          case compareRaw rel mine theirs of
            Just failure -> pure (Just failure)
            Nothing -> do
              (_, sorted, _) <- readProcessWithExitCode ott ["-i", file, "-show_sort", "true"] ""
              pure (compareChecked rel (checkDocument raw) (T.pack sorted))
  let failures = [f | Just f <- results]
  putStrLn (show (length entries) ++ " files compared with ott -showraw and -show_sort, " ++ show (length failures) ++ " disagreements")
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
