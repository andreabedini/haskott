{-# LANGUAGE OverloadedStrings #-}

-- | A property test of rename over the acceptance corpus: in every file
-- Ott accepts, every root that can be renamed is renamed to a fresh name
-- and back, and the second rename must give back the original bytes.
-- Refusing the first rename is allowed (a line that does not parse, an
-- ambiguous identifier), and the suite reports refusals by reason; a
-- crash, a refusal on the way back, or a round trip that does not
-- restore the files is a failure. Roots that could not be given
-- back their name (a keyword, quoted in the source) are skipped. The
-- Haskell report is renamed together with its filtered document.
module Main (main) where

import Control.Exception (ErrorCall, evaluate, try)
import Control.Monad (forM, unless)
import qualified Data.ByteString as B
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Haskott.Load (Loaded (..), loadSpec)
import Haskott.Rename
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (joinPath, splitDirectories, (</>))

main :: IO ()
main = do
  ottDir <- fromMaybe "../ott" <$> lookupEnv "HASKOTT_OTT"
  reportDir <- fromMaybe "../haskell-2010-revised-report/formalisation" <$> lookupEnv "HASKOTT_REPORT_OTT"
  let resolve rel = case splitDirectories rel of
        ("ott" : more) -> ottDir </> joinPath more
        ("haskell-report-ott" : more) -> reportDir </> joinPath more
        _ -> rel
  table <- TIO.readFile "test/ott-acceptance.tsv"
  let accepted =
        [ T.unpack path
        | line <- T.lines table
        , let (cls, rest) = T.breakOn "\t" line
        , cls == "accepted"
        , let path = T.drop 1 rest
        , not ("haskell-report-ott" `T.isPrefixOf` path)
        ]
      report =
        ( "haskell-report-ott"
        , ["haskell-report-ott/ott/style.ott", "haskell-report-ott/ott/expressions.ott"]
        , ["haskell-report-ott/doc/report.src.typ"]
        )
      cases = [(f, [f], []) | f <- accepted] ++ [report]
  results <- forM cases $ \(label, specs, docs) -> do
    specTexts <- mapM (\f -> (,) f <$> readText (resolve f)) specs
    docTexts <- mapM (\f -> (,) f <$> readText (resolve f)) docs
    case loadSpec specTexts of
      Left _ -> pure [] -- checks only with options, or fails later in Ott
      Right l -> forM (filter validNewName (renameableRoots (ldSpec l))) $ \r -> do
        outcome <- roundTrip specTexts docTexts r
        pure (label, r, outcome)
  let all' = concat results
      failures = [(f, r, m) | (f, r, Failed m) <- all']
      refusals = M.fromListWith (+) [(reason m, 1 :: Int) | (_, _, Refused m) <- all']
      examples = M.fromListWith (\_ a -> a) [(reason m, (f, r, m)) | (f, r, Refused m) <- all']
      ok = length [() | (_, _, Restored) <- all']
  putStrLn (show (length all') ++ " renames in " ++ show (length (filter (not . null) results)) ++ " files: " ++ show ok ++ " round trips, " ++ show (sum (M.elems refusals)) ++ " refusals, " ++ show (length failures) ++ " failures")
  mapM_
    ( \(m, n) -> do
        putStrLn ("  refused " ++ show n ++ "x: " ++ T.unpack m)
        case M.lookup m examples of
          Just (f, r, full) -> putStrLn ("    for example " ++ f ++ ", " ++ T.unpack r ++ ":\n    " ++ T.unpack (T.replace "\n" "\n    " (T.take 700 full)))
          Nothing -> pure ()
    )
    (sortOn (negate . snd) (M.toList refusals))
  mapM_ (\(f, r, m) -> putStrLn (f ++ ": " ++ T.unpack r ++ ": " ++ T.unpack m)) failures
  unless (null failures) exitFailure
  where
    -- the kind of refusal, without the names in it
    reason m = T.unwords (filter (not . quoted) (T.words (T.takeWhile (/= '\n') m)))
    quoted w = "\"" `T.isPrefixOf` w

data Outcome = Restored | Refused T.Text | Failed T.Text

roundTrip :: [(FilePath, T.Text)] -> [(FilePath, T.Text)] -> T.Text -> IO Outcome
roundTrip specs docs r = do
  let fresh = r <> "Qz"
  first <- guarded (renameRoot r fresh specs docs)
  case first of
    Left m -> pure (Failed ("crash: " <> m))
    Right (Left ps) -> pure (Refused (messages ps))
    Right (Right renamed) -> do
      let n = length specs
          specs' = [(frPath x, frNew x) | x <- take n renamed]
          docs' = [(frPath x, frNew x) | x <- drop n renamed]
      second <- guarded (renameRoot fresh r specs' docs')
      pure $ case second of
        Left m -> Failed ("crash on the way back: " <> m)
        Right (Left ps) -> Failed ("refused on the way back: " <> messages ps)
        Right (Right back)
          | map frNew back == map snd (specs ++ docs) -> Restored
          | otherwise -> Failed "the round trip does not restore the files"
  where
    messages = T.intercalate "; " . map problemMessage
    guarded x = do
      e <- try (evaluate (forceResult x)) :: IO (Either ErrorCall (Either [Problem] [FileRename]))
      pure (either (Left . T.pack . show) Right e)
    forceResult x = case x of
      Left ps -> sum (map (T.length . problemMessage) ps) `seq` x
      Right rs -> sum (map (T.length . frNew) rs) `seq` x

readText :: FilePath -> IO T.Text
readText f = TE.decodeUtf8With (\_ _ -> Just '\xfffd') <$> B.readFile f
