-- | haskott's extensions over Ott 0.34, which no Ott can check.
--
-- @test/extensions/@ holds one small specification per extension: quoted
-- terminals (@quoted_terminal.ott@), nested dot forms (@nested_dots.ott@),
-- shifted indices (@shifted_index.ott@) and Typst output with a filtered
-- document (@lambda.ott@ with @lambda.src.typ@). For each, the @haskott@
-- executable must accept the file and write exactly the recorded TeX and
-- Typst output beside it (@NAME.tex@, @NAME.typ@, and @lambda.doc.typ@ for
-- the filtered document). The recorded output was checked once against the
-- Ott fork the extensions were prototyped in; from then on it is a
-- regression record.
--
-- The Haskell 2010 report's formalisation uses every extension, so when
-- its checkout is found (at @../haskell-2010-revised-report/formalisation@,
-- or where @HASKOTT_REPORT_OTT@ points) @haskott check --picky@ must accept
-- each of its specifications; its output is not recorded here because the
-- report changes on its own.
--
-- Run from the repository root; @haskott@ is the executable cabal puts on
-- the path. Set @HASKOTT_RECORD=1@ to rewrite the recorded outputs.
module Main (main) where

import Control.Monad (filterM, forM, unless, when)
import qualified Data.ByteString as B
import Data.List (sort)
import Data.Maybe (fromMaybe)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, listDirectory)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath (replaceExtension, takeExtension, (</>))
import System.Process (readProcessWithExitCode)

main :: IO ()
main = do
  record <- (/= Nothing) <$> lookupEnv "HASKOTT_RECORD"
  let dir = "test" </> "extensions"
      tmp = "dist-newstyle" </> "extensions-tmp"
  createDirectoryIfMissing True tmp
  specs <- sort . filter ((== ".ott") . takeExtension) <$> listDirectory dir
  results <- forM specs $ \name -> do
    let spec = dir </> name
        outputs =
          [ (replaceExtension spec "tex", ["-i", spec, "-o", tmp </> replaceExtension name "tex"], tmp </> replaceExtension name "tex")
          , (replaceExtension spec "typ", ["-i", spec, "-o", tmp </> replaceExtension name "typ"], tmp </> replaceExtension name "typ")
          ]
    -- a NAME.src.typ beside the specification is filtered with it
    let srcDoc = replaceExtension spec "src.typ"
    hasDoc <- doesFileExist srcDoc
    let filtered =
          [ (replaceExtension spec "doc.typ", ["-i", spec, "-o", tmp </> replaceExtension name "typ", "-tex_wrap", "false", "-typst_filter", srcDoc, tmp </> replaceExtension name "doc.typ"], tmp </> replaceExtension name "doc.typ")
          | hasDoc
          ]
    checked <- run ["check", "--picky", spec]
    perOutput <- forM (outputs ++ filtered) $ \(golden, args, out) -> do
      (code, _, err) <- readProcessWithExitCode "haskott" args ""
      case code of
        ExitFailure _ -> pure [spec ++ ": haskott failed to write " ++ out ++ ": " ++ lastLine err]
        ExitSuccess -> do
          actual <- B.readFile out
          when record (B.writeFile golden actual)
          exists <- doesFileExist golden
          if not exists
            then pure [golden ++ ": no recorded output (set HASKOTT_RECORD=1 to record)"]
            else do
              expected <- B.readFile golden
              pure [golden ++ ": output changed at byte " ++ show (diffAt expected actual) | expected /= actual]
    pure (checked ++ concat perOutput)
  -- the report
  reportDir <- fromMaybe "../haskell-2010-revised-report/formalisation" <$> lookupEnv "HASKOTT_REPORT_OTT"
  hasReport <- doesDirectoryExist (reportDir </> "ott")
  reportResults <-
    if not hasReport
      then do
        putStrLn ("report not found at " ++ reportDir ++ "; skipped")
        pure []
      else do
        let spec files = run ("check" : "--picky" : [reportDir </> "ott" </> f | f <- files])
        present <- filterM (\f -> doesFileExist (reportDir </> "ott" </> f)) ["style.ott", "expressions.ott", "layout.ott"]
        concat <$> mapM (\f -> spec ["style.ott", f]) (filter (/= "style.ott") present)
  let failures = concat results ++ reportResults
  putStrLn (show (length specs) ++ " extension files, " ++ show (length failures) ++ " failures")
  mapM_ putStrLn failures
  unless (null failures) exitFailure
  where
    run args = do
      (code, out, err) <- readProcessWithExitCode "haskott" args ""
      pure [unwords args ++ ": exit " ++ show n ++ "\n" ++ out ++ err | ExitFailure n <- [code]]
    lastLine s = case reverse (filter (not . null) (lines s)) of
      (l : _) -> l
      [] -> ""
    diffAt a b = length (takeWhile id (B.zipWith (==) a b))
