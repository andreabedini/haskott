{-# LANGUAGE OverloadedStrings #-}

-- | Error recovery on the acceptance corpus.
--
-- Every file, including those Ott rejects, parses with recovery into a
-- tree that renders back to the input, and the first error it reports is
-- the one the strict parser stops at (none when the strict one succeeds).
-- And for the first three productions of every file that parses, breaking that one production (an unclosed @</@
-- after its bar) costs exactly that production: the recovering parser
-- reports one error, the production becomes an error node, and every
-- other item, rule, production and definition is still there. Parsing
-- resumes at the start of a line, so the productions written after the
-- broken one on the same line go with it.
module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.ByteString as B
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Graft
import qualified Graft.Cursor as Cursor
import qualified Graft.Range as Range
import Haskott.Syntax
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (joinPath, splitDirectories, (</>))

main :: IO ()
main = do
  ottDir <- fromMaybe "../ott" <$> lookupEnv "HASKOTT_OTT"
  let resolve rel = case splitDirectories rel of
        ("ott" : more) -> ottDir </> joinPath more
        _ -> rel
  table <- TIO.readFile "test/ott-acceptance.tsv"
  let rels = [T.unpack (T.drop 1 rest) | l <- T.lines table, not ("#" `T.isPrefixOf` l), not (T.null l), let (_, rest) = T.breakOn "\t" l]
  results <- forM rels $ \rel -> do
    bytes <- B.readFile (resolve rel)
    case TE.decodeUtf8' bytes of
      Left _ -> pure ([], 0)
      Right src -> pure (checkFile rel src)
  let failures = concatMap fst results
      mutations = sum (map snd results)
  putStrLn (show (length rels) ++ " files and " ++ show mutations ++ " broken productions, " ++ show (length failures) ++ " failures")
  mapM_ putStrLn failures
  unless (null failures) exitFailure

checkFile :: FilePath -> T.Text -> ([String], Int)
checkFile rel src =
  let (tree, errs) = parseDocumentRecovering src
      roundTrip = [rel ++ ": the recovering parse does not round-trip" | render tree /= src]
      strict = case (parseDocument src, errs) of
        (Left e, e' : _) | e /= e' -> [rel ++ ": the first recovered error is not the strict one"]
        (Left _, []) -> [rel ++ ": the strict parse fails but the recovering one reports nothing"]
        (Right _, _ : _) -> [rel ++ ": the recovering parse reports an error the strict one does not"]
        _ -> []
      mutated = case parseDocument src of
        Right t -> [mutate rel src t bar (sameLine (TE.encodeUtf8 src) bar (barOffsets t)) | bar <- take 3 (barOffsets t)]
        Left _ -> []
   in (roundTrip ++ strict ++ concat mutated, length mutated)

-- | The offsets just after the bar of each production.
barOffsets :: GreenNode Kind -> [Int]
barOffsets t =
  [ fromIntegral (Range.end (Cursor.range b))
  | c <- Cursor.descendants (Cursor.fromGreen (Node t))
  , Cursor.kind c == Prod
  , b <- take 1 [x | x <- Cursor.children c, Cursor.kind x == Bar]
  ]

-- | The productions from this one to the end of its line.
sameLine :: B.ByteString -> Int -> [Int] -> Int
sameLine srcBytes off bars = 1 + length [b | b <- bars, b > off, not (B.elem 10 (B.take (b - off) (B.drop off srcBytes)))]

mutate :: FilePath -> T.Text -> GreenNode Kind -> Int -> Int -> [String]
mutate rel src t off lost =
  let bytes = TE.encodeUtf8 src
      src' = TE.decodeUtf8 (B.take off bytes <> " </" <> B.drop off bytes)
      (t', errs) = parseDocumentRecovering src'
      before = counts t
      after = counts t'
      expected = M.insertWith (+) ErrorItem 1 (M.adjust (subtract lost) Prod before)
      label = rel ++ " (production at byte " ++ show off ++ ")"
   in [label ++ ": does not round-trip" | render t' /= src']
        ++ [label ++ ": " ++ show (length errs) ++ " errors, expected 1" | length errs /= 1]
        ++ [label ++ ": the tree lost more than the production: " ++ show (M.toList (M.filter (/= 0) (M.unionWith (-) expected after))) | M.filter (/= 0) expected /= M.filter (/= 0) after]

-- | The number of nodes of each structural kind.
counts :: GreenNode Kind -> M.Map Kind Int
counts t =
  M.fromListWith (+)
    [ (Cursor.kind c, 1)
    | c <- Cursor.descendants (Cursor.fromGreen (Node t))
    , Cursor.kind c `elem` [Prod, Rule, ErrorItem, MetavarDecl, GrammarSection, Defns, Defn, DRule, Funs, Fundefn, Subrule, Substitution, Embed, HomsItem]
    ]
