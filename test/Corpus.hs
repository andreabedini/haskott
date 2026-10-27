{-# LANGUAGE OverloadedStrings #-}
-- | The acceptance corpus (GRAMMAR.md §8).
--
-- @test/ott-acceptance.tsv@ records, for every @.ott@ file in Ott's
-- @tests/@ and @examples/@ directories, what Ott 0.34 did with it:
-- @accepted@, @other-error@ (parsed, then failed later), or @parse-error@.
-- It is produced by @scripts/ott-acceptance.zsh@. This suite checks that
-- haskott parses exactly the files Ott parses, and that rendering a parsed
-- file gives the input back, before and after the rule lines are parsed as
-- terms, and that the first problem @haskott check@ reports for each file
-- is still the one in @test/first-diagnostics.tsv@. 'inlineCases' cover
-- what the corpus does not exercise.
--
-- Paths in the table start with @ott/@, which names the checkout of
-- upstream Ott, found at @../ott@ by default or where @HASKOTT_OTT@ points.
module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.ByteString as B
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import qualified Graft.Range as Range
import Haskott.Defns (processDefns)
import Haskott.Raw (rawDocument)
import Haskott.Spec (Diagnostic (..))
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
  let resolve rel = case splitDirectories rel of
        ("ott" : more) -> ottDir </> joinPath more
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
  -- the inline cases: the first problem is the recorded one, and a file
  -- that parses round-trips
  let inlineFailures =
        concat
          [ [name ++ ": first problem\n  expected: " ++ T.unpack expected ++ "\n  got:      " ++ T.unpack actual | actual /= expected]
              ++ [f | Right _ <- [parseDocument src], Just f <- [check name ShouldParse src]]
          | (name, expected, src) <- inlineCases
          , let actual = firstProblem src
          ]
      failures = [f | Just f <- results] ++ inlineFailures
  putStrLn (show (length entries + length inlineCases) ++ " files, " ++ show (length failures) ++ " disagreements")
  mapM_ putStrLn failures
  -- the first problem of each file is the one recorded before error
  -- recovery existed, which is Ott's first
  golden <- TIO.readFile "test/first-diagnostics.tsv"
  firsts <- forM [(T.unpack a, T.drop 1 b) | l <- T.lines golden, not ("#" `T.isPrefixOf` l), let (a, b) = T.breakOn "\t" l] $ \(rel, expected) -> do
    bytes <- B.readFile (resolve rel)
    let actual = case TE.decodeUtf8' bytes of
          Left e -> T.pack (": not valid UTF-8: " ++ show e)
          Right src -> firstProblem src
    pure (if actual == expected then Nothing else Just (rel ++ ": first problem changed\n  was: " ++ T.unpack expected ++ "\n  now: " ++ T.unpack actual))
  let firstFailures = [f | Just f <- firsts]
  putStrLn (show (length firsts) ++ " first problems, " ++ show (length firstFailures) ++ " changed")
  mapM_ putStrLn firstFailures
  unless (null failures && null firstFailures) exitFailure
  where
    expectation cls
      | cls == "parse-error" = ShouldFail
      | otherwise = ShouldParse

-- | Specifications for what the corpus does not exercise: the quirks of
-- GRAMMAR.md §6 and the two intended divergences, each with the first
-- problem haskott reports (@: ok@ for none). Every case was run through
-- Ott 0.34; where Ott's verdict differs the comment says so.
inlineCases :: [(FilePath, T.Text, T.Text)]
inlineCases =
  [ ( "<quotations with leading blanks>"
    , ": ok"
    , T.unlines
        [ "metavar x ::= {{ coq nat }}"
        , "grammar"
        , "t :: t_ ::="
        , "  | x :: :: var"
        , "  | t t' :: :: app"
        , "defns"
        , "J :: '' ::="
        , "defn t1 => t2 :: :: red :: '' by"
        , "    {{ com see [[  t1  t2 ]] and [[x]] }}"
        , "    {{ coq [[  t1 ]] }}"
        , "    ---- :: one"
        , "    t1 => t1"
        ]
    )
  , ( "<unclosed block comment>"
    , ":2:1: unclosed >> comment (Ott lexing error)"
    , T.unlines ["metavar x ::= {{ coq nat }}", ">> never closed"]
    )
  , ( "<% comment at end of file without a newline>"
    , ":2:1: a % comment must end with a newline here (Ott lexing error)"
    , T.intercalate "\n" ["metavar x ::= {{ coq nat }}", "% trailing comment no newline"]
    )
  , ( "<single-word last line without a newline: the intended divergence, Ott rejects it>"
    , ": ok"
    , T.intercalate "\n" (okDefn ++ ["---- :: one", "ok"])
    )
  , ( "<single-word last line with a newline>"
    , ": ok"
    , T.unlines (okDefn ++ ["---- :: one", "ok"])
    )
  , ( "<multi-word last line without a newline>"
    , ": ok"
    , T.intercalate "\n" (redDefn ++ ["---- :: one", "t1 => t1"])
    )
  , ( "<% comment on a dashed line>"
    , ":12:13: a % comment must end with a newline here (Ott lexing error)"
    , T.unlines (redDefn ++ ["---- :: one % a comment", "t1 => t1"])
    )
  , ( "<a block of comment lines only between two rules>"
    , ": ok"
    , T.unlines (redDefn ++ ["---- :: one", "t1 => t1", "", "% only a comment here", "", "---- :: two", "t1 => t1"])
    )
  , ( "<embedded premise with trailing text, which Ott drops>"
    , ": ok"
    , T.unlines (redDefn ++ ["{{ coq True }} junk after", "---- :: one", "t1 => t1"])
    )
  , ( "<by followed by a comment>"
    , ":10:33: a rule must be preceded by a blank line"
    , T.unlines (take 9 redDefn ++ ["defn t1 => t2 :: :: red :: '' by % comment", "", "---- :: one", "t1 => t1"])
    )
  , ( "<hom name without a following blank>"
    , ":4:24: a hom name must be followed by whitespace"
    , T.unlines ["metavar x ::= {{ coq nat }}", "grammar", "t :: t_ ::=", "  | x :: :: var {{com}}"]
    )
  , ( "<quoted << and >> as elements>"
    , ": ok"
    , T.unlines ["metavar x ::= {{ coq nat }}", "grammar", "t :: t_ ::=", "  | x :: :: var", "  | '<<' x '>>' t :: :: s"]
    )
  , ( "<comprehension in a hom without spaces: one string>"
    , ": ok"
    , T.unlines (compGrammar "{{ tex [[</x_i//i/>]] }}")
    )
  , ( "<comprehension in a hom with a leading space only: never leaves comp_bound mode>"
    , ":8:1: expected //"
    , T.unlines (compGrammar "{{ coq [[ </x_i//i/> ]] }}")
    )
  , ( "<dots inside an embed's [[ ]]>"
    , ":7:26: unexpected token inside [[ ]]"
    , T.unlines
        [ "metavar x ::= {{ coq nat }}"
        , "indexvar i, n ::= {{ coq nat }}"
        , "grammar"
        , "t :: t_ ::="
        , "  | x :: :: var"
        , "  | x1 .. xn :: :: tup"
        , "embed {{ coq foo [[ x1 .. xn ]] }}"
        ]
    )
  ]
  where
    -- a definition of t1 => t2 whose rules follow (nine lines, so the first
    -- rule line is line 11)
    redDefn =
      [ "metavar x ::= {{ coq nat }}"
      , "grammar"
      , "t :: t_ ::="
      , "  | x :: :: var"
      , "  | t t' :: :: app"
      , "formula :: formula_ ::="
      , "  | judgement :: :: judgement"
      , "defns"
      , "J :: '' ::="
      , "defn t1 => t2 :: :: red :: '' by"
      , ""
      ]
    okDefn =
      [ "metavar x ::= {{ coq nat }}"
      , "grammar"
      , "formula :: formula_ ::="
      , "  | judgement :: :: judgement"
      , "defns"
      , "J :: '' ::="
      , "defn ok :: :: ok :: '' by"
      , ""
      ]
    compGrammar hom =
      [ "metavar x ::= {{ coq nat }}"
      , "indexvar i, n ::= {{ coq nat }}"
      , "grammar"
      , "t :: t_ ::="
      , "  | x :: :: var"
      , "  | </ x_i // i /> :: :: tup " <> hom
      , "  | t t' :: :: app"
      ]

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

-- | The first line @haskott check@ prints: the first parse error, else the
-- first check error, else the first problem of the definitions or
-- quotations, else ok.
firstProblem :: T.Text -> T.Text
firstProblem src = case parseDocument src of
  Left e -> at (parseErrorOffset e) (parseErrorMessage e)
  Right tree -> case checkDocument (rawDocument tree) of
    Left d -> diag d
    Right spec ->
      let (_, tp, warnings) = spliceTerms (FirstIfSame []) (makeTermParser spec) tree
          (_, diags) = processDefns (FirstIfSame []) tp spec
       in case map diag diags ++ map (\d -> diag d {diagMessage = "warning: " <> diagMessage d}) warnings of
            (l : _) -> l
            [] -> ": ok"
  where
    diag d = at (fromIntegral (Range.start (diagRange d))) (diagMessage d)
    at off m =
      let (l, c) = parseErrorPosition src (ParseError off T.empty)
       in T.pack (":" ++ show l ++ ":" ++ show c ++ ": ") <> T.takeWhile (/= '\n') m
