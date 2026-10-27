{-# LANGUAGE OverloadedStrings #-}

-- | The command line.
--
-- With Ott's options (@-i FILE@, @-o FILE@ for TeX, Typst and the prover
-- targets, the @-*_filter SRC DST@ options, @-picky_multiple_parses BOOL@,
-- ...) haskott runs the whole pipeline and writes the outputs, so that it
-- can stand in for @ott@ in a Makefile. Its exit status is Ott's: 2 on an
-- error, 0 when rules fail to parse unless @-signal_parse_errors true@,
-- which makes that 1. Unlike Ott it writes diagnostics to stderr and only
-- the rule counts to stdout. @check@ reports every problem of a
-- specification, @rename@ renames a root across a specification and its
-- documents and @lsp@ runs a language server over stdio. The development
-- subcommands @roots@, @dump@, @showraw@, @spec@, @structure@ and @parse@
-- look at one stage each.
module Main (main) where

import Control.Monad (foldM, forM, forM_, unless, when)
import qualified Data.ByteString as B
import Data.List (isSuffixOf)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import qualified Graft.Range as Range
import Haskott.Defns
import Haskott.Prover.Bounds (boundsConsistency)
import Haskott.Term.Symterm (Symterm (..))
import Haskott.Diagnostics
import Haskott.Load
import Haskott.Rename
import Haskott.SourceLoc (makeSources)
import Haskott.Raw (rawDocument)
import Haskott.Raw.Show (showRaw)
import Haskott.Spec (Diagnostic (..))
import Haskott.Spec.Check (checkDocument)
import Haskott.Spec.Show (showSpec)
import Haskott.Syntax
import Haskott.Term.Parse
import Haskott.Term.Splice (spliceTerms)
import Haskott.Term.Symterm (ppPlainSymterm)
import Haskott.Tex
import Haskott.Prover
import Haskott.Term.Grammar (nonterminalCount)
import Server (serverMain)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitWith)
import System.IO (hPutStr, hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("check" : files@(_ : _)) -> do
      let (picky, files') = (any (== "--picky") files, filter (/= "--picky") files)
      ok <- checkSpec picky files'
      unless ok exitFailure
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
      -- the tree after the term splice
      src <- readSource file
      case parseDocument src of
        Left e -> reportError file src e >> exitFailure
        Right tree -> case checkDocument (rawDocument tree) of
          Left d -> reportDiagnostic file src d >> exitFailure
          Right spec -> do
            let (tree', _, _) = spliceTerms (FirstIfSame []) (makeTermParser spec) tree
            TIO.putStr (dumpTree tree')
    ("rename" : rest) -> renameMain rest
    ("structure" : files@(_ : _)) -> do
      -- the structure of the prover output, for debugging
      texts <- forM files $ \f -> (,) f <$> readSource f
      case loadSpec texts of
        Left e -> reportLoadError e >> exitFailure
        Right l -> TIO.putStr (debugStructure [Input (srcPath s) (srcText s) (srcBase s) | s <- ldSources l] (ldSpec l))
    -- editors may add --stdio
    ("lsp" : _) -> serverMain
    ("roots" : files@(_ : _)) -> do
      -- the names rename accepts, one per line
      texts <- forM files $ \f -> (,) f <$> readSource f
      case loadSpec texts of
        Left e -> reportLoadError e >> exitFailure
        Right l -> mapM_ TIO.putStrLn (renameableRoots (ldSpec l))
    [h] | h `elem` ["help", "-help", "--help"] -> putStr usage
    (('-' : _) : _) -> ottMain args
    _ -> hPutStr stderr usage >> exitFailure

usage :: String
usage =
  unlines
    [ "usage: haskott [-i FILE]... [-o OUT]... [-tex_filter SRC DST]... [-typst_filter SRC DST]... [OPTION]..."
    , "                                           Ott's command line: check the inputs, write the outputs"
    , "       haskott check [--picky] FILE...     report every problem of a specification"
    , "       haskott rename [--write] OLD NEW FILE..."
    , "                                           rename a root across a specification and its documents"
    , "       haskott roots FILE...               the names rename accepts"
    , "       haskott lsp                         run the language server over stdio"
    , "       haskott dump [--terms] FILE         the lossless tree, before or after the rule lines are parsed"
    , "       haskott showraw FILE                the raw specification, as ott -showraw prints it"
    , "       haskott spec FILE                   the checked specification"
    , "       haskott structure FILE...           the entries of the prover output, in order"
    , "       haskott parse FILE ':root: text'    every parse of a term, as ott -parse prints them"
    , "       haskott help                        this text"
    , ""
    , "OUT ends in .tex, .typ, .v, .thy, .sml, .lem, .ml or .twf. OPTION is one of Ott's:"
    , "-picky_multiple_parses, -merge, -output_source_locations, -signal_parse_errors,"
    , "the -coq_*, -isa*, -ocaml_include_terminals, -no_rbcatn and -tex_* options and the"
    , "prover -*_filter options; see README.md."
    ]

------------------------------------------------------------------------
-- Ott's command line

data Options = Options
  { oInputs :: [FilePath]
  , oOutputs :: [FilePath]
  , oFileArgs :: [(Bool, FilePath)]
  -- ^ the inputs (True) and outputs in command-line order
  , oProver :: ProverOptions
  , oFilters :: [(Dialect, FilePath, FilePath)]
  , oProverFilters :: [(Target, FilePath, FilePath)]
  , oPicky :: Bool
  , oMerge :: Bool
  , oSignalParseErrors :: Bool
  -- ^ exit 1 when a rule or clause fails to parse, as Ott's option
  , oTex :: TexOptions
  }

parseOptions :: [String] -> Either String Options
parseOptions = go (Options [] [] [] defaultProverOptions [] [] False False False (defaultTexOptions Latex))
  where
    go o args = case args of
      [] -> Right o {oInputs = reverse (oInputs o), oOutputs = reverse (oOutputs o), oFileArgs = reverse (oFileArgs o), oFilters = reverse (oFilters o), oProverFilters = reverse (oProverFilters o)}
      flag : s : d : rest | Just t <- lookup flag proverFilterFlags -> go o {oProverFilters = (t, s, d) : oProverFilters o} rest
      "-i" : f : rest -> go o {oInputs = f : oInputs o, oFileArgs = (True, f) : oFileArgs o} rest
      "-o" : f : rest -> go o {oOutputs = f : oOutputs o, oFileArgs = (False, f) : oFileArgs o} rest
      "-coq_avoid" : n : rest
        | [(v, "")] <- reads n -> go (prover o (\p -> p {optCoqAvoid = v})) rest
        | otherwise -> Left ("expected a number, found " ++ show n)
      "-coq_expand_list_types" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optCoqExpandLists = v})) rest
      "-coq_names_in_rules" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optCoqNamesInRules = v})) rest
      "-coq_use_filter_fn" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optCoqUseFilterFn = v})) rest
      "-coq_lngen" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optCoqLngen = v})) rest
      "-isabelle_primrec" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optIsaPrimrec = v})) rest
      "-isabelle_inductive" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optIsaInductive = v})) rest
      "-isa_syntax" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optIsaSyntax = v})) rest
      "-isa_generate_lemmas" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optIsaGenerateLemmas = v})) rest
      "-ocaml_include_terminals" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optCamlIncludeTerminals = v})) rest
      "-no_rbcatn" : b : rest -> bool b >>= \v -> go (prover o (\p -> p {optNoRbcatn = v})) rest
      "-tex_filter" : s : d : rest -> go o {oFilters = (Latex, s, d) : oFilters o} rest
      "-typst_filter" : s : d : rest -> go o {oFilters = (Typst, s, d) : oFilters o} rest
      "-picky_multiple_parses" : b : rest -> bool b >>= \v -> go o {oPicky = v} rest
      "-merge" : b : rest -> bool b >>= \v -> go o {oMerge = v} rest
      "-signal_parse_errors" : b : rest -> bool b >>= \v -> go o {oSignalParseErrors = v} rest
      "-output_source_locations" : n : rest
        | [(v, "")] <- reads n -> go (tex (prover o (\p -> p {optSourceLocations = v})) (\t -> t {optTexSourceLocations = v})) rest
        | otherwise -> Left ("expected a number, found " ++ show n)
      "-tex_name_prefix" : p : rest -> go (tex o (\t -> t {optPrefix = T.pack p})) rest
      "-tex_show_meta" : b : rest -> bool b >>= \v -> go (tex o (\t -> t {optShowMeta = v})) rest
      "-tex_show_categories" : b : rest -> bool b >>= \v -> go (tex o (\t -> t {optShowCategories = v})) rest
      "-tex_colour" : b : rest -> bool b >>= \v -> go (tex o (\t -> t {optColour = v})) rest
      "-tex_wrap" : b : rest -> bool b >>= \v -> go (tex o (\t -> t {optWrap = v})) rest
      "-tex_suppress_category" : c : rest -> go (tex o (\t -> t {optSuppressedCategories = optSuppressedCategories t ++ [T.pack c]})) rest
      "-tex_suppress_ntr" : n : rest -> go (tex o (\t -> t {optSuppressedNtrs = optSuppressedNtrs t ++ [T.pack n]})) rest
      f : rest | ".ott" `isSuffixOf` f -> go o {oInputs = f : oInputs o, oFileArgs = (True, f) : oFileArgs o} rest
      opt : _ -> Left ("unknown option or argument " ++ show opt)
    bool b = case b of
      "true" -> Right True
      "false" -> Right False
      _ -> Left ("expected true or false, found " ++ show b)
    tex o f = o {oTex = f (oTex o)}
    prover o f = o {oProver = f (oProver o)}
    proverFilterFlags = [("-coq_filter", Coq), ("-isa_filter", Isa), ("-hol_filter", Hol), ("-lem_filter", Lem), ("-ocaml_filter", Caml)]

-- | The dialect an output file is written in, by its extension.
outputDialect :: FilePath -> Maybe Dialect
outputDialect f
  | ".tex" `isSuffixOf` f = Just Latex
  | ".typ" `isSuffixOf` f = Just Typst
  | otherwise = Nothing

-- | Ott's exit status for an error.
ottError :: IO a
ottError = exitWith (ExitFailure 2)

ottMain :: [String] -> IO ()
ottMain args = do
  opts <- either (\m -> hPutStrLn stderr m >> ottError) pure (parseOptions args)
  when (null (oInputs opts)) $ hPutStrLn stderr "no input files" >> ottError
  outputs <- fmap concat $ forM (oOutputs opts) $ \o -> case (outputDialect o, targetOfOutput o) of
    (Just d, _) -> pure [(d, o)]
    (_, Just _) -> pure []
    _ -> hPutStrLn stderr ("unrecognised extension of output file " ++ show o) >> ottError
  -- the prover targets, each once, in the order of their last output
  let proverTargets = removeDuplicatesLast [t | o <- oOutputs opts, Just t <- [targetOfOutput o]]
  -- every file is parsed into its own tree and the raw documents are
  -- checked as one, as Ott does with several -i options
  sourcesText <- forM (oInputs opts) $ \f -> (,) f <$> readSource f
  loaded <- case loadSpecWith (oMerge opts) sourcesText of
    Left e -> reportLoadError e >> ottError
    Right l -> pure l
  let spec = ldSpec loaded
      files = ldSources loaded
      sources = T.pack (unwords (oInputs opts))
      report d = let (f, src, d') = locateDiagnostic files d in reportDiagnostic f src d'
      tp = makeTermParser spec
      envOf d = withSources (makeSources files) (makeEnv (oTex opts) {optDialect = d} spec (quotationParser policy tp))
      -- several parses of a term are no error when every target Ott
      -- compares them in prints them the same: TeX and the provers but
      -- OCaml (Ott's targets_for_non_picky), not Typst
      policy
        | oPicky opts = Picky
        | otherwise =
            FirstIfSame
              ( [renderSymterm (envOf Latex) | Latex `elem` map fst outputs]
                  ++ [renderProverSymterm t (oProver opts) spec | t <- proverTargets, t /= Caml]
              )
      (processed, diags) = processDefns policy tp spec
      -- stage two on every tree, for its warnings about quotations
      warnings = concat [map (shiftDiag (srcBase s)) ws | s <- files, let (_, _, ws) = spliceTerms policy tp (srcTree s)]
  mapM_ report diags
  -- Ott stops at some problems of the definitions before any output
  when (any isFatalDiagnostic diags) ottError
  mapM_ (\d -> report d {diagMessage = "warning: " <> diagMessage d}) warnings
  -- Ott extracts the bounds of every rule and clause while printing TeX,
  -- and stops at inconsistent ones
  unless (null outputs) $
    case mapM_ boundsConsistency (ruleTerms processed) of
      Left m -> hPutStrLn stderr ("Error in generating output:\n" ++ T.unpack m ++ "\n") >> ottError
      Right () -> pure ()
  forM_ outputs $ \(d, o) -> writeText o (texDocument (envOf d) sources processed)
  unless (null proverTargets) $ do
    let inputs = [Input (srcPath s) (srcText s) (srcBase s) | s <- files]
    prepared <- case prepareProvers (oMerge opts) proverTargets inputs spec (nonterminalCount (termGrammar tp)) of
      Left d -> report d >> ottError
      Right p -> pure p
    let job t =
          ProverJob
            { pjTarget = t
            , pjOptions = oProver opts
            , pjSpec = spec
            , pjProcessed = processed
            , pjInputs = inputs
            , pjQuotation = quotationParser policy tp
            , pjParse = \root txt -> parseTerms tp root False txt
            , pjOutputs = outputsOf t (oFileArgs opts)
            , pjMerge = oMerge opts
            , pjSources = makeSources files
            }
        run vertex t = case proverOutputs prepared (job t) vertex of
          Left m -> hPutStrLn stderr ("Error: " ++ T.unpack m) >> ottError
          Right (written, vertex') -> do
            forM_ written (uncurry writeText)
            pure vertex'
    _ <- foldM run (prVertex prepared) proverTargets
    pure ()
  forM_ (oFilters opts) $ \(d, s, dst) -> do
    src <- readSource s
    case filterDocument (envOf d) src of
      Left m -> hPutStrLn stderr (s ++ ": " ++ T.unpack m) >> ottError
      Right out -> reportQuotations s src (quotationParser policy tp) >> writeText dst out
  -- Ott filters with the TeX dialects first, then the provers in this order
  forM_ [f | t <- [Coq, Isa, Hol, Lem, Caml], f@(t', _, _) <- oProverFilters opts, t' == t] $ \(t, s, dst) -> do
    src <- readSource s
    case filteredDocument src >>= proverFilter t (oProver opts) spec (quotationParser policy tp) of
      Left m -> hPutStrLn stderr (s ++ ": " ++ T.unpack m) >> ottError
      Right out -> reportQuotations s src (quotationParser policy tp) >> writeText dst out
  let counts = countsString processed
  unless (T.null counts) (TIO.putStr counts)
  -- Ott's "N bad": exit 1 only when asked to
  when (oSignalParseErrors opts && not (null diags)) (exitWith (ExitFailure 1))
  where
    shiftDiag base d = d {diagRange = shiftRange base (diagRange d)}

-- | A quotation of a filtered document that does not parse is typeset as
-- written, as Ott does; Ott also says so, and so does this, on stderr.
reportQuotations :: FilePath -> T.Text -> (T.Text -> Symterm) -> IO ()
reportQuotations file src parse = case documentQuotations src of
  Left _ -> pure ()
  Right quotations -> forM_ quotations $ \(off, written, text) -> case parse text of
    StUninterpreted _ m ->
      let (l, c) = offsetPosition src off
          what
            | m == "multiple parses" = "multiple parses of \"" ++ T.unpack written ++ "\""
            | otherwise = "no parses of \"" ++ T.unpack written ++ "\": " ++ T.unpack (T.takeWhile (/= '\n') m)
       in hPutStrLn stderr (file ++ ":" ++ show l ++ ":" ++ show c ++ ": warning: " ++ what)
    _ -> pure ()

-- | The terms of each rule and clause, in Ott's printing order.
ruleTerms :: Processed -> [[Symterm]]
ruleTerms processed =
  concat
    [ case it of
        PReln pc -> [druleConclusion dr : map snd (drulePremises dr) | d <- pcDefns pc, ItemRule dr <- pdRules d]
        PFuns pfc -> [[fcLhs fc, fcRhs fc] | f <- pfcFuns pfc, fc <- pfClauses f]
    | it <- processedItems processed
    ]

-- | Ott's @compute_output@: each output of a target with the inputs since
-- the previous one, most recent first.
outputsOf :: Target -> [(Bool, FilePath)] -> [(FilePath, [FilePath])]
outputsOf t = go []
  where
    go ib args = case args of
      [] -> []
      (True, f) : more -> go (f : ib) more
      (False, f) : more
        | targetOfOutput f == Just t -> (f, ib) : go [] more
        | otherwise -> go ib more

removeDuplicatesLast :: Eq a => [a] -> [a]
removeDuplicatesLast xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicatesLast more else x : removeDuplicatesLast more

writeText :: FilePath -> T.Text -> IO ()
writeText f = B.writeFile f . TE.encodeUtf8

------------------------------------------------------------------------
-- Rename

-- | @haskott rename [--write] OLD NEW FILE...@: the @.ott@ files are the
-- specification, in the order Ott reads them, and the other files are
-- documents whose @[[ ]]@ quotations are renamed too. Without @--write@
-- the edits are listed and nothing is changed.
renameMain :: [String] -> IO ()
renameMain args = do
  let write = "--write" `elem` args
  case filter (/= "--write") args of
    old : new : files@(_ : _) -> do
      texts <- forM files $ \f -> (,) f <$> readSource f
      let (specs, docs) = (filter ((".ott" `isSuffixOf`) . fst) texts, filter (not . (".ott" `isSuffixOf`) . fst) texts)
      when (null specs) $ hPutStrLn stderr "rename: no .ott file given" >> exitFailure
      case renameRoot (T.pack old) (T.pack new) specs docs of
        Left problems -> do
          forM_ problems $ \p -> case problemWhere p of
            Just (f, src, off) ->
              let (l, c) = offsetPosition src off
               in hPutStrLn stderr (f ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (problemMessage p))
            Nothing -> hPutStrLn stderr ("rename: " ++ T.unpack (problemMessage p))
          exitFailure
        Right renamed -> do
          forM_ renamed $ \r -> forM_ (frEdits r) $ \e ->
            let (l, c) = offsetPosition (frOld r) (editStart e)
             in putStrLn (frPath r ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (editOld e) ++ " -> " ++ T.unpack (editNew e))
          forM_ renamed $ \r -> forM_ (frNotes r) $ \(off, w) ->
            let (l, c) = offsetPosition (frOld r) off
             in putStrLn (frPath r ++ ":" ++ show l ++ ":" ++ show c ++ ": note: " ++ T.unpack w ++ " in a comment or hom body is left as written")
          let n = sum (map (length . frEdits) renamed)
              changed = [r | r <- renamed, not (null (frEdits r))]
          putStrLn (show n ++ " occurrences in " ++ show (length changed) ++ " files; the renamed specification checks and parses every term as before")
          if write
            then forM_ changed $ \r -> writeText (frPath r) (frNew r)
            else putStrLn "nothing written: pass --write to change the files"
    _ -> hPutStrLn stderr "usage: haskott rename [--write] OLD NEW FILE..." >> exitFailure

reportLoadError :: LoadError -> IO ()
reportLoadError e = case e of
  LoadParse f src pe -> reportError f src pe
  LoadCheck f src d -> reportDiagnostic f src d

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

-- | The whole pipeline on the files of one specification, in Ott's order,
-- reporting every problem (see "Haskott.Diagnostics").
checkSpec :: Bool -> [FilePath] -> IO Bool
checkSpec picky files = do
  texts <- forM files $ \f -> (,) f <$> readSource f
  let report = diagnose picky texts
      errors = [p | p <- reportProblems report, problemSeverity p == Error]
      label = unwords files
  forM_ (reportProblems report) $ \p ->
    let d = problemDiagnostic p
        prefix = if problemSeverity p == Warning then "warning: " else ""
     in reportDiagnostic (problemFile p) (problemText p) d {diagMessage = prefix <> diagMessage d}
  unless (reportRulesChecked report) $
    hPutStrLn stderr (label ++ ": the rules of the definitions are checked once the errors above are fixed")
  let n = length errors
  if not (reportRoundTrips report)
    then putStrLn (label ++ ": TERMS DO NOT ROUND-TRIP") >> pure False
    else
      if n == 0
        then putStrLn (label ++ ": ok") >> pure True
        else putStrLn (label ++ ": " ++ show n ++ (if n == 1 then " error" else " errors")) >> pure False

reportDiagnostic :: FilePath -> T.Text -> Diagnostic -> IO ()
reportDiagnostic file src d =
  let (l, c) = offsetPosition src (fromIntegral (Range.start (diagRange d)))
   in hPutStrLn stderr (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (diagMessage d))

reportError :: FilePath -> T.Text -> ParseError -> IO ()
reportError file src e =
  let (l, c) = parseErrorPosition src e
   in hPutStrLn stderr (file ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ T.unpack (parseErrorMessage e))

-- | Line and column of a byte offset.
offsetPosition :: T.Text -> Int -> (Int, Int)
offsetPosition src off = parseErrorPosition src (ParseError off T.empty)
