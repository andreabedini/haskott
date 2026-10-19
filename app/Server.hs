{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | @haskott lsp@: a language server over stdio.
--
-- It reports every problem of the specifications an edited file is part
-- of ('Haskott.Diagnostics.diagnose'), with the specifications read from
-- the nearest @haskott.json@ at or above the file ('Haskott.Project'). Open files are
-- read from the editor and the others from disk.
--
-- A check starts a short while after the last change and a newer change to
-- the same specification cancels it, since checking the Haskell report
-- takes a second or two. A file that is part of several specifications
-- shows the problems of all of them.
--
-- Semantic tokens say what the grammar of a specification makes of its
-- identifiers ('Haskott.Highlight'): terminals, nonterminals,
-- metavariables and index variables, in rule lines, productions and
-- quotations. The rest is left to the editor's grammar of Ott.
module Server (serverMain) where

import Control.Concurrent (ThreadId, forkIO, killThread, myThreadId, threadDelay)
import Control.Concurrent.MVar
import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate, uninterruptibleMask_)
import Control.Lens ((^.))
import Control.Monad (filterM, forM, forM_, unless, void)
import Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString as B
import Data.Int (Int32)
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Graft (Position (..))
import qualified Graft.Green as Green
import qualified Graft.LineIndex as LineIndex
import qualified Graft.Range as Range
import Haskott.Diagnostics
import Haskott.Highlight
import Haskott.Outline
import Haskott.Project
import Haskott.Rename (Edit (..), FileRename (..), Index, declarations, indexRenameable, indexRoots, indexSpec, indexTree, occurrences, renameRoot, rootAt)
import qualified Haskott.Rename as Rename
import Haskott.Syntax (parseDocumentRecovering)
import Haskott.Spec (Diagnostic (..))
import qualified Language.LSP.Protocol.Lens as LSP
import qualified Language.LSP.Protocol.Message as L
import qualified Language.LSP.Protocol.Types as L
import Language.LSP.Server
import Language.LSP.VFS (virtualFileText, virtualFileVersion)
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (normalise, takeDirectory, takeExtension, takeFileName, (</>))

data State = State
  { stPending :: MVar (M.Map SpecConfig ThreadId)
  -- ^ the check waiting or running for each specification
  , stReported :: MVar (M.Map SpecConfig (M.Map FilePath [L.Diagnostic]))
  -- ^ what each specification last reported, for each of its files
  , stIndexes :: MVar (M.Map SpecConfig ([(FilePath, Text)], [(FilePath, Text)], Maybe Index))
  -- ^ the index of each specification, with the texts it was built from
  }

serverMain :: IO ()
serverMain = do
  st <- State <$> newMVar M.empty <*> newMVar M.empty <*> newMVar M.empty
  rc <-
    runServer
      ServerDefinition
        { parseConfig = \c _ -> Right c
        , onConfigChange = const (pure ())
        , defaultConfig = ()
        , configSection = "haskott"
        , doInitialize = \env _ -> pure (Right env)
        , staticHandlers = const (handlers st)
        , interpretHandler = \env -> Iso (runLspT env) liftIO
        , options = defaultOptions {optTextDocumentSync = Just sync}
        }
  exitWith (if rc == 0 then ExitSuccess else ExitFailure rc)
  where
    -- open and close, incremental changes, no will-save, save without text
    sync =
      L.TextDocumentSyncOptions
        (Just True)
        (Just L.TextDocumentSyncKind_Incremental)
        (Just False)
        (Just False)
        (Just (L.InR (L.SaveOptions (Just False))))

handlers :: State -> Handlers (LspM ())
handlers st =
  mconcat
    [ notificationHandler L.SMethod_Initialized (const (pure ()))
    , notificationHandler L.SMethod_TextDocumentDidOpen $ \n ->
        changed st (n ^. LSP.params . LSP.textDocument . LSP.uri)
    , notificationHandler L.SMethod_TextDocumentDidChange $ \n ->
        changed st (n ^. LSP.params . LSP.textDocument . LSP.uri)
    , notificationHandler L.SMethod_TextDocumentDidSave $ \n ->
        changed st (n ^. LSP.params . LSP.textDocument . LSP.uri)
    , notificationHandler L.SMethod_TextDocumentDidClose $ \n ->
        -- the file is read from disk again
        changed st (n ^. LSP.params . LSP.textDocument . LSP.uri)
    , notificationHandler L.SMethod_WorkspaceDidChangeConfiguration (const (pure ()))
    , navigationHandlers st
    , renameHandlers st
    , semanticTokensHandler st
    ]

-- | Check again the specifications a file is part of.
changed :: State -> L.Uri -> LspM () ()
changed st uri = case L.uriToFilePath uri of
  Nothing -> pure ()
  Just file -> do
    project <- loadProject file
    env <- getLspEnv
    liftIO (forM_ (specsOf project file) (schedule env st))

-- | The nearest @haskott.json@ at or above a file's directory, up to the
-- workspace root, with paths relative to its own directory. It is read at
-- every use, so that an edit to it needs no restart.
loadProject :: FilePath -> LspM () Project
loadProject file = do
  root <- fmap normalise <$> getRootPath
  let dirs = takeWhileInclusive (\d -> Just d /= root) (ancestors (takeDirectory (normalise file)))
  found <- liftIO (filterM (doesFileExist . (</> projectFile)) dirs)
  case found of
    [] -> pure emptyProject
    dir : _ -> do
      let path = dir </> projectFile
      bytes <- liftIO (B.readFile path)
      case decodeProject dir bytes of
        Right p -> pure p
        Left e -> do
          sendNotification L.SMethod_WindowShowMessage (L.ShowMessageParams L.MessageType_Error (T.pack (path ++ ": " ++ e)))
          pure emptyProject
  where
    ancestors d = let up = takeDirectory d in if up == d then [d] else d : ancestors up
    takeWhileInclusive keep xs = case break (not . keep) xs of
      (kept, stop : _) -> kept ++ [stop]
      (kept, []) -> kept

-- | Start a check of a specification, cancelling the one it supersedes.
schedule :: LanguageContextEnv () -> State -> SpecConfig -> IO ()
schedule env st spec = modifyMVar_ (stPending st) $ \pending -> do
  mapM_ killThread (M.lookup spec pending)
  tid <- forkIO (threadDelay debounce >> runCheck env st spec)
  pure (M.insert spec tid pending)
  where
    debounce = 200000

runCheck :: LanguageContextEnv () -> State -> SpecConfig -> IO ()
runCheck env st spec = do
  texts <- runLspT env (mapM source (specFiles spec))
  case sequence texts of
    Left message -> finish (runLspT env (sendNotification L.SMethod_WindowShowMessage (L.ShowMessageParams L.MessageType_Error message)))
    Right files -> do
      let report = diagnose (specPicky spec) files
          found = M.map (uncurry toDiagnostics) (byFile (reportProblems report))
      reported <- evaluate (force (M.union found (M.fromList [(f, []) | f <- specFiles spec])))
      finish (publish env st spec reported)
  where
    -- publish only if no newer check has replaced this one, and without
    -- being cancelled half way
    finish act = uninterruptibleMask_ $ do
      me <- myThreadId
      modifyMVar_ (stPending st) $ \pending ->
        if M.lookup spec pending == Just me
          then act >> pure (M.delete spec pending)
          else pure pending

-- | A file's text: the editor's if it is open, otherwise the one on disk.
source :: FilePath -> LspM () (Either Text (FilePath, Text))
source file = fmap (\(t, _) -> (file, t)) <$> sourceVersioned file

-- | A file's text and, when it is open, the editor's version of it.
sourceVersioned :: FilePath -> LspM () (Either Text (Text, Maybe Int32))
sourceVersioned file = do
  open <- getVirtualFile (L.toNormalizedUri (L.filePathToUri file))
  case open of
    Just vf -> pure (Right (virtualFileText vf, Just (virtualFileVersion vf)))
    Nothing -> liftIO $ do
      exists <- doesFileExist file
      if not exists
        then pure (Left (T.pack (file ++ ": no such file (listed in " ++ projectFile ++ ")")))
        else do
          bytes <- B.readFile file
          pure $ case TE.decodeUtf8' bytes of
            Right t -> Right (t, Nothing)
            Left _ -> Left (T.pack (file ++ ": not valid UTF-8"))

-- | The problems of each file, with the file's text.
byFile :: [Problem] -> M.Map FilePath (Text, [Problem])
byFile ps = M.fromListWith (\(_, new) (src, old) -> (src, old ++ new)) [(normalise (problemFile p), (problemText p, [p])) | p <- ps]

toDiagnostics :: Text -> [Problem] -> [L.Diagnostic]
toDiagnostics src = map diagnostic
  where
    index = LineIndex.fromText src
    position off = case LineIndex.utf16Position off index of
      Just (Position l c) -> L.Position (fromIntegral l) (fromIntegral c)
      Nothing -> L.Position 0 0
    diagnostic p =
      let d = problemDiagnostic p
          r = diagRange d
       in -- range, severity, code, code description, source, message,
          -- tags, related information, data
          L.Diagnostic
            (L.Range (position (Range.start r)) (position (Range.end r)))
            (Just (severity (problemSeverity p)))
            Nothing
            Nothing
            (Just "haskott")
            (diagMessage d)
            Nothing
            Nothing
            Nothing
    severity Error = L.DiagnosticSeverity_Error
    severity Warning = L.DiagnosticSeverity_Warning

-- | Record what a specification found and send every file it touched,
-- now or before, the problems of all its specifications.
publish :: LanguageContextEnv () -> State -> SpecConfig -> M.Map FilePath [L.Diagnostic] -> IO ()
publish env st spec found = do
  (before, after) <- modifyMVar (stReported st) $ \all' ->
    let all'' = M.insert spec found all' in pure (all'', (all', all''))
  let files = M.keys (M.union found (fromMaybe M.empty (M.lookup spec before)))
  runLspT env $ forM_ files $ \f -> do
    let ds = nub (concat [M.findWithDefault [] f m | m <- M.elems after])
    sendNotification L.SMethod_TextDocumentPublishDiagnostics (L.PublishDiagnosticsParams (L.filePathToUri f) Nothing ds)

------------------------------------------------------------------------
-- Navigation

-- | The indexes of the specifications a file is part of, for the texts
-- the files have now. An index is built when first needed and kept until
-- one of its texts changes.
indexesFor :: State -> FilePath -> LspM () [Index]
indexesFor st file = do
  project <- loadProject file
  found <- forM (specsOf project file) $ \spec -> do
    files <- sequence <$> mapM source (specFiles spec)
    docs <- sequence <$> mapM source (specDocuments spec)
    case (files, docs) of
      (Right fs, Right ds) -> liftIO $ modifyMVar (stIndexes st) $ \cache ->
        case M.lookup spec cache of
          Just (fs', ds', ix) | fs' == fs && ds' == ds -> pure (cache, ix)
          _ -> let ix = indexSpec fs ds in pure (M.insert spec (fs, ds, ix) cache, ix)
      _ -> pure Nothing
  pure (catMaybes found)

-- | The file and byte offset of a request's position.
located :: L.Uri -> L.Position -> LspM () (Maybe (FilePath, Text, Int))
located uri pos = case L.uriToFilePath uri of
  Nothing -> pure Nothing
  Just f -> do
    let file = normalise f
    text <- source file
    pure $ case text of
      Right (_, src) -> (\off -> (file, src, off)) <$> offsetOf src pos
      Left _ -> Nothing

offsetOf :: Text -> L.Position -> Maybe Int
offsetOf src (L.Position l c) = fromIntegral <$> LineIndex.fromUtf16Position (Position (fromIntegral l) (fromIntegral c)) (LineIndex.fromText src)

rangeOf :: Text -> (Int, Int) -> L.Range
rangeOf src (a, b) = L.Range (position a) (position b)
  where
    index = LineIndex.fromText src
    position off = case LineIndex.utf16Position (fromIntegral off) index of
      Just (Position l c) -> L.Position (fromIntegral l) (fromIntegral c)
      Nothing -> L.Position 0 0

locations :: [(FilePath, Text, (Int, Int))] -> [L.Location]
locations xs = [L.Location (L.filePathToUri f) (rangeOf src r) | (f, src, r) <- nubOn (\(f, _, r) -> (f, r)) xs]

nubOn :: Ord k => (a -> k) -> [a] -> [a]
nubOn key = go Set.empty
  where
    go _ [] = []
    go seen (x : xs)
      | key x `Set.member` seen = go seen xs
      | otherwise = x : go (Set.insert (key x) seen) xs

-- | Answer a request about the root at a position from another thread,
-- since building an index can take seconds: the texts are read now, the
-- answer is computed there.
aboutRoot ::
  NFData a =>
  State ->
  L.Uri ->
  L.Position ->
  (Either (L.TResponseError m) a -> LspM () ()) ->
  a ->
  ([Index] -> FilePath -> Text -> Int -> Text -> a) ->
  LspM () ()
aboutRoot st uri pos respond none answer = do
  here <- located uri pos
  case here of
    Nothing -> respond (Right none)
    Just (file, src, off) -> do
      ixs <- indexesFor st file
      env <- getLspEnv
      void . liftIO . forkIO $ do
        let result = case mapMaybe (\ix -> rootAt ix file off) ixs of
              root : _ -> answer ixs file src off root
              [] -> none
        r <- evaluate (force result)
        runLspT env (respond (Right r))

navigationHandlers :: State -> Handlers (LspM ())
navigationHandlers st =
  mconcat
    [ requestHandler L.SMethod_TextDocumentDefinition $ \req respond -> do
        let p = req ^. LSP.params
        aboutRoot st (p ^. LSP.textDocument . LSP.uri) (p ^. LSP.position) respond (L.InR (L.InR L.Null)) $ \ixs _ _ _ root ->
          L.InL (L.Definition (L.InR (locations (concat [declarations ix root | ix <- ixs]))))
    , requestHandler L.SMethod_TextDocumentReferences $ \req respond -> do
        let p = req ^. LSP.params
            withDecls = p ^. LSP.context . LSP.includeDeclaration
        aboutRoot st (p ^. LSP.textDocument . LSP.uri) (p ^. LSP.position) respond (L.InR L.Null) $ \ixs _ _ _ root ->
          let decls = Set.fromList [(f, r) | ix <- ixs, (f, _, r) <- declarations ix root]
              refs = [(f, src, r) | ix <- ixs, (f, src, rs) <- occurrences ix root, r <- rs, withDecls || not ((f, r) `Set.member` decls)]
           in L.InL (locations refs)
    , requestHandler L.SMethod_TextDocumentDocumentHighlight $ \req respond -> do
        let p = req ^. LSP.params
        aboutRoot st (p ^. LSP.textDocument . LSP.uri) (p ^. LSP.position) respond (L.InR L.Null) $ \ixs file src _ root ->
          let decls = Set.fromList [r | ix <- ixs, (f, _, r) <- declarations ix root, f == file]
              here = nubOn id [r | ix <- ixs, (f, _, rs) <- occurrences ix root, f == file, r <- rs]
              kind r = if r `Set.member` decls then L.DocumentHighlightKind_Write else L.DocumentHighlightKind_Read
           in L.InL [L.DocumentHighlight (rangeOf src r) (Just (kind r)) | r <- here]
    , requestHandler L.SMethod_TextDocumentDocumentSymbol $ \req respond ->
        case L.uriToFilePath (req ^. LSP.params . LSP.textDocument . LSP.uri) of
          Just f | takeExtension f == ".ott" -> do
            text <- source (normalise f)
            respond . Right $ case text of
              Right (_, src) -> L.InR (L.InL (map (documentSymbol src) (outline (fst (parseDocumentRecovering src)))))
              Left _ -> L.InR (L.InR L.Null)
          _ -> respond (Right (L.InR (L.InR L.Null)))
    ]

documentSymbol :: Text -> Symbol -> L.DocumentSymbol
documentSymbol src s =
  -- name, detail, kind, tags, deprecated, range, selection range, children
  L.DocumentSymbol
    (symName s)
    Nothing
    (symbolKind (symKind s))
    Nothing
    Nothing
    (rangeOf src (symRange s))
    (rangeOf src (symSelection s))
    (Just (map (documentSymbol src) (symChildren s)))
  where
    symbolKind k = case k of
      SymMetavar -> L.SymbolKind_Variable
      SymIndexvar -> L.SymbolKind_TypeParameter
      SymRule -> L.SymbolKind_Class
      SymProduction -> L.SymbolKind_Constructor
      SymDefns -> L.SymbolKind_Namespace
      SymDefn -> L.SymbolKind_Function
      SymDRule -> L.SymbolKind_Method
      SymFuns -> L.SymbolKind_Namespace
      SymFundefn -> L.SymbolKind_Function

------------------------------------------------------------------------
-- Rename

renameHandlers :: State -> Handlers (LspM ())
renameHandlers st =
  mconcat
    [ requestHandler L.SMethod_TextDocumentPrepareRename $ \req respond -> do
        let p = req ^. LSP.params
        aboutRoot st (p ^. LSP.textDocument . LSP.uri) (p ^. LSP.position) respond (L.InR L.Null) $ \ixs file src off root ->
          let here = [r | ix <- ixs, (f, _, rs) <- occurrences ix root, f == file, r@(a, b) <- rs, a <= off, off <= b]
           in case here of
                r : _ | any ((root `elem`) . indexRenameable) ixs -> L.InL (L.PrepareRenameResult (L.InR (L.InL (L.PrepareRenamePlaceholder (rangeOf src r) root))))
                _ -> L.InR L.Null
    , requestHandler L.SMethod_TextDocumentRename $ \req respond -> do
        let p = req ^. LSP.params
        here <- located (p ^. LSP.textDocument . LSP.uri) (p ^. LSP.position)
        case here of
          Nothing -> respond (Right (L.InR L.Null))
          Just (file, _, off) -> do
            ixs <- indexesFor st file
            case mapMaybe (\ix -> rootAt ix file off) ixs of
              [] -> respond (Left (failed "there is no metavariable, index variable or grammar rule here"))
              old : _ -> renameFrom file old (p ^. LSP.newName) respond
    ]

failed :: Text -> L.TResponseError m
failed m = L.TResponseError (L.InL L.LSPErrorCodes_RequestFailed) m Nothing

-- | Rename a root in every specification the edit reaches: those of the
-- file it starts from, then those of every file it changes, so that a
-- file shared by several specifications is renamed in all of them alike.
-- 'renameRoot' verifies each. Every file the project names is read now,
-- with its version, and the renaming runs on another thread; the edit
-- names the versions, so an editor refuses it if a file changed since.
renameFrom ::
  FilePath ->
  Text ->
  Text ->
  (Either (L.TResponseError L.Method_TextDocumentRename) (L.WorkspaceEdit L.|? L.Null) -> LspM () ()) ->
  LspM () ()
renameFrom file old new respond = do
  project <- loadProject file
  let start = specsOf project file
      wanted = nub (concat [specFiles sp ++ specDocuments sp | sp <- projectSpecs project ++ start])
  snapshot <- M.fromList <$> mapM (\f -> (,) f <$> sourceVersioned f) wanted
  env <- getLspEnv
  void . liftIO . forkIO $ do
    answer <- evaluate (force (renameAcross project snapshot start old new))
    runLspT env $ case answer of
      Left m -> respond (Left (failed m))
      Right (edit, notes) -> do
        respond (Right (L.InL edit))
        unless (notes == 0) $
          sendNotification L.SMethod_WindowShowMessage . L.ShowMessageParams L.MessageType_Info $
            T.pack (show notes) <> " mention" <> (if notes == 1 then "" else "s") <> " of " <> old <> " in comments and homs left as written"

renameAcross ::
  Project ->
  M.Map FilePath (Either Text (Text, Maybe Int32)) ->
  [SpecConfig] ->
  Text ->
  Text ->
  Either Text (L.WorkspaceEdit, Int)
renameAcross project snapshot start old new = reach [] start >>= merge
  where
    text f = case M.lookup f snapshot of
      Just (Right (t, _)) -> Right (f, t)
      Just (Left m) -> Left m
      Nothing -> Left (T.pack (f ++ ": not read"))
    reach done [] = Right (reverse done)
    reach done (spec : todo)
      | spec `elem` map fst done = reach done todo
      | otherwise = do
          fs <- mapM text (specFiles spec)
          ds <- mapM text (specDocuments spec)
          let result = renameRoot old new fs ds
              touched = either (const []) (map frPath . filter (not . null . frEdits)) result
          reach ((spec, result) : done) (todo ++ concatMap (specsOf project) touched)
    merge results = do
      renamed <- fmap concat . forM results $ \(spec, r) -> case r of
        Left ps -> Left (T.intercalate "\n" (map describe ps) <> inSpec spec)
        Right frs -> Right (filter (not . null . frEdits) frs)
      let byPath = M.fromListWith (flip (++)) [(frPath fr, [fr]) | fr <- renamed]
          firsts = [fr | fr : _ <- M.elems byPath]
      forM_ (M.toList byPath) $ \(f, frs) ->
        unless (all ((== map frNew (take 1 frs)) . pure . frNew) frs) $
          Left (T.pack (takeFileName f) <> ": the specifications it is part of would rename it differently")
      pure
        ( L.WorkspaceEdit Nothing (Just (map (L.InL . textDocumentEdit) firsts)) Nothing
        , sum (map (length . frNotes) firsts)
        )
    inSpec spec = case specFiles spec of
      [_] -> ""
      fs -> "\n(in the specification of " <> T.intercalate ", " (map (T.pack . takeFileName) fs) <> ")"
    describe pr = case Rename.problemWhere pr of
      Just (f, src, off) -> case LineIndex.utf8Position (fromIntegral off) (LineIndex.fromText src) of
        Just (Position l c) -> T.pack (takeFileName f ++ ":" ++ show (l + 1) ++ ":" ++ show (c + 1) ++ ": ") <> Rename.problemMessage pr
        Nothing -> T.pack (takeFileName f ++ ": ") <> Rename.problemMessage pr
      Nothing -> Rename.problemMessage pr
    version f = case M.lookup f snapshot of
      Just (Right (_, Just v)) -> L.InL v
      _ -> L.InR L.Null
    textDocumentEdit fr =
      L.TextDocumentEdit
        (L.OptionalVersionedTextDocumentIdentifier (L.filePathToUri (frPath fr)) (version (frPath fr)))
        [L.InL (L.TextEdit (rangeOf (frOld fr) (editStart e, editEnd e)) (editNew e)) | e <- frEdits fr]

------------------------------------------------------------------------
-- Semantic tokens

-- | The tokens of the first specification of a file that has it, from
-- another thread, since building an index can take seconds. Positions are
-- taken from the tree's own text, so they match the index even if the
-- file changed meanwhile.
semanticTokensHandler :: State -> Handlers (LspM ())
semanticTokensHandler st =
  requestHandler L.SMethod_TextDocumentSemanticTokensFull $ \req respond ->
    case L.uriToFilePath (req ^. LSP.params . LSP.textDocument . LSP.uri) of
      Just f | takeExtension f == ".ott" -> do
        let file = normalise f
        ixs <- indexesFor st file
        env <- getLspEnv
        void . liftIO . forkIO $ do
          let tokens = case mapMaybe (\ix -> (,) ix <$> indexTree ix file) ixs of
                (ix, tree) : _ -> semanticTokens (Green.renderNode tree) (highlights (indexRoots ix) tree)
                [] -> []
          r <- evaluate (force (L.makeSemanticTokens L.defaultSemanticTokensLegend tokens))
          runLspT env (respond (either (Left . failed) (Right . L.InL) r))
      _ -> respond (Right (L.InR L.Null))

semanticTokens :: Text -> [(Int, Int, Class)] -> [L.SemanticTokenAbsolute]
semanticTokens src tokens =
  [ L.SemanticTokenAbsolute (fromIntegral l) (fromIntegral c) (fromIntegral (c' - c)) (tokenType cls) []
  | (a, b, cls) <- tokens
  , Just (Position l c) <- [LineIndex.utf16Position (fromIntegral a) index]
  , Just (Position l' c') <- [LineIndex.utf16Position (fromIntegral b) index]
  , l == l'
  ]
  where
    index = LineIndex.fromText src
    tokenType cls = case cls of
      Terminal -> L.SemanticTokenTypes_Keyword
      Operator -> L.SemanticTokenTypes_Operator
      Nonterminal -> L.SemanticTokenTypes_Variable
      Metavariable -> L.SemanticTokenTypes_Parameter
      IndexVariable -> L.SemanticTokenTypes_TypeParameter
      Variable -> L.SemanticTokenTypes_String
      ProdName -> L.SemanticTokenTypes_Macro
      Number -> L.SemanticTokenTypes_Number
      ListSyntax -> L.SemanticTokenTypes_Operator
      Label -> L.SemanticTokenTypes_Decorator
