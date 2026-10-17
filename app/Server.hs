{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | @haskott lsp@: a language server over stdio.
--
-- It reports every problem of the specifications an edited file is part
-- of ('Haskott.Diagnostics.diagnose'), with the specifications read from
-- @haskott.json@ at the workspace root ('Haskott.Project'). Open files are
-- read from the editor and the others from disk.
--
-- A check starts a short while after the last change and a newer change to
-- the same specification cancels it, since checking the Haskell report
-- takes a second or two. A file that is part of several specifications
-- shows the problems of all of them.
module Server (serverMain) where

import Control.Concurrent (ThreadId, forkIO, killThread, myThreadId, threadDelay)
import Control.Concurrent.MVar
import Control.DeepSeq (force)
import Control.Exception (evaluate, uninterruptibleMask_)
import Control.Lens ((^.))
import Control.Monad (forM_)
import Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString as B
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Graft (Position (..))
import qualified Graft.LineIndex as LineIndex
import qualified Graft.Range as Range
import Haskott.Diagnostics
import Haskott.Project
import Haskott.Spec (Diagnostic (..))
import qualified Language.LSP.Protocol.Lens as LSP
import qualified Language.LSP.Protocol.Message as L
import qualified Language.LSP.Protocol.Types as L
import Language.LSP.Server
import Language.LSP.VFS (virtualFileText)
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (normalise, (</>))

data State = State
  { stPending :: MVar (M.Map SpecConfig ThreadId)
  -- ^ the check waiting or running for each specification
  , stReported :: MVar (M.Map SpecConfig (M.Map FilePath [L.Diagnostic]))
  -- ^ what each specification last reported, for each of its files
  }

serverMain :: IO ()
serverMain = do
  st <- State <$> newMVar M.empty <*> newMVar M.empty
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
    ]

-- | Check again the specifications a file is part of.
changed :: State -> L.Uri -> LspM () ()
changed st uri = case L.uriToFilePath uri of
  Nothing -> pure ()
  Just file -> do
    project <- loadProject
    env <- getLspEnv
    liftIO (forM_ (specsOf project file) (schedule env st))

-- | @haskott.json@ at the root, read at every check so that an edit to it
-- needs no restart.
loadProject :: LspM () Project
loadProject = do
  root <- getRootPath
  case root of
    Nothing -> pure emptyProject
    Just r -> do
      let path = r </> projectFile
      exists <- liftIO (doesFileExist path)
      if not exists
        then pure emptyProject
        else do
          bytes <- liftIO (B.readFile path)
          case decodeProject r bytes of
            Right p -> pure p
            Left e -> do
              sendNotification L.SMethod_WindowShowMessage (L.ShowMessageParams L.MessageType_Error (T.pack (path ++ ": " ++ e)))
              pure emptyProject

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
source file = do
  open <- getVirtualFile (L.toNormalizedUri (L.filePathToUri file))
  case open of
    Just vf -> pure (Right (file, virtualFileText vf))
    Nothing -> liftIO $ do
      exists <- doesFileExist file
      if not exists
        then pure (Left (T.pack (file ++ ": no such file (listed in " ++ projectFile ++ ")")))
        else do
          bytes <- B.readFile file
          pure $ case TE.decodeUtf8' bytes of
            Right t -> Right (file, t)
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
