{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

-- | @haskott lsp@ driven by a client: the problems of a specification
-- listed in @haskott.json@ reach the file they are about, they go when the
-- file is fixed, and a file no specification lists is checked alone.
module Main (main) where

import Control.Applicative.Combinators (skipManyTill)
import Control.Lens ((^.))
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as T
import qualified Language.LSP.Protocol.Lens as L
import Language.LSP.Protocol.Message (FromServerMessage' (..), SMethod (..), TNotificationMessage (..))
import Language.LSP.Protocol.Types
import Language.LSP.Test
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)

main :: IO ()
main = withSystemTempDirectory "haskott-lsp" $ \root -> do
  writeFile (root </> "haskott.json") "{ \"specs\": [ { \"files\": [\"a.ott\", \"b.ott\"] } ] }"
  writeFile (root </> "a.ott") "metavar x ::= {{ com variable }}\n"
  -- x again: an error only together with a.ott
  writeFile (root </> "b.ott") (T.unpack (metavarAgain <> grammar))
  writeFile (root </> "c.ott") (T.unpack (grammar <> "  | x :: :: var\n"))
  writeFile (root </> "d.ott") (T.unpack (metavarAgain <> grammar))
  runSession "haskott lsp" fullLatestClientCaps root $ do
    b <- openDoc "b.ott" ott
    ds <- diagnosticsFor (b ^. L.uri)
    check "b.ott, with a.ott: x is declared twice" (any (T.isInfixOf "multiple lexes" . (^. L.message)) ds)
    changeDoc b [TextDocumentContentChangeEvent (InR (TextDocumentContentChangeWholeDocument grammar))]
    ds' <- diagnosticsFor (b ^. L.uri)
    check "b.ott without its own x: no problems" (null ds')
    c <- openDoc "c.ott" ott
    dc <- diagnosticsFor (c ^. L.uri)
    check "c.ott, alone: a repeated production name" (any (T.isInfixOf "t_var" . (^. L.message)) dc)
    d <- openDoc "d.ott" ott
    dd <- diagnosticsFor (d ^. L.uri)
    check "d.ott, alone: its x is the only one" (null dd)
  putStrLn "lsp: ok"
  where
    ott = LanguageKind_Custom "ott"
    metavarAgain = "metavar x ::= {{ com again }}\n\n"
    grammar = "grammar\nt :: t_ ::=\n  | x :: :: var\n"

-- | The next diagnostics published for a document.
diagnosticsFor :: Uri -> Session [Diagnostic]
diagnosticsFor uri = skipManyTill anyMessage $ satisfyMaybe $ \m -> case m of
  FromServerMess SMethod_TextDocumentPublishDiagnostics (TNotificationMessage _ _ p)
    | toNormalizedUri (p ^. L.uri) == toNormalizedUri uri -> Just (p ^. L.diagnostics)
  _ -> Nothing

check :: String -> Bool -> Session ()
check what ok = liftIO $ unless ok (putStrLn ("lsp: failed: " ++ what) >> exitFailure)
