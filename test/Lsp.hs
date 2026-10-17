{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

-- | @haskott lsp@ driven by a client: the problems of a specification
-- listed in @haskott.json@ reach the file they are about, they go when the
-- file is fixed, and a file no specification lists is checked alone;
-- definitions, references, highlights and the outline find the roots of
-- a specification across its files; and a rename reaches every file and
-- document of every specification it touches.
module Main (main) where

import Control.Applicative.Combinators (skipManyTill)
import Control.Lens ((^.))
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as T
import qualified Language.LSP.Protocol.Lens as L
import Language.LSP.Protocol.Message (FromServerMessage' (..), SMethod (..), TNotificationMessage (..), TResponseMessage (..))
import Language.LSP.Protocol.Types
import Language.LSP.Test
import System.Exit (exitFailure)
import System.FilePath (takeFileName, (</>))
import System.IO.Temp (withSystemTempDirectory)

main :: IO ()
main = withSystemTempDirectory "haskott-lsp" $ \root -> do
  writeFile (root </> "haskott.json") . unlines $
    [ "{ \"specs\": [ { \"files\": [\"a.ott\", \"b.ott\"] },"
    , "             { \"files\": [\"s.ott\", \"u.ott\"], \"documents\": [\"doc.typ\"] },"
    , "             { \"files\": [\"s.ott\", \"v.ott\"] } ] }"
    ]
  -- s.ott is shared by two specifications; u.ott has a rule line
  writeFile (root </> "s.ott") . unlines $
    [ "metavar termvar, x ::= {{ com term variable }}"
    , ""
    , "grammar"
    , "t :: 't_' ::="
    , "  | x :: :: var"
    , "  | \\ x . t :: :: lam"
    , "  | t t' :: :: app"
    , "  | ( t ) :: S :: paren"
    , ""
    , "terminals :: 'terminals_' ::="
    , "  | --> :: :: red"
    ]
  writeFile (root </> "u.ott") . unlines $
    ["defns", "Jop :: '' ::=", "", "defn", "t --> t' :: :: reduce :: '' by", "", "  -------------------------- :: beta", "  ( \\ x . t ) t' --> t"]
  writeFile (root </> "v.ott") . unlines $
    ["defns", "Jv :: '' ::=", "", "defn", "x --> t :: :: vred :: '' by"]
  writeFile (root </> "doc.typ") "Abstraction [[\\ x1 . x1]] binds x1.\n"
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
    navigation
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

-- | In u.ott, line 8 is @  ( \\ x . t ) t' --> t@: x at column 6, t' at 14.
navigation :: Session ()
navigation = do
  u <- openDoc "u.ott" (LanguageKind_Custom "ott")
  sUri <- getDocUri "s.ott"
  defs <- getDefinitions u (Position 7 6)
  check "the definition of x is its declaration in s.ott" $ case defs of
    InL (Definition (InR [l])) -> l ^. L.uri == sUri && l ^. L.range == Range (Position 0 17) (Position 0 18)
    _ -> False
  refs <- references u (Position 7 14) True
  check ("t' is one of 10 occurrences of t, got " ++ show (length refs)) (length refs == 10)
  refs' <- references u (Position 7 14) False
  check "without the declaration, 9" (length refs' == 9)
  hs <- getHighlights u (Position 7 14)
  check "5 occurrences of t in u.ott" (length hs == 5)
  s <- openDoc "s.ott" (LanguageKind_Custom "ott")
  symbols <- getDocumentSymbols s
  let names = either (const []) (map (\x -> (x ^. L.name, maybe [] (map (^. L.name)) (x ^. L.children)))) symbols
  check ("the outline of s.ott, got " ++ show names) $
    ("x", []) `elem` names && maybe False ("t_var" `elem`) (lookup "t" names)
  TResponseMessage _ _ prep <- request SMethod_TextDocumentPrepareRename (PrepareRenameParams u (Position 7 6) Nothing)
  check "x can be renamed" $ case prep of
    Right (InL (PrepareRenameResult (InR (InL ph)))) -> ph ^. L.placeholder == "x"
    _ -> False
  TResponseMessage _ _ clash <- request SMethod_TextDocumentRename (RenameParams Nothing u (Position 7 6) "t")
  check "x cannot become t, a root already" (either (const True) (const False) clash)
  TResponseMessage _ _ renamed <- request SMethod_TextDocumentRename (RenameParams Nothing u (Position 7 6) "y")
  edits <- case renamed of
    Right (InL e) -> pure [(T.unpack (getUri (tde ^. L.textDocument . L.uri)), length (tde ^. L.edits)) | Just changes <- [e ^. L.documentChanges], InL tde <- changes]
    _ -> pure []
  let counts = [(takeFileName f, n) | (f, n) <- edits]
  check ("renaming x to y reaches s, u, v and the document, got " ++ show counts) $
    all (`elem` counts) [("s.ott", 3), ("u.ott", 1), ("v.ott", 1), ("doc.typ", 2)] && length counts == 4

references :: TextDocumentIdentifier -> Position -> Bool -> Session [Location]
references doc pos decls = do
  TResponseMessage _ _ r <- request SMethod_TextDocumentReferences (ReferenceParams doc pos Nothing Nothing (ReferenceContext decls))
  pure $ case r of
    Right (InL ls) -> ls
    _ -> []
