-- | Every problem of a specification, for a person or an editor rather
-- than for Ott compatibility.
--
-- Parsing recovers after each error and checking drops only the
-- construct an error is about, so one run reports the problems of the
-- whole specification. The rule lines of the definitions are parsed with
-- the grammar, so they are checked only when the parse and the check found
-- nothing: with errors in the grammar most of their problems would be
-- consequences of those.
module Haskott.Diagnostics
  ( Severity (..)
  , Problem (..)
  , Report (..)
  , diagnose
  ) where

import Data.Text (Text)
import qualified Graft.Green as Green
import Haskott.Defns (processDefns)
import Haskott.Load
import Haskott.Spec (Diagnostic (..), Spec)
import Haskott.Term.Parse (ParsePolicy (..), makeTermParser)
import Haskott.Term.Splice (spliceTerms)

data Severity = Error | Warning
  deriving (Eq, Show)

data Problem = Problem
  { problemFile :: FilePath
  , problemText :: Text
  -- ^ the file's text, for positions
  , problemSeverity :: Severity
  , problemDiagnostic :: Diagnostic
  }

data Report = Report
  { reportProblems :: [Problem]
  -- ^ parse errors, check errors, then those of the definitions and
  -- quotations, and the warnings
  , reportRulesChecked :: Bool
  -- ^ whether the definitions were checked
  , reportSpec :: Maybe Spec
  , reportRoundTrips :: Bool
  -- ^ whether every tree, with its terms, renders back to its file
  }

-- | Diagnose the files of a specification, in the order Ott reads them.
-- With @picky@ several parses of a term are an error.
diagnose :: Bool -> [(FilePath, Text)] -> Report
diagnose picky files =
  let checked = loadSpecRecovering files
      early = [Problem f src Error d | (f, src, d) <- ckDiagnostics checked]
      policy = if picky then Picky else FirstIfSame []
   in case ckSpec checked of
        Just spec
          | null early ->
              let tp0 = makeTermParser spec
                  step (t, ws, rt) s =
                    let (tree', tp', ws') = spliceTerms policy t (srcTree s)
                     in (tp', ws ++ [(s, w) | w <- ws'], rt && Green.renderNode tree' == srcText s)
                  (tp, warnings, ok) = foldl step (tp0, [], True) (ckSources checked)
                  (_, diags) = processDefns policy tp spec
                  located = [Problem f src Error d' | d <- diags, let (f, src, d') = locateDiagnostic (ckSources checked) d]
                  warned = [Problem (srcPath s) (srcText s) Warning w | (s, w) <- warnings]
               in Report (located ++ warned) True (Just spec) ok
        spec -> Report early False spec True
