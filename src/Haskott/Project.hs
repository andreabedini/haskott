{-# LANGUAGE OverloadedStrings #-}

-- | The specifications of a workspace, as an editor sees them.
--
-- Ott reads a specification from several files (@-i@ options, in order),
-- and one file can be part of several specifications: the Haskell report
-- builds one from @style.ott@ and @expressions.ott@ and another from
-- @style.ott@ and @layout.ott@. Nothing in the files says so, so they are
-- listed in a @haskott.json@; for a file, the nearest one at or above its
-- directory counts:
--
-- > { "specs": [ { "files": ["ott/style.ott", "ott/expressions.ott"], "picky": true,
-- >                "documents": ["doc/report.src.typ"] },
-- >              { "files": ["ott/style.ott", "ott/layout.ott"], "picky": true } ] }
--
-- Paths are relative to the directory of @haskott.json@. @picky@ (Ott's @-picky_multiple_parses@)
-- defaults to false. @documents@, none by default, are the documents
-- filtered against the specification (Ott's @-typst_filter@ sources),
-- whose quotations a rename rewrites too. A file no specification lists
-- is a specification of its own.
module Haskott.Project
  ( Project (..)
  , SpecConfig (..)
  , projectFile
  , emptyProject
  , decodeProject
  , specsOf
  ) where

import Data.Aeson (FromJSON (..), eitherDecodeStrict, withObject, (.!=), (.:), (.:?))
import qualified Data.ByteString as B
import System.FilePath (normalise, (</>))

-- | One specification: its files in the order Ott reads them.
data SpecConfig = SpecConfig
  { specFiles :: [FilePath]
  , specPicky :: Bool
  , specDocuments :: [FilePath]
  }
  deriving (Eq, Ord, Show)

newtype Project = Project {projectSpecs :: [SpecConfig]}
  deriving (Eq, Show)

instance FromJSON SpecConfig where
  parseJSON = withObject "specification" $ \o ->
    SpecConfig <$> o .: "files" <*> o .:? "picky" .!= False <*> o .:? "documents" .!= []

instance FromJSON Project where
  parseJSON = withObject "project" $ \o -> Project <$> o .: "specs"

projectFile :: FilePath
projectFile = "haskott.json"

emptyProject :: Project
emptyProject = Project []

-- | Decode @haskott.json@ with its paths resolved against its directory.
decodeProject :: FilePath -> B.ByteString -> Either String Project
decodeProject root bytes = do
  Project specs <- eitherDecodeStrict bytes
  let resolve = map (normalise . (root </>))
  pure (Project [s {specFiles = resolve (specFiles s), specDocuments = resolve (specDocuments s)} | s <- specs])

-- | The specifications a file is part of: those that list it, as a file
-- or a document, or else the file alone. Paths are compared after
-- 'normalise'.
specsOf :: Project -> FilePath -> [SpecConfig]
specsOf (Project specs) file = case filter (\s -> normalise file `elem` specFiles s ++ specDocuments s) specs of
  [] -> [SpecConfig [normalise file] False []]
  ss -> ss
