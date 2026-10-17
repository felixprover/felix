{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The immutable module aggregate produced by workspace parsing.
module Felix.Parsed.Workspace
    ( ParsedSourceWorkspace
    , parsedSourceWorkspace
    , parsedWorkspaceRoot
    , parsedWorkspaceRootModule
    , parsedWorkspaceModules
    , parsedWorkspaceImportedBeforeImporter
    , importedBeforeImporterBlocks
    ) where

import Base
import Felix.Parsed.Module
import Felix.Source (ResolvedSource)
import Felix.Syntax.Abstract qualified as Raw

import Data.List.NonEmpty qualified as NonEmpty


newtype ParsedSourceWorkspace = ParsedSourceWorkspace
    (NonEmpty ParsedModule)
    deriving stock (Show)

parsedSourceWorkspace :: NonEmpty ParsedModule -> ParsedSourceWorkspace
parsedSourceWorkspace = ParsedSourceWorkspace

parsedWorkspaceRoot :: ParsedSourceWorkspace -> ResolvedSource
parsedWorkspaceRoot = parsedModuleResolved . parsedWorkspaceRootModule

parsedWorkspaceRootModule :: ParsedSourceWorkspace -> ParsedModule
parsedWorkspaceRootModule (ParsedSourceWorkspace modules) =
    NonEmpty.last modules

parsedWorkspaceModules :: ParsedSourceWorkspace -> [ParsedModule]
parsedWorkspaceModules (ParsedSourceWorkspace modules) =
    NonEmpty.toList modules

parsedWorkspaceImportedBeforeImporter
    :: ParsedSourceWorkspace
    -> NonEmpty ParsedModule
parsedWorkspaceImportedBeforeImporter (ParsedSourceWorkspace modules) = modules

-- | Flatten source-local blocks in deterministic imported-before-importer
-- order.
importedBeforeImporterBlocks :: ParsedSourceWorkspace -> [Raw.Block]
importedBeforeImporterBlocks =
    concatMap parsedModuleBlocks . parsedWorkspaceImportedBeforeImporter
