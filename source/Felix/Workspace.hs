{-# LANGUAGE NoImplicitPrelude #-}

-- | Stable source-mount policy and authority-free workspace preparation.
module Felix.Workspace
    ( WorkspaceEnvironment
    , prepareDefaultWorkspaceEnvironment
    , workspaceSourceMounts
    , workspaceHtmlMountPrefixes
    , workspaceLibraryRoot
    , prepareWorkspaceRoot
    , prepareSourceGraphMeasured
    , prepareSourceGraph
    , prepareDefaultSourceGraph
    , AuthorityFreeParseError(..)
    , renderAuthorityFreeParseError
    , authorityFreeParseDiagnostic
    , parseWorkspace
    , parse
    , tokenize
    , extractLexiconItems
    , simpleStream
    , TokStream
    , ParseException(..)
    , builtins
    ) where

import Base
import Felix.Parse (ParseException(..), ParseWorkspaceError(..))
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Prelude qualified as Prelude
import Felix.Source
import Felix.Source.Content qualified as Content
import Felix.Source.Graph
    ( ResolvedSourceGraph
    , SourceGraphPreparation
    , sourceGraphPreparationGraph
    )
import Felix.Source.Graph qualified as SourceGraph
import Felix.Source.Scan qualified as SourceScan
import Felix.Report.Diagnostic (Diagnostic)
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Adapt
    ( ExtractedLexiconItem
    , prepareLexicalChunk
    , preparedLexicalItems
    )
import Felix.Syntax.Lexicon (builtins)
import Felix.Syntax.Token

import Control.Exception qualified as Exception
import Data.Bifunctor (first)
import Data.Text qualified as Text
import System.Directory (getCurrentDirectory)
import System.Environment (lookupEnv)
import System.FilePath.Posix ((</>), isAbsolute)

data WorkspaceEnvironment = WorkspaceEnvironment
    !SourceMounts
    ![(SourceMountId, [Text])]
    !FilePath

workspaceSourceMounts :: WorkspaceEnvironment -> SourceMounts
workspaceSourceMounts (WorkspaceEnvironment mounts _prefixes _libraryRoot) =
    mounts

workspaceHtmlMountPrefixes
    :: WorkspaceEnvironment
    -> [(SourceMountId, [Text])]
workspaceHtmlMountPrefixes
        (WorkspaceEnvironment _mounts prefixes _libraryRoot) =
    prefixes

workspaceLibraryRoot :: WorkspaceEnvironment -> FilePath
workspaceLibraryRoot
        (WorkspaceEnvironment _mounts _prefixes libraryRoot) =
    libraryRoot

prepareDefaultWorkspaceEnvironment
    :: IO (Either ParseWorkspaceError WorkspaceEnvironment)
prepareDefaultWorkspaceEnvironment = do
    currentDir <- getCurrentDirectory
    configuredLibrary <- lookupEnv "NAPROCHE_LIB"
    let libraryDir = fromMaybe (currentDir </> "library") configuredLibrary
        debugDir = currentDir </> "debug"
        prefixes =
            [ (sourceMountId "project", [])
            , (sourceMountId "library", ["library"])
            , (sourceMountId "debug", ["debug"])
            ]
    fmap (first SourceWorkspaceError)
        (fmap
            (\mounts ->
                WorkspaceEnvironment mounts prefixes libraryDir)
            <$> prepareSourceMounts
                [ (sourceMountId "project", currentDir)
                , (sourceMountId "library", libraryDir)
                , (sourceMountId "debug", debugDir)
                ])

prepareWorkspaceRoot
    :: WorkspaceEnvironment
    -> FilePath
    -> IO (Either ParseWorkspaceError RootRequest)
prepareWorkspaceRoot _environment file =
    first SourceWorkspaceError <$> classifyRootRequest file

prepareSourceGraph
    :: WorkspaceEnvironment
    -> RootRequest
    -> IO (Either ParseWorkspaceError ResolvedSourceGraph)
prepareSourceGraph environment request =
    fmap sourceGraphPreparationGraph
        <$> prepareSourceGraphMeasured environment request

prepareSourceGraphMeasured
    :: WorkspaceEnvironment
    -> RootRequest
    -> IO (Either ParseWorkspaceError SourceGraphPreparation)
prepareSourceGraphMeasured environment request =
    first SourceWorkspaceError
        <$> SourceGraph.buildResolvedSourceGraphMeasured
            (workspaceSourceMounts environment)
            request

prepareDefaultSourceGraph
    :: FilePath
    -> IO (Either ParseWorkspaceError ResolvedSourceGraph)
prepareDefaultSourceGraph file = do
    preparedEnvironment <- prepareDefaultWorkspaceEnvironment
    case preparedEnvironment of
        Left failure -> pure (Left failure)
        Right environment -> do
            preparedRoot <- prepareWorkspaceRoot environment file
            case preparedRoot of
                Left failure -> pure (Left failure)
                Right request -> prepareSourceGraph environment request

classifyRootRequest :: FilePath -> IO (Either SourceError RootRequest)
classifyRootRequest file
    | isAbsolute file = existingRoot file
    | otherwise = pure (searchedRoot file)

data AuthorityFreeParseError
    = AuthorityFreePreludeLoadFailed !Prelude.PreludeLoadError
    | AuthorityFreePreludeParseFailed !Prelude.PreludeParseError
    | AuthorityFreeWorkspaceFailed !ParseWorkspaceError
    deriving (Show)

instance Exception.Exception AuthorityFreeParseError

renderAuthorityFreeParseError :: AuthorityFreeParseError -> Text
renderAuthorityFreeParseError = \case
    AuthorityFreePreludeLoadFailed failure ->
        "prelude loading failed: "
            <> Prelude.renderPreludeLoadError failure
    AuthorityFreePreludeParseFailed failure ->
        "prelude parsing failed: "
            <> Prelude.renderPreludeParseError failure
    AuthorityFreeWorkspaceFailed failure ->
        Parse.renderParseWorkspaceError failure

authorityFreeParseDiagnostic
    :: AuthorityFreeParseError
    -> Maybe Diagnostic
authorityFreeParseDiagnostic = \case
    AuthorityFreeWorkspaceFailed failure ->
        Parse.parseWorkspaceErrorDiagnostic failure
    _failure -> Nothing

parseWorkspace
    :: FilePath
    -> IO (Either AuthorityFreeParseError [Raw.Block])
parseWorkspace file =
    fmap Parsed.importedBeforeImporterBlocks
        <$> parseDefaultWorkspaceWithPrelude file

parse :: FilePath -> IO [Raw.Block]
parse file = parseWorkspace file >>= either Exception.throwIO pure

parseDefaultWorkspaceWithPrelude
    :: FilePath
    -> IO (Either AuthorityFreeParseError Parsed.ParsedSourceWorkspace)
parseDefaultWorkspaceWithPrelude file =
    Prelude.loadReservedPreludeSourceInput >>= \case
        Left failure ->
            pure (Left (AuthorityFreePreludeLoadFailed failure))
        Right source ->
            Prelude.parseReservedPreludeSource source >>= \case
                Left failure ->
                    pure (Left (AuthorityFreePreludeParseFailed failure))
                Right prelude -> do
                    preparedEnvironment <- prepareDefaultWorkspaceEnvironment
                    case preparedEnvironment of
                        Left failure ->
                            pure (Left (AuthorityFreeWorkspaceFailed failure))
                        Right environment -> do
                            preparedRoot <- prepareWorkspaceRoot environment file
                            case preparedRoot of
                                Left failure ->
                                    pure
                                        (Left
                                            (AuthorityFreeWorkspaceFailed
                                                failure))
                                Right request -> do
                                    let syntax =
                                            Parsed.identifiedParsedModuleSyntaxInterface
                                                (Prelude.reservedParsedPreludeModule
                                                    prelude)
                                    first AuthorityFreeWorkspaceFailed
                                        <$> Parse.parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
                                            (workspaceSourceMounts environment)
                                            request
                                            (const [syntax])
                                            (Prelude.rejectOrdinaryPreludeSourceGraph
                                                source)

lexFile :: FilePath -> IO (Text, [[Located Token]])
lexFile file = do
    environment <- prepareDefaultWorkspaceEnvironment
        >>= either throwWorkspaceError pure
    request <- prepareWorkspaceRoot environment file
        >>= either throwWorkspaceError pure
    loaded <- resolveAndLoadRoot (workspaceSourceMounts environment) request
        >>= either Exception.throwIO pure
    identified <- Content.identifyLoadedSource loaded

    let raw = loadedText (Content.identifiedSourceLoaded identified)
    case SourceScan.scanCompleteSourceTokens identified of
        Left (SourceScan.SourceInputFailure failure) ->
            Exception.throwIO
                (TokenError
                    (Text.unpack
                        (SourceScan.renderTokenSourceScanError failure)))
        Left (SourceScan.SourceScannerInvariantFailure failure) ->
            Exception.throwIO (SourceScannerInvariant failure)
        Right chunks -> do
            _ <- Exception.evaluate
                (SourceScan.forceSourceTokenChunksHandoff chunks)
            pure (raw, chunks)

tokenize :: FilePath -> IO TokStream
tokenize file = do
    (raw, chunks) <- lexFile file
    pure (TokStream raw chunks)

extractLexiconItems :: FilePath -> IO [ExtractedLexiconItem]
extractLexiconItems input = do
    tokenStream <- tokenize input
    concatMap (fmap unLocated)
        <$> traverse
            (either
                (Exception.throwIO . LexiconExtractionFailure)
                pure
                . fmap preparedLexicalItems
                . prepareLexicalChunk)
            (unTokStream tokenStream)

simpleStream :: TokStream -> [[Token]]
simpleStream TokStream{unTokStream = chunks} =
    [unLocated <$> chunk | chunk <- chunks]

throwWorkspaceError :: ParseWorkspaceError -> IO value
throwWorkspaceError = \case
    SourceWorkspaceError err -> Exception.throwIO err
    err@SourceLexiconCollision{} -> Exception.throwIO err
    err@SourceSyntaxPragmaError{} -> Exception.throwIO err
    err@SourceSyntaxDeclarationError{} -> Exception.throwIO err
    err@SourceSyntaxMaterializationError{} -> Exception.throwIO err
    err@SourceParsedModuleKeyError{} -> Exception.throwIO err
    err@SourceParsedModuleBindingInvariant{} -> Exception.throwIO err
    SourceParseError _source err -> Exception.throwIO err
