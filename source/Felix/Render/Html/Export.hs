{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Prepare a complete HTML export from retained parsed presentation.
module Felix.Render.Html.Export
    ( HtmlPresentation
    , HtmlPresentationAssemblyError(..)
    , renderHtmlPresentationAssemblyError
    , htmlPresentationFromParsedWorkspaceWithSyntaxInputs
    , htmlPresentationFromCheckedWorkspace
    , PreparedPresentationAnalysis
    , preparedPresentationDiagnostics
    , preparedPresentationMissingHints
    , PresentationAnalysisError(..)
    , renderPresentationAnalysisError
    , preparePresentationAnalysis
    , preparePresentationAnalysisFromLibraryRoot
    , HtmlArtefactError(..)
    , renderHtmlArtefactError
    , prepareHtmlArtefacts
    , HtmlExportError(..)
    , renderHtmlExportError
    , PreparedHtmlExport
    , preparedHtmlExportArtefacts
    , preparedHtmlExportDiagnostics
    , prepareHtmlExport
    , prepareHtmlExportWithLayout
    , prepareHtmlExportWithLayoutFromLibraryRoot
    ) where

import Base
import Felix.Checking.Identity (fieldIdDigest, structureIdDigest)
import Felix.Math.Codec (mathematicalDigestHex)
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Semantic qualified as Semantic
import Felix.Render.Html.Contracts qualified as Contracts
import Felix.Render.Html.Consequences qualified as Consequences
import Felix.Checking.Module qualified as Typed
import Felix.Checking.Declaration qualified as Declaration
import Felix.Parsed.Module
import Felix.Parsed.Workspace
import Felix.Source
import Felix.Source.Scan qualified as SourceScan
import Felix.Render.Html qualified as Html
import Felix.Render.Html.Assets qualified as Assets
import Felix.Render.Html.Context
import Felix.Render.Html.Hints
import Felix.Render.Html.Layout
import Felix.Render.Html.Output
import Felix.Report.Diagnostic (Diagnostic, DiagnosticSeverity(..))
import Felix.Syntax.Abstract (Block, Marker)
import Felix.Syntax.Adapt (materializeEffectiveSyntax)
import Felix.Render.Html.Markup (prepareMarkupParser)
import Felix.Syntax.Interface
    ( ModuleSyntaxInterface
    , moduleSyntaxAssertedId
    )

import Control.Exception (Exception, IOException, displayException)
import Control.Exception qualified as Exception
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import Data.Text.Encoding.Error (UnicodeException)
import Data.Text.IO qualified as TextIO
import System.Directory (doesFileExist)
import System.FilePath.Posix ((</>), takeFileName)


-- | The strict, invocation-local subset of parsed presentation needed by the
-- renderer. Construction forces the complete module sequence and every page
-- shell, severing references to parser payloads, syntax interfaces, and
-- canonical cache payloads.
data HtmlPresentation = HtmlPresentation
    !(Maybe Contracts.NotationBindings)
    !(Map Marker [Consequences.PublicConsequence])
    !ResolvedSource
    !(NonEmpty HtmlSourcePresentation)

data HtmlPresentationAssemblyError
    = HtmlPresentationNotationBindingFailure !Text
    | HtmlPresentationConsequenceFailure !Text
    | HtmlPresentationMissingSealedModule
        !ResolvedSourceAddress
    | HtmlPresentationUnresolvedParsedImport
        !ResolvedSourceAddress
        !ResolvedSourceAddress
    | HtmlPresentationSidecarLengthMismatch !Int !Int
    | HtmlPresentationSourceBindingMismatch
        !ResolvedSource
        !SourceScan.SourcePresentationBindingError
    | HtmlPresentationScannerInvariant
        !ResolvedSource
        !SourceScan.SourceScanInvariantError
    deriving stock (Show, Eq)

renderHtmlPresentationAssemblyError
    :: HtmlPresentationAssemblyError
    -> Text
renderHtmlPresentationAssemblyError = \case
    HtmlPresentationConsequenceFailure failure -> "checked record consequence presentation: " <> failure
    HtmlPresentationNotationBindingFailure reason -> reason
    HtmlPresentationMissingSealedModule address ->
        "checked HTML presentation is missing sealed module "
            <> Text.pack (show address)
    HtmlPresentationUnresolvedParsedImport importer imported ->
        "HTML presentation module " <> Text.pack (show importer)
            <> " has unresolved parsed import " <> Text.pack (show imported)
    HtmlPresentationSidecarLengthMismatch modules entries ->
        "HTML presentation has " <> Text.pack (show entries)
            <> " source entries for " <> Text.pack (show modules)
            <> " parsed modules"
    HtmlPresentationSourceBindingMismatch source failure ->
        "HTML presentation source binding failed for "
            <> assemblySourceLabel source
            <> ": "
            <> SourceScan.renderSourcePresentationBindingError failure
    HtmlPresentationScannerInvariant source failure ->
        "HTML presentation scanner invariant failed for "
            <> assemblySourceLabel source
            <> ": " <> SourceScan.renderSourceScanInvariantError failure
  where
    assemblySourceLabel = Text.pack . resolvedSourceLocationPath

data PreparedHtmlExport = PreparedHtmlExport
    ![PreparedHtmlArtefact]
    ![Diagnostic]

preparedHtmlExportArtefacts :: PreparedHtmlExport -> [PreparedHtmlArtefact]
preparedHtmlExportArtefacts (PreparedHtmlExport artefacts _diagnostics) =
    artefacts

preparedHtmlExportDiagnostics :: PreparedHtmlExport -> [Diagnostic]
preparedHtmlExportDiagnostics (PreparedHtmlExport _artefacts diagnostics) =
    diagnostics

data HtmlSourcePresentation = HtmlSourcePresentation
    !ResolvedSource
    ![ResolvedSource]
    ![Block]
    !(Map Marker Html.StructureSchemaPresentation)
    !(Either
        Html.HtmlDocumentProjectionError
        Html.HtmlDocumentDraft)

htmlPresentationFromParsedWorkspaceWithSyntaxInputs
    :: (ResolvedSource -> [ModuleSyntaxInterface])
    -> ParsedSourceWorkspace
    -> NonEmpty SourceScan.SourcePresentationEntry
    -> Either HtmlPresentationAssemblyError HtmlPresentation
htmlPresentationFromParsedWorkspaceWithSyntaxInputs syntaxInputs workspace =
    htmlPresentationFromWorkspace syntaxInputs Map.empty workspace

-- | Retain only presentation-safe structure information reconstructed from
-- successfully checked semantic descriptors. Raw parse-only rendering has no
-- such annotations, which prevents source text from masquerading as an
-- elaborated schema decision.
htmlPresentationFromCheckedWorkspace
    :: Typed.SealedTypedModule
    -> Map ResolvedSourceAddress Typed.SealedTypedModule
    -> ParsedSourceWorkspace
    -> NonEmpty SourceScan.SourcePresentationEntry
    -> Either HtmlPresentationAssemblyError HtmlPresentation
htmlPresentationFromCheckedWorkspace prelude checked workspace presentation = do
    checkedModules <-
        traverse resolveCheckedModule (NonEmpty.toList parsedModules)
    let checkedSchemas = concatMap (Declaration.evidenceLocalStructureSchemas . Typed.sealedTypedModuleEvidence)
            (prelude : checkedModules)
        schemas = structureSchemaPresentations checkedSchemas
    bindings <- first HtmlPresentationNotationBindingFailure (Contracts.checkedNotationBindings
        (concatMap (Semantic.semanticInterfaceDeclarations . Typed.sealedTypedModuleSemantic) (prelude : checkedModules)))
    structureBindings <- first HtmlPresentationNotationBindingFailure
        (Contracts.withStructurePhraseBindings checkedSchemas bindings)
    consequences <- first HtmlPresentationConsequenceFailure
        (Consequences.checkedRecordConsequences [prelude]
            (zip checkedModules (parsedModuleBlocks <$> NonEmpty.toList parsedModules)))
    HtmlPresentation _ _ root pages <- htmlPresentationFromWorkspace
        (const [Typed.sealedTypedModuleSyntax prelude])
        schemas
        workspace
        presentation
    pure (HtmlPresentation (Just (Contracts.withFieldBindings checkedSchemas structureBindings)) consequences root pages)
  where
    parsedModules = parsedWorkspaceImportedBeforeImporter workspace
    resolveCheckedModule parsedModule =
        let address = parsedModuleAddress parsedModule
        in maybe
            (Left (HtmlPresentationMissingSealedModule address))
            Right
            (Map.lookup address checked)


htmlPresentationFromWorkspace
    :: (ResolvedSource -> [ModuleSyntaxInterface])
    -> Map Marker Html.StructureSchemaPresentation
    -> ParsedSourceWorkspace
    -> NonEmpty SourceScan.SourcePresentationEntry
    -> Either HtmlPresentationAssemblyError HtmlPresentation
htmlPresentationFromWorkspace implicitSyntax schemas workspace presentation = do
    aligned <- alignPresentation parsedModules presentation
    pages <- strictTraverseNonEmpty project aligned
    pure (HtmlPresentation Nothing Map.empty
        (parsedWorkspaceRoot workspace)
        pages)
  where
    parsedModules =
        parsedWorkspaceImportedBeforeImporter workspace
    sourceByAddress =
        Map.fromList
            [ (parsedModuleAddress parsedModule, parsedModuleResolved parsedModule)
            | parsedModule <- NonEmpty.toList parsedModules
            ]
    syntaxById =
        Map.fromList
            [ (moduleSyntaxAssertedId interface, interface)
            | interface <-
                (parsedModuleSyntaxInterface
                    <$> NonEmpty.toList parsedModules)
                    <> concat
                        [ implicitSyntax (parsedModuleResolved parsedModule)
                        | parsedModule <- NonEmpty.toList parsedModules
                        ]
            ]

    project (parsedModule, presentationEntry) = do
        imports <-
            nubOrd <$> traverse
                (resolveParsedImport parsedModule)
                (parsedModuleImports parsedModule)
        projected <-
            first (presentationProjectionError parsedModule)
                (SourceScan.projectSourcePresentationEntry
                    (parsedModuleIdentifiedSource parsedModule)
                    presentationEntry)
        let blocks = parsedModuleBlocks parsedModule
            document = do
                lexicon <-
                    first Html.HtmlDocumentSyntaxFailed
                        (materializeEffectiveSyntax
                            syntaxById
                            (parsedModuleSyntaxInterface parsedModule))
                let mathParser =
                        prepareMarkupParser lexicon
                case projected of
                    SourceScan.SourcePresentationUnavailable failure ->
                        Left
                            (Html.HtmlDocumentScanFailed
                                (SourceScan.renderPresentationScanError failure))
                    SourceScan.SourcePresentationDecoded segments ->
                        Html.projectHtmlDocumentWithMathParser
                            mathParser segments blocks
        retainedDocument <-
            retainDocumentProjection parsedModule document
        pure (HtmlSourcePresentation
            (parsedModuleResolved parsedModule)
            imports
            blocks
            schemas
            retainedDocument)

    retainDocumentProjection parsedModule = \case
        Right projected -> Right (Right projected)
        Left failure -> case failure of
            Html.HtmlDocumentScannerInvariant invariant ->
                Left
                    (HtmlPresentationScannerInvariant
                        (parsedModuleResolved parsedModule)
                        invariant)
            ordinary@Html.HtmlDocumentScanFailed{} ->
                Right (Left ordinary)
            ordinary@Html.HtmlDocumentSyntaxFailed{} ->
                Right (Left ordinary)
            ordinary@Html.HtmlDocumentFormalCountMismatch{} ->
                Right (Left ordinary)
            ordinary@Html.HtmlDocumentFormalSlotMismatch{} ->
                Right (Left ordinary)
            ordinary@Html.HtmlDocumentPhraseAmbiguity{} ->
                Right (Left ordinary)
            ordinary@Html.HtmlDocumentAnchorCollision{} ->
                Right (Left ordinary)

    presentationProjectionError parsedModule = \case
        SourceScan.SourcePresentationBindingFailure failure ->
            HtmlPresentationSourceBindingMismatch
                (parsedModuleResolved parsedModule)
                failure
        SourceScan.SourcePresentationDecodeInvariant failure ->
            HtmlPresentationScannerInvariant
                (parsedModuleResolved parsedModule)
                failure

    resolveParsedImport parsedModule parsedImport =
        let importer = parsedModuleAddress parsedModule
            imported = parsedImportedAddress parsedImport
        in maybe
            (Left
                (HtmlPresentationUnresolvedParsedImport importer imported))
            Right
            (Map.lookup imported sourceByAddress)

alignPresentation
    :: NonEmpty ParsedModule
    -> NonEmpty SourceScan.SourcePresentationEntry
    -> Either
        HtmlPresentationAssemblyError
        (NonEmpty (ParsedModule, SourceScan.SourcePresentationEntry))
alignPresentation modules entries
    | moduleCount /= entryCount =
        Left
            (HtmlPresentationSidecarLengthMismatch
                moduleCount entryCount)
    | otherwise =
        Right (NonEmpty.zip modules entries)
  where
    moduleCount = NonEmpty.length modules
    entryCount = NonEmpty.length entries

structureSchemaPresentations
    :: [Schema.ResolvedStructureSchema] -> Map Marker Html.StructureSchemaPresentation
structureSchemaPresentations schemas = Map.fromList
    [(Schema.structurePhraseMarker (Schema.resolvedSchemaPhrase schema),
        Html.structureSchemaPresentation
            (mathematicalDigestHex (structureIdDigest (Schema.resolvedSchemaId schema)))
            [(Schema.resolvedFieldSymbol (fromMaybe
                (impossible "checked schema presentation lost a field")
                (Map.lookup identity (Schema.resolvedSchemaFields schema))),
                mathematicalDigestHex (fieldIdDigest identity))
            | identity <- Schema.resolvedPresentationFieldOrder (Schema.resolvedSchemaPresentation schema)])
    | schema <- schemas]

strictTraverseNonEmpty
    :: (a -> Either error b)
    -> NonEmpty a
    -> Either error (NonEmpty b)
strictTraverseNonEmpty f (value :| values) = do
    !firstPage <- f value
    !rest <- strictTraverseList f values
    pure (firstPage :| rest)

strictTraverseList
    :: (a -> Either error b)
    -> [a]
    -> Either error [b]
strictTraverseList _ [] =
    Right []
strictTraverseList f (value : values) = do
    !next <- f value
    !rest <- strictTraverseList f values
    pure (next : rest)

data PreparedPresentationAnalysis = PreparedPresentationAnalysis
    !RenderHints
    !ResolvedSource
    !(NonEmpty Html.HtmlPagePresentation)
    !Html.HtmlRenderIndex
    ![Diagnostic]
    ![Html.MissingRenderHint]

preparedPresentationDiagnostics
    :: PreparedPresentationAnalysis
    -> [Diagnostic]
preparedPresentationDiagnostics
        (PreparedPresentationAnalysis
            _hints _root _pages _renderIndex diagnostics _missing) =
    diagnostics

preparedPresentationMissingHints
    :: PreparedPresentationAnalysis
    -> [Html.MissingRenderHint]
preparedPresentationMissingHints
        (PreparedPresentationAnalysis
            _hints _root _pages _renderIndex _diagnostics missing) =
    missing

data PresentationAnalysisError
    = PresentationRendererDataNotFound !FilePath
    | PresentationRendererDataLookupFailed !FilePath !Text
    | PresentationRendererDataReadFailed !FilePath !Text
    | PresentationRendererDataInvalid !(NonEmpty RenderHintError)
    | PresentationRendererDataInvalidAt
        !FilePath
        !(NonEmpty RenderHintError)
    | PresentationDocumentError
        !ResolvedSource
        !Html.HtmlDocumentProjectionError
    deriving stock (Show)

renderPresentationAnalysisError :: PresentationAnalysisError -> Text
renderPresentationAnalysisError = \case
    PresentationRendererDataNotFound path ->
        "renderer data " <> quotePath (takeFileName path)
            <> " was not found at " <> quotePath path
    PresentationRendererDataLookupFailed path reason ->
        "could not locate renderer data " <> quotePath path <> ": " <> reason
    PresentationRendererDataReadFailed path reason ->
        "could not read renderer data " <> quotePath path <> ": " <> reason
    PresentationRendererDataInvalid failures ->
        "invalid renderer data: " <> renderHintFailures failures
    PresentationRendererDataInvalidAt path failures ->
        "invalid renderer data " <> quotePath path <> ": "
            <> renderHintFailures failures
    PresentationDocumentError source failure ->
        "could not project document presentation for " <> sourceLabel source
            <> ": " <> Html.renderHtmlDocumentProjectionError failure
  where
    renderHintFailures =
        Text.intercalate "; "
            . fmap renderRenderHintError
            . NonEmpty.toList

data HtmlArtefactError
    = HtmlArtefactLayoutError !HtmlLayoutError
    | HtmlArtefactContextError !HtmlRenderContextError
    deriving stock (Show)

renderHtmlArtefactError :: HtmlArtefactError -> Text
renderHtmlArtefactError = \case
    HtmlArtefactLayoutError failure ->
        renderHtmlLayoutError failure
    HtmlArtefactContextError failure ->
        case failure of
            HtmlCurrentSourceNotRouted source ->
                "current source has no HTML route: " <> sourceLabel source
            HtmlReferencedSourceNotRouted source ->
                "referenced source has no HTML route: " <> sourceLabel source

data HtmlExportError
    = HtmlExportAnalysisFailed !PresentationAnalysisError
    | HtmlExportArtefactFailed !HtmlArtefactError
    deriving stock (Show)

instance Exception HtmlExportError

renderHtmlExportError :: HtmlExportError -> Text
renderHtmlExportError = \case
    HtmlExportAnalysisFailed failure ->
        renderPresentationAnalysisError failure
    HtmlExportArtefactFailed failure ->
        renderHtmlArtefactError failure

sourceLabel :: ResolvedSource -> Text
sourceLabel source =
    sourceMountIdText (resolvedSourceMount source)
        <> ":"
        <> Text.pack
            (safeRelativePathFilePath
                (resolvedSourceRelativePath source))

quotePath :: FilePath -> Text
quotePath = Text.pack . show

prepareHtmlExport
    :: [(SourceMountId, [Text])]
    -> HtmlPresentation
    -> Text
    -> Either HtmlExportError PreparedHtmlExport
prepareHtmlExport mountPrefixes presentation hintsSource = do
    analysis <- first HtmlExportAnalysisFailed
        (preparePresentationAnalysis presentation hintsSource)
    let PreparedPresentationAnalysis
            _hints root pages _renderIndex _diagnostics _missing = analysis
        sources = Html.htmlPagePresentationSource <$> NonEmpty.toList pages
    layout <-
        first (HtmlExportArtefactFailed . HtmlArtefactLayoutError)
            (layoutHtmlSources mountPrefixes root sources)
    first HtmlExportArtefactFailed (prepareHtmlArtefacts layout analysis)

prepareHtmlExportWithLayout
    :: HtmlLayout
    -> HtmlPresentation
    -> Text
    -> Either HtmlExportError PreparedHtmlExport
prepareHtmlExportWithLayout
        layout
        presentation
        hintsSource = do
    analysis <- first HtmlExportAnalysisFailed
        (preparePresentationAnalysis presentation hintsSource)
    first HtmlExportArtefactFailed (prepareHtmlArtefacts layout analysis)

prepareHtmlExportWithLayoutFromLibraryRoot
    :: FilePath
    -> HtmlLayout
    -> HtmlPresentation
    -> IO (Either HtmlExportError PreparedHtmlExport)
prepareHtmlExportWithLayoutFromLibraryRoot libraryRoot layout presentation = do
    analysisResult <-
        preparePresentationAnalysisFromLibraryRoot libraryRoot presentation
    pure do
        analysis <- first HtmlExportAnalysisFailed analysisResult
        first HtmlExportArtefactFailed (prepareHtmlArtefacts layout analysis)

preparePresentationAnalysis
    :: HtmlPresentation
    -> Text
    -> Either PresentationAnalysisError PreparedPresentationAnalysis
preparePresentationAnalysis presentation hintsSource = do
    hints <- first PresentationRendererDataInvalid
        (parseRenderHints hintsSource)
    preparePresentationAnalysisWithHints hints presentation

preparePresentationAnalysisFromLibraryRoot
    :: FilePath
    -> HtmlPresentation
    -> IO
        (Either
            PresentationAnalysisError
            PreparedPresentationAnalysis)
preparePresentationAnalysisFromLibraryRoot libraryRoot presentation = do
    hintsResult <- readRendererFile libraryRoot "lexicon.tsv"
    pure do
        (path, hintsSource) <- hintsResult
        hints <- first (PresentationRendererDataInvalidAt path)
            (parseRenderHints hintsSource)
        preparePresentationAnalysisWithHints hints presentation

readRendererFile
    :: FilePath
    -> FilePath
    -> IO (Either PresentationAnalysisError (FilePath, Text))
readRendererFile libraryRoot relativePath = do
    let path = libraryRoot </> relativePath
    tryRendererIO (doesFileExist path) >>= \case
        Left failure ->
            pure
                (Left
                    (PresentationRendererDataLookupFailed
                        path
                        (Text.pack (displayException failure))))
        Right False ->
            pure (Left (PresentationRendererDataNotFound path))
        Right True -> do
            readResult <- tryRendererRead (TextIO.readFile path)
            pure case readResult of
                Left reason ->
                    Left (PresentationRendererDataReadFailed path reason)
                Right contents -> Right (path, contents)

tryRendererIO :: IO value -> IO (Either IOException value)
tryRendererIO = Exception.try

tryRendererRead :: IO value -> IO (Either Text value)
tryRendererRead action =
    Exception.catch
        (Exception.catch (Right <$> action) renderIOException)
        renderUnicodeException
  where
    renderIOException :: IOException -> IO (Either Text value)
    renderIOException = pure . Left . Text.pack . displayException

    renderUnicodeException
        :: UnicodeException
        -> IO (Either Text value)
    renderUnicodeException = pure . Left . Text.pack . displayException

preparePresentationAnalysisWithHints
    :: RenderHints
    -> HtmlPresentation
    -> Either PresentationAnalysisError PreparedPresentationAnalysis
preparePresentationAnalysisWithHints
        hints
        (HtmlPresentation bindings consequences root presentation) = do
    sourceBlocks <-
        traverse
            (\(HtmlSourcePresentation source imports blocks schemas projected) ->
                case projected of
                    Left failure ->
                        Left (PresentationDocumentError source failure)
                    Right draft ->
                        let (document, warnings) = Html.resolveHtmlDocument hints draft
                        in Right
                            ( (source, imports, blocks, schemas, document)
                            , warnings
                            ))
            presentation
    let renderSources = fst <$> sourceBlocks
        presentationDiagnostics = concatMap snd (NonEmpty.toList sourceBlocks)
        (unforcedRenderIndex, rawPages) =
            Html.buildRenderIndexWithConsequences consequences root renderSources
        !renderIndex = unforcedRenderIndex
        pages = case bindings of
            Nothing -> rawPages
            Just checked -> Html.withNotationContracts (Contracts.resolveNotationContracts hints checked) <$> rawPages
    missing <- first (uncurry PresentationDocumentError)
        (Html.collectMissingRenderHintsChecked
            hints
            (NonEmpty.toList pages))
    Right
        (PreparedPresentationAnalysis
            hints
            root
            pages
            renderIndex
            presentationDiagnostics
            missing)

prepareHtmlArtefacts
    :: HtmlLayout
    -> PreparedPresentationAnalysis
    -> Either HtmlArtefactError PreparedHtmlExport
prepareHtmlArtefacts
        layout
        (PreparedPresentationAnalysis
            hints root pages renderIndex diagnostics missing) = do
    let renderEnvironment = htmlRenderEnvironment layout
    pageArtefacts <-
        traverse
            (prepareSourceArtefact
                renderEnvironment
                layout
                hints
                renderIndex)
            pages
    declarationArtefact <-
        prepareDeclarationArtefact
            renderEnvironment
            layout
            root
            renderIndex
    let assetArtefacts =
            [ preparedHtmlArtefact
                (routeDestination (htmlAssetRoute layout asset))
                (Right (TextEncoding.encodeUtf8 (assetContents asset)))
            | asset <- allHtmlAssets
            ]
    Right
        (PreparedHtmlExport
            ( NonEmpty.toList pageArtefacts
                <> [declarationArtefact]
                <> assetArtefacts
            )
            ( diagnostics
                <> Html.renderMissingRenderHintDiagnostics
                    DiagnosticWarning
                    missing
            ))
  where
    assetContents = \case
        HtmlSupportScriptAsset -> Assets.supportScriptAssetContents
        HtmlStylesheetAsset -> Assets.stylesheetAssetContents

prepareDeclarationArtefact
    :: HtmlRenderEnvironment
    -> HtmlLayout
    -> ResolvedSource
    -> Html.HtmlRenderIndex
    -> Either HtmlArtefactError PreparedHtmlArtefact
prepareDeclarationArtefact renderEnvironment layout root renderIndex = do
    let route = htmlDeclarationIndexRoute layout
    context <-
        first HtmlArtefactContextError
            (htmlRenderContextAtRoute renderEnvironment root route)
    Right
        (preparedHtmlArtefact
            (routeDestination route)
            (first renderHtmlArtefactError
                (TextEncoding.encodeUtf8
                    <$> first HtmlArtefactContextError
                        (Html.renderDeclarationIndex context renderIndex))))

prepareSourceArtefact
    :: HtmlRenderEnvironment
    -> HtmlLayout
    -> RenderHints
    -> Html.HtmlRenderIndex
    -> Html.HtmlPagePresentation
    -> Either
        HtmlArtefactError
        PreparedHtmlArtefact
prepareSourceArtefact renderEnvironment layout hints renderIndex page = do
    let source = Html.htmlPagePresentationSource page
    context <-
        first
            HtmlArtefactContextError
            (htmlRenderContextFromEnvironment
                renderEnvironment
                source)
    route <-
        maybe
            (Left
                (HtmlArtefactContextError
                    (HtmlCurrentSourceNotRouted source)))
            Right
            (htmlPageRoute layout source)
    Right
        (preparedHtmlArtefact
            (routeDestination route)
            (first renderHtmlArtefactError
                (TextEncoding.encodeUtf8
                    <$> first
                        HtmlArtefactContextError
                        (Html.renderDocument
                            context
                            hints
                            renderIndex
                            page))))
