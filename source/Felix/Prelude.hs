{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The reserved packaged prelude source and its authority-free parser.
module Felix.Prelude
    ( preludeDataFilePath
    , ReservedPreludeSourceInput
    , reservedPreludeSourceInput
    , loadReservedPreludeSourceInput
    , emptyBootstrapSourceInput
    , reservedPreludeSourceOwner
    , reservedPreludeSourceLabel
    , reservedPreludeSourceCanonicalPath
    , reservedPreludeSourceBytes
    , reservedPreludeSourceText
    , rejectOrdinaryPreludeSourceGraph
    , preludeDiagnosticLabel
    , PreludeLoadError(..)
    , renderPreludeLoadError
    , PreludeParseError(..)
    , renderPreludeParseError
    , ReservedParsedPrelude
    , reservedParsedPreludeInput
    , reservedParsedPreludeModule
    , parseReservedPreludeSource
    ) where

import Base
import Felix.Module
import Felix.Parse
import Felix.Parsed.Module
import Felix.Source
import Felix.Source.Graph
import Felix.Report.Location
import Felix.Syntax.Adapt (SyntaxMaterializationError)
import Felix.Syntax.Interface
import Felix.Syntax.Pragma

import Control.Exception (IOException, displayException, try)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Text qualified as Text
import Data.Text.Encoding.Error (UnicodeException)
import Paths_felix qualified as Paths


data ReservedPreludeSourceInput = ReservedPreludeSourceInput
    !ReservedSource
    !(Maybe CanonicalPath)

reservedPreludeSourceInput
    :: ByteString
    -> Either UnicodeException ReservedPreludeSourceInput
reservedPreludeSourceInput bytes =
    ReservedPreludeSourceInput
        <$> reservedSource preludeModuleName preludeDiagnosticLabel bytes
        <*> pure Nothing

data PreludeLoadError
    = PreludeSourceReadFailed !FilePath !Text
    | PreludeSourceCanonicalizationFailed !FilePath !SourceError
    | PreludeSourceUtf8Failed !UnicodeException

instance Show PreludeLoadError where
    show = Text.unpack . renderPreludeLoadError

renderPreludeLoadError :: PreludeLoadError -> Text
renderPreludeLoadError = \case
    PreludeSourceReadFailed path failure ->
        Text.pack path
            <> ": unable to read packaged prelude: "
            <> failure
    PreludeSourceCanonicalizationFailed path failure ->
        Text.pack path
            <> ": unable to resolve packaged prelude: "
            <> renderSourceError failure
    PreludeSourceUtf8Failed failure ->
        preludeErrorPrefix
            <> "malformed UTF-8: "
            <> Text.pack (displayException failure)

loadReservedPreludeSourceInput
    :: IO (Either PreludeLoadError ReservedPreludeSourceInput)
loadReservedPreludeSourceInput = do
    path <- Paths.getDataFileName preludeDataFilePath
    canonicalized <- canonicalizeExistingSourcePath path
    case canonicalized of
        Left failure ->
            pure
                (Left
                    (PreludeSourceCanonicalizationFailed path failure))
        Right canonical -> do
            loaded <- try
                (ByteString.readFile
                    (canonicalPathFilePath canonical))
                :: IO (Either IOException ByteString)
            pure case loaded of
                Left failure ->
                    Left
                        (PreludeSourceReadFailed
                            path
                            (Text.pack (displayException failure)))
                Right bytes ->
                    case reservedSource
                            preludeModuleName
                            preludeDiagnosticLabel
                            bytes of
                        Left failure ->
                            Left (PreludeSourceUtf8Failed failure)
                        Right source ->
                            Right
                                (ReservedPreludeSourceInput
                                    source
                                    (Just canonical))

-- | Empty prelude input used only by focused compiler fixtures.
--
-- Production verification always calls 'loadReservedPreludeSourceInput'.
emptyBootstrapSourceInput :: ReservedPreludeSourceInput
emptyBootstrapSourceInput =
    ReservedPreludeSourceInput
        (reservedSourceFromText
            preludeModuleName
            preludeDiagnosticLabel
            Text.empty)
        Nothing

reservedPreludeSourceOwner
    :: ReservedPreludeSourceInput
    -> ModuleName
reservedPreludeSourceOwner
        (ReservedPreludeSourceInput source _canonical) =
    reservedSourceOwner source

reservedPreludeSourceLabel
    :: ReservedPreludeSourceInput
    -> FilePath
reservedPreludeSourceLabel
        (ReservedPreludeSourceInput source _canonical) =
    reservedSourceLabel source

reservedPreludeSourceCanonicalPath
    :: ReservedPreludeSourceInput
    -> Maybe CanonicalPath
reservedPreludeSourceCanonicalPath
        (ReservedPreludeSourceInput _source canonical) =
    canonical

reservedPreludeSourceBytes
    :: ReservedPreludeSourceInput
    -> ByteString
reservedPreludeSourceBytes
        (ReservedPreludeSourceInput source _canonical) =
    reservedSourceBytes source

reservedPreludeSourceText :: ReservedPreludeSourceInput -> Text
reservedPreludeSourceText
        (ReservedPreludeSourceInput source _canonical) =
    reservedSourceText source

-- | Reject an ordinary source graph containing the reserved prelude, whether
-- it was selected through the packaged path or through its standard logical
-- library path.
rejectOrdinaryPreludeSourceGraph
    :: ReservedPreludeSourceInput
    -> ResolvedSourceGraph
    -> Either SourceError ()
rejectOrdinaryPreludeSourceGraph sourceInput graph =
    case listToMaybe
            [ source
            | node <- sourceGraphNodes graph
            , let source = sourceNodeResolved node
            , isReservedPreludeSource source
            ] of
        Nothing ->
            Right ()
        Just source ->
            Left (ReservedPreludeSelectedAsOrdinarySource source)
  where
    isReservedPreludeSource source =
        maybe False
            (== resolvedSourceCanonicalPath source)
            (reservedPreludeSourceCanonicalPath sourceInput)
        || isLogicalPreludeSource source

    isLogicalPreludeSource source =
        let mount = resolvedSourceMount source
            relative =
                safeRelativePathFilePath
                    (resolvedSourceRelativePath source)
         in (mount == sourceMountId "library" && relative == "prelude.tex")
            || (mount == sourceMountId "project"
                && relative == preludeDataFilePath)

preludeDataFilePath :: FilePath
preludeDataFilePath =
    "library/prelude.tex"

preludeDiagnosticLabel :: FilePath
preludeDiagnosticLabel =
    preludeDataFilePath

data PreludeParseError
    = PreludeSyntaxPragmaFailed !SyntaxPragmaError
    | PreludeImportNotSupported ![FilePath]
    | PreludeLexiconExtractionFailed !LexiconExtractionError
    | PreludeSyntaxDeclarationFailed !SyntaxDeclarationError
    | PreludeLexiconCollision !LexiconCollision
    | PreludeSyntaxDeltaFailed !CanonicalSyntaxCollision
    | PreludeSyntaxInterfaceFailed !SyntaxInterfaceError
    | PreludeSyntaxMaterializationFailed !SyntaxMaterializationError
    | PreludeParseFailed !ParseException
    | PreludeParseInvariantFailed !Text

instance Show PreludeParseError where
    show = Text.unpack . renderPreludeParseError

renderPreludeParseError :: PreludeParseError -> Text
renderPreludeParseError = \case
    PreludeSyntaxPragmaFailed failure ->
        renderSyntaxPragmaError failure
    PreludeImportNotSupported imports ->
        preludeErrorPrefix
            <> "imports are not supported"
            <> case imports of
                [] -> ""
                _ ->
                    ": "
                        <> Text.intercalate
                            ", "
                            (Text.pack . show <$> imports)
    PreludeLexiconExtractionFailed failure ->
        Text.pack (show failure)
    PreludeSyntaxDeclarationFailed failure ->
        Text.pack (show failure)
    PreludeLexiconCollision collision ->
        Text.pack (show collision)
    PreludeSyntaxDeltaFailed collision ->
        preludeErrorPrefix
            <> "syntax delta has conflicting entries for pattern "
            <> Text.pack (show (canonicalCollisionPattern collision))
            <> ": "
            <> Text.pack
                (show (toList (canonicalCollisionEntries collision)))
    PreludeSyntaxInterfaceFailed failure ->
        preludeErrorPrefix <> renderSyntaxInterfaceError failure
    PreludeSyntaxMaterializationFailed failure ->
        preludeErrorPrefix <> renderSyntaxMaterializationError failure
    PreludeParseFailed failure ->
        preludeErrorPrefix <> Text.pack (show failure)
    PreludeParseInvariantFailed failure ->
        preludeErrorPrefix <> "parse invariant failed: " <> failure

preludeErrorPrefix :: Text
preludeErrorPrefix =
    Text.pack preludeDiagnosticLabel <> ": "

renderSyntaxInterfaceError :: SyntaxInterfaceError -> Text
renderSyntaxInterfaceError = \case
    DuplicateDirectSyntaxInterface duplicate ->
        "duplicate direct syntax input " <> Text.pack (show duplicate)
    UnexpectedBaseSyntaxInterface actual expected ->
        "base syntax interface mismatch: expected "
            <> Text.pack (show expected)
            <> ", got "
            <> Text.pack (show actual)
    SyntaxInterfaceIdMismatch asserted computed ->
        "syntax interface identity mismatch: asserted "
            <> Text.pack (show asserted)
            <> ", computed "
            <> Text.pack (show computed)

data ReservedParsedPrelude = ReservedParsedPrelude
    !FreshModuleInput
    !IdentifiedParsedModule

reservedParsedPreludeInput
    :: ReservedParsedPrelude
    -> FreshModuleInput
reservedParsedPreludeInput (ReservedParsedPrelude input _parsed) =
    input

reservedParsedPreludeModule
    :: ReservedParsedPrelude
    -> IdentifiedParsedModule
reservedParsedPreludeModule (ReservedParsedPrelude _input parsed) =
    parsed

-- | Parse reserved final-prelude input through the ordinary fresh-source path.
parseReservedPreludeSource
    :: ReservedPreludeSourceInput
    -> IO (Either PreludeParseError ReservedParsedPrelude)
parseReservedPreludeSource sourceInput =
    pure
        (case parseReservedFreshModule
                (reservedPreludeSource sourceInput)
                (sourceDescriptorForPath label) of
            Left failure -> Left (fromReservedParseError failure)
            Right (input, parsed) -> Right (ReservedParsedPrelude input parsed))
  where
    label = reservedPreludeSourceLabel sourceInput

    reservedPreludeSource
            (ReservedPreludeSourceInput source _canonical) =
        source

fromReservedParseError
    :: ReservedModuleParseError
    -> PreludeParseError
fromReservedParseError = \case
    ReservedModuleSyntaxPragmaError failure ->
        PreludeSyntaxPragmaFailed failure
    ReservedModuleImportError imports ->
        PreludeImportNotSupported imports
    ReservedModuleLexiconExtractionError failure ->
        PreludeLexiconExtractionFailed failure
    ReservedModuleSyntaxDeclarationError failure ->
        PreludeSyntaxDeclarationFailed failure
    ReservedModuleLexiconCollision collision ->
        PreludeLexiconCollision collision
    ReservedModuleSyntaxInterfaceError failure ->
        PreludeSyntaxInterfaceFailed failure
    ReservedModuleSyntaxMaterializationError failure ->
        PreludeSyntaxMaterializationFailed failure
    ReservedModuleParseException failure ->
        PreludeParseFailed failure
    ReservedModuleInvariantError message ->
        PreludeParseInvariantFailed message
