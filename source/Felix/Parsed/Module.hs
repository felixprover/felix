{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Immutable products of parsing one Felix module.
module Felix.Parsed.Module
    ( ParsedModuleImport
    , parsedModuleImport
    , parsedImportReference
    , parsedImportedAddress
    , ParsedSyntaxOccurrence
    , parsedSyntaxOccurrence
    , parsedSyntaxOccurrenceBlockIndex
    , parsedSyntaxOccurrenceLocation
    , parsedSyntaxOccurrenceMarker
    , parsedSyntaxOccurrenceEntry
    , IdentifiedParsedModule
    , freshParsedModule
    , admitParsedModule
    , ParsedModuleContextError(..)
    , identifiedParsedModuleArtefact
    , identifiedParsedModuleBlocks
    , identifiedParsedModuleSyntaxInterface
    , identifiedParsedModuleSourceContentId
    , identifiedParsedModuleKey
    , identifiedParsedModulePayload
    , identifiedParsedModuleId
    , identifiedParsedModuleSyntaxOccurrences
    , ParsedModule
    , ParsedModuleSourceBindingError(..)
    , renderParsedModuleSourceBindingError
    , bindParsedModule
    , parsedModuleIdentifiedSource
    , parsedModuleLoaded
    , parsedModuleSourceDescriptor
    , parsedModuleIdentified
    , parsedModuleResolved
    , parsedModuleAddress
    , parsedModuleImports
    , parsedModuleBlocks
    , parsedModuleSyntaxInterface
    , parsedModuleSourceContentId
    , parsedModuleKey
    , parsedModuleArtefact
    , parsedModulePayload
    , parsedModuleId
    , parsedModuleSyntaxOccurrences
    ) where

import Base
import Felix.Cache.Codec (cacheDigestHex)
import Felix.Parsed.Identity (ParsedModuleId, ParsedModuleKey, parsedModuleKeyFromSyntax)
import Felix.Parsed.Payload
import Felix.Report.Location (SourceDescriptor)
import Felix.Source
import Felix.Source.Content
    ( IdentifiedLoadedSource
    , SourceContentId
    , identifiedSourceContentId
    , identifiedSourceDescriptor
    , identifiedSourceLoaded
    , sourceContentIdDigest
    )
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface
    ( ModuleSyntaxInterface
    , SyntaxInterfaceId
    , moduleSyntaxAssertedId
    )

import Control.DeepSeq (NFData(..))
import Data.Text qualified as Text


data ParsedModuleImport = ParsedModuleImport
    !ImportRef
    !ResolvedSourceAddress
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

parsedModuleImport
    :: ImportRef
    -> ResolvedSourceAddress
    -> ParsedModuleImport
parsedModuleImport = ParsedModuleImport

parsedImportReference :: ParsedModuleImport -> ImportRef
parsedImportReference (ParsedModuleImport reference _imported) = reference

parsedImportedAddress :: ParsedModuleImport -> ResolvedSourceAddress
parsedImportedAddress (ParsedModuleImport _reference imported) = imported

-- | A decoded artifact admitted to its source-content and syntax context.
-- All syntax and parsed identity projections come from the owned artifact.
data IdentifiedParsedModule = IdentifiedParsedModule
    !SourceContentId
    !ModuleSyntaxInterface
    !DecodedParsedArtefact
    deriving stock (Show)

instance NFData IdentifiedParsedModule where
    rnf (IdentifiedParsedModule content syntax decoded) =
        rnf content `seq` rnf syntax `seq` rnf decoded

freshParsedModule
    :: SourceContentId
    -> ModuleSyntaxInterface
    -> [ImportRef]
    -> [Raw.Block]
    -> [ParsedSyntaxOccurrence]
    -> IdentifiedParsedModule
freshParsedModule content syntax imports blocks occurrences =
    IdentifiedParsedModule content syntax
        (freshParsedArtefact
            (parsedModuleKeyFromSyntax content syntax)
            imports blocks occurrences (moduleSyntaxAssertedId syntax))

data ParsedModuleContextError
    = ParsedModuleContextKeyMismatch !ParsedModuleKey !ParsedModuleKey
    | ParsedModuleSyntaxIdMismatch !SyntaxInterfaceId !SyntaxInterfaceId
    deriving stock (Show, Eq)

admitParsedModule
    :: SourceContentId
    -> ModuleSyntaxInterface
    -> DecodedParsedArtefact
    -> Either ParsedModuleContextError IdentifiedParsedModule
admitParsedModule content syntax decoded
    | expectedKey /= storedKey =
        Left (ParsedModuleContextKeyMismatch expectedKey storedKey)
    | expectedSyntax /= storedSyntax =
        Left (ParsedModuleSyntaxIdMismatch expectedSyntax storedSyntax)
    | otherwise =
        Right (IdentifiedParsedModule content syntax decoded)
  where
    expectedKey = parsedModuleKeyFromSyntax content syntax
    storedKey = parsedArtefactKey (decodedParsedArtefact decoded)
    expectedSyntax = moduleSyntaxAssertedId syntax
    storedSyntax = decodedParsedSyntaxInterface decoded

identifiedParsedModuleArtefact :: IdentifiedParsedModule -> ParsedArtefact
identifiedParsedModuleArtefact (IdentifiedParsedModule _ _ decoded) =
    decodedParsedArtefact decoded

identifiedParsedModuleBlocks :: IdentifiedParsedModule -> [Raw.Block]
identifiedParsedModuleBlocks (IdentifiedParsedModule _ _ decoded) =
    decodedParsedBlocks decoded

identifiedParsedModuleSyntaxInterface
    :: IdentifiedParsedModule -> ModuleSyntaxInterface
identifiedParsedModuleSyntaxInterface (IdentifiedParsedModule _ syntax _) =
    syntax

identifiedParsedModuleSourceContentId :: IdentifiedParsedModule -> SourceContentId
identifiedParsedModuleSourceContentId (IdentifiedParsedModule content _ _) =
    content

identifiedParsedModuleKey :: IdentifiedParsedModule -> ParsedModuleKey
identifiedParsedModuleKey = parsedArtefactKey . identifiedParsedModuleArtefact

identifiedParsedModulePayload :: IdentifiedParsedModule -> CanonicalParsedPayload
identifiedParsedModulePayload = parsedArtefactPayload . identifiedParsedModuleArtefact

identifiedParsedModuleId :: IdentifiedParsedModule -> ParsedModuleId
identifiedParsedModuleId = parsedArtefactId . identifiedParsedModuleArtefact

identifiedParsedModuleSyntaxOccurrences
    :: IdentifiedParsedModule -> [ParsedSyntaxOccurrence]
identifiedParsedModuleSyntaxOccurrences (IdentifiedParsedModule _ _ decoded) =
    decodedParsedOccurrences decoded

data ParsedModuleSourceBindingError
    = ParsedModuleSourceContentMismatch !SourceContentId !SourceContentId
    | ParsedModuleImportMismatch ![ImportRef] ![ImportRef]
    deriving stock (Eq, Generic)
    deriving anyclass (NFData)

instance Show ParsedModuleSourceBindingError where
    show = Text.unpack . renderParsedModuleSourceBindingError

renderParsedModuleSourceBindingError
    :: ParsedModuleSourceBindingError
    -> Text
renderParsedModuleSourceBindingError = \case
    ParsedModuleSourceContentMismatch sourceContent parsedContent ->
        "parsed module source content identity mismatch: loaded source has "
            <> renderSourceContentId sourceContent
            <> ", parsed payload names "
            <> renderSourceContentId parsedContent
    ParsedModuleImportMismatch sourceImports parsedImports ->
        "parsed module import references disagree: source graph has "
            <> Text.pack (show sourceImports)
            <> ", parsed payload names "
            <> Text.pack (show parsedImports)
  where
    renderSourceContentId = cacheDigestHex . sourceContentIdDigest


data ParsedModule = ParsedModule
    !IdentifiedLoadedSource
    ![ParsedModuleImport]
    !IdentifiedParsedModule
    deriving stock (Show)

instance NFData ParsedModule where
    rnf (ParsedModule source imports identified) =
        rnf source `seq` rnf imports `seq` rnf identified

bindParsedModule
    :: IdentifiedLoadedSource
    -> [ParsedModuleImport]
    -> IdentifiedParsedModule
    -> Either ParsedModuleSourceBindingError ParsedModule
bindParsedModule source imports identified@(IdentifiedParsedModule _ _ decoded)
    | sourceContent /= parsedContent =
        Left (ParsedModuleSourceContentMismatch sourceContent parsedContent)
    | sourceImports /= parsedImports =
        Left (ParsedModuleImportMismatch sourceImports parsedImports)
    | otherwise =
        Right (ParsedModule source imports identified)
  where
    sourceContent = identifiedSourceContentId source
    parsedContent = identifiedParsedModuleSourceContentId identified
    sourceImports = parsedImportReference <$> imports
    parsedImports = decodedParsedImports decoded

parsedModuleIdentifiedSource :: ParsedModule -> IdentifiedLoadedSource
parsedModuleIdentifiedSource (ParsedModule source _imports _identified) =
    source

parsedModuleLoaded :: ParsedModule -> LoadedSource
parsedModuleLoaded = identifiedSourceLoaded . parsedModuleIdentifiedSource

parsedModuleSourceDescriptor :: ParsedModule -> SourceDescriptor
parsedModuleSourceDescriptor = identifiedSourceDescriptor . parsedModuleIdentifiedSource

parsedModuleIdentified :: ParsedModule -> IdentifiedParsedModule
parsedModuleIdentified (ParsedModule _source _imports identified) =
    identified

parsedModuleResolved :: ParsedModule -> ResolvedSource
parsedModuleResolved = loadedSource . parsedModuleLoaded

parsedModuleAddress :: ParsedModule -> ResolvedSourceAddress
parsedModuleAddress = resolvedSourceAddress . parsedModuleResolved

parsedModuleImports :: ParsedModule -> [ParsedModuleImport]
parsedModuleImports (ParsedModule _source imports _identified) = imports

parsedModuleBlocks :: ParsedModule -> [Raw.Block]
parsedModuleBlocks (ParsedModule _source _imports identified) =
    identifiedParsedModuleBlocks identified

parsedModuleSyntaxInterface :: ParsedModule -> ModuleSyntaxInterface
parsedModuleSyntaxInterface (ParsedModule _source _imports identified) =
    identifiedParsedModuleSyntaxInterface identified

parsedModuleSourceContentId :: ParsedModule -> SourceContentId
parsedModuleSourceContentId =
    identifiedSourceContentId . parsedModuleIdentifiedSource

parsedModuleKey :: ParsedModule -> ParsedModuleKey
parsedModuleKey (ParsedModule _source _imports identified) =
    identifiedParsedModuleKey identified

parsedModuleArtefact :: ParsedModule -> ParsedArtefact
parsedModuleArtefact = identifiedParsedModuleArtefact . parsedModuleIdentified

parsedModulePayload :: ParsedModule -> CanonicalParsedPayload
parsedModulePayload (ParsedModule _source _imports identified) =
    identifiedParsedModulePayload identified

parsedModuleId :: ParsedModule -> ParsedModuleId
parsedModuleId (ParsedModule _source _imports identified) =
    identifiedParsedModuleId identified

parsedModuleSyntaxOccurrences
    :: ParsedModule
    -> [ParsedSyntaxOccurrence]
parsedModuleSyntaxOccurrences
        (ParsedModule _source _imports identified) =
    identifiedParsedModuleSyntaxOccurrences identified
