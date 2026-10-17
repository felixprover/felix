{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

-- | Parsing over an already resolved physical source graph.
module Felix.Parse
    ( ParseException(..)
    , parseExceptionDiagnostic
    , ParseWorkspaceError(..)
    , renderParseWorkspaceError
    , parseWorkspaceErrorDiagnostic
    , renderSyntaxMaterializationError
    , ParseExecutionError(..)
    , PresentationDemand(..)
    , ParsePresentation(..)
    , SourceCompletionMeasurements(..)
    , sourceBodyScanCount
    , ParsedArtefactAccess(..)
    , ParseExecution
    , parseExecutionWorkspace
    , parseExecutionPresentation
    , parseExecutionMeasurements
    , parseResolvedSourceGraphExecution
    , ParsedArtefactIntegrityError(..)
    , SyntaxDeclarationError(..)
    , LexiconCollision
    , LexiconCollisionOrigin(..)
    , lexiconCollisionPattern
    , lexiconCollisionOrigins
    , lexiconCollisionDeclarations
    , lexiconCollisionFirstDeclaration
    , lexiconCollisionSecondDeclaration
    , LexiconExtractionError(..)
    , ReservedSource
    , reservedSource
    , reservedSourceFromText
    , reservedSourceOwner
    , reservedSourceLabel
    , reservedSourceBytes
    , reservedSourceText
    , FreshModuleInput
    , ReservedModuleParseError(..)
    , freshModuleInputOwner
    , freshModuleInputIsReserved
    , freshModuleInputSourceDescriptor
    , freshModuleInputContentId
    , freshModuleInputLocationPath
    , freshModuleInputBytes
    , freshModuleInputImports
    , freshModuleInputSyntaxInterface
    , parseReservedFreshModule
    , parsePreparedTokenChunk
    , parseSourceWorkspaceWithSyntaxInputs
    , parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
    , parseSourceWorkspaceWithStoreAndSyntaxInputs
    , parseSourceWorkspaceWithStoreAndSyntaxInputsAndGraphValidation
    , parseResolvedSourceGraph
    , parseResolvedSourceGraphWithSyntaxInputs
    , parseResolvedSourceGraphWithStoreAndSyntaxInputsAndGraphValidation
    ) where

import Base
import Felix.Parsed.Identity qualified as Parsed
import Felix.Parsed.Module
import Felix.Parsed.Payload qualified as Parsed
import Felix.Parsed.Workspace
import Felix.Module
import Felix.Source
import Felix.Source.Content qualified as Content
import Felix.Source.Graph
import Felix.Source.Scan qualified as SourceScan
import Felix.Store qualified as Store
import Felix.Report.Diagnostic
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Adapt
    ( LexiconExtractionError(..)
    , ExtractedLexiconItem
    , prepareLexicalChunk
    , preparedLexicalTokens
    , preparedLexicalItems
    , SyntaxMaterializationError(..)
    , canonicalExtractedItem
    , materializeSyntaxDelta
    , extractedItemMarker
    )
import Felix.Syntax.Concrete (ConcreteSyntaxError, grammarPrepared)
import Felix.Syntax.Earley qualified as EarleySession
import Felix.Syntax.Interface
import Felix.Syntax.Lexicon (Lexicon)
import Felix.Syntax.Prepared (prepareLexicon, forcePreparedLexicon)
import Felix.Syntax.Pragma
import Felix.Syntax.Token

import Control.DeepSeq (force)
import Control.Exception (Exception, evaluate)
import Control.Monad (foldM, unless, when)
import Control.Monad.Trans.Except
    ( ExceptT(..)
    , runExceptT
    , throwE
    , withExceptT
    )
import Data.Bifunctor qualified as Bifunctor
import Data.List (intercalate)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.ByteString (ByteString)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.Encoding.Error (UnicodeException)
import Numeric.Natural (Natural)
import Text.Earley (Parser, Report(..), fullParses)
import Prettyprinter (Doc)


data ParseException
    = UnconsumedTokens [Text] (NonEmpty (Located Token))
    | AmbiguousParse !Int
    | EmptyParse
    | ConcreteSyntaxFailure !ConcreteSyntaxError
    | TokenError String
    | SourceScannerInvariant !SourceScan.SourceScanInvariantError
    | LexiconExtractionFailure !LexiconExtractionError

instance Show ParseException where
    show = \case
        UnconsumedTokens expectations (locatedToken :| locatedTokens) ->
            let token = unLocated locatedToken
                tokens = unLocated <$> locatedTokens
            in
                "unconsumed " <> describeToken token <> " at "
                    <> prettyLocation (startPos locatedToken) <> "\n"
                    <> "  " <> unwords (tokToString <$> (token : take 4 tokens)) <> "\n"
                    <> "  " <> replicate (length (tokToString token)) '^' <> "\n"
                    <> case retainedExpectations expectations of
                        [] ->
                            "while expecting nothing"
                        retained ->
                            "while expecting one of the following:\n"
                                <> intercalate ", "
                                    (Text.unpack <$> retained)
                                <> omittedExpectationSuffix expectations
        AmbiguousParse parseCount ->
            "ambiguous parse: " <> show parseCount <> " distinct parses"
        EmptyParse ->
            "empty parse"
        ConcreteSyntaxFailure failure ->
            show failure
        TokenError err ->
            err
        SourceScannerInvariant failure ->
            Text.unpack (SourceScan.renderSourceScanInvariantError failure)
        LexiconExtractionFailure err ->
            show err

instance Exception ParseException

parseExceptionDiagnostic :: ParseException -> Maybe Diagnostic
parseExceptionDiagnostic = \case
    UnconsumedTokens expectations (locatedToken :| locatedTokens) ->
        let retained = retainedExpectations expectations
            omitted = omittedExpectationCount expectations
            token = unLocated locatedToken
            following = take 4 (unLocated <$> locatedTokens)
        in Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticParseUnconsumedInput
                , diagnosticTitle = "the parser could not continue at this token"
                , diagnosticPrimary = Just (startPos locatedToken)
                , diagnosticMessage =
                    pretty
                        ("unconsumed " <> Text.pack (describeToken token)
                            <> " `" <> Text.pack (tokToString token) <> "`")
                , diagnosticNotes =
                    expectationNotes retained omitted
                        <> [ pretty
                                ("token context: "
                                    <> Text.pack
                                        (unwords
                                            (tokToString
                                                <$> (token : following))))
                           ]
                , diagnosticHelp =
                    [pretty ("check the syntax near the marked token" :: Text)]
                }
    AmbiguousParse parseCount ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticParseAmbiguous
                , diagnosticTitle = "the source has more than one distinct parse"
                , diagnosticPrimary = Nothing
                , diagnosticMessage =
                    pretty
                        (Text.pack (show parseCount)
                            <> " distinct parses remain after deduplication")
                , diagnosticNotes = []
                , diagnosticHelp =
                    [ pretty
                        ("make the notation or grouping more explicit" :: Text)
                    ]
                }
    _failure -> Nothing

parseExpectationLimit :: Int
parseExpectationLimit = 8

uniqueExpectations :: [Text] -> [Text]
uniqueExpectations = nubOrd

retainedExpectations :: [Text] -> [Text]
retainedExpectations = take parseExpectationLimit . uniqueExpectations

omittedExpectationCount :: [Text] -> Int
omittedExpectationCount expectations =
    length unique - length (take parseExpectationLimit unique)
  where
    unique = uniqueExpectations expectations

omittedExpectationSuffix :: [Text] -> String
omittedExpectationSuffix expectations =
    let omitted = omittedExpectationCount expectations
    in if omitted == 0
        then ""
        else "\n  (" <> show omitted <> " additional expectations omitted)"

expectationNotes :: [Text] -> Int -> [Doc ()]
expectationNotes retained omitted =
    [ pretty
        (if null retained
            then ("the parser accepted no continuation here" :: Text)
            else "expected one of: " <> Text.intercalate ", " retained)
    ]
        <> [ pretty
                (Text.pack (show omitted)
                    <> " additional expectations omitted")
           | omitted > 0
           ]


data ParseWorkspaceError
    = SourceWorkspaceError !SourceError
    | SourceLexiconCollision !LexiconCollision
    | SourceSyntaxPragmaError !ResolvedSource !SyntaxPragmaError
    | SourceSyntaxDeclarationError
        !ResolvedSource
        !SyntaxDeclarationError
    | SourceSyntaxMaterializationError
        !SyntaxMaterializationError
    | SourceParsedModuleKeyError
        !ResolvedSource
        !Parsed.ParsedModuleKeyError
    | SourceParsedModuleBindingInvariant
        !ResolvedSource
        !ParsedModuleSourceBindingError
    | SourceParseError !ResolvedSource !ParseException

instance Exception ParseWorkspaceError

instance Show ParseWorkspaceError where
    show = Text.unpack . renderParseWorkspaceError

renderParseWorkspaceError :: ParseWorkspaceError -> Text
renderParseWorkspaceError = \case
    SourceWorkspaceError err ->
        renderSourceError err
    SourceLexiconCollision collision ->
        Text.pack (show collision)
    SourceSyntaxPragmaError source err ->
        resolvedSourceLabel source <> ": " <> renderSyntaxPragmaError err
    SourceSyntaxDeclarationError source err ->
        resolvedSourceLabel source <> ": " <> Text.pack (show err)
    SourceSyntaxMaterializationError err ->
        renderSyntaxMaterializationError err
    SourceParsedModuleKeyError source err ->
        resolvedSourceLabel source
            <> ": parsed module has duplicate direct syntax input "
            <> case err of
                Parsed.DuplicateParsedDirectSyntaxInput duplicate ->
                    Text.pack (show duplicate)
    SourceParsedModuleBindingInvariant source err ->
        resolvedSourceLabel source
            <> ": parsed module source binding failed: "
            <> renderParsedModuleSourceBindingError err
    SourceParseError source err ->
        resolvedSourceLabel source <> ": " <> Text.pack (show err)

parseWorkspaceErrorDiagnostic :: ParseWorkspaceError -> Maybe Diagnostic
parseWorkspaceErrorDiagnostic = \case
    SourceParseError source failure ->
        fmap (addSourceWhenUnlocated source)
            (parseExceptionDiagnostic failure)
    _failure -> Nothing
  where
    addSourceWhenUnlocated source diagnostic =
        case diagnosticPrimary diagnostic of
            Just _location -> diagnostic
            Nothing ->
                diagnostic
                    { diagnosticNotes =
                        pretty ("source: " <> resolvedSourceLabel source)
                            : diagnosticNotes diagnostic
                    }

data ParsedArtefactIntegrityError
    = ParsedArtefactImportMismatch ![ImportRef] ![ImportRef]
    | ParsedArtefactOccurrenceFailure !Text
    | ParsedArtefactAssociationFailure !SyntaxDeclarationError
    | ParsedArtefactSyntaxFailure !ParseWorkspaceError
    | ParsedArtefactContextKeyMismatch
        !Parsed.ParsedModuleKey !Parsed.ParsedModuleKey
    | ParsedArtefactSyntaxInterfaceMismatch
        !SyntaxInterfaceId !SyntaxInterfaceId
    | ParsedArtefactSourceBindingMismatch
        !ParsedModuleSourceBindingError
    deriving stock (Show)

data ParseExecutionError
    = ParseExecutionWorkspaceError !ParseWorkspaceError
    | ParseExecutionStoreFailure !Store.StoreFailure
    | ParseExecutionArtefactIntegrityFailure
        !ResolvedSource
        !ParsedArtefactIntegrityError
    deriving stock (Show)

data PresentationDemand
    = NoPresentation
    | HtmlPresentationRequested
    deriving stock (Show, Eq)

data ParsePresentation
    = ParseWithoutPresentation
    | ParseWithPresentation
        !(NonEmpty SourceScan.SourcePresentationEntry)
    deriving stock (Show, Eq)

data SourceCompletionMeasurements = SourceCompletionMeasurements
    { verificationCompletionWorkNanoseconds :: !Word64
    , presentationOnlyCompletionWorkNanoseconds :: !Word64
    , verificationCompletionCount :: !Natural
    , presentationOnlyCompletionCount :: !Natural
    }
    deriving stock (Show, Eq)

sourceBodyScanCount :: SourceCompletionMeasurements -> Natural
sourceBodyScanCount measurements =
    verificationCompletionCount measurements
        + presentationOnlyCompletionCount measurements

data ParsedArtefactAccess
    = UncachedParsedArtefacts
    | PersistentParsedArtefacts !Store.Store

data ParseExecution = ParseExecution
    !ParsedSourceWorkspace
    !ParsePresentation
    !SourceCompletionMeasurements

parseExecutionWorkspace :: ParseExecution -> ParsedSourceWorkspace
parseExecutionWorkspace (ParseExecution workspace _presentation _measurements) =
    workspace

parseExecutionPresentation :: ParseExecution -> ParsePresentation
parseExecutionPresentation (ParseExecution _workspace presentation _measurements) =
    presentation

parseExecutionMeasurements
    :: ParseExecution
    -> SourceCompletionMeasurements
parseExecutionMeasurements
        (ParseExecution _workspace _presentation measurements) =
    measurements

renderSyntaxMaterializationError :: SyntaxMaterializationError -> Text
renderSyntaxMaterializationError = \case
    MaterializedSyntaxCollision collision ->
        "effective syntax has conflicting entries for pattern "
            <> Text.pack (show (canonicalCollisionPattern collision))
            <> ": "
            <> Text.pack
                (show (toList (canonicalCollisionEntries collision)))
    PrefixPredicateArityOutOfRange arity ->
        "prefix predicate arity is outside the supported range: "
            <> Text.pack (show arity)

resolvedSourceLabel :: ResolvedSource -> Text
resolvedSourceLabel source =
    sourceMountIdText (resolvedSourceMount source)
        <> ":"
        <> Text.pack
            (safeRelativePathFilePath
                (resolvedSourceRelativePath source))

data SyntaxDeclarationError
    = SyntaxPragmaOutsideDeclaration !Location
    | DuplicateSyntaxPragma !Location !Location
    | IrrelevantSyntaxPragma !Location !Location
    | MissingSyntaxPragma !Location !Raw.Pattern
    | AmbiguousSyntaxPragmaTarget
        !Location
        !(NonEmpty Raw.Pattern)
    | MultipleNewSyntaxPatternsWithoutPragma
        !Location
        !(NonEmpty Raw.Pattern)
    | SyntaxPragmaOnFixedReuse !Location !Raw.Pattern
    | SyntaxPragmaOnImportedReuse !Location !Raw.Pattern
    | SyntaxOccurrenceMarkerMismatch
        !Location
        !Raw.Marker
        !Raw.Marker
    | SyntaxOccurrenceMissingBlockMarker
        !Location
        !Raw.Marker
    deriving stock (Eq)

instance Show SyntaxDeclarationError where
    show = \case
        SyntaxPragmaOutsideDeclaration location ->
            "syntax pragma at "
                <> prettyLocation location
                <> " is outside a syntax-producing declaration"
        DuplicateSyntaxPragma first second ->
            "duplicate syntax pragma at "
                <> prettyLocation second
                <> "; the first pragma is at "
                <> prettyLocation first
        IrrelevantSyntaxPragma pragma declaration ->
            "syntax pragma at "
                <> prettyLocation pragma
                <> " does not apply to the declaration at "
                <> prettyLocation declaration
        MissingSyntaxPragma location pat ->
            "expression pattern "
                <> show pat
                <> " at "
                <> prettyLocation location
                <> " requires a syntax pragma"
        AmbiguousSyntaxPragmaTarget location patterns ->
            "syntax pragma at "
                <> prettyLocation location
                <> " has several eligible patterns: "
                <> intercalate ", " (show <$> toList patterns)
        MultipleNewSyntaxPatternsWithoutPragma location patterns ->
            "syntax declaration at "
                <> prettyLocation location
                <> " has several new eligible patterns that V1 cannot select between: "
                <> intercalate ", " (show <$> toList patterns)
                <> "; make the declaration unambiguous"
        SyntaxPragmaOnFixedReuse location pat ->
            "syntax pragma at "
                <> prettyLocation location
                <> " cannot override fixed-base pattern "
                <> show pat
        SyntaxPragmaOnImportedReuse location pat ->
            "syntax pragma at "
                <> prettyLocation location
                <> " cannot override imported pattern "
                <> show pat
        SyntaxOccurrenceMarkerMismatch
                location
                extractedMarker
                actual ->
            "syntax declaration at "
                <> prettyLocation location
                <> " has extracted-item marker "
                <> show extractedMarker
                <> " but parsed block marker "
                <> show actual
        SyntaxOccurrenceMissingBlockMarker location extractedMarker ->
            "syntax declaration at "
                <> prettyLocation location
                <> " with extracted-item marker "
                <> show extractedMarker
                <> " is associated with a block without a marker"

data LexiconCollisionOrigin
    = FixedLexiconOrigin !CanonicalLexicalEntry
    | ImportedLexiconOrigin
        !CanonicalLexicalEntry
        !SyntaxInterfaceId
    | SourceLexiconOrigin
        !CanonicalLexicalEntry
        !ResolvedSource
        !Location
    | ReservedLexiconOrigin
        !CanonicalLexicalEntry
        !FilePath
        !Location
    deriving stock (Show, Eq, Ord)

data LexiconCollision = LexiconCollision
    !Raw.Pattern
    !LexiconCollisionOrigin
    !LexiconCollisionOrigin
    ![LexiconCollisionOrigin]
    deriving stock (Eq)

lexiconCollisionPattern :: LexiconCollision -> Raw.Pattern
lexiconCollisionPattern
        (LexiconCollision pat _first _second _rest) =
    pat

lexiconCollisionOrigins
    :: LexiconCollision
    -> NonEmpty LexiconCollisionOrigin
lexiconCollisionOrigins
        (LexiconCollision _pat first second rest) =
    first :| (second : rest)

lexiconCollisionDeclarations :: LexiconCollision -> [Location]
lexiconCollisionDeclarations collision =
    [ location
    | Just location <-
        originLocation
            <$> toList
                (lexiconCollisionOrigins collision)
    ]

lexiconCollisionFirstDeclaration
    :: LexiconCollision
    -> Maybe Location
lexiconCollisionFirstDeclaration =
    listToMaybe . lexiconCollisionDeclarations

lexiconCollisionSecondDeclaration
    :: LexiconCollision
    -> Maybe Location
lexiconCollisionSecondDeclaration collision =
    listToMaybe
        (drop 1 (lexiconCollisionDeclarations collision))

originLocation :: LexiconCollisionOrigin -> Maybe Location
originLocation = \case
    FixedLexiconOrigin _entry ->
        Nothing
    ImportedLexiconOrigin _entry _interface ->
        Nothing
    SourceLexiconOrigin _entry _source location ->
        Just location
    ReservedLexiconOrigin _entry _label location ->
        Just location

instance Show LexiconCollision where
    show collision =
        "lexical pattern "
            <> show (lexiconCollisionPattern collision)
            <> " has conflicting providers:\n"
            <> unlines
                [ "  " <> renderOrigin origin
                | origin <- toList (lexiconCollisionOrigins collision)
                ]
      where
        origins =
            toList (lexiconCollisionOrigins collision)

        renderOrigin = \case
            FixedLexiconOrigin entry ->
                "fixed base entry " <> show entry
            ImportedLexiconOrigin entry interface ->
                "implicit syntax interface "
                    <> show interface
                    <> " provides "
                    <> show entry
            SourceLexiconOrigin entry source location ->
                "source declaration at "
                    <> renderSourceLocation origins source location
                    <> " provides "
                    <> show entry
            ReservedLexiconOrigin entry label location ->
                "reserved declaration at "
                    <> prettyLocation location
                    <> " ("
                    <> show label
                    <> ") provides "
                    <> show entry

renderSourceLocation
    :: [LexiconCollisionOrigin]
    -> ResolvedSource
    -> Location
    -> String
renderSourceLocation origins source location
    | any sameDisplayDifferentSource origins =
        prettyLocation location
            <> " (canonical "
            <> show
                (canonicalPathFilePath
                    (resolvedSourceCanonicalPath source))
            <> ")"
    | otherwise =
        prettyLocation location
  where
    sameDisplayDifferentSource = \case
        FixedLexiconOrigin _entry ->
            False
        ImportedLexiconOrigin _entry _interface ->
            False
        SourceLexiconOrigin _entry other otherLocation ->
            locFile otherLocation == locFile location
                && resolvedSourceCanonicalPath other
                    /= resolvedSourceCanonicalPath source
        ReservedLexiconOrigin{} ->
            False


data ReservedSource = ReservedSource
    !ModuleName
    !FilePath
    !ByteString
    !Text
    !Content.SourceContentId
    deriving stock (Show, Eq)

reservedSource
    :: ModuleName
    -> FilePath
    -> ByteString
    -> Either UnicodeException ReservedSource
reservedSource owner label bytes =
    (\sourceText ->
        ReservedSource
            owner
            label
            bytes
            sourceText
            (Content.sourceContentIdBytes bytes))
        <$> Text.decodeUtf8' bytes

reservedSourceFromText :: ModuleName -> FilePath -> Text -> ReservedSource
reservedSourceFromText owner label sourceText =
    let bytes = Text.encodeUtf8 sourceText
    in ReservedSource
        owner
        label
        bytes
        sourceText
        (Content.sourceContentIdBytes bytes)

reservedSourceOwner :: ReservedSource -> ModuleName
reservedSourceOwner (ReservedSource owner _label _bytes _text _content) = owner

reservedSourceLabel :: ReservedSource -> FilePath
reservedSourceLabel (ReservedSource _owner label _bytes _text _content) = label

reservedSourceBytes :: ReservedSource -> ByteString
reservedSourceBytes (ReservedSource _owner _label bytes _text _content) = bytes

reservedSourceText :: ReservedSource -> Text
reservedSourceText
        (ReservedSource _owner _label _bytes sourceText _content) =
    sourceText

reservedSourceContentId :: ReservedSource -> Content.SourceContentId
reservedSourceContentId
        (ReservedSource _owner _label _bytes _text content) =
    content

data FreshSource
    = FreshPhysical !Content.IdentifiedLoadedSource
    | FreshReserved !ReservedSource !SourceDescriptor

data FreshModuleInput = FreshModuleInput
    !FreshSource
    ![ImportRef]
    !ModuleSyntaxInterface

data ReservedModuleParseError
    = ReservedModuleSyntaxPragmaError !SyntaxPragmaError
    | ReservedModuleImportError ![FilePath]
    | ReservedModuleLexiconExtractionError !LexiconExtractionError
    | ReservedModuleSyntaxDeclarationError !SyntaxDeclarationError
    | ReservedModuleLexiconCollision !LexiconCollision
    | ReservedModuleSyntaxInterfaceError !SyntaxInterfaceError
    | ReservedModuleSyntaxMaterializationError !SyntaxMaterializationError
    | ReservedModuleParseException !ParseException
    | ReservedModuleInvariantError !Text
    deriving stock (Show)

freshModuleInput
    :: FreshSource
    -> [ImportRef]
    -> ModuleSyntaxInterface
    -> FreshModuleInput
freshModuleInput source imports syntax =
    FreshModuleInput source imports syntax

freshModuleInputOwner :: FreshModuleInput -> ModuleName
freshModuleInputOwner
        (FreshModuleInput source _imports _syntax) =
    case source of
        FreshPhysical identified ->
            moduleName
                (resolvedSourceAddress
                    (loadedSource
                        (Content.identifiedSourceLoaded identified)))
        FreshReserved reserved _descriptor ->
            reservedSourceOwner reserved

freshModuleInputIsReserved :: FreshModuleInput -> Bool
freshModuleInputIsReserved
        (FreshModuleInput source _imports _syntax) =
    case source of
        FreshPhysical{} -> False
        FreshReserved{} -> True

freshModuleInputSourceDescriptor :: FreshModuleInput -> SourceDescriptor
freshModuleInputSourceDescriptor
        (FreshModuleInput source _imports _syntax) =
    case source of
        FreshPhysical identified ->
            Content.identifiedSourceDescriptor identified
        FreshReserved _reserved descriptor ->
            descriptor

freshModuleInputContentId
    :: FreshModuleInput
    -> Content.SourceContentId
freshModuleInputContentId
        (FreshModuleInput source _imports _syntax) =
    case source of
        FreshPhysical identified ->
            Content.identifiedSourceContentId identified
        FreshReserved reserved _descriptor ->
            reservedSourceContentId reserved

freshModuleInputLocationPath :: FreshModuleInput -> FilePath
freshModuleInputLocationPath
        (FreshModuleInput source _imports _syntax) =
    case source of
        FreshPhysical identified ->
            resolvedSourceLocationPath
                (loadedSource
                    (Content.identifiedSourceLoaded identified))
        FreshReserved reserved _descriptor ->
            reservedSourceLabel reserved

freshModuleInputBytes :: FreshModuleInput -> ByteString
freshModuleInputBytes
        (FreshModuleInput source _imports _syntax) =
    case source of
        FreshPhysical identified ->
            loadedBytes (Content.identifiedSourceLoaded identified)
        FreshReserved reserved _descriptor -> reservedSourceBytes reserved

freshModuleInputImports :: FreshModuleInput -> [ImportRef]
freshModuleInputImports
        (FreshModuleInput _source imports _syntax) =
    imports

freshModuleInputSyntaxInterface
    :: FreshModuleInput
    -> ModuleSyntaxInterface
freshModuleInputSyntaxInterface
        (FreshModuleInput _source _imports syntax) =
    syntax


identifyParsedModule
    :: FreshModuleInput
    -> [Raw.Block]
    -> [ParsedSyntaxOccurrence]
    -> IdentifiedParsedModule
identifyParsedModule input =
    freshParsedModule
        (freshModuleInputContentId input)
        (freshModuleInputSyntaxInterface input)
        (freshModuleInputImports input)

-- | Parse one reserved, import-free module through the ordinary tokenizer,
-- lexicon-extraction, syntax, grammar, and occurrence-association stages.
parseReservedFreshModule
    :: ReservedSource
    -> SourceDescriptor
    -> Either
        ReservedModuleParseError
        (FreshModuleInput, IdentifiedParsedModule)
parseReservedFreshModule reserved descriptor = do
    verification <-
        case SourceScan.scanCompleteVerificationText
                descriptor label sourceText of
            Left (SourceScan.SourceInputFailure failure) ->
                Left (reservedVerificationScanError failure)
            Left (SourceScan.SourceScannerInvariantFailure failure) ->
                Left
                    (ReservedModuleInvariantError
                        (SourceScan.renderSourceScanInvariantError failure))
            Right result -> Right result
    let imports = unLocated <$> SourceScan.verificationImports verification
        pragmas = SourceScan.verificationPragmas verification
        tokenChunks = SourceScan.verificationChunks verification
    SourceScan.forceVerificationScanHandoff verification `seq` pure ()
    unless (null imports)
        (Left (ReservedModuleImportError imports))
    associated <-
        Bifunctor.first ReservedModuleSyntaxDeclarationError
            (associateSyntaxPragmas tokenChunks pragmas)
    chunks <- traverse extractReservedChunk (zip tokenChunks associated)
    (localEntries, preparedOccurrences) <-
        Bifunctor.first reservedLocalSyntaxError
            (prepareLocalSyntax
                0
                (ReservedSyntaxSite label)
                Map.empty
                chunks)
    delta <-
        Bifunctor.first reservedLocalSyntaxError
            (validateSyntaxInventory localEntries)
    syntax <-
        Bifunctor.first ReservedModuleSyntaxInterfaceError
            (moduleSyntaxInterface [] delta)
    lexicon <-
        Bifunctor.first ReservedModuleSyntaxMaterializationError
            (materializeSyntaxDelta delta)
    let input =
            freshModuleInput
                (FreshReserved reserved descriptor)
                []
                syntax
    let preparedLexicon = prepareLexicon lexicon
    forcePreparedLexicon preparedLexicon `seq` pure ()
    unless (length chunks == length preparedOccurrences)
        (Left (ReservedModuleInvariantError
            "reserved syntax occurrence groups do not match source chunks"))
    reversed <- EarleySession.foldParses (grammarPrepared preparedLexicon)
        (\(_, ExtractedChunk tokens _ _, _) -> tokens)
        parseReservedChunk [] (zip3 [0 ..] chunks preparedOccurrences)
    let parsed = reverse reversed
        blocks = map fst parsed
        occurrences = concatMap snd parsed
    pure (input, identifyParsedModule input blocks occurrences)
  where
    label = reservedSourceLabel reserved
    sourceText = reservedSourceText reserved

    reservedVerificationScanError = \case
        SourceScan.VerificationPragmaFailure failure ->
            ReservedModuleSyntaxPragmaError failure
        failure ->
            ReservedModuleParseException
                (TokenError
                    (Text.unpack
                        (SourceScan.renderVerificationScanError failure)))

    extractReservedChunk (tokens, chunkPragmas) = do
        prepared <-
            Bifunctor.first ReservedModuleLexiconExtractionError
                (prepareLexicalChunk tokens)
        pure
            (ExtractedChunk
                (preparedLexicalTokens prepared)
                chunkPragmas
                (preparedLexicalItems prepared))

    reservedLocalSyntaxError = \case
        LocalSyntaxDeclarationError failure ->
            ReservedModuleSyntaxDeclarationError failure
        LocalSyntaxCollision collision ->
            ReservedModuleLexiconCollision collision

    parseReservedChunk
        :: [(Raw.Block, [ParsedSyntaxOccurrence])]
        -> (Int, ExtractedChunk, [PreparedSyntaxOccurrence])
        -> ([Either ConcreteSyntaxError Raw.Block], Report Text [Located Token])
        -> Either ReservedModuleParseError [(Raw.Block, [ParsedSyntaxOccurrence])]
    parseReservedChunk parsed (blockIndex, _chunk, prepared) result = do
        selected <- Bifunctor.first ReservedModuleParseException (parseChunkResult result)
        let block = force selected
        block `seq` Bifunctor.first reservedAssociationError
            (validateOccurrenceAssociation
                (ReservedSyntaxSite label)
                blockIndex
                block
                prepared)
        pure
            (( block
             , [ parsedSyntaxOccurrence
                    blockIndex
                    (syntaxSiteLocation (preparedSyntaxSite occurrence))
                    (syntaxSiteMarker (preparedSyntaxSite occurrence))
                    (preparedSyntaxEntry occurrence)
               | occurrence <- prepared
               ]
             ) : parsed)
    reservedAssociationError = \case
        OccurrenceAssociationDeclarationError failure ->
            ReservedModuleSyntaxDeclarationError failure
        OccurrenceAssociationInvariantError message ->
            ReservedModuleInvariantError message

data TokenizedModule = TokenizedModule
    !SourceNode
    ![ParsedModuleImport]
    ![SyntaxPragma]
    ![[Located Token]]

data ExtractedChunk = ExtractedChunk
    ![Located Token]
    ![SyntaxPragma]
    ![Located ExtractedLexiconItem]

data ExtractedModule = ExtractedModule
    !SourceNode
    ![ParsedModuleImport]
    ![ExtractedChunk]

data SyntaxSiteSource
    = PhysicalSyntaxSite !ResolvedSource
    | ReservedSyntaxSite !FilePath
    deriving stock (Show, Eq, Ord)

data SyntaxDeclarationSite = SyntaxDeclarationSite
    { syntaxSiteModuleIndex :: !Int
    , syntaxSiteBlockIndex :: !Int
    , syntaxSiteItemIndex :: !Int
    , syntaxSiteSource :: !SyntaxSiteSource
    , syntaxSiteLocation :: !Location
    , syntaxSiteMarker :: !Raw.Marker
    }
    deriving stock (Show, Eq, Ord)

data SyntaxEntryProvider
    = DeclarationSyntaxProvider !SyntaxDeclarationSite
    | ImplicitSyntaxProvider !SyntaxInterfaceId
    deriving stock (Show, Eq, Ord)

type SyntaxEntryInventory =
    Map CanonicalLexicalEntry (Set SyntaxEntryProvider)

data LocalSyntaxError
    = LocalSyntaxDeclarationError !SyntaxDeclarationError
    | LocalSyntaxCollision !LexiconCollision

localSyntaxWorkspaceError
    :: ResolvedSource
    -> LocalSyntaxError
    -> ParseWorkspaceError
localSyntaxWorkspaceError source = \case
    LocalSyntaxDeclarationError failure ->
        SourceSyntaxDeclarationError source failure
    LocalSyntaxCollision collision ->
        SourceLexiconCollision collision

localSyntaxCollisionWorkspaceError
    :: LocalSyntaxError
    -> ParseWorkspaceError
localSyntaxCollisionWorkspaceError = \case
    LocalSyntaxCollision collision ->
        SourceLexiconCollision collision
    LocalSyntaxDeclarationError{} ->
        impossible
            "canonical syntax validation produced a declaration error"

data OccurrenceAssociationError
    = OccurrenceAssociationDeclarationError !SyntaxDeclarationError
    | OccurrenceAssociationInvariantError !Text

occurrenceWorkspaceError
    :: ResolvedSource
    -> OccurrenceAssociationError
    -> ParseWorkspaceError
occurrenceWorkspaceError source = \case
    OccurrenceAssociationDeclarationError failure ->
        SourceSyntaxDeclarationError source failure
    OccurrenceAssociationInvariantError message ->
        SourceWorkspaceError (SourceGraphInvariantViolation message)

data PreparedSyntaxOccurrence = PreparedSyntaxOccurrence
    { preparedSyntaxSite :: !SyntaxDeclarationSite
    , preparedSyntaxEntry :: !CanonicalLexicalEntry
    }

data SyntaxItemDisposition
    = EmitSyntaxEntry !CanonicalLexicalEntry
    | ReuseFixedSyntax !CanonicalLexicalEntry
    | ReuseImportedSyntax !CanonicalLexicalEntry

data ClassifiedSyntaxItem = ClassifiedSyntaxItem
    !SyntaxDeclarationSite
    !SyntaxItemDisposition
    !Bool

data PreparedSyntaxModule = PreparedSyntaxModule
    { preparedAddress :: !ResolvedSourceAddress
    , preparedInterface :: !ModuleSyntaxInterface
    , preparedSyntaxDirectAddresses :: ![ResolvedSourceAddress]
    , preparedLocalEntries :: !SyntaxEntryInventory
    }

data FreshRuntimeSyntax = FreshRuntimeSyntax
    { freshRuntimePrepared :: !PreparedSyntaxModule
    , freshRuntimeLexicon :: !Lexicon
    , freshRuntimeOccurrences :: ![[PreparedSyntaxOccurrence]]
    }

data ModuleSyntaxContext = ModuleSyntaxContext
    { syntaxContextDirectIds :: ![SyntaxInterfaceId]
    , syntaxContextDirectAddresses :: ![ResolvedSourceAddress]
    , syntaxContextImportedEntries :: !SyntaxEntryInventory
    }

parseSourceWorkspaceWithSyntaxInputs
    :: SourceMounts
    -> RootRequest
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> IO (Either ParseWorkspaceError ParsedSourceWorkspace)
-- Implicit syntax inputs must be self-contained module interfaces.
parseSourceWorkspaceWithSyntaxInputs mounts request syntaxInputs =
    parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
        mounts
        request
        syntaxInputs
        (const (Right ()))

parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
    :: SourceMounts
    -> RootRequest
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> (ResolvedSourceGraph -> Either SourceError ())
    -> IO (Either ParseWorkspaceError ParsedSourceWorkspace)
parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
        mounts request syntaxInputs validateGraph =
    buildResolvedSourceGraph mounts request >>= \case
        Left err ->
            pure (Left (SourceWorkspaceError err))
        Right graph ->
            case validateGraph graph of
                Left err -> pure (Left (SourceWorkspaceError err))
                Right () ->
                    parseResolvedSourceGraphWithSyntaxInputs
                        graph
                        syntaxInputs

parseSourceWorkspaceWithStoreAndSyntaxInputs
    :: Store.Store
    -> SourceMounts
    -> RootRequest
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> IO (Either ParseExecutionError ParsedSourceWorkspace)
parseSourceWorkspaceWithStoreAndSyntaxInputs
        store mounts request syntaxInputs =
    parseSourceWorkspaceWithStoreAndSyntaxInputsAndGraphValidation
        store mounts request syntaxInputs (const (Right ()))

parseSourceWorkspaceWithStoreAndSyntaxInputsAndGraphValidation
    :: Store.Store
    -> SourceMounts
    -> RootRequest
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> (ResolvedSourceGraph -> Either SourceError ())
    -> IO (Either ParseExecutionError ParsedSourceWorkspace)
parseSourceWorkspaceWithStoreAndSyntaxInputsAndGraphValidation
        store mounts request syntaxInputs validateGraph = do
    graphResult <- buildResolvedSourceGraph mounts request
    case graphResult of
        Left err ->
            pure
                (Left
                    (ParseExecutionWorkspaceError
                        (SourceWorkspaceError err)))
        Right graph ->
            case validateGraph graph of
                Left err ->
                    pure
                        (Left
                            (ParseExecutionWorkspaceError
                                (SourceWorkspaceError err)))
                Right () ->
                    parseResolvedSourceGraphWithArtefacts
                        (PersistentParsedArtefacts store)
                        graph
                        syntaxInputs

-- | Parse in the graph's deterministic imported-before-importer order.
--
-- Graph construction errors occur before this order exists.
--
-- Every source is tokenized from its already loaded text, so this function
-- performs no source resolution or file reads.
parseResolvedSourceGraph
    :: ResolvedSourceGraph
    -> IO (Either ParseWorkspaceError ParsedSourceWorkspace)
parseResolvedSourceGraph graph =
    parseResolvedSourceGraphWithSyntaxInputs graph (const [])

parseResolvedSourceGraphWithStoreAndSyntaxInputsAndGraphValidation
    :: Store.Store
    -> ResolvedSourceGraph
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> (ResolvedSourceGraph -> Either SourceError ())
    -> IO (Either ParseExecutionError ParsedSourceWorkspace)
parseResolvedSourceGraphWithStoreAndSyntaxInputsAndGraphValidation
        store graph syntaxInputs validateGraph =
    case validateGraph graph of
        Left err ->
            pure
                (Left
                    (ParseExecutionWorkspaceError
                        (SourceWorkspaceError err)))
        Right () ->
            parseResolvedSourceGraphWithArtefacts
                (PersistentParsedArtefacts store)
                graph
                syntaxInputs

parseResolvedSourceGraphWithSyntaxInputs
    :: ResolvedSourceGraph
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> IO (Either ParseWorkspaceError ParsedSourceWorkspace)
parseResolvedSourceGraphWithSyntaxInputs graph syntaxInputs =
    fmap unwrapUncachedExecution
        (parseResolvedSourceGraphWithArtefacts
            UncachedParsedArtefacts
            graph
            syntaxInputs)

unwrapUncachedExecution
    :: Either ParseExecutionError value
    -> Either ParseWorkspaceError value
unwrapUncachedExecution = \case
    Left (ParseExecutionWorkspaceError failure) ->
        Left failure
    Left ParseExecutionStoreFailure{} ->
        impossible "uncached parsing attempted a store operation"
    Left ParseExecutionArtefactIntegrityFailure{} ->
        impossible "uncached parsing installed a parsed artefact"
    Right value ->
        Right value

parseResolvedSourceGraphWithArtefacts
    :: ParsedArtefactAccess
    -> ResolvedSourceGraph
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> IO (Either ParseExecutionError ParsedSourceWorkspace)
parseResolvedSourceGraphWithArtefacts
        artefactAccess graph syntaxInputs =
    fmap (fmap parseExecutionWorkspace)
        (parseResolvedSourceGraphExecution
            artefactAccess
            NoPresentation
            graph
            syntaxInputs
            (const (Right ())))

parseResolvedSourceGraphExecution
    :: ParsedArtefactAccess
    -> PresentationDemand
    -> ResolvedSourceGraph
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> (ResolvedSourceGraph -> Either SourceError ())
    -> IO (Either ParseExecutionError ParseExecution)
parseResolvedSourceGraphExecution
        artefactAccess demand graph syntaxInputs validateGraph =
    case validateGraph graph of
        Left failure ->
            pure
                (Left
                    (ParseExecutionWorkspaceError
                        (SourceWorkspaceError failure)))
        Right () ->
            parseResolvedSourceGraphExecutionUnchecked
                artefactAccess demand graph syntaxInputs

parseResolvedSourceGraphExecutionUnchecked
    :: ParsedArtefactAccess
    -> PresentationDemand
    -> ResolvedSourceGraph
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> IO (Either ParseExecutionError ParseExecution)
parseResolvedSourceGraphExecutionUnchecked
        artefactAccess demand graph syntaxInputs =
    runExceptT do
        let orderedNodes =
                sourceGraphImportedBeforeImporter graph
            addresses =
                Map.fromList
                    [ ( resolvedSourceCanonicalPath
                            (sourceNodeResolved node)
                      , resolvedSourceAddress
                            (sourceNodeResolved node)
                      )
                    | node <- NonEmpty.toList orderedNodes
                    ]
        completed <- foldM
            (parseOneModule
                artefactAccess graph addresses syntaxInputs)
            (emptyModuleParseState demand)
            (zip [0 ..] (NonEmpty.toList orderedNodes))
        parsedModules <- case NonEmpty.nonEmpty
                (reverse (moduleParseReversed completed)) of
            Just modules ->
                pure modules
            Nothing ->
                throwE
                    (ParseExecutionWorkspaceError
                        (SourceWorkspaceError
                            (SourceGraphInvariantViolation
                                "source graph produced no parsed modules")))
        presentation <- case moduleParsePresentationReversed completed of
            Nothing -> pure ParseWithoutPresentation
            Just reversedEntries ->
                case NonEmpty.nonEmpty (reverse reversedEntries) of
                    Just entries -> pure (ParseWithPresentation entries)
                    Nothing ->
                        throwE
                            (ParseExecutionWorkspaceError
                                (SourceWorkspaceError
                                    (SourceGraphInvariantViolation
                                        "presentation scan produced no entries")))
        pure
            (ParseExecution
                (parsedSourceWorkspace parsedModules)
                presentation
                (moduleParseMeasurements completed))

data ModuleParseState = ModuleParseState
    { moduleParsePrepared
        :: !(Map ResolvedSourceAddress PreparedSyntaxModule)
    , moduleParseReversed :: ![ParsedModule]
    , moduleParsePresentationReversed
        :: !(Maybe [SourceScan.SourcePresentationEntry])
    , moduleParseMeasurements :: !SourceCompletionMeasurements
    }

emptyModuleParseState :: PresentationDemand -> ModuleParseState
emptyModuleParseState demand =
    ModuleParseState
        Map.empty
        []
        (case demand of
            NoPresentation -> Nothing
            HtmlPresentationRequested -> Just [])
        emptySourceCompletionMeasurements

emptySourceCompletionMeasurements :: SourceCompletionMeasurements
emptySourceCompletionMeasurements =
    SourceCompletionMeasurements
        { verificationCompletionWorkNanoseconds = 0
        , presentationOnlyCompletionWorkNanoseconds = 0
        , verificationCompletionCount = 0
        , presentationOnlyCompletionCount = 0
        }

parseOneModule
    :: ParsedArtefactAccess
    -> ResolvedSourceGraph
    -> Map CanonicalPath ResolvedSourceAddress
    -> (ResolvedSource -> [ModuleSyntaxInterface])
    -> ModuleParseState
    -> (Int, SourceNode)
    -> ExceptT ParseExecutionError IO ModuleParseState
parseOneModule artefactAccess graph addresses syntaxInputs state
        (moduleIndex, node) = do
    imports <- liftWorkspaceEither
        (resolveParsedModuleImports graph addresses node)
    context <- liftWorkspaceEither
        (prepareModuleSyntaxContext
            (moduleParsePrepared state)
            (syntaxInputs (sourceNodeResolved node))
            imports)
    key <- liftWorkspaceEither
        (moduleParsedKey node context)
    selected <- case artefactAccess of
        UncachedParsedArtefacts ->
            pure Nothing
        PersistentParsedArtefacts store ->
            liftIO (Store.loadParsedArtefact store (sourceNodeDescriptor node) key) >>= \case
                Left failure ->
                    throwE (ParseExecutionStoreFailure failure)
                Right found ->
                    pure found
    case selected of
        Just decoded ->
            installCachedModule
                moduleIndex
                node
                imports
                context
                decoded
                state
        Nothing ->
            parseAndPublishFreshModule
                artefactAccess
                moduleIndex
                node
                imports
                context
                key
                state

parseAndPublishFreshModule
    :: ParsedArtefactAccess
    -> Int
    -> SourceNode
    -> [ParsedModuleImport]
    -> ModuleSyntaxContext
    -> Parsed.ParsedModuleKey
    -> ModuleParseState
    -> ExceptT ParseExecutionError IO ModuleParseState
parseAndPublishFreshModule artefactAccess moduleIndex node imports
        context expectedKey state = do
    (tokenized, presentation, completionWork) <-
        withExceptT ParseExecutionWorkspaceError
            (ExceptT (tokenizeModule node imports))
    extracted <- withExceptT ParseExecutionWorkspaceError
        (extractTokenizedModule tokenized)
    runtime <- liftWorkspaceEither
        (prepareFreshRuntimeSyntaxModule
            moduleIndex
            context
            extracted)
    parsed <- withExceptT ParseExecutionWorkspaceError
        (parseExtractedModule runtime extracted)
    unless
        (parsedModuleKey parsed == expectedKey)
        (throwE
            (ParseExecutionWorkspaceError
                (SourceWorkspaceError
                    (SourceGraphInvariantViolation
                        "fresh parsed module key disagrees with its syntax context"))))
    case artefactAccess of
        UncachedParsedArtefacts ->
            pure ()
        PersistentParsedArtefacts store -> do
            let artefact = parsedModuleArtefact parsed
            liftIO
                (Store.writeParsedArtefact store artefact)
                >>= \case
                    Left failure ->
                        throwE (ParseExecutionStoreFailure failure)
                    Right acknowledged ->
                        unless
                            (acknowledged == artefact)
                            (throwE
                                (ParseExecutionStoreFailure
                                    Store.StoreParsedArtefactIdMismatch))
    let prepared = freshRuntimePrepared runtime
        address = preparedAddress prepared
    when
        (Map.member address (moduleParsePrepared state))
        (throwE
            (ParseExecutionWorkspaceError
                (SourceWorkspaceError
                    (SourceGraphInvariantViolation
                        "prepared syntax module address is duplicated"))))
    pure
        (retainPresentationEntry presentation
            state
            { moduleParsePrepared =
                Map.insert address prepared (moduleParsePrepared state)
            , moduleParseReversed =
                parsed : moduleParseReversed state
            , moduleParseMeasurements =
                addVerificationCompletion
                    completionWork
                    (moduleParseMeasurements state)
            })

liftWorkspaceEither
    :: Either ParseWorkspaceError value
    -> ExceptT ParseExecutionError IO value
liftWorkspaceEither =
    either (throwE . ParseExecutionWorkspaceError) pure

installCachedModule
    :: Int
    -> SourceNode
    -> [ParsedModuleImport]
    -> ModuleSyntaxContext
    -> Parsed.DecodedParsedArtefact
    -> ModuleParseState
    -> ExceptT ParseExecutionError IO ModuleParseState
installCachedModule moduleIndex node imports context decoded
        state = do
    let source = sourceNodeResolved node
        expectedImports = parsedImportReference <$> imports
        storedImports = Parsed.decodedParsedImports decoded
    unless
        (storedImports == expectedImports)
        (throwIntegrity source
            (ParsedArtefactImportMismatch expectedImports storedImports))
    localEntries <-
        either (throwIntegrity source) pure
            (prepareCachedOccurrences
                moduleIndex
                node
                context
                (Parsed.decodedParsedBlocks decoded)
                (Parsed.decodedParsedOccurrences decoded))
    (prepared, _effectiveDelta) <-
        either
            (throwIntegrity source . ParsedArtefactSyntaxFailure)
            pure
            (prepareSyntaxModule
                (resolvedSourceAddress source)
                context
                localEntries)
    identified <-
        either (throwIntegrity source . contextIntegrityError) pure
            (admitParsedModule
                (sourceNodeContentId node)
                (preparedInterface prepared)
                decoded)
    parsed <-
        either
            (throwIntegrity source . ParsedArtefactSourceBindingMismatch)
            pure
            (bindParsedModule
                (sourceNodeIdentified node)
                imports
                identified)
    forced <- liftIO (evaluate (force parsed))
    let address = preparedAddress prepared
    when
        (Map.member address (moduleParsePrepared state))
        (throwE
            (ParseExecutionWorkspaceError
                (SourceWorkspaceError
                    (SourceGraphInvariantViolation
                        "prepared syntax module address is duplicated"))))
    completion <- case moduleParsePresentationReversed state of
        Nothing -> pure Nothing
        Just _entries -> do
            completed <- liftIO (completePresentationModule node)
            case completed of
                Left failure -> throwScannerInvariant node failure
                Right result -> pure (Just result)
    let nextState =
            state
            { moduleParsePrepared =
                Map.insert address prepared (moduleParsePrepared state)
            , moduleParseReversed =
                forced : moduleParseReversed state
            , moduleParseMeasurements =
                case completion of
                    Nothing -> moduleParseMeasurements state
                    Just (_entry, presentationWork) ->
                        addPresentationOnlyCompletion
                            presentationWork
                            (moduleParseMeasurements state)
            }
    pure case completion of
        Nothing -> nextState
        Just (entry, _work) -> retainPresentationEntry entry nextState
  where
    contextIntegrityError = \case
        ParsedModuleContextKeyMismatch expectedKey storedKey ->
            ParsedArtefactContextKeyMismatch expectedKey storedKey
        ParsedModuleSyntaxIdMismatch expectedSyntax storedSyntax ->
            ParsedArtefactSyntaxInterfaceMismatch storedSyntax expectedSyntax

throwIntegrity
    :: ResolvedSource
    -> ParsedArtefactIntegrityError
    -> ExceptT ParseExecutionError IO value
throwIntegrity source =
    throwE . ParseExecutionArtefactIntegrityFailure source

throwScannerInvariant
    :: SourceNode
    -> SourceScan.SourceScanInvariantError
    -> ExceptT ParseExecutionError IO value
throwScannerInvariant node failure =
    throwE
        (ParseExecutionWorkspaceError
            (SourceWorkspaceError
                (SourceGraphScanningInvariantViolation
                    (sourceNodeResolved node)
                    (SourceScan.renderSourceScanInvariantError failure))))

retainPresentationEntry
    :: SourceScan.SourcePresentationEntry
    -> ModuleParseState
    -> ModuleParseState
retainPresentationEntry entry state =
    case moduleParsePresentationReversed state of
        Nothing -> state
        Just entries ->
            state
                { moduleParsePresentationReversed = Just (entry : entries)
                }

addVerificationCompletion
    :: Word64
    -> SourceCompletionMeasurements
    -> SourceCompletionMeasurements
addVerificationCompletion work measurements =
    measurements
        { verificationCompletionWorkNanoseconds =
            verificationCompletionWorkNanoseconds measurements + work
        , verificationCompletionCount =
            verificationCompletionCount measurements + 1
        }

addPresentationOnlyCompletion
    :: Word64
    -> SourceCompletionMeasurements
    -> SourceCompletionMeasurements
addPresentationOnlyCompletion work measurements =
    measurements
        { presentationOnlyCompletionWorkNanoseconds =
            presentationOnlyCompletionWorkNanoseconds measurements + work
        , presentationOnlyCompletionCount =
            presentationOnlyCompletionCount measurements + 1
        }

prepareCachedOccurrences
    :: Int
    -> SourceNode
    -> ModuleSyntaxContext
    -> [Raw.Block]
    -> [ParsedSyntaxOccurrence]
    -> Either ParsedArtefactIntegrityError SyntaxEntryInventory
prepareCachedOccurrences moduleIndex node context blocks supplied = do
    (localEntries, groups, _previous) <-
        foldM insertOccurrence
            (Map.empty, Map.empty, Nothing)
            supplied
    forM_
        (zip [0 ..] blocks)
        \(blockIndex, block) ->
            case validateOccurrenceAssociation
                    (PhysicalSyntaxSite source)
                    blockIndex
                    block
                    (reverse
                        (Map.findWithDefault [] blockIndex groups)) of
                Left (OccurrenceAssociationDeclarationError failure) ->
                    Left (ParsedArtefactAssociationFailure failure)
                Left (OccurrenceAssociationInvariantError message) ->
                    Left
                        (ParsedArtefactOccurrenceFailure
                            message)
                Right () ->
                    Right ()
    pure localEntries
  where
    source = sourceNodeResolved node
    expectedSourceDescriptor = sourceNodeDescriptor node
    importedEntries = syntaxContextImportedEntries context
    importedIndex = syntaxSurfaceIndex importedEntries
    blockBounds = Map.fromAscList (indexBlockBounds 0 blocks)

    indexBlockBounds _index [] =
        []
    indexBlockBounds index [block] =
        [(index, (locate block, Nothing))]
    indexBlockBounds index (block : rest@(next : _)) =
        (index, (locate block, Just (locate next)))
            : indexBlockBounds (index + 1) rest

    insertOccurrence (entries, groups, previous) occurrence = do
        let blockIndex = parsedSyntaxOccurrenceBlockIndex occurrence
            location = parsedSyntaxOccurrenceLocation occurrence
            marker = parsedSyntaxOccurrenceMarker occurrence
            entry = parsedSyntaxOccurrenceEntry occurrence
        unless
            (locSourceDescriptor location == Just expectedSourceDescriptor)
            (Left
                (ParsedArtefactOccurrenceFailure
                    "syntax occurrence has an invalid source location"))
        (blockStart, nextStart) <-
            maybe
                (Left
                    (ParsedArtefactOccurrenceFailure
                        "syntax occurrence has an invalid block index"))
                Right
                (Map.lookup blockIndex blockBounds)
        let orderedLocation =
                ( blockIndex
                , locLine location
                , locColumn location
                )
        unless
            (location >= blockStart
                && maybe True (location <) nextStart)
            (Left
                (ParsedArtefactOccurrenceFailure
                    "syntax occurrence lies outside its decoded block"))
        case previous of
            Just prior
                | orderedLocation < prior ->
                    Left
                        (ParsedArtefactOccurrenceFailure
                            "syntax occurrences are not in source order")
            _ ->
                Right ()
        let itemIndex =
                length (Map.findWithDefault [] blockIndex groups)
            site =
                SyntaxDeclarationSite
                    { syntaxSiteModuleIndex = moduleIndex
                    , syntaxSiteBlockIndex = blockIndex
                    , syntaxSiteItemIndex = itemIndex
                    , syntaxSiteSource = PhysicalSyntaxSite source
                    , syntaxSiteLocation = location
                    , syntaxSiteMarker = marker
                    }
        disposition <-
            Bifunctor.first ParsedArtefactSyntaxFailure
                (classifyCachedSyntaxItem
                    importedEntries importedIndex site entry)
        let entries' = case disposition of
                EmitSyntaxEntry emitted ->
                    Map.insertWith
                        Set.union
                        emitted
                        (Set.singleton
                            (DeclarationSyntaxProvider site))
                        entries
                ReuseFixedSyntax _fixed ->
                    entries
                ReuseImportedSyntax _imported ->
                    entries
            prepared = PreparedSyntaxOccurrence site entry
        pure
            ( entries'
            , Map.insertWith (++) blockIndex [prepared] groups
            , Just orderedLocation
            )

classifyCachedSyntaxItem
    :: SyntaxEntryInventory
    -> Map Raw.Pattern (Set CanonicalLexicalEntry)
    -> SyntaxDeclarationSite
    -> CanonicalLexicalEntry
    -> Either ParseWorkspaceError SyntaxItemDisposition
classifyCachedSyntaxItem importedEntries importedIndex site entry =
    case Set.toAscList
            (entriesForSurfaces fixedBaseSurfaceIndex entry) of
        [] ->
            classifyImported
        [fixedEntry]
            | entry == fixedEntry ->
                Right (ReuseFixedSyntax fixedEntry)
            | otherwise ->
                Left
                    (SourceLexiconCollision
                        (makeLexiconCollision
                            (sharedSurface entry fixedEntry)
                            [ FixedLexiconOrigin fixedEntry
                            , sourceCollisionOrigin entry site
                            ]))
        _ ->
            impossible
                "fixed base has several entries for one parser surface"
  where
    classifyImported = case entry of
        CanonicalExpressionFunction localPattern marker _fixity ->
            case Set.toAscList
                    (entriesForSurfaces importedIndex entry) of
                [] ->
                    Right (EmitSyntaxEntry entry)
                [importedEntry@(CanonicalExpressionFunction
                        importedPattern importedMarker _importedFixity)]
                    | localPattern == importedPattern
                        && marker == importedMarker
                        && entry == importedEntry ->
                        Right (ReuseImportedSyntax importedEntry)
                entries ->
                    Left
                        (SourceLexiconCollision
                            (makeLexiconCollision
                                (firstSharedSurface entry entries)
                                ( importedCollisionOrigins
                                    importedEntries entries
                                  <> [sourceCollisionOrigin entry site]
                                )))
        _ ->
            Right (EmitSyntaxEntry entry)

tokenizeModule
    :: SourceNode
    -> [ParsedModuleImport]
    -> IO
        (Either
            ParseWorkspaceError
            ( TokenizedModule
            , SourceScan.SourcePresentationEntry
            , Word64
            ))
tokenizeModule node imports = do
    started <- getMonotonicTimeNSec
    case SourceScan.resumeVerificationScan
            (sourceNodeScanPrefix node) of
        Left (SourceScan.SourceInputFailure failure) ->
            pure (Left (verificationScanWorkspaceError source failure))
        Left (SourceScan.SourceScannerInvariantFailure failure) ->
            pure
                (Left
                    (SourceWorkspaceError
                        (SourceGraphScanningInvariantViolation
                            source
                            (SourceScan.renderSourceScanInvariantError
                                failure))))
        Right (verification, presentation) -> do
            _ <- evaluate
                (SourceScan.forceVerificationScanHandoff verification
                    `seq` SourceScan.forceSourcePresentationEntryHandoff
                        presentation)
            finished <- getMonotonicTimeNSec
            pure
                (Right
                    ( TokenizedModule
                        node
                        imports
                        (SourceScan.verificationPragmas verification)
                        (SourceScan.verificationChunks verification)
                    , presentation
                    , finished - started
                    ))
  where
    source = sourceNodeResolved node

    verificationScanWorkspaceError resolved = \case
        SourceScan.VerificationPragmaFailure failure ->
            SourceSyntaxPragmaError resolved failure
        failure ->
            SourceParseError
                resolved
                (TokenError
                    (Text.unpack
                        (SourceScan.renderVerificationScanError failure)))

completePresentationModule
    :: SourceNode
    -> IO
        (Either
            SourceScan.SourceScanInvariantError
            (SourceScan.SourcePresentationEntry, Word64))
completePresentationModule node = do
    started <- getMonotonicTimeNSec
    case SourceScan.resumePresentationScan (sourceNodeScanPrefix node) of
        Left failure -> pure (Left failure)
        Right presentation -> do
            _ <- evaluate
                (SourceScan.forceSourcePresentationEntryHandoff presentation)
            finished <- getMonotonicTimeNSec
            pure (Right (presentation, finished - started))

resolveParsedModuleImports
    :: ResolvedSourceGraph
    -> Map CanonicalPath ResolvedSourceAddress
    -> SourceNode
    -> Either ParseWorkspaceError [ParsedModuleImport]
resolveParsedModuleImports graph addresses node =
    traverse
        (parsedImport addresses)
        [ edge
        | edge <- sourceGraphImportEdges graph
        , sourceImportingNode edge
            == resolvedSourceCanonicalPath source
        ]
  where
    source = sourceNodeResolved node

parsedImport
    :: Map CanonicalPath ResolvedSourceAddress
    -> SourceImportEdge
    -> Either ParseWorkspaceError ParsedModuleImport
parsedImport addresses edge =
    case Map.lookup (sourceImportedNode edge) addresses of
        Nothing ->
            Left
                (SourceWorkspaceError
                    (SourceGraphInvariantViolation
                        "logical import refers to an unknown source node"))
        Just imported ->
            Right
                (parsedModuleImport
                    (sourceImportReference edge)
                    imported)

extractTokenizedModule
    :: TokenizedModule
    -> ExceptT
        ParseWorkspaceError
        IO
        ExtractedModule
extractTokenizedModule
        (TokenizedModule node imports pragmas chunks) = do
    associated <- either
        (throwE . SourceSyntaxDeclarationError source)
        pure
        (associateSyntaxPragmas chunks pragmas)
    extractedChunks <- traverse extractOne
        (zip chunks associated)
    pure (ExtractedModule node imports extractedChunks)
  where
    source = sourceNodeResolved node

    extractOne (tokens, chunkPragmas) =
        case prepareLexicalChunk tokens of
            Left err ->
                throwE
                    (SourceParseError
                        source
                        (LexiconExtractionFailure err))
            Right prepared ->
                pure
                    (ExtractedChunk
                        (preparedLexicalTokens prepared)
                        chunkPragmas
                        (preparedLexicalItems prepared))

associateSyntaxPragmas
    :: [[Located Token]]
    -> [SyntaxPragma]
    -> Either SyntaxDeclarationError [[SyntaxPragma]]
associateSyntaxPragmas chunks =
    foldM associate (replicate (length chunks) [])
  where
    associate groups pragma =
        case
            [ index
            | (index, chunk) <- zip [0 :: Int ..] chunks
            , pragmaWithinChunk pragma chunk
            ] of
            [] ->
                Left
                    (SyntaxPragmaOutsideDeclaration
                        (syntaxPragmaLocation pragma))
            [selected] ->
                Right
                    [ if index == selected
                        then group <> [pragma]
                        else group
                    | (index, group) <- zip [0 :: Int ..] groups
                    ]
            _ ->
                impossible
                    "one syntax pragma belongs to overlapping top-level chunks"

pragmaWithinChunk
    :: SyntaxPragma
    -> [Located Token]
    -> Bool
pragmaWithinChunk pragma = \case
    firstToken : rest ->
        case reverse rest of
            finalToken : _ ->
                let pragmaLocation =
                        syntaxPragmaLocation pragma
                    firstLocation =
                        startPos firstToken
                    finalLocation =
                        startPos finalToken
                in
                    locSourceDescriptor pragmaLocation
                        == locSourceDescriptor firstLocation
                        && locLine firstLocation
                            < locLine pragmaLocation
                        && locLine pragmaLocation
                            < locLine finalLocation
            [] ->
                False
    [] ->
        False

prepareFreshRuntimeSyntaxModule
    :: Int
    -> ModuleSyntaxContext
    -> ExtractedModule
    -> Either ParseWorkspaceError FreshRuntimeSyntax
prepareFreshRuntimeSyntaxModule moduleIndex context
        (ExtractedModule node _imports chunks) = do
    (localEntries, preparedOccurrences) <-
        Bifunctor.first
            (localSyntaxWorkspaceError source)
            (prepareLocalSyntax
                moduleIndex
                (PhysicalSyntaxSite source)
                (syntaxContextImportedEntries context)
                chunks)
    (prepared, effectiveDelta) <-
        prepareSyntaxModule address context localEntries
    lexicon <-
        Bifunctor.first
            SourceSyntaxMaterializationError
            (materializeSyntaxDelta effectiveDelta)
    pure
        FreshRuntimeSyntax
            { freshRuntimePrepared = prepared
            , freshRuntimeLexicon = lexicon
            , freshRuntimeOccurrences = preparedOccurrences
            }
  where
    source = sourceNodeResolved node
    address = resolvedSourceAddress source

prepareSyntaxModule
    :: ResolvedSourceAddress
    -> ModuleSyntaxContext
    -> SyntaxEntryInventory
    -> Either
        ParseWorkspaceError
        (PreparedSyntaxModule, CanonicalSyntaxDelta)
prepareSyntaxModule address context localEntries = do
    localDelta <-
        Bifunctor.first
            localSyntaxCollisionWorkspaceError
            (validateSyntaxInventory localEntries)
    interface <-
        Bifunctor.first
            (const
                (SourceWorkspaceError
                    (SourceGraphInvariantViolation
                        "module syntax interface rejected distinct direct inputs")))
            (moduleSyntaxInterface
                (syntaxContextDirectIds context)
                localDelta)
    let effectiveEntries =
            Map.unionWith
                Set.union
                (syntaxContextImportedEntries context)
                localEntries
    effectiveDelta <-
        Bifunctor.first
            localSyntaxCollisionWorkspaceError
            (validateSyntaxInventory effectiveEntries)
    pure
        ( PreparedSyntaxModule
            { preparedAddress = address
            , preparedInterface = interface
            , preparedSyntaxDirectAddresses =
                syntaxContextDirectAddresses context
            , preparedLocalEntries = localEntries
            }
        , effectiveDelta
        )

prepareModuleSyntaxContext
    :: Map ResolvedSourceAddress PreparedSyntaxModule
    -> [ModuleSyntaxInterface]
    -> [ParsedModuleImport]
    -> Either ParseWorkspaceError ModuleSyntaxContext
prepareModuleSyntaxContext preparedByAddress implicitSyntax imports = do
    unless
        (all (null . moduleSyntaxDirectInputs) implicitSyntax)
        (Left
            (SourceWorkspaceError
                (SourceGraphInvariantViolation
                    "implicit syntax input is not self-contained")))
    directModules <- traverse
        (lookupPreparedSyntaxModule preparedByAddress)
        (nubOrd (parsedImportedAddress <$> imports))
    let (seenImplicit, implicitReversed) =
            foldl' insertImplicit (Set.empty, []) implicitSyntax
        (_seenAll, directReversed) =
            foldl' insertDirect (seenImplicit, []) directModules
        implicitSelected = reverse implicitReversed
        directSelected = reverse directReversed
        directAddresses = preparedAddress <$> directSelected
        directIds =
            (moduleSyntaxAssertedId <$> implicitSelected)
                <> ( moduleSyntaxAssertedId . preparedInterface
                        <$> directSelected
                   )
    directEntries <-
        foldImportedSyntax preparedByAddress directAddresses
    let importedEntries =
            foldl'
                (Map.unionWith Set.union)
                directEntries
                (implicitSyntaxInventory <$> implicitSelected)
    pure
        ModuleSyntaxContext
            { syntaxContextDirectIds = directIds
            , syntaxContextDirectAddresses = directAddresses
            , syntaxContextImportedEntries = importedEntries
            }
  where
    insertImplicit (seen, reversed) interface =
        let identity = moduleSyntaxAssertedId interface
        in
            if identity `Set.member` seen
                then (seen, reversed)
                else
                    (Set.insert identity seen, interface : reversed)

    insertDirect (seen, reversed) prepared =
        let identity =
                moduleSyntaxAssertedId (preparedInterface prepared)
        in
            if identity `Set.member` seen
                then (seen, reversed)
                else
                    (Set.insert identity seen, prepared : reversed)

    implicitSyntaxInventory interface =
        Map.fromList
            [ ( entry
              , Set.singleton
                    (ImplicitSyntaxProvider
                        (moduleSyntaxAssertedId interface))
              )
            | entry <-
                canonicalSyntaxDeltaEntries
                    (moduleSyntaxLocalDelta interface)
            ]

moduleParsedKey
    :: SourceNode
    -> ModuleSyntaxContext
    -> Either ParseWorkspaceError Parsed.ParsedModuleKey
moduleParsedKey node context =
    Bifunctor.first
        (SourceParsedModuleKeyError source)
        (Parsed.parsedModuleKey
            (sourceNodeContentId node)
            baseSyntaxInterfaceId
            (syntaxContextDirectIds context))
  where
    source = sourceNodeResolved node

lookupPreparedSyntaxModule
    :: Map ResolvedSourceAddress PreparedSyntaxModule
    -> ResolvedSourceAddress
    -> Either ParseWorkspaceError PreparedSyntaxModule
lookupPreparedSyntaxModule preparedByAddress address =
    maybe
        (Left
            (SourceWorkspaceError
                (SourceGraphInvariantViolation
                    "syntax import refers to an unprepared module")))
        Right
        (Map.lookup address preparedByAddress)

foldImportedSyntax
    :: Map ResolvedSourceAddress PreparedSyntaxModule
    -> [ResolvedSourceAddress]
    -> Either ParseWorkspaceError SyntaxEntryInventory
foldImportedSyntax preparedByAddress addresses =
    snd <$> foldM visit (Set.empty, Map.empty) addresses
  where
    visit state address = do
        prepared <- lookupPreparedSyntaxModule preparedByAddress address
        let identity =
                moduleSyntaxAssertedId
                    (preparedInterface prepared)
        if identity `Set.member` fst state
            then
                Right state
            else do
                let marked =
                        (Set.insert identity (fst state), snd state)
                afterImports <- foldM
                    visit
                    marked
                    (preparedSyntaxDirectAddresses prepared)
                Right
                    ( fst afterImports
                    , Map.unionWith
                        Set.union
                        (snd afterImports)
                        (preparedLocalEntries prepared)
                    )

prepareLocalSyntax
    :: Int
    -> SyntaxSiteSource
    -> SyntaxEntryInventory
    -> [ExtractedChunk]
    -> Either
        LocalSyntaxError
        ( SyntaxEntryInventory
        , [[PreparedSyntaxOccurrence]]
        )
prepareLocalSyntax
        moduleIndex
        source
        importedEntries
        chunks = do
    (localEntries, reversedOccurrences) <-
        foldM
            prepareOne
            (Map.empty, [])
            (zip [0 ..] chunks)
    pure
        ( localEntries
        , reverse reversedOccurrences
        )
  where
    importedIndex =
        syntaxSurfaceIndex importedEntries

    prepareOne
            (localEntries, reversedOccurrences)
            (blockIndex, chunk) = do
        classified <-
            prepareSyntaxChunk
                moduleIndex
                source
                blockIndex
                importedEntries
                importedIndex
                chunk
        (localEntries', reversedPrepared) <-
            foldM
                insertClassified
                (localEntries, [])
                classified
        pure
            ( localEntries'
            , reverse reversedPrepared : reversedOccurrences
            )

    insertClassified
            (entries, reversed)
            (ClassifiedSyntaxItem site disposition _eligible) =
        case disposition of
            EmitSyntaxEntry entry ->
                Right
                    ( Map.insertWith
                        Set.union
                        entry
                        (Set.singleton
                            (DeclarationSyntaxProvider site))
                        entries
                    , PreparedSyntaxOccurrence
                        site
                        entry
                        : reversed
                    )
            ReuseImportedSyntax entry ->
                Right
                    ( entries
                    , PreparedSyntaxOccurrence
                        site
                        entry
                        : reversed
                    )
            ReuseFixedSyntax entry ->
                Right
                    ( entries
                    , PreparedSyntaxOccurrence
                        site
                        entry
                        : reversed
                    )

prepareSyntaxChunk
    :: Int
    -> SyntaxSiteSource
    -> Int
    -> SyntaxEntryInventory
    -> Map Raw.Pattern (Set CanonicalLexicalEntry)
    -> ExtractedChunk
    -> Either LocalSyntaxError [ClassifiedSyntaxItem]
prepareSyntaxChunk
        moduleIndex
        source
        blockIndex
        importedEntries
        importedIndex
        (ExtractedChunk tokens pragmas declarations) = do
    classified <- traverse classify
        (zip [0 ..] declarations)
    case (classified, pragmas) of
        ([], pragma : _) ->
            Left
                (LocalSyntaxDeclarationError
                    (SyntaxPragmaOutsideDeclaration
                        (syntaxPragmaLocation pragma)))
        (_, firstPragma : secondPragma : _) ->
            Left
                (LocalSyntaxDeclarationError
                    (DuplicateSyntaxPragma
                        (syntaxPragmaLocation firstPragma)
                        (syntaxPragmaLocation secondPragma)))
        (_, [pragma]) ->
            applyOnePragma pragma classified
        (_, []) ->
            requireNewFixities classified
  where
    declarationLocation =
        case tokens of
            token : _ ->
                startPos token
            [] ->
                Nowhere

    classify (itemIndex, locatedItem) = do
        let item = unLocated locatedItem
            location = startPos locatedItem
            site =
                SyntaxDeclarationSite
                    { syntaxSiteModuleIndex = moduleIndex
                    , syntaxSiteBlockIndex = blockIndex
                    , syntaxSiteItemIndex = itemIndex
                    , syntaxSiteSource = source
                    , syntaxSiteLocation = location
                    , syntaxSiteMarker = extractedItemMarker item
                    }
            localEntry =
                canonicalExtractedItem
                    defaultSourceFixity
                    item
            eligible =
                case localEntry of
                    CanonicalExpressionFunction pat _marker _fixity ->
                        eligibleExpressionPattern pat
                    _ ->
                        False
            fixedMatches =
                entriesForSurfaces
                    fixedBaseSurfaceIndex
                    localEntry
        disposition <- case Set.toAscList fixedMatches of
            [] ->
                classifyImported
                    site
                    localEntry
            [fixedEntry]
                | sameFixedSyntaxShape localEntry fixedEntry ->
                    Right (ReuseFixedSyntax fixedEntry)
                | otherwise ->
                    Left
                        (LocalSyntaxCollision
                            (makeLexiconCollision
                                (sharedSurface
                                    localEntry
                                    fixedEntry)
                                [ FixedLexiconOrigin fixedEntry
                                , sourceCollisionOrigin
                                    localEntry
                                    site
                                ]))
            _ ->
                impossible
                    "fixed base has several entries for one parser surface"
        Right
            (ClassifiedSyntaxItem
                site
                disposition
                eligible)

    classifyImported site localEntry =
        let importedMatches =
                entriesForSurfaces importedIndex localEntry
        in
            case localEntry of
                CanonicalExpressionFunction
                        localPattern
                        localMarker
                        _localFixity ->
                    case Set.toAscList importedMatches of
                        [] ->
                            Right (EmitSyntaxEntry localEntry)
                        [ importedEntry@(CanonicalExpressionFunction
                                importedPattern
                                importedMarker
                                _importedFixity)
                          ]
                            | localPattern == importedPattern
                                && localMarker == importedMarker ->
                                Right
                                    (ReuseImportedSyntax importedEntry)
                        entries ->
                            Left
                                (LocalSyntaxCollision
                                    (makeLexiconCollision
                                        (firstSharedSurface
                                            localEntry
                                            entries)
                                        (importedCollisionOrigins
                                            importedEntries
                                            entries
                                            <> [ sourceCollisionOrigin
                                                localEntry
                                                site
                                               ])))
                _ ->
                    Right (EmitSyntaxEntry localEntry)

    applyOnePragma pragma classified =
        case List.filter classifiedItemEligible classified of
            [] ->
                Left
                    (LocalSyntaxDeclarationError
                        (IrrelevantSyntaxPragma
                            (syntaxPragmaLocation pragma)
                            declarationLocation))
            [only] ->
                case classifiedDisposition only of
                    ReuseFixedSyntax entry ->
                        Left
                            (LocalSyntaxDeclarationError
                                (SyntaxPragmaOnFixedReuse
                                    (syntaxPragmaLocation pragma)
                                    (entryPrimarySurface entry)))
                    ReuseImportedSyntax entry ->
                        Left
                            (LocalSyntaxDeclarationError
                                (SyntaxPragmaOnImportedReuse
                                    (syntaxPragmaLocation pragma)
                                    (entryPrimarySurface entry)))
                    EmitSyntaxEntry entry ->
                        Right
                            [ replaceClassifiedEntry
                                only
                                (setExpressionFixity
                                    (sourcePragmaFixity pragma)
                                    entry)
                                current
                            | current <- classified
                            ]
            several ->
                Left
                    (LocalSyntaxDeclarationError
                        (AmbiguousSyntaxPragmaTarget
                            (syntaxPragmaLocation pragma)
                            (eligiblePatterns several)))

    requireNewFixities classified =
        case
            [ item
            | item <- classified
            , classifiedItemEligible item
            , case classifiedDisposition item of
                EmitSyntaxEntry _entry ->
                    True
                _ ->
                    False
            ] of
            [] ->
                Right classified
            [only] ->
                Left
                    (LocalSyntaxDeclarationError
                        (MissingSyntaxPragma
                            (classifiedLocation only)
                            (classifiedPattern only)))
            several@(firstItem : _) ->
                Left
                    (LocalSyntaxDeclarationError
                        (MultipleNewSyntaxPatternsWithoutPragma
                            (classifiedLocation firstItem)
                            (eligiblePatterns several)))

defaultSourceFixity :: Fixity
defaultSourceFixity =
    Fixity
        Raw.NonAssoc
        (case mixfixLevel 9 of
            Right level ->
                level
            Left err ->
                impossible
                    ("source default fixity is invalid: "
                        <> show err))

fixedBaseSurfaceIndex
    :: Map Raw.Pattern (Set CanonicalLexicalEntry)
fixedBaseSurfaceIndex =
    entrySurfaceIndex fixedBaseSyntaxEntries

syntaxSurfaceIndex
    :: SyntaxEntryInventory
    -> Map Raw.Pattern (Set CanonicalLexicalEntry)
syntaxSurfaceIndex =
    entrySurfaceIndex . Map.keys

entrySurfaceIndex
    :: [CanonicalLexicalEntry]
    -> Map Raw.Pattern (Set CanonicalLexicalEntry)
entrySurfaceIndex =
    foldl' insertEntry Map.empty
  where
    insertEntry index entry =
        foldl'
            (\current pat ->
                Map.insertWith
                    Set.union
                    pat
                    (Set.singleton entry)
                    current)
            index
            (canonicalLexicalSurfacePatterns entry)

entriesForSurfaces
    :: Map Raw.Pattern (Set CanonicalLexicalEntry)
    -> CanonicalLexicalEntry
    -> Set CanonicalLexicalEntry
entriesForSurfaces index entry =
    Set.unions
        [ Map.findWithDefault Set.empty pat index
        | pat <- toList
            (canonicalLexicalSurfacePatterns entry)
        ]

sameFixedSyntaxShape
    :: CanonicalLexicalEntry
    -> CanonicalLexicalEntry
    -> Bool
sameFixedSyntaxShape left right =
    case (left, right) of
        ( CanonicalIntrinsicAdjective
                leftSide leftPattern leftMarker
          , CanonicalIntrinsicAdjective
                rightSide rightPattern rightMarker
          ) ->
            (leftSide, leftPattern, leftMarker)
                == (rightSide, rightPattern, rightMarker)
        ( CanonicalFunctionPhrase leftSingular leftPlural _leftMarker
          , CanonicalFunctionPhrase rightSingular rightPlural _rightMarker
          ) ->
            (leftSingular, leftPlural)
                == (rightSingular, rightPlural)
        ( CanonicalNoun leftSingular leftPlural _leftMarker
          , CanonicalNoun rightSingular rightPlural _rightMarker
          ) ->
            (leftSingular, leftPlural)
                == (rightSingular, rightPlural)
        ( CanonicalStructureNoun leftSingular leftPlural _leftMarker
          , CanonicalStructureNoun rightSingular rightPlural _rightMarker
          ) ->
            (leftSingular, leftPlural)
                == (rightSingular, rightPlural)
        ( CanonicalVerb leftSurfaces _leftMarker
          , CanonicalVerb rightSurfaces _rightMarker
          ) ->
            leftSurfaces == rightSurfaces
        ( CanonicalRelation leftToken leftArity _leftMarker
          , CanonicalRelation rightToken rightArity _rightMarker
          ) ->
            (leftToken, leftArity)
                == (rightToken, rightArity)
        ( CanonicalExpressionFunction
                leftPattern
                _leftMarker
                _leftFixity
          , CanonicalExpressionFunction
                rightPattern
                _rightMarker
                _rightFixity
          ) ->
            leftPattern == rightPattern
        ( CanonicalPrefixPredicate
                leftCommand
                leftArity
                _leftMarker
          , CanonicalPrefixPredicate
                rightCommand
                rightArity
                _rightMarker
          ) ->
            (leftCommand, leftArity)
                == (rightCommand, rightArity)
        ( CanonicalStructureOperation leftCommand
          , CanonicalStructureOperation rightCommand
          ) ->
            leftCommand == rightCommand
        _ ->
            False

sharedSurface
    :: CanonicalLexicalEntry
    -> CanonicalLexicalEntry
    -> Raw.Pattern
sharedSurface left right =
    case Set.lookupMin
            (Set.intersection
                (entrySurfaces left)
                (entrySurfaces right)) of
        Just pat ->
            pat
        Nothing ->
            impossible
                "colliding syntax entries have no shared parser surface"

firstSharedSurface
    :: CanonicalLexicalEntry
    -> [CanonicalLexicalEntry]
    -> Raw.Pattern
firstSharedSurface localEntry entries =
    case Set.lookupMin
            (Set.unions
                [ Set.intersection
                    (entrySurfaces localEntry)
                    (entrySurfaces entry)
                | entry <- entries
                ]) of
        Just pat ->
            pat
        Nothing ->
            impossible
                "imported syntax collision has no shared parser surface"

entryPrimarySurface :: CanonicalLexicalEntry -> Raw.Pattern
entryPrimarySurface entry =
    NonEmpty.head (canonicalLexicalSurfacePatterns entry)

entrySurfaces :: CanonicalLexicalEntry -> Set Raw.Pattern
entrySurfaces =
    Set.fromList
        . toList
        . canonicalLexicalSurfacePatterns

classifiedItemEligible :: ClassifiedSyntaxItem -> Bool
classifiedItemEligible
        (ClassifiedSyntaxItem _site _disposition eligible) =
    eligible

classifiedDisposition
    :: ClassifiedSyntaxItem
    -> SyntaxItemDisposition
classifiedDisposition
        (ClassifiedSyntaxItem _site disposition _eligible) =
    disposition

classifiedLocation :: ClassifiedSyntaxItem -> Location
classifiedLocation
        (ClassifiedSyntaxItem site _disposition _eligible) =
    syntaxSiteLocation site

classifiedPattern :: ClassifiedSyntaxItem -> Raw.Pattern
classifiedPattern =
    entryPrimarySurface . dispositionEntry . classifiedDisposition

dispositionEntry :: SyntaxItemDisposition -> CanonicalLexicalEntry
dispositionEntry = \case
    EmitSyntaxEntry entry ->
        entry
    ReuseFixedSyntax entry ->
        entry
    ReuseImportedSyntax entry ->
        entry

eligiblePatterns
    :: [ClassifiedSyntaxItem]
    -> NonEmpty Raw.Pattern
eligiblePatterns = \case
    [] ->
        impossible
            "an ambiguous pragma target has no eligible patterns"
    item : rest ->
        classifiedPattern item
            :| (classifiedPattern <$> rest)

replaceClassifiedEntry
    :: ClassifiedSyntaxItem
    -> CanonicalLexicalEntry
    -> ClassifiedSyntaxItem
    -> ClassifiedSyntaxItem
replaceClassifiedEntry
        (ClassifiedSyntaxItem targetSite _targetDisposition _targetEligible)
        replacement
        current@(ClassifiedSyntaxItem site _disposition eligible)
    | site == targetSite =
        ClassifiedSyntaxItem
            site
            (EmitSyntaxEntry replacement)
            eligible
    | otherwise =
        current

setExpressionFixity
    :: Fixity
    -> CanonicalLexicalEntry
    -> CanonicalLexicalEntry
setExpressionFixity fixity = \case
    CanonicalExpressionFunction pat marker _oldFixity ->
        CanonicalExpressionFunction pat marker fixity
    entry ->
        impossible
            ("a pragma targeted a non-expression entry: "
                <> show entry)

validateSyntaxInventory
    :: SyntaxEntryInventory
    -> Either LocalSyntaxError CanonicalSyntaxDelta
validateSyntaxInventory inventory =
    case canonicalSyntaxDelta (Map.keys inventory) of
        Right delta ->
            Right delta
        Left collision ->
            Left
                (LocalSyntaxCollision
                    (inventoryCollision inventory collision))

inventoryCollision
    :: SyntaxEntryInventory
    -> CanonicalSyntaxCollision
    -> LexiconCollision
inventoryCollision inventory collision =
    makeLexiconCollision
        (canonicalCollisionPattern collision)
        (syntaxCollisionOrigins
            inventory
            (toList (canonicalCollisionEntries collision)))

importedCollisionOrigins
    :: SyntaxEntryInventory
    -> [CanonicalLexicalEntry]
    -> [LexiconCollisionOrigin]
importedCollisionOrigins inventory entries =
    syntaxCollisionOrigins inventory entries

syntaxCollisionOrigins
    :: SyntaxEntryInventory
    -> [CanonicalLexicalEntry]
    -> [LexiconCollisionOrigin]
syntaxCollisionOrigins inventory entries =
    [ providerCollisionOrigin entry provider
    | (provider, entry) <-
        List.sortOn fst
            [ (provider, entry)
            | entry <- entries
            , provider <-
                Set.toList
                    (Map.findWithDefault
                        Set.empty
                        entry
                        inventory)
            ]
    ]

providerCollisionOrigin
    :: CanonicalLexicalEntry
    -> SyntaxEntryProvider
    -> LexiconCollisionOrigin
providerCollisionOrigin entry = \case
    DeclarationSyntaxProvider site ->
        sourceCollisionOrigin entry site
    ImplicitSyntaxProvider interface ->
        ImportedLexiconOrigin entry interface

sourceCollisionOrigin
    :: CanonicalLexicalEntry
    -> SyntaxDeclarationSite
    -> LexiconCollisionOrigin
sourceCollisionOrigin entry site =
    case syntaxSiteSource site of
        PhysicalSyntaxSite source ->
            SourceLexiconOrigin
                entry
                source
                (syntaxSiteLocation site)
        ReservedSyntaxSite label ->
            ReservedLexiconOrigin
                entry
                label
                (syntaxSiteLocation site)

makeLexiconCollision
    :: Raw.Pattern
    -> [LexiconCollisionOrigin]
    -> LexiconCollision
makeLexiconCollision pat origins =
    case origins of
        firstOrigin : secondOrigin : rest ->
            LexiconCollision
                pat
                firstOrigin
                secondOrigin
                rest
        _ ->
            impossible
                "a lexical collision has fewer than two providers"

-- V1 associates extracted items with one parsed declaration. The block-head
-- marker anchors the declaration; additional datatype and structure items
-- retain extraction order and are not matched to individual AST nodes here.
validateOccurrenceAssociation
    :: SyntaxSiteSource
    -> Int
    -> Raw.Block
    -> [PreparedSyntaxOccurrence]
    -> Either OccurrenceAssociationError ()
validateOccurrenceAssociation _source _blockIndex _block [] =
    Right ()
validateOccurrenceAssociation source blockIndex block prepared = do
    forM_ prepared
        \occurrence -> do
            let site =
                    preparedSyntaxSite occurrence
            unless
                (syntaxSiteSource site == source)
                (Left
                    (OccurrenceAssociationInvariantError
                        "syntax occurrence belongs to a different source"))
            unless
                (syntaxSiteBlockIndex site == blockIndex)
                (Left
                    (OccurrenceAssociationInvariantError
                        "syntax occurrence belongs to a different block"))
    validateHeadMarker
  where
    validateHeadMarker = case prepared of
        occurrence : _rest -> do
            let site =
                    preparedSyntaxSite occurrence
                location =
                    syntaxSiteLocation site
                expectedMarker =
                    syntaxSiteMarker site
            case rawBlockMarker block of
                Nothing ->
                    Left
                        (OccurrenceAssociationDeclarationError
                            (SyntaxOccurrenceMissingBlockMarker
                                location
                                expectedMarker))
                Just actual ->
                    unless
                        (actual == expectedMarker)
                        (Left
                            (OccurrenceAssociationDeclarationError
                                (SyntaxOccurrenceMarkerMismatch
                                    location
                                    expectedMarker
                                    actual)))

rawBlockMarker :: Raw.Block -> Maybe Raw.Marker
rawBlockMarker = \case
    Raw.BlockAxiom _location _title marker _axiom ->
        Just marker
    Raw.BlockClaim _kind _location _title marker _claim ->
        Just marker
    Raw.BlockProof{} ->
        Nothing
    Raw.BlockDefn _location _title marker _definition ->
        Just marker
    Raw.BlockAbbr _location _title marker _abbreviation ->
        Just marker
    Raw.BlockData _location _title marker _datatype ->
        Just marker
    Raw.BlockRecursive _location _title marker _definition ->
        Just marker
    Raw.BlockInductive _location _title marker _inductive ->
        Just marker
    Raw.BlockSig _location _title marker _assumptions _signature ->
        Just marker
    Raw.BlockStruct _location _title marker _structure ->
        Just marker
    Raw.BlockInstance _location _title marker _instance ->
        Just marker
    Raw.BlockConstruction _location _title marker _construction ->
        Just marker

parseExtractedModule
    :: FreshRuntimeSyntax
    -> ExtractedModule
    -> ExceptT ParseWorkspaceError IO ParsedModule
parseExtractedModule
        runtime
        (ExtractedModule node imports chunks) = do
    let preparedRuntime = freshRuntimePrepared runtime
    unless
        (preparedAddress preparedRuntime
            == resolvedSourceAddress source)
        (throwE
            (SourceWorkspaceError
                (SourceGraphInvariantViolation
                    "runtime syntax was paired with the wrong source module")))
    unless
        (length chunks
            == length (freshRuntimeOccurrences runtime))
        (throwE
            (SourceWorkspaceError
                (SourceGraphInvariantViolation
                    "runtime syntax occurrence groups do not match source chunks")))
    let input =
            freshModuleInput
                (FreshPhysical (sourceNodeIdentified node))
                (parsedImportReference <$> imports)
                (preparedInterface preparedRuntime)
    liftIO (evaluate (forcePreparedLexicon preparedLexicon))
    (reversedBlocks, reversedOccurrences) <- ExceptT (evaluate
        (EarleySession.foldParses (grammarPrepared preparedLexicon)
            (\(_, ExtractedChunk tokens _ _, _) -> tokens)
            parsePreparedChunk
            ([], [])
            (zip3 [0 ..] chunks (freshRuntimeOccurrences runtime))))
    let blocks = reverse reversedBlocks
        occurrences = reverse reversedOccurrences
    let fresh = identifyParsedModule input blocks occurrences
    resultModule <-
        either
            (throwE . SourceParsedModuleBindingInvariant source)
            pure
            (bindParsedModule
                (sourceNodeIdentified node)
                imports
                fresh)
    -- Force each module before it leaves the parser producer.
    liftIO (evaluate (force resultModule))
  where
    source = sourceNodeResolved node
    preparedLexicon = prepareLexicon (freshRuntimeLexicon runtime)
    parsePreparedChunk
            (currentBlocks, currentOccurrences)
            (blockIndex, _chunk, prepared)
            result = do
        selected <- Bifunctor.first (SourceParseError source) (parseChunkResult result)
        let block = force selected
        block `seq` Bifunctor.first (occurrenceWorkspaceError source)
            (validateOccurrenceAssociation
                (PhysicalSyntaxSite source)
                blockIndex
                block
                prepared)
        pure
            ( block : currentBlocks
            , foldl'
                (flip (:))
                currentOccurrences
                [ parsedSyntaxOccurrence
                    blockIndex
                    (syntaxSiteLocation (preparedSyntaxSite occurrence))
                    (syntaxSiteMarker (preparedSyntaxSite occurrence))
                    (preparedSyntaxEntry occurrence)
                | occurrence <- prepared
                ]
            )

parseChunkResult
    :: ( [Either ConcreteSyntaxError Raw.Block]
       , Report Text [Located Token]
       )
    -> Either ParseException Raw.Block
parseChunkResult = \case
    (_, Report _ expectations (token : tokens)) ->
        Left (UnconsumedTokens expectations (token :| tokens))
    (results, _) ->
        case nubOrd [block | Right block <- results] of
            [block] -> Right block
            _first : _second : remaining ->
                Left (AmbiguousParse (2 + length remaining))
            [] ->
                case nubOrd [failure | Left failure <- results] of
                    failure : _ -> Left (ConcreteSyntaxFailure failure)
                    [] -> Left EmptyParse

parsePreparedTokenChunk
    :: Parser
        Text
        [Located Token]
        (Either ConcreteSyntaxError Raw.Block)
    -> [Located Token]
    -> Either ParseException Raw.Block
parsePreparedTokenChunk prepared tokens =
    parseChunkResult (fullParses prepared tokens)


describeToken :: Token -> String
describeToken = \case
    Word _ -> "word"
    Variable _ -> "variable"
    Symbol _ -> "symbol"
    Integer _ -> "integer"
    Command _ -> "command"
    BeginEnv _ -> "begin of environment"
    EndEnv _ -> "end of environment"
    _ -> "delimiter"
