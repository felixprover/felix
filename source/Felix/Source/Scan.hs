{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Resumable structural scanning of validated physical Felix sources.
--
-- The prefix pass discovers imports and retains enough private state for a
-- later body pass. It scans the exact source bytes, while 'LoadedSource'
-- remains the authority that those bytes have already been validated as
-- UTF-8.
module Felix.Source.Scan
    ( DocumentHeadingLevel(..)
    , SourceScanFailure(..)
    , SourceScanRejection(..)
    , SourcePrefixError(..)
    , VerificationScanError(..)
    , TokenSourceScanError(..)
    , PresentationScanError(..)
    , SourceFragmentError(..)
    , renderSourcePrefixError
    , renderVerificationScanError
    , renderTokenSourceScanError
    , renderPresentationScanError
    , renderSourceFragmentError
    , SourceScanInvariantError
    , renderSourceScanInvariantError
    , SourceScanPrefix
    , VerificationScan(..)
    , SourcePresentationEntry
    , SourcePresentationBindingError
    , renderSourcePresentationBindingError
    , SourcePresentationProjectionError(..)
    , DecodedPresentationSegment(..)
    , ProjectedSourcePresentation(..)
    , scanSourcePrefix
    , sourcePrefixImports
    , sourcePrefixIdentifiedSource
    , forceSourceScanPrefixHandoff
    , resumeVerificationScan
    , resumePresentationScan
    , forceVerificationScanHandoff
    , forceSourcePresentationEntryHandoff
    , projectSourcePresentationEntry
    , scanCompleteVerificationText
    , scanCompleteSourceTokens
    , forceSourceTokenChunksHandoff
    , scanCompletePresentationText
    , scanMathSnippet
    , parsePresentationVariableFragment
    , parsePresentationReferenceFragment
    ) where

import Base

import Felix.Report.Location
    ( SourceDescriptor
    , Location
    , anonymousSourceDescriptor
    , locColumn
    , locLine
    , locationToText
    , mkLocationChecked
    )
import Felix.Source
import Felix.Source.Content
import Felix.Syntax.Pragma
    ( SyntaxPragma
    , SyntaxPragmaError
    , SyntaxPragmaLineEnding(..)
    , parseSyntaxPragmaLine
    , renderSyntaxPragmaError
    )
import Felix.Syntax.Token
    ( Located(..)
    , Token(..)
    , Whitespace(..)
    , canonicalVariableControlWord
    )
import Felix.Text.Identifier
    ( isPortableIdentifierInitial
    , isPortableIdentifierSubsequent
    )

import Control.Monad (unless, when)
import Control.Monad.State.Strict
    ( State
    , get
    , gets
    , modify'
    , put
    , runState
    )
import Control.Monad.Trans.Except
    ( ExceptT
    , runExceptT
    , throwE
    )
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Char (chr, isAlphaNum, isLetter, isSpace, ord)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word (Word8)
import Data.Vector (Vector)
import Data.Vector qualified as Vector


newtype ByteOffset = ByteOffset Int
    deriving stock (Show, Eq, Ord)

data ByteSpan = ByteSpan
    !ByteOffset
    !ByteOffset
    deriving stock (Show, Eq)

data PendingProseStart = PendingProseStart
    !ByteOffset
    !Int
    !Int
    deriving stock (Show, Eq)

data DocumentHeadingLevel
    = DocumentSection
    | DocumentSubsection
    | DocumentSubsubsection
    deriving stock (Show, Eq, Ord, Enum, Bounded)

data PresentationSpan
    = PresentationHeading
        !DocumentHeadingLevel
        !Location
        !ByteSpan
        !(Maybe ByteSpan)
    | PresentationProse !Location !ByteSpan
    | PresentationFormal !Location !Text
    deriving stock (Show, Eq)

data PragmaCandidate = PragmaCandidate
    !Int
    !SyntaxPragmaLineEnding
    !ByteSpan
    deriving stock (Show, Eq)

data LineObservation
    = ObservingLineIndent !ByteOffset !Int
    | ObservingPragmaCandidate !ByteOffset !Int
    | IgnoringPhysicalLine
    deriving stock (Show, Eq)

data ScanOwner
    = PhysicalScanOwner !IdentifiedLoadedSource
    | EphemeralScanOwner !SourceDescriptor !FilePath !ByteString
    deriving stock (Show, Eq)

data SourceScanCursor = SourceScanCursor
    !ScanOwner
    !ByteOffset
    !Int
    !Int
    !LineObservation
    ![PragmaCandidate]
    !Bool
    !(Maybe PendingProseStart)
    deriving stock (Show, Eq)

data ScannedPrefix = ScannedPrefix
    !SourceScanCursor
    ![Located FilePath]
    ![PresentationSpan]
    deriving stock (Show, Eq)

newtype SourceScanPrefix = SourceScanPrefix ScannedPrefix
    deriving stock (Show, Eq)

data VerificationScan = VerificationScan
    { verificationImports :: ![Located FilePath]
    , verificationPragmas :: ![SyntaxPragma]
    , verificationChunks :: ![[Located Token]]
    }
    deriving stock (Show, Eq)

newtype SourcePresentation =
    SourcePresentation (Vector PresentationSpan)
    deriving stock (Show, Eq)

data SourcePresentationBinding = SourcePresentationBinding
    !SourceDescriptor
    !ResolvedSourceAddress
    !SourceContentId
    deriving stock (Show, Eq)

data SourcePresentationBindingError =
    SourcePresentationBindingMismatch
        !SourcePresentationBinding
        !SourcePresentationBinding
    deriving stock (Eq)

instance Show SourcePresentationBindingError where
    show = Text.unpack . renderSourcePresentationBindingError

data SourcePresentationEntry = SourcePresentationEntry
    !SourcePresentationBinding
    !(Either PresentationScanError SourcePresentation)
    deriving stock (Show, Eq)

data SourcePresentationProjectionError
    = SourcePresentationBindingFailure
        !SourcePresentationBindingError
    | SourcePresentationDecodeInvariant
        !SourceScanInvariantError
    deriving stock (Show, Eq)

data DecodedPresentationSegment
    = DecodedPresentationHeading
        !DocumentHeadingLevel
        !Location
        !Text
        !(Maybe Text)
    | DecodedPresentationProse !Location !Text
    | DecodedPresentationFormal !Location !Text
    deriving stock (Show, Eq)

data ProjectedSourcePresentation
    = SourcePresentationUnavailable !PresentationScanError
    | SourcePresentationDecoded !(Vector DecodedPresentationSegment)
    deriving stock (Show, Eq)

data SourceScanInvariantError
    = SourceScanValidatedUtf8Invariant
        !FilePath
        !Text
        !Int
        !Int
    | SourceScanPositionOverflow
        !FilePath
        !Text
        !Int
    deriving stock (Show, Eq)

data SourceScanFailure error
    = SourceInputFailure !error
    | SourceScannerInvariantFailure !SourceScanInvariantError
    deriving stock (Show, Eq)

data SourceScanRejection
    = SourceScanUnexpectedInput !Location !Text
    | SourceScanUnexpectedEndOfInput !Location
    | SourceScanExplicitFailure !Location !Text
    | SourceScanLocationOutOfRange !FilePath !Int !Int
    deriving stock (Show, Eq)

newtype SourcePrefixError
    = SourcePrefixRejected SourceScanRejection
    deriving stock (Show, Eq)

data VerificationScanError
    = VerificationPrefixFailure !SourcePrefixError
    | VerificationPragmaFailure !SyntaxPragmaError
    | VerificationBodyFailure !SourceScanRejection
    deriving stock (Show, Eq)

data TokenSourceScanError
    = TokenSourcePrefixFailure !SourcePrefixError
    | TokenSourceBodyFailure !SourceScanRejection
    deriving stock (Show, Eq)

newtype PresentationScanError
    = PresentationScanRejected SourceScanRejection
    deriving stock (Show, Eq)

newtype SourceFragmentError
    = SourceFragmentRejected SourceScanRejection
    deriving stock (Show, Eq)

renderSourcePrefixError :: SourcePrefixError -> Text
renderSourcePrefixError (SourcePrefixRejected rejection) =
    renderSourceScanRejection "source prefix" rejection

renderVerificationScanError :: VerificationScanError -> Text
renderVerificationScanError = \case
    VerificationPrefixFailure failure ->
        renderSourcePrefixError failure
    VerificationPragmaFailure failure ->
        renderSyntaxPragmaError failure
    VerificationBodyFailure rejection ->
        renderSourceScanRejection "source body" rejection

renderTokenSourceScanError :: TokenSourceScanError -> Text
renderTokenSourceScanError = \case
    TokenSourcePrefixFailure failure ->
        renderSourcePrefixError failure
    TokenSourceBodyFailure rejection ->
        renderSourceScanRejection "source tokenization" rejection

renderPresentationScanError :: PresentationScanError -> Text
renderPresentationScanError (PresentationScanRejected rejection) =
    renderSourceScanRejection "source presentation" rejection

renderSourceFragmentError :: SourceFragmentError -> Text
renderSourceFragmentError (SourceFragmentRejected rejection) =
    renderSourceScanRejection "source fragment" rejection

renderSourcePresentationBindingError
    :: SourcePresentationBindingError
    -> Text
renderSourcePresentationBindingError
        (SourcePresentationBindingMismatch entry supplied) =
    "source presentation binding mismatch: entry "
        <> Text.pack (show entry)
        <> ", supplied source "
        <> Text.pack (show supplied)

renderSourceScanRejection :: Text -> SourceScanRejection -> Text
renderSourceScanRejection phase = \case
    SourceScanUnexpectedInput location input ->
        locationToText location
            <> ": unexpected input " <> Text.pack (show input)
    SourceScanUnexpectedEndOfInput location ->
        locationToText location <> ": unexpected end of input"
    SourceScanExplicitFailure location message ->
        locationToText location <> ": " <> message
    SourceScanLocationOutOfRange file line column ->
        Text.pack file
            <> ": " <> phase <> " location is out of range at "
            <> Text.pack (show line)
            <> ":"
            <> Text.pack (show column)

renderSourceScanInvariantError :: SourceScanInvariantError -> Text
renderSourceScanInvariantError = \case
    SourceScanValidatedUtf8Invariant file operation start end ->
        Text.pack file
            <> ": validated UTF-8 scanner invariant failed while "
            <> operation
            <> " over byte range "
            <> Text.pack (show start)
            <> ".."
            <> Text.pack (show end)
    SourceScanPositionOverflow file operation offset ->
        Text.pack file
            <> ": scanner position overflow while "
            <> operation
            <> " at byte offset "
            <> Text.pack (show offset)


-- The scanner cursor is always on a validated UTF-8 scalar boundary. Each
-- consumed scalar advances the byte cursor, source coordinates, physical-line
-- observation, and pragma candidates exactly once through
-- 'advanceScannerState'. A 'DecodedScalar' supplied to
-- 'consumePeekedScalar' must have been read at the current cursor, with no
-- intervening cursor change.
data ScannerState = ScannerState
    { scannerSource :: !ScanOwner
    , scannerOffset :: !Int
    , scannerLine :: !Int
    , scannerColumn :: !Int
    , scannerLineObservation :: !LineObservation
    , scannerPragmaCandidatesReversed :: ![PragmaCandidate]
    , scannerPresentationReversed :: ![PresentationSpan]
    , scannerEndedAtEof :: !Bool
    }

data DecodedScalar = DecodedScalar
    !Char
    !Int

data ScanAbort
    = ScanInputAbort !SourceScanRejection
    | ScanInvariantAbort !SourceScanInvariantError

type PrefixScanner = ExceptT ScanAbort (State ScannerState)

data PrefixAttempt
    = PrefixAccepted !ScannedPrefix
    | PrefixRejected !SourcePrefixError !ScannerState
    | PrefixInvariantRejected !SourceScanInvariantError

data TokenDemand
    = RetainTokens
    | DiscardTokens
    deriving stock (Show, Eq)

data HeadingScan
    = HeadingNotRecognized
    | HeadingScanned !(Maybe PendingProseStart)

data DocumentLead
    = DocumentEnd
    | DocumentTopLevel !MatchedTopLevelEnvironment
    | DocumentImport !Int
    | DocumentHeading !MatchedHeadingStart
    | DocumentRawHeading
    | DocumentComment
    | DocumentProse

data MatchedTopLevelEnvironment = MatchedTopLevelEnvironment
    !Int
    !Text

data TopLevelBoundary
    = TopLevelBegin
    | TopLevelEnd

data MatchedTopLevelBoundary = MatchedTopLevelBoundary
    !TopLevelBoundary
    !Int
    !Text

data MatchedHeadingStart = MatchedHeadingStart
    !DocumentHeadingLevel
    !Int

data FrameOpening = FrameOpening
    !Location
    !Text
    deriving stock (Show, Eq)

data ScanFrame
    = ScanTopText
    | ScanMath !Text !(Maybe FrameOpening)
    | ScanText !Int !FrameOpening
    deriving stock (Show, Eq)

data TokenEffect
    = TokenBegins !Text
    | TokenOpensFrame !Text !Text
    | TokenEnds !Text
    | TokenInvisibleBraceLeft
    | TokenInvisibleBraceRight
    | TokenHasNoFrameEffect
    deriving stock (Show, Eq)

data ScannedToken = ScannedToken
    !Location
    !TokenEffect
    !(Maybe (Located Token))

data BodyScan = BodyScan
    ![[Located Token]]
    !SourcePresentation
    ![PragmaCandidate]

data BodyAttempt
    = BodyAccepted !BodyScan
    | BodyRejected !SourceScanRejection !ScannerState
    | BodyInvariantRejected !SourceScanInvariantError

scanSourcePrefix
    :: IdentifiedLoadedSource
    -> Either (SourceScanFailure SourcePrefixError) SourceScanPrefix
scanSourcePrefix identified =
    case scanSourcePrefixAttempt (PhysicalScanOwner identified) of
        PrefixAccepted prefix ->
            Right (SourceScanPrefix prefix)
        PrefixRejected failure _state ->
            Left (SourceInputFailure failure)
        PrefixInvariantRejected failure ->
            Left (SourceScannerInvariantFailure failure)

scanSourcePrefixAttempt :: ScanOwner -> PrefixAttempt
scanSourcePrefixAttempt owner =
    case runState (runExceptT scanDocumentPrefix) initialState of
        (Right prefix, _finalState) ->
            PrefixAccepted prefix
        (Left (ScanInputAbort rejection), finalState) ->
            PrefixRejected (SourcePrefixRejected rejection) finalState
        (Left (ScanInvariantAbort failure), _finalState) ->
            PrefixInvariantRejected failure
  where
    initialState = initialScannerState owner

initialScannerState :: ScanOwner -> ScannerState
initialScannerState owner =
    ScannerState
        { scannerSource = owner
        , scannerOffset = 0
        , scannerLine = 1
        , scannerColumn = 1
        , scannerLineObservation =
            ObservingLineIndent (ByteOffset 0) 1
        , scannerPragmaCandidatesReversed = []
        , scannerPresentationReversed = []
        , scannerEndedAtEof = False
        }

sourcePrefixImports :: SourceScanPrefix -> [Located FilePath]
sourcePrefixImports
        (SourceScanPrefix (ScannedPrefix _cursor imports _presentation)) =
    imports

sourcePrefixIdentifiedSource
    :: SourceScanPrefix
    -> IdentifiedLoadedSource
sourcePrefixIdentifiedSource
        (SourceScanPrefix
            (ScannedPrefix cursor _imports _presentation)) =
    cursorIdentifiedSource cursor

forceSourceScanPrefixHandoff :: SourceScanPrefix -> ()
forceSourceScanPrefixHandoff
        (SourceScanPrefix
            (ScannedPrefix cursor imports presentation)) =
    forceCursor cursor
        `seq` forceList forceLocatedImport imports
        `seq` forceList forcePresentationSpan presentation
  where
    forceCursor
            (SourceScanCursor source offset line column observation
                candidates ended pending) =
        forceScanOwner source
            `seq` forceByteOffset offset
            `seq` line
            `seq` column
            `seq` forceLineObservation observation
            `seq` forceList forcePragmaCandidate candidates
            `seq` ended
            `seq` forceMaybe forcePendingProseStart pending

    forceScanOwner = \case
        PhysicalScanOwner source ->
            identifiedSourceLoaded source
                `seq` identifiedSourceDescriptor source
                `seq` identifiedSourceContentId source
                `seq` ()
        EphemeralScanOwner descriptor file bytes ->
            descriptor
                `seq` forceString file
                `seq` ByteString.length bytes
                `seq` ()

    forceLineObservation = \case
        ObservingLineIndent offset line ->
            forceByteOffset offset `seq` line `seq` ()
        ObservingPragmaCandidate offset line ->
            forceByteOffset offset `seq` line `seq` ()
        IgnoringPhysicalLine -> ()

    forcePragmaCandidate (PragmaCandidate line ending span') =
        line `seq` ending `seq` forceByteSpan span'

    forcePendingProseStart (PendingProseStart offset line column) =
        forceByteOffset offset `seq` line `seq` column `seq` ()

resumeVerificationScan
    :: SourceScanPrefix
    -> Either
        (SourceScanFailure VerificationScanError)
        (VerificationScan, SourcePresentationEntry)
resumeVerificationScan (SourceScanPrefix prefix) = do
    (verification, presentation) <- resumeVerificationData prefix
    pure
        ( verification
        , sourcePresentationEntry prefix presentation
        )

resumePresentationScan
    :: SourceScanPrefix
    -> Either SourceScanInvariantError SourcePresentationEntry
resumePresentationScan (SourceScanPrefix prefix) =
    case scanBodyAttempt DiscardTokens prefix of
        BodyRejected rejection _state ->
            Right
                (sourcePresentationUnavailableEntry
                    prefix
                    (PresentationScanRejected rejection))
        BodyInvariantRejected failure ->
            Left failure
        BodyAccepted body ->
            Right
                (sourcePresentationEntry
                    prefix
                    (bodyScanPresentation body))

resumeVerificationData
    :: ScannedPrefix
    -> Either
        (SourceScanFailure VerificationScanError)
        (VerificationScan, SourcePresentation)
resumeVerificationData prefix =
    case scanBodyAttempt RetainTokens prefix of
        BodyInvariantRejected failure ->
            Left (SourceScannerInvariantFailure failure)
        BodyAccepted body ->
            finishSuccessful body
        BodyRejected rejection failedState -> do
            completedState <- first SourceScannerInvariantFailure
                (finishLineObservationOnly failedState)
            pragmas <- parseVerificationPragmas
                (scannerSource completedState)
                (reverse
                    (scannerPragmaCandidatesReversed completedState))
            pragmas `seq`
                Left
                    (SourceInputFailure
                        (VerificationBodyFailure rejection))
  where
    finishSuccessful body = do
        pragmas <- parseVerificationPragmas
            (cursorScanOwner (scannedPrefixCursor prefix))
            (bodyScanPragmaCandidates body)
        pure
            ( VerificationScan
                (scannedPrefixImports prefix)
                pragmas
                (bodyScanChunks body)
            , bodyScanPresentation body
            )

parseVerificationPragmas
    :: ScanOwner
    -> [PragmaCandidate]
    -> Either
        (SourceScanFailure VerificationScanError)
        [SyntaxPragma]
parseVerificationPragmas owner candidates =
    case parseObservedPragmas owner candidates of
        Left (SourceInputFailure failure) ->
            Left
                (SourceInputFailure
                    (VerificationPragmaFailure failure))
        Left (SourceScannerInvariantFailure failure) ->
            Left (SourceScannerInvariantFailure failure)
        Right pragmas -> Right pragmas

scanBodyAttempt
    :: TokenDemand
    -> ScannedPrefix
    -> BodyAttempt
scanBodyAttempt demand prefix =
    case runState
            (runExceptT
                (scanDocumentBody
                    demand
                    (cursorPendingProseStart (scannedPrefixCursor prefix))
                    []))
            (scannerStateFromPrefix prefix) of
        (Left (ScanInputAbort rejection), finalState) ->
            BodyRejected rejection finalState
        (Left (ScanInvariantAbort failure), _state) ->
            BodyInvariantRejected failure
        (Right chunks, finalState) ->
            BodyAccepted
                (BodyScan
                    chunks
                    (SourcePresentation
                        (Vector.fromList
                            (reverse
                                (scannerPresentationReversed finalState))))
                    (reverse
                        (scannerPragmaCandidatesReversed finalState)))

finishLineObservationOnly
    :: ScannerState
    -> Either SourceScanInvariantError ScannerState
finishLineObservationOnly initial =
    case runState (runExceptT go) initial of
        (Left (ScanInvariantAbort failure), _state) -> Left failure
        (Left (ScanInputAbort _rejection), _state) ->
            impossible
                "physical-line observation produced an input rejection"
        (Right (), finalState) -> Right finalState
  where
    go = do
        eof <- atEnd
        if eof
            then finalizeEndOfFileObservation
            else void consumeNextScalar *> go

scanDocumentBody
    :: TokenDemand
    -> Maybe PendingProseStart
    -> [[Located Token]]
    -> PrefixScanner [[Located Token]]
scanDocumentBody demand pending reversedChunks = do
    lead <- classifyDocumentLead <$> get
    case lead of
        DocumentEnd -> do
            finalizeEndOfFileObservation
            pure (reverse reversedChunks)
        DocumentTopLevel environment -> do
            chunk <- scanFormalEnvironment demand environment
            scanDocumentBody
                demand
                Nothing
                (maybe reversedChunks (: reversedChunks) chunk)
        DocumentImport after -> do
            consumeToOffset after
            throwExplicit
                "imports must form one contiguous top-level block; this import occurs after that block was closed"
        DocumentHeading headingStart -> do
            heading <- scanHeadingAtCursor headingStart
            case heading of
                HeadingScanned nextPending ->
                    scanDocumentBody demand nextPending reversedChunks
                HeadingNotRecognized ->
                    continueProse
        DocumentComment -> do
            skipComment
            scanDocumentBody demand Nothing reversedChunks
        DocumentRawHeading ->
            continueProse
        DocumentProse ->
            continueProse
  where
    continueProse = do
        scanDocumentProse pending
        scanDocumentBody demand Nothing reversedChunks

scanFormalEnvironment
    :: TokenDemand
    -> MatchedTopLevelEnvironment
    -> PrefixScanner (Maybe [Located Token])
scanFormalEnvironment demand
        (MatchedTopLevelEnvironment after environment) = do
    location <- currentPrefixLocation
    consumeToOffset after
    whitespace <- scanFormalWhitespace
    let opening = Located location (BeginEnv environment) whitespace
        initialBuild =
            case demand of
                RetainTokens -> (opening :)
                DiscardTokens -> id
    modify' \state ->
        state
            { scannerPresentationReversed =
                PresentationFormal location environment
                    : scannerPresentationReversed state
            }
    tokens <- go (ScanTopText :| []) initialBuild
    pure
        (case demand of
            RetainTokens -> Just tokens
            DiscardTokens -> Nothing)
  where
    rootFrames = ScanTopText :| []

    -- A formal chunk is completed only by its matching top-level end sentinel
    -- while the frame stack is exactly 'rootFrames'. No known top-level
    -- boundary is dispatched according to an inner lexical frame, and EOF
    -- cannot complete the chunk.
    go frames build = do
        eof <- atEnd
        if eof
            then throwAtEnd frames
            else do
                boundary <- matchingTopLevelBoundary <$> get
                case boundary of
                    Just matched -> handleBoundary frames build matched
                    Nothing -> scanOrdinaryToken frames build

    scanOrdinaryToken frames build = do
        scanned <- scanNextToken demand (NonEmpty.head frames)
        case scanned of
            Nothing -> requireChar >>= throwUnexpected
            Just (ScannedToken location effect retained) ->
                go
                    (advanceFrames location effect frames)
                    (extendBuild retained build)

    handleBoundary frames build
            (MatchedTopLevelBoundary boundary _after encountered) =
        case boundary of
            TopLevelBegin ->
                if frames == rootFrames
                    then throwExplicit
                        ("cannot begin top-level "
                            <> encountered
                            <> " inside "
                            <> environment
                            <> "; expected "
                            <> endSentinel environment
                            <> " first")
                    else throwExplicit
                        (renderUnclosedFrame
                            (NonEmpty.head frames)
                            (beginSentinel encountered)
                            <> "; outer "
                            <> environment
                            <> " is still open; expected "
                            <> endSentinel environment)
            TopLevelEnd
                | encountered == environment ->
                    if frames == rootFrames
                        then scanMatchingEnd build
                        else throwExplicit
                            (renderUnclosedFrame
                                (NonEmpty.head frames)
                                (endSentinel encountered))
                | frames == rootFrames ->
                    throwExplicit
                        ("unexpected "
                            <> endSentinel encountered
                            <> " while scanning "
                            <> environment
                            <> "; expected "
                            <> endSentinel environment)
                | otherwise ->
                    throwExplicit
                        (renderUnclosedFrame
                            (NonEmpty.head frames)
                            (endSentinel encountered)
                            <> "; outer "
                            <> environment
                            <> " is still open; expected "
                            <> endSentinel environment)

    scanMatchingEnd build = do
        scanned <- scanNextToken demand ScanTopText
        case scanned of
            Just (ScannedToken _location (TokenEnds ended) retained)
                | ended == environment ->
                    pure (extendBuild retained build [])
            _ ->
                impossible
                    "matched top-level end was not scanned as its EndEnv token"

    throwAtEnd frames
        | frames == rootFrames =
            throwExplicit
                ("unexpected end of input while scanning "
                    <> environment
                    <> "; expected "
                    <> endSentinel environment)
        | otherwise =
            throwExplicit
                (renderUnclosedFrameAtEnd (NonEmpty.head frames)
                    <> "; outer "
                    <> environment
                    <> " is also not closed; expected "
                    <> endSentinel environment)

    extendBuild retained build =
        case retained of
            Nothing -> build
            Just token -> build . (token :)

advanceFrames
    :: Location
    -> TokenEffect
    -> NonEmpty ScanFrame
    -> NonEmpty ScanFrame
advanceFrames location effect frames@(frame :| rest) =
    case (frame, effect) of
        (ScanTopText, TokenOpensFrame opened expected)
            | opened == "math" || opened == "align*" ->
            ScanMath opened (Just (FrameOpening location expected))
                :| (frame : rest)
        (ScanText{}, TokenOpensFrame opened expected)
            | opened == "math" || opened == "align*" ->
            ScanMath opened (Just (FrameOpening location expected))
                :| (frame : rest)
        (ScanMath environment _, TokenEnds ended)
            | environment == ended ->
                popFrame frames
        (ScanMath{}, TokenOpensFrame "text" expected) ->
            ScanText 1 (FrameOpening location expected) :| (frame : rest)
        (ScanText depth opening, TokenInvisibleBraceLeft) ->
            ScanText (depth + 1) opening :| rest
        (ScanText depth opening, TokenInvisibleBraceRight)
            | depth > 1 ->
                ScanText (depth - 1) opening :| rest
        (ScanText 1 _, TokenEnds "text") ->
            popFrame frames
        _ -> frames

renderUnclosedFrame :: ScanFrame -> Text -> Text
renderUnclosedFrame frame boundary =
    let (description, FrameOpening location expected) =
            reportableFrameOpening frame
    in description
        <> " opened at "
        <> locationCoordinates location
        <> " is not closed before "
        <> boundary
        <> "; expected '"
        <> expected
        <> "'"

renderUnclosedFrameAtEnd :: ScanFrame -> Text
renderUnclosedFrameAtEnd frame = renderUnclosedFrame frame "end of input"

reportableFrameOpening :: ScanFrame -> (Text, FrameOpening)
reportableFrameOpening = \case
    ScanMath "math" (Just opening@(FrameOpening _ expected)) ->
        (if expected == "\\]" then "displayed math" else "inline math", opening)
    ScanMath "align*" (Just opening) -> ("align*", opening)
    ScanMath environment (Just opening) -> (environment, opening)
    ScanText _ opening -> ("embedded text", opening)
    ScanTopText -> impossible "root scanner frame has no unclosed-frame report"
    ScanMath _ Nothing ->
        impossible "synthetic scanner frame has no unclosed-frame report"

locationCoordinates :: Location -> Text
locationCoordinates location =
    Text.pack (show (locLine location))
        <> ":"
        <> Text.pack (show (locColumn location))

beginSentinel :: Text -> Text
beginSentinel environment = "\\begin{" <> environment <> "}"

endSentinel :: Text -> Text
endSentinel environment = "\\end{" <> environment <> "}"

popFrame :: NonEmpty ScanFrame -> NonEmpty ScanFrame
popFrame singleton@(_frame :| []) = singleton
popFrame (_frame :| (next : rest)) = next :| rest

scannedPrefixCursor :: ScannedPrefix -> SourceScanCursor
scannedPrefixCursor (ScannedPrefix cursor _imports _presentation) =
    cursor

scannedPrefixImports :: ScannedPrefix -> [Located FilePath]
scannedPrefixImports (ScannedPrefix _cursor imports _presentation) =
    imports

cursorScanOwner :: SourceScanCursor -> ScanOwner
cursorScanOwner
        (SourceScanCursor owner _offset _line _column _observation
            _candidates _ended _pending) =
    owner

cursorPendingProseStart
    :: SourceScanCursor
    -> Maybe PendingProseStart
cursorPendingProseStart
        (SourceScanCursor _owner _offset _line _column _observation
            _candidates _ended pending) =
    pending

scannerStateFromPrefix :: ScannedPrefix -> ScannerState
scannerStateFromPrefix
        (ScannedPrefix
            (SourceScanCursor owner (ByteOffset offset) line column
                observation candidates ended _pending)
            _imports
            presentation) =
    ScannerState
        { scannerSource = owner
        , scannerOffset = offset
        , scannerLine = line
        , scannerColumn = column
        , scannerLineObservation = observation
        , scannerPragmaCandidatesReversed = reverse candidates
        , scannerPresentationReversed = reverse presentation
        , scannerEndedAtEof = ended
        }

bodyScanChunks :: BodyScan -> [[Located Token]]
bodyScanChunks (BodyScan chunks _presentation _candidates) = chunks

bodyScanPresentation :: BodyScan -> SourcePresentation
bodyScanPresentation (BodyScan _chunks presentation _candidates) =
    presentation

bodyScanPragmaCandidates :: BodyScan -> [PragmaCandidate]
bodyScanPragmaCandidates (BodyScan _chunks _presentation candidates) =
    candidates

sourcePresentationEntry
    :: ScannedPrefix
    -> SourcePresentation
    -> SourcePresentationEntry
sourcePresentationEntry prefix presentation =
    SourcePresentationEntry
        (sourcePresentationBinding prefix)
        (Right presentation)

sourcePresentationUnavailableEntry
    :: ScannedPrefix
    -> PresentationScanError
    -> SourcePresentationEntry
sourcePresentationUnavailableEntry prefix failure =
    SourcePresentationEntry
        (sourcePresentationBinding prefix)
        (Left failure)

sourcePresentationBinding :: ScannedPrefix -> SourcePresentationBinding
sourcePresentationBinding prefix =
    bindingFromIdentified
        (cursorIdentifiedSource (scannedPrefixCursor prefix))

bindingFromIdentified
    :: IdentifiedLoadedSource
    -> SourcePresentationBinding
bindingFromIdentified identified =
    SourcePresentationBinding
        (identifiedSourceDescriptor identified)
        (resolvedSourceAddress
            (loadedSource (identifiedSourceLoaded identified)))
        (identifiedSourceContentId identified)

parseObservedPragmas
    :: ScanOwner
    -> [PragmaCandidate]
    -> Either
        (SourceScanFailure SyntaxPragmaError)
        [SyntaxPragma]
parseObservedPragmas owner =
    traverse parseCandidate
  where
    parseCandidate (PragmaCandidate line ending span') = do
        source <- first SourceScannerInvariantFailure
            (decodeOwnerSpan owner "decoding a syntax pragma" span')
        first SourceInputFailure
            (parseSyntaxPragmaLine
                (scanOwnerSourceDescriptor owner)
                (scanOwnerLocationPath owner)
                line
                ending
                source)


projectSourcePresentationEntry
    :: IdentifiedLoadedSource
    -> SourcePresentationEntry
    -> Either
        SourcePresentationProjectionError
        ProjectedSourcePresentation
projectSourcePresentationEntry identified
        (SourcePresentationEntry entryBinding payload) = do
    let suppliedBinding = bindingFromIdentified identified
    unless (entryBinding == suppliedBinding)
        (Left
            (SourcePresentationBindingFailure
                (SourcePresentationBindingMismatch
                    entryBinding
                    suppliedBinding)))
    case payload of
        Left failure -> pure (SourcePresentationUnavailable failure)
        Right presentation ->
            SourcePresentationDecoded
                <$> first SourcePresentationDecodeInvariant
                    (decodeSourcePresentation
                        (PhysicalScanOwner identified)
                        presentation)

scanCompleteVerificationText
    :: SourceDescriptor
    -> FilePath
    -> Text
    -> Either
        (SourceScanFailure VerificationScanError)
        VerificationScan
scanCompleteVerificationText descriptor file source =
    case scanSourcePrefixAttempt owner of
        PrefixInvariantRejected failure ->
            Left (SourceScannerInvariantFailure failure)
        PrefixAccepted prefix ->
            fst <$> resumeVerificationData prefix
        PrefixRejected prefixFailure failedState -> do
            completedState <- first SourceScannerInvariantFailure
                (finishLineObservationOnly failedState)
            case parseVerificationPragmas
                    owner
                    (reverse
                        (scannerPragmaCandidatesReversed completedState)) of
                Left failure -> Left failure
                Right _pragmas ->
                    Left
                        (SourceInputFailure
                            (VerificationPrefixFailure prefixFailure))
  where
    owner = EphemeralScanOwner descriptor file (Text.encodeUtf8 source)

scanCompleteSourceTokens
    :: IdentifiedLoadedSource
    -> Either
        (SourceScanFailure TokenSourceScanError)
        [[Located Token]]
scanCompleteSourceTokens identified =
    case scanSourcePrefixAttempt (PhysicalScanOwner identified) of
        PrefixInvariantRejected failure ->
            Left (SourceScannerInvariantFailure failure)
        PrefixRejected prefixFailure _state ->
            Left
                (SourceInputFailure
                    (TokenSourcePrefixFailure prefixFailure))
        PrefixAccepted prefix ->
            case scanBodyAttempt RetainTokens prefix of
                BodyInvariantRejected failure ->
                    Left (SourceScannerInvariantFailure failure)
                BodyRejected rejection _state ->
                    Left
                        (SourceInputFailure
                            (TokenSourceBodyFailure rejection))
                BodyAccepted body -> Right (bodyScanChunks body)

scanCompletePresentationText
    :: SourceDescriptor
    -> FilePath
    -> Text
    -> Either
        (SourceScanFailure PresentationScanError)
        (Vector DecodedPresentationSegment)
scanCompletePresentationText descriptor file source =
    case scanSourcePrefixAttempt owner of
        PrefixInvariantRejected failure ->
            Left (SourceScannerInvariantFailure failure)
        PrefixRejected (SourcePrefixRejected rejection) _state ->
            Left
                (SourceInputFailure
                    (PresentationScanRejected rejection))
        PrefixAccepted prefix ->
            case scanBodyAttempt DiscardTokens prefix of
                BodyInvariantRejected failure ->
                    Left (SourceScannerInvariantFailure failure)
                BodyRejected rejection _state ->
                    Left
                        (SourceInputFailure
                            (PresentationScanRejected rejection))
                BodyAccepted body ->
                    first SourceScannerInvariantFailure
                        (decodeSourcePresentation
                            owner
                            (bodyScanPresentation body))
  where
    owner = EphemeralScanOwner descriptor file (Text.encodeUtf8 source)

scanMathSnippet
    :: Text
    -> Either
        (SourceScanFailure SourceFragmentError)
        [Located Token]
scanMathSnippet source =
    runSourceFragment "<presentation-math>" source do
        void scanFormalWhitespace
        go initialFrames id
  where
    initialFrames = ScanMath "presentation" Nothing :| []

    go frames build = do
        scanned <- scanNextToken RetainTokens (NonEmpty.head frames)
        case scanned of
            Nothing -> do
                eof <- atEnd
                if eof && frames == initialFrames
                    then pure (build [])
                    else if eof
                        then throwUnexpectedEnd
                        else requireChar >>= throwUnexpected
            Just (ScannedToken location effect retained) ->
                case retained of
                    Nothing ->
                        impossible
                            "retained fragment token scan discarded a token"
                    Just token ->
                        go
                            (advanceFrames location effect frames)
                            (build . (token :))

parsePresentationVariableFragment
    :: Text
    -> Either SourceScanInvariantError (Maybe (NonEmpty Text))
parsePresentationVariableFragment source =
    runOptionalSourceFragment "<presentation-variable>" source do
        skipPresentationFragmentSpace
        firstVariable <- scanPresentationVariableName
        remaining <- go []
        pure (firstVariable :| reverse remaining)
  where
    go reversed = do
        skipPresentationFragmentSpace
        comma <- consumeIfChar ','
        if comma
            then do
                skipPresentationFragmentSpace
                variable <- scanPresentationVariableName
                go (variable : reversed)
            else do
                eof <- atEnd
                if eof
                    then pure reversed
                    else requireChar >>= throwUnexpected

parsePresentationReferenceFragment
    :: Text
    -> Either SourceScanInvariantError (Maybe (NonEmpty Text))
parsePresentationReferenceFragment source =
    runOptionalSourceFragment "<presentation-reference>" source do
        opening <- matchingLiteral ["\\ref{", "\\cref{", "\\obv{"]
        case opening of
            Nothing -> requireChar >>= throwUnexpected
            Just literal -> consumeLiteral literal
        spans <- scanFormattedReferenceMarkers
        consumeExpected '}'
        eof <- atEnd
        unless eof (requireChar >>= throwUnexpected)
        traverse (decodeSpan "decoding a presentation reference") spans

runSourceFragment
    :: FilePath
    -> Text
    -> PrefixScanner value
    -> Either (SourceScanFailure SourceFragmentError) value
runSourceFragment file source action =
    case runState
            (runExceptT action)
            (initialScannerState
                (EphemeralScanOwner
                    anonymousSourceDescriptor
                    file
                    (Text.encodeUtf8 source))) of
        (Right value, _finalState) -> Right value
        (Left (ScanInputAbort rejection), _finalState) ->
            Left
                (SourceInputFailure
                    (SourceFragmentRejected rejection))
        (Left (ScanInvariantAbort failure), _finalState) ->
            Left (SourceScannerInvariantFailure failure)

runOptionalSourceFragment
    :: FilePath
    -> Text
    -> PrefixScanner value
    -> Either SourceScanInvariantError (Maybe value)
runOptionalSourceFragment file source action =
    case runSourceFragment file source action of
        Right value -> Right (Just value)
        Left (SourceInputFailure _failure) -> Right Nothing
        Left (SourceScannerInvariantFailure failure) -> Left failure

skipPresentationFragmentSpace :: PrefixScanner ()
skipPresentationFragmentSpace =
    consumeWhile \character ->
        character == ' '
            || character == '\t'
            || character == '\r'
            || character == '\n'

scanPresentationVariableName :: PrefixScanner Text
scanPresentationVariableName = do
    base <- scanVariableBase RetainTokens
    case base of
        Nothing -> requireChar >>= throwUnexpected
        Just retainedBase -> do
            variation <- scanVariableVariation RetainTokens
            pure
                (fromMaybe "" retainedBase
                    <> fromMaybe "" variation)

decodeSourcePresentation
    :: ScanOwner
    -> SourcePresentation
    -> Either
        SourceScanInvariantError
        (Vector DecodedPresentationSegment)
decodeSourcePresentation owner (SourcePresentation spans) =
    traverse decodeSegment spans
  where
    decodeSegment = \case
        PresentationHeading level location title marker -> do
            decodedTitle <- decodeOwnerSpan
                owner "decoding a presentation heading" title
            decodedMarker <- traverse
                (decodeOwnerSpan
                    owner
                    "decoding a presentation heading marker")
                marker
            pure
                (DecodedPresentationHeading
                    level location decodedTitle decodedMarker)
        PresentationProse location prose ->
            DecodedPresentationProse location <$>
                decodeOwnerSpan owner "decoding presentation prose" prose
        PresentationFormal location environment ->
            pure (DecodedPresentationFormal location environment)

forceVerificationScanHandoff :: VerificationScan -> ()
forceVerificationScanHandoff
        (VerificationScan imports pragmas chunks) =
    forceList forceLocatedImport imports
        `seq` forceList (\pragma -> pragma `seq` ()) pragmas
        `seq` forceTokenChunks chunks

forceSourceTokenChunksHandoff :: [[Located Token]] -> ()
forceSourceTokenChunksHandoff = forceTokenChunks

forceSourcePresentationEntryHandoff :: SourcePresentationEntry -> ()
forceSourcePresentationEntryHandoff
        (SourcePresentationEntry binding payload) =
    forcePresentationBinding binding
        `seq` case payload of
            Left failure -> forcePresentationScanError failure
            Right (SourcePresentation spans) ->
                Vector.foldl'
                    (\forced span' -> forced `seq` forcePresentationSpan span')
                    ()
                    spans

forcePresentationBinding :: SourcePresentationBinding -> ()
forcePresentationBinding
        (SourcePresentationBinding descriptor address content) =
    descriptor `seq` address `seq` content `seq` ()

forcePresentationScanError :: PresentationScanError -> ()
forcePresentationScanError (PresentationScanRejected rejection) =
    forceSourceScanRejection rejection

forceSourceScanRejection :: SourceScanRejection -> ()
forceSourceScanRejection = \case
    SourceScanUnexpectedInput location input ->
        location `seq` Text.length input `seq` ()
    SourceScanUnexpectedEndOfInput location -> location `seq` ()
    SourceScanExplicitFailure location message ->
        location `seq` Text.length message `seq` ()
    SourceScanLocationOutOfRange file line column ->
        forceString file `seq` line `seq` column `seq` ()

forceLocatedImport :: Located FilePath -> ()
forceLocatedImport (Located location path whitespace) =
    location `seq` forceString path `seq` whitespace `seq` ()

forceTokenChunks :: [[Located Token]] -> ()
forceTokenChunks = forceList (forceList forceLocatedToken)

forceLocatedToken :: Located Token -> ()
forceLocatedToken (Located location token whitespace) =
    location `seq` forceToken token `seq` whitespace `seq` ()

forceToken :: Token -> ()
forceToken = \case
    Word payload -> Text.length payload `seq` ()
    Variable payload -> Text.length payload `seq` ()
    Symbol payload -> Text.length payload `seq` ()
    Integer value -> value `seq` ()
    Command payload -> Text.length payload `seq` ()
    NamedItem payload -> Text.length payload `seq` ()
    CaseHeading payload -> Text.length payload `seq` ()
    CommandReference command markers ->
        Text.length command `seq` forceNonEmpty forceText markers
    Label marker -> Text.length marker `seq` ()
    Ref markers -> forceNonEmpty forceText markers
    BeginEnv environment -> Text.length environment `seq` ()
    EndEnv environment -> Text.length environment `seq` ()
    ParenL -> ()
    ParenR -> ()
    BracketL -> ()
    BracketR -> ()
    VisibleBraceL -> ()
    VisibleBraceR -> ()
    InvisibleBraceL -> ()
    InvisibleBraceR -> ()

forcePresentationSpan :: PresentationSpan -> ()
forcePresentationSpan = \case
    PresentationHeading level location title marker ->
        level
            `seq` location
            `seq` forceByteSpan title
            `seq` forceMaybe forceByteSpan marker
    PresentationProse location prose ->
        location `seq` forceByteSpan prose
    PresentationFormal location environment ->
        location `seq` Text.length environment `seq` ()

forceByteSpan :: ByteSpan -> ()
forceByteSpan (ByteSpan start end) =
    forceByteOffset start `seq` forceByteOffset end

forceByteOffset :: ByteOffset -> ()
forceByteOffset (ByteOffset offset) = offset `seq` ()

forceText :: Text -> ()
forceText value = Text.length value `seq` ()

forceString :: String -> ()
forceString = foldr (\character rest -> character `seq` rest) ()

forceList :: (value -> ()) -> [value] -> ()
forceList forceValue = \case
    [] -> ()
    value : rest ->
        forceValue value `seq` forceList forceValue rest

forceNonEmpty :: (value -> ()) -> NonEmpty value -> ()
forceNonEmpty forceValue (value :| rest) =
    forceValue value `seq` forceList forceValue rest

forceMaybe :: (value -> ()) -> Maybe value -> ()
forceMaybe forceValue = \case
    Nothing -> ()
    Just value -> forceValue value


scanDocumentPrefix :: PrefixScanner ScannedPrefix
scanDocumentPrefix =
    scanBeforeImports Nothing

scanBeforeImports
    :: Maybe PendingProseStart
    -> PrefixScanner ScannedPrefix
scanBeforeImports pending = do
    lead <- classifyDocumentLead <$> get
    case lead of
        DocumentEnd -> finishPrefix [] Nothing
        DocumentTopLevel{} -> finishPrefix [] Nothing
        DocumentImport after -> scanImportBlock after
        DocumentHeading headingStart -> do
            heading <- scanHeadingAtCursor headingStart
            case heading of
                HeadingScanned nextPending ->
                    scanBeforeImports nextPending
                HeadingNotRecognized ->
                    continueProse
        DocumentComment -> do
            skipComment
            scanBeforeImports Nothing
        DocumentRawHeading ->
            continueProse
        DocumentProse ->
            continueProse
  where
    continueProse = do
        scanDocumentProse pending
        scanBeforeImports Nothing

scanImportBlock :: Int -> PrefixScanner ScannedPrefix
scanImportBlock after = do
    firstImport <- scanImport after
    go [firstImport]
  where
    go reversedImports = do
        pending <- scanImportTrivia
        state <- get
        case matchingImportStart state of
            Just nextAfter -> do
                nextImport <- scanImport nextAfter
                go (nextImport : reversedImports)
            Nothing ->
                finishPrefix (reverse reversedImports) pending

finishPrefix
    :: [Located FilePath]
    -> Maybe PendingProseStart
    -> PrefixScanner ScannedPrefix
finishPrefix imports pending = do
    eof <- atEnd
    when eof finalizeEndOfFileObservation
    state <- get
    let retainedPending = if eof then Nothing else pending
        cursor = SourceScanCursor
            (scannerSource state)
            (ByteOffset (scannerOffset state))
            (scannerLine state)
            (scannerColumn state)
            (scannerLineObservation state)
            (reverse (scannerPragmaCandidatesReversed state))
            eof
            retainedPending
    pure
        (ScannedPrefix
            cursor
            imports
            (reverse (scannerPresentationReversed state)))


scanHeading
    :: MatchedHeadingStart
    -> PrefixScanner (Maybe PendingProseStart)
scanHeading (MatchedHeadingStart level openerEnd) = do
    location <- currentPrefixLocation
    consumeToOffset openerEnd
    titleStart <- gets scannerOffset
    titleEnd <- scanBalancedHeading 1
    gapStart <- currentPendingProseStart
    consumeWhile isHeadingGap
    gapEnd <- gets scannerOffset
    let pending =
            if pendingOffset gapStart == gapEnd
                then Nothing
                else Just gapStart
    marker <- matchHeadingLabel
    markerSpan <- case marker of
        Nothing -> pure Nothing
        Just (start, end, markerEnd) -> do
            consumeToOffset markerEnd
            pure
                (Just
                    (ByteSpan (ByteOffset start) (ByteOffset end)))
    modify' \state ->
        state
            { scannerPresentationReversed =
                PresentationHeading
                    level
                    location
                    (ByteSpan
                        (ByteOffset titleStart)
                        (ByteOffset titleEnd))
                    markerSpan
                    : scannerPresentationReversed state
            }
    pure (if isJust marker then Nothing else pending)

scanBalancedHeading :: Int -> PrefixScanner Int
scanBalancedHeading depth = do
    next <- peekScalar
    case next of
        Nothing -> throwUnexpectedEnd
        Just scalar@(DecodedScalar '{' _) ->
            consumePeekedScalar scalar *> scanBalancedHeading (depth + 1)
        Just scalar@(DecodedScalar '}' _)
            | depth == 1 -> do
                end <- gets scannerOffset
                consumePeekedScalar scalar
                pure end
            | otherwise ->
                consumePeekedScalar scalar *> scanBalancedHeading (depth - 1)
        Just scalar ->
            consumePeekedScalar scalar *> scanBalancedHeading depth

scanDocumentProse
    :: Maybe PendingProseStart
    -> PrefixScanner ()
scanDocumentProse pending = do
    start <- maybe currentPendingProseStart pure pending
    firstCharacter <- consumeNextScalar
    nonWhitespace <- go (not (isSpace firstCharacter))
    end <- gets scannerOffset
    when nonWhitespace do
        location <- locationAtPending start
        modify' \state ->
            state
                { scannerPresentationReversed =
                    PresentationProse
                        location
                        (ByteSpan
                            (pendingByteOffset start)
                            (ByteOffset end))
                        : scannerPresentationReversed state
                }
  where
    go foundNonWhitespace = do
        lead <- classifyDocumentLead <$> get
        case lead of
            DocumentProse -> do
                character <- consumeNextScalar
                go (foundNonWhitespace || not (isSpace character))
            _ -> pure foundNonWhitespace

skipComment :: PrefixScanner ()
skipComment = do
    consumeExpected '%'
    go
  where
    go = do
        scalar <- peekScalar
        case scalar of
            Nothing -> pure ()
            Just (DecodedScalar '\n' _) -> pure ()
            Just value -> consumePeekedScalar value *> go

scanFormalWhitespace :: PrefixScanner Whitespace
scanFormalWhitespace =
    go NoSpace
  where
    go accumulated = do
        scalar <- peekScalar
        case scalar of
            Just value@(DecodedScalar character _)
                | character == ' ' || character == '\n' || character == '\r' ->
                    consumePeekedScalar value *> go Space
            Just (DecodedScalar '%' _) ->
                skipComment *> go accumulated
            Just (DecodedScalar '\\' _) -> do
                state <- get
                let nextOffset = scannerOffset state + 1
                if maybe False isFormalSpaceEscapeByte
                        (byteAt (scannerBytes state) nextOffset)
                    then consumeToOffset (nextOffset + 1) *> go Space
                    else pure accumulated
            _ -> pure accumulated

matchingLiteral :: [ByteString] -> PrefixScanner (Maybe ByteString)
matchingLiteral literals = do
    state <- get
    let bytes = scannerBytes state
        offset = scannerOffset state
        go = \case
            [] -> Nothing
            literal : remaining
                | literalAt bytes offset literal -> Just literal
                | otherwise -> go remaining
    pure (go literals)

mathCloserFor :: ByteString -> Text
mathCloserFor = \case
    "$" -> "$"
    "\\(" -> "\\)"
    "\\[" -> "\\]"
    literal ->
        impossible
            ("no corresponding math closer for " <> show literal)


scanNextToken
    :: TokenDemand
    -> ScanFrame
    -> PrefixScanner (Maybe ScannedToken)
scanNextToken demand = \case
    ScanTopText -> scanNormalToken demand
    ScanMath{} -> scanMathToken demand
    ScanText depth _ -> scanTextToken demand depth

scanNormalToken
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanNormalToken demand = do
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar value _)
            | isWordCharacter value ->
                Just <$> scanWordToken demand decoded
            | isFormalSymbol value ->
                Just <$> scanSymbolToken demand decoded
            | isAsciiDigit value ->
                Just <$> scanIntegerToken demand decoded
        Just (DecodedScalar '$' _) ->
            Just <$> scanFixedLexeme
                demand "$" (BeginEnv "math") (TokenOpensFrame "math" "$")
        Just (DecodedScalar '(' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar '[' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar '{' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar ')' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar ']' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar '}' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar '\\' _) -> scanNormalControlSequence demand
        _ -> pure Nothing

scanNormalControlSequence
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanNormalControlSequence demand = do
    beginMath <- matchingLiteral ["\\(", "\\["]
    case beginMath of
        Just literal ->
            Just <$> scanFixedLexeme
                demand
                literal
                (BeginEnv "math")
                (TokenOpensFrame "math" (mathCloserFor literal))
        Nothing -> do
            align <- startsWith "\\begin{align*}"
            if align
                then Just <$> scanFixedLexeme
                    demand
                    "\\begin{align*}"
                    (BeginEnv "align*")
                    (TokenOpensFrame "align*" "\\end{align*}")
                else do
                    subEnvironment <- matchingSubEnvironment
                    case subEnvironment of
                        Just (literal, token, effect) ->
                            Just <$> scanFixedLexeme
                                demand literal token effect
                        Nothing -> do
                            opening <- startsOpeningDelimiter
                            if opening
                                then Just <$> scanOpeningDelimiter demand
                                else do
                                    closing <- startsClosingDelimiter
                                    if closing
                                        then Just <$> scanClosingDelimiter demand
                                        else scanNormalNamedControl demand

scanNormalNamedControl
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanNormalNamedControl demand = do
    label <- startsWith "\\label{"
    if label
        then Just <$> scanLabelToken demand
        else do
            reference <- startsOrdinaryOrHyperReference
            if reference
                then Just <$> scanReferenceToken demand
                else do
                    method <- startsProofMethodReference
                    if method
                        then Just <$> scanProofMethodReferenceToken demand
                        else do
                            environmentEnd <- startsGenericEnvironmentEnd
                            if environmentEnd
                                then Just <$> scanEnvironmentEndToken demand
                                else Just <$> scanCommandToken demand

scanMathToken
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanMathToken demand = do
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar value _)
            | isLetter value ->
                Just <$> scanLetterVariableToken demand decoded
            | isFormalSymbol value ->
                Just <$> scanSymbolToken demand decoded
            | isAsciiDigit value ->
                Just <$> scanIntegerToken demand decoded
        Just (DecodedScalar '(' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar '[' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar '{' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar ')' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar ']' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar '}' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar '$' _) ->
            Just <$> scanFixedLexeme
                demand "$" (EndEnv "math") (TokenEnds "math")
        Just (DecodedScalar '\\' _) -> do
            variable <- scanControlVariableToken demand
            maybe (scanMathControlSequence demand) (pure . Just) variable
        _ -> pure Nothing

scanMathControlSequence
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanMathControlSequence demand = do
    casesBegin <- startsWith "\\begin{cases}"
    if casesBegin
        then Just <$> scanFixedLexeme
            demand
            "\\begin{cases}"
            (BeginEnv "cases")
            (TokenBegins "cases")
        else do
            alignEnd <- startsWith "\\end{align*}"
            if alignEnd
                then Just <$> scanFixedLexeme
                    demand
                    "\\end{align*}"
                    (EndEnv "align*")
                    (TokenEnds "align*")
                else do
                    casesEnd <- startsWith "\\end{cases}"
                    if casesEnd
                        then Just <$> scanFixedLexeme
                            demand
                            "\\end{cases}"
                            (EndEnv "cases")
                            (TokenEnds "cases")
                        else do
                            opening <- startsOpeningDelimiter
                            if opening
                                then Just <$> scanOpeningDelimiter demand
                                else do
                                    closing <- startsClosingDelimiter
                                    if closing
                                        then Just <$> scanClosingDelimiter demand
                                        else scanMathNamedControl demand

scanMathNamedControl
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanMathNamedControl demand = do
    text <- matchingLiteral ["\\text{", "\\textbox{"]
    case text of
        Just literal ->
            Just <$> scanFixedLexeme
                demand literal (BeginEnv "text") (TokenOpensFrame "text" "}")
        Nothing -> do
            explanation <- startsWith "\\explanation{"
            if explanation
                then Just <$> scanFixedLexeme
                    demand
                    "\\explanation{"
                    (BeginEnv "text")
                    (TokenOpensFrame "text" "}")
                else do
                    mathEnd <- matchingLiteral ["\\)", "\\]"]
                    case mathEnd of
                        Just literal ->
                            Just <$> scanFixedLexeme
                                demand literal (EndEnv "math")
                                (TokenEnds "math")
                        Nothing -> Just <$> scanCommandToken demand

scanTextToken
    :: TokenDemand
    -> Int
    -> PrefixScanner (Maybe ScannedToken)
scanTextToken demand depth = do
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar value _)
            | isWordCharacter value ->
                Just <$> scanWordToken demand decoded
            | isFormalSymbol value ->
                Just <$> scanSymbolToken demand decoded
        Just (DecodedScalar '}' _)
            | depth == 1 ->
                Just <$> scanFixedLexeme
                    demand "}" (EndEnv "text") (TokenEnds "text")
            | otherwise -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar '$' _) ->
            Just <$> scanFixedLexeme
                demand "$" (BeginEnv "math") (TokenOpensFrame "math" "$")
        Just (DecodedScalar '(' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar '[' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar '{' _) -> Just <$> scanOpeningDelimiter demand
        Just (DecodedScalar ')' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar ']' _) -> Just <$> scanClosingDelimiter demand
        Just (DecodedScalar '\\' _) -> scanTextControlSequence demand
        _ -> pure Nothing

scanTextControlSequence
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanTextControlSequence demand = do
    beginMath <- matchingLiteral ["\\(", "\\["]
    case beginMath of
        Just literal ->
            Just <$> scanFixedLexeme
                demand
                literal
                (BeginEnv "math")
                (TokenOpensFrame "math" (mathCloserFor literal))
        Nothing -> do
            align <- startsWith "\\begin{align*}"
            if align
                then Just <$> scanFixedLexeme
                    demand
                    "\\begin{align*}"
                    (BeginEnv "align*")
                    (TokenOpensFrame "align*" "\\end{align*}")
                else do
                    opening <- startsOpeningDelimiter
                    if opening
                        then Just <$> scanOpeningDelimiter demand
                        else do
                            closing <- startsClosingDelimiter
                            if closing
                                then Just <$> scanClosingDelimiter demand
                                else do
                                    reference <- startsOrdinaryOrHyperReference
                                    if reference
                                        then Just <$> scanReferenceToken demand
                                        else do
                                            method <- startsProofMethodReference
                                            if method
                                                then Just <$>
                                                    scanProofMethodReferenceToken
                                                        demand
                                                else Just <$>
                                                    scanCommandToken demand

scanFixedLexeme
    :: TokenDemand
    -> ByteString
    -> Token
    -> TokenEffect
    -> PrefixScanner ScannedToken
scanFixedLexeme demand literal token effect = do
    location <- currentPrefixLocation
    consumeLiteral literal
    finishLexeme demand location effect (pure token)

finishLexeme
    :: TokenDemand
    -> Location
    -> TokenEffect
    -> PrefixScanner Token
    -> PrefixScanner ScannedToken
finishLexeme demand location effect makeToken = do
    retained <- case demand of
        RetainTokens -> Just <$> makeToken
        DiscardTokens -> pure Nothing
    whitespace <- scanFormalWhitespace
    pure
        (ScannedToken
            location
            effect
            (fmap (\token -> Located location token whitespace) retained))

finishDelimiterLexeme
    :: TokenDemand
    -> Location
    -> TokenEffect
    -> Token
    -> PrefixScanner ScannedToken
finishDelimiterLexeme demand location effect token = do
    -- The legacy delimiter alternatives have an inner and an outer `lexeme`.
    -- The inner one consumes all trivia, so the outer token records NoSpace.
    void scanFormalWhitespace
    pure
        (ScannedToken
            location
            effect
            (case demand of
                RetainTokens -> Just (Located location token NoSpace)
                DiscardTokens -> Nothing))

scanWordToken
    :: TokenDemand
    -> DecodedScalar
    -> PrefixScanner ScannedToken
scanWordToken demand initial = do
    location <- currentPrefixLocation
    start <- gets scannerOffset
    consumeRunFrom initial isWordCharacter
    end <- gets scannerOffset
    finishLexeme demand location TokenHasNoFrameEffect do
        Word . Text.toCaseFold <$> decodeSlice
            "decoding a word token" start end

scanSymbolToken
    :: TokenDemand
    -> DecodedScalar
    -> PrefixScanner ScannedToken
scanSymbolToken demand initial = do
    location <- currentPrefixLocation
    start <- gets scannerOffset
    consumeRunFrom initial isFormalSymbol
    end <- gets scannerOffset
    finishLexeme demand location TokenHasNoFrameEffect do
        Symbol <$> decodeSlice "decoding a symbol token" start end

scanIntegerToken
    :: TokenDemand
    -> DecodedScalar
    -> PrefixScanner ScannedToken
scanIntegerToken demand initial@(DecodedScalar firstDigit _) = do
    location <- currentPrefixLocation
    value <- case demand of
        RetainTokens -> do
            consumePeekedScalar initial
            Just <$> consumeDecimal (digitValue firstDigit)
        DiscardTokens ->
            consumeRunFrom initial isAsciiDigit *> pure Nothing
    finishLexeme demand location TokenHasNoFrameEffect
        (pure (Integer (fromMaybe 0 value)))
  where
    digitValue digit = fromIntegral (ord digit - ord '0')

    consumeDecimal accumulated = do
        scalar <- peekScalar
        case scalar of
            Just decoded@(DecodedScalar digit _)
                | isAsciiDigit digit -> do
                    consumePeekedScalar decoded
                    consumeDecimal
                        (accumulated * 10 + digitValue digit)
            _ -> pure accumulated

consumeRunFrom
    :: DecodedScalar
    -> (Char -> Bool)
    -> PrefixScanner ()
consumeRunFrom initial predicate =
    consumePeekedScalar initial *> consumeWhile predicate

scanLetterVariableToken
    :: TokenDemand
    -> DecodedScalar
    -> PrefixScanner ScannedToken
scanLetterVariableToken demand initial = do
    location <- currentPrefixLocation
    retainedBase <- consumeLetterVariableBase demand initial
    finishVariableToken demand location retainedBase

scanControlVariableToken
    :: TokenDemand
    -> PrefixScanner (Maybe ScannedToken)
scanControlVariableToken demand = do
    location <- currentPrefixLocation
    base <- scanControlVariableBase demand
    traverse (finishVariableToken demand location) base

finishVariableToken
    :: TokenDemand
    -> Location
    -> Maybe Text
    -> PrefixScanner ScannedToken
finishVariableToken demand location retainedBase = do
    retainedVariation <- scanVariableVariation demand
    finishLexeme demand location TokenHasNoFrameEffect
        (pure
            (Variable
                (fromMaybe "" retainedBase
                    <> fromMaybe "" retainedVariation)))

scanVariableBase
    :: TokenDemand
    -> PrefixScanner (Maybe (Maybe Text))
scanVariableBase demand = do
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar letter _)
            | isLetter letter ->
                Just <$> consumeLetterVariableBase demand decoded
        _ -> scanControlVariableBase demand

consumeLetterVariableBase
    :: TokenDemand
    -> DecodedScalar
    -> PrefixScanner (Maybe Text)
consumeLetterVariableBase demand scalar@(DecodedScalar letter _) = do
    consumePeekedScalar scalar
    pure
        (case demand of
            RetainTokens -> Just (Text.singleton letter)
            DiscardTokens -> Nothing)

scanControlVariableBase
    :: TokenDemand
    -> PrefixScanner (Maybe (Maybe Text))
scanControlVariableBase demand = do
    blackboard <- consumeIfLiteral "\\mathbb{"
    if blackboard
        then Just <$> scanBlackboardBaseAfterOpening demand
        else scanGreekBase demand

scanBlackboardBaseAfterOpening :: TokenDemand -> PrefixScanner (Maybe Text)
scanBlackboardBaseAfterOpening demand = do
    scalar <- peekScalar >>= maybe throwUnexpectedEnd pure
    let DecodedScalar character _ = scalar
    if character >= 'A' && character <= 'Z'
        then consumePeekedScalar scalar
        else throwUnexpected character
    consumeExpected '}'
    pure
        (case demand of
            RetainTokens -> Just ("bb" <> Text.singleton character)
            DiscardTokens -> Nothing)

scanGreekBase
    :: TokenDemand
    -> PrefixScanner (Maybe (Maybe Text))
scanGreekBase demand = do
    slash <- (== Just '\\') <$> peekChar
    if not slash
        then pure Nothing
        else do
            state <- get
            let start = scannerOffset state + 1
            end <- liftInvariant
                (decodedRunEnd
                    (scannerLocationPath state)
                    "recognizing a Greek variable"
                    (scannerBytes state)
                    start
                    isLetter)
            if end == start
                then pure Nothing
                else do
                    spelling <- decodeSlice
                        "decoding a Greek variable" start end
                    case canonicalVariableControlWord spelling of
                        Nothing -> pure Nothing
                        Just canonical -> do
                            consumeToOffset end
                            pure
                                (Just
                                    (case demand of
                                        RetainTokens -> Just canonical
                                        DiscardTokens -> Nothing))

scanVariableVariation :: TokenDemand -> PrefixScanner (Maybe Text)
scanVariableVariation demand = do
    subscript <- (== Just '_') <$> peekChar
    if subscript
        then scanVariableSubscript demand
        else do
            tick <- (== Just '\'') <$> peekChar
            if tick
                then scanVariableTicks demand
                else pure
                    (case demand of
                        RetainTokens -> Just ""
                        DiscardTokens -> Nothing)

scanVariableSubscript :: TokenDemand -> PrefixScanner (Maybe Text)
scanVariableSubscript demand = do
    consumeExpected '_'
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar value _)
            | isAlphaNum value -> do
                consumePeekedScalar decoded
                pure
                    (case demand of
                        RetainTokens -> Just (Text.singleton value)
                        DiscardTokens -> Nothing)
        Just (DecodedScalar '{' _) -> scanBracedVariableSuffix demand
        _ -> do
            text <- consumeIfLiteral "\\text"
            if text
                then scanBracedVariableSuffix demand
                else case scalar of
                    Nothing -> throwUnexpectedEnd
                    Just (DecodedScalar value _) -> throwUnexpected value

scanBracedVariableSuffix :: TokenDemand -> PrefixScanner (Maybe Text)
scanBracedVariableSuffix demand = do
    consumeExpected '{'
    case demand of
        RetainTokens -> Just . Text.pack . reverse <$> goRetained [] False
        DiscardTokens -> goDiscarded False *> pure Nothing
  where
    goRetained reversed seen = do
        scalar <- peekScalar
        case scalar of
            Just decoded@(DecodedScalar '}' _)
                | seen -> consumePeekedScalar decoded *> pure reversed
                | otherwise -> throwUnexpected '}'
            Just decoded@(DecodedScalar value _)
                | isAlphaNum value || value == '\'' -> do
                    consumePeekedScalar decoded
                    goRetained
                        ((if value == '\'' then '_' else value) : reversed)
                        True
            Nothing -> throwUnexpectedEnd
            Just (DecodedScalar value _) -> throwUnexpected value

    goDiscarded seen = do
        scalar <- peekScalar
        case scalar of
            Just decoded@(DecodedScalar '}' _)
                | seen -> consumePeekedScalar decoded
                | otherwise -> throwUnexpected '}'
            Just decoded@(DecodedScalar value _)
                | isAlphaNum value || value == '\'' ->
                    consumePeekedScalar decoded *> goDiscarded True
            Nothing -> throwUnexpectedEnd
            Just (DecodedScalar value _) -> throwUnexpected value

scanVariableTicks :: TokenDemand -> PrefixScanner (Maybe Text)
scanVariableTicks demand = do
    tickCount <- go 0
    pure
        (case demand of
            RetainTokens -> Just (Text.replicate tickCount "_")
            DiscardTokens -> Nothing)
  where
    go tickCount = do
        tick <- consumeIfChar '\''
        if tick
            then go (tickCount + 1)
            else pure tickCount

scanLabelToken :: TokenDemand -> PrefixScanner ScannedToken
scanLabelToken demand = do
    location <- currentPrefixLocation
    consumeLiteral "\\label{"
    marker <- scanMarkerSpan
    consumeExpected '}'
    finishLexeme demand location TokenHasNoFrameEffect do
        Label <$> decodeSpan "decoding a label marker" marker

scanReferenceToken :: TokenDemand -> PrefixScanner ScannedToken
scanReferenceToken demand = do
    location <- currentPrefixLocation
    ordinary <- matchingLiteral ["\\ref{", "\\cref{"]
    spans <- case ordinary of
        Just literal -> do
            consumeLiteral literal
            markers <- scanFormattedReferenceMarkers
            consumeExpected '}'
            pure markers
        Nothing -> do
            consumeLiteral "\\hyperref["
            markers <- scanFormattedReferenceMarkers
            consumeLiteral "]{"
            firstCharacter <- peekChar
            case firstCharacter of
                Nothing -> throwUnexpectedEnd
                Just '}' -> throwUnexpected '}'
                Just _ -> consumeUntilClosingBrace
            consumeExpected '}'
            pure markers
    finishLexeme demand location TokenHasNoFrameEffect do
        Ref <$> traverse (decodeSpan "decoding a reference marker") spans
  where
    consumeUntilClosingBrace = do
        scalar <- peekScalar
        case scalar of
            Nothing -> throwUnexpectedEnd
            Just (DecodedScalar '}' _) -> pure ()
            Just value ->
                consumePeekedScalar value *> consumeUntilClosingBrace

scanProofMethodReferenceToken
    :: TokenDemand
    -> PrefixScanner ScannedToken
scanProofMethodReferenceToken demand = do
    location <- currentPrefixLocation
    method <- do
        auto <- consumeIfLiteral "\\auto{"
        if auto
            then pure "auto"
            else consumeLiteral "\\obv{" *> pure "obv"
    spans <- scanFormattedReferenceMarkers
    consumeExpected '}'
    finishLexeme demand location TokenHasNoFrameEffect do
        CommandReference method <$>
            traverse (decodeSpan "decoding a proof reference marker") spans

scanFormattedReferenceMarkers
    :: PrefixScanner (NonEmpty (Int, Int))
scanFormattedReferenceMarkers = do
    void scanFormalWhitespace
    firstMarker <- scanMarkerSpan
    remaining <- go []
    pure (firstMarker :| reverse remaining)
  where
    go reversed = do
        void scanFormalWhitespace
        comma <- consumeIfChar ','
        if comma
            then do
                void scanFormalWhitespace
                marker <- scanMarkerSpan
                go (marker : reversed)
            else pure reversed

scanMarkerSpan :: PrefixScanner (Int, Int)
scanMarkerSpan = do
    start <- gets scannerOffset
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar value _)
            | isPortableIdentifierInitial value -> do
                consumePeekedScalar decoded
                consumeWhile isPortableIdentifierSubsequent
                end <- gets scannerOffset
                pure (start, end)
        Nothing -> throwUnexpectedEnd
        Just (DecodedScalar value _) -> throwUnexpected value

scanEnvironmentEndToken
    :: TokenDemand
    -> PrefixScanner ScannedToken
scanEnvironmentEndToken demand = do
    location <- currentPrefixLocation
    consumeLiteral "\\end{"
    start <- gets scannerOffset
    firstScalar <- peekScalar
    case firstScalar of
        Just decoded@(DecodedScalar value _)
            | isLetter value || value == '*' -> consumePeekedScalar decoded
            | otherwise -> throwUnexpected value
        Nothing -> throwUnexpectedEnd
    consumeWhile (\value -> isLetter value || value == '*' || value == '-')
    end <- gets scannerOffset
    consumeExpected '}'
    environment <- decodeSlice "decoding an environment name" start end
    finishLexeme demand location (TokenEnds environment)
        (pure (EndEnv environment))

scanCommandToken :: TokenDemand -> PrefixScanner ScannedToken
scanCommandToken demand = do
    location <- currentPrefixLocation
    consumeExpected '\\'
    start <- gets scannerOffset
    firstScalar <- peekScalar
    case firstScalar of
        Just decoded@(DecodedScalar value _)
            | isLetter value -> consumePeekedScalar decoded
            | otherwise -> throwUnexpected value
        Nothing -> throwUnexpectedEnd
    consumeWhile isLetter
    end <- gets scannerOffset
    bytes <- gets scannerBytes
    if end - start == 4 && literalAt bytes start "item"
        then do
            whitespace <- scanFormalWhitespace
            named <- startsWith "["
            if named
                then do
                    consumeExpected '['
                    nameStart <- gets scannerOffset
                    consumeWhile (/= ']')
                    nameEnd <- gets scannerOffset
                    consumeExpected ']'
                    finishLexeme demand location TokenHasNoFrameEffect
                        (NamedItem <$> decodeSlice "decoding an item name" nameStart nameEnd)
                else pure (ScannedToken location TokenHasNoFrameEffect
                    (case demand of
                        RetainTokens -> Just (Located location (Command "item") whitespace)
                        DiscardTokens -> Nothing))
        else if end - start == 6 && literalAt bytes start "caseOf"
            then do
                whitespace <- scanFormalWhitespace
                offset <- gets scannerOffset
                let heading = caseHeading (ByteString.drop offset bytes)
                pure (ScannedToken location TokenHasNoFrameEffect
                    (case demand of
                        RetainTokens -> Just (Located location (maybe (Command "caseOf") CaseHeading heading) whitespace)
                        DiscardTokens -> Nothing))
            else finishLexeme demand location TokenHasNoFrameEffect do
                Command <$> decodeSlice "decoding a command" start end

-- Inspect only a plain heading, without consuming its ordinary argument.
-- Mathematical or grammatical statements remain available to logical cases.
caseHeading :: ByteString -> Maybe Text
caseHeading input = do
    (123, rest) <- ByteString.uncons input
    let allowed byte = (65 <= byte && byte <= 90) || (97 <= byte && byte <= 122)
            || (48 <= byte && byte <= 57) || byte == 95 || byte `elem` [32,9,10,13]
        (name, suffix) = ByteString.span allowed rest
    afterDot <- ByteString.stripPrefix "." suffix
    guard (not (ByteString.null name) && ByteString.isPrefixOf "}" (ByteString.dropWhile (`elem` [32,9,10,13]) afterDot))
    pure (Text.decodeUtf8 name)

scanOpeningDelimiter :: TokenDemand -> PrefixScanner ScannedToken
scanOpeningDelimiter = scanDelimiter True

scanClosingDelimiter :: TokenDemand -> PrefixScanner ScannedToken
scanClosingDelimiter = scanDelimiter False

scanDelimiter
    :: Bool
    -> TokenDemand
    -> PrefixScanner ScannedToken
scanDelimiter opening demand = do
    location <- currentPrefixLocation
    let side = if opening then "\\left" else "\\right"
    void (consumeIfLiteral side)
    choice <- delimiterChoice opening
    case choice of
        Nothing -> do
            character <- peekChar
            maybe throwUnexpectedEnd throwUnexpected character
        Just (literal, token, effect) -> do
            consumeLiteral literal
            finishDelimiterLexeme demand location effect token

delimiterChoice
    :: Bool
    -> PrefixScanner (Maybe (ByteString, Token, TokenEffect))
delimiterChoice opening = do
    character <- peekChar
    let choice =
            if opening
                then case character of
                    Just '{' -> Just ("{", InvisibleBraceL,
                        TokenInvisibleBraceLeft)
                    Just '(' -> Just ("(", ParenL, TokenHasNoFrameEffect)
                    Just '[' -> Just ("[", BracketL, TokenHasNoFrameEffect)
                    _ -> Nothing
                else case character of
                    Just '}' -> Just ("}", InvisibleBraceR,
                        TokenInvisibleBraceRight)
                    Just ')' -> Just (")", ParenR, TokenHasNoFrameEffect)
                    Just ']' -> Just ("]", BracketR, TokenHasNoFrameEffect)
                    _ -> Nothing
    case choice of
        Just value -> pure (Just value)
        Nothing -> do
            visible <- startsWith (if opening then "\\{" else "\\}")
            pure
                (if visible
                    then Just
                        ( if opening then "\\{" else "\\}"
                        , if opening then VisibleBraceL else VisibleBraceR
                        , TokenHasNoFrameEffect
                        )
                    else Nothing)

startsOpeningDelimiter :: PrefixScanner Bool
startsOpeningDelimiter =
    isJust <$> matchingLiteral
        ["{", "(", "[", "\\{", "\\left(", "\\left[", "\\left\\{"]

startsClosingDelimiter :: PrefixScanner Bool
startsClosingDelimiter =
    isJust <$> matchingLiteral
        ["}", ")", "]", "\\}", "\\right)", "\\right]", "\\right\\}"]

startsOrdinaryOrHyperReference :: PrefixScanner Bool
startsOrdinaryOrHyperReference =
    isJust <$> matchingLiteral ["\\ref{", "\\cref{", "\\hyperref["]

startsProofMethodReference :: PrefixScanner Bool
startsProofMethodReference =
    isJust <$> matchingLiteral ["\\auto{", "\\obv{"]

startsGenericEnvironmentEnd :: PrefixScanner Bool
startsGenericEnvironmentEnd = do
    cases <- startsWith "\\end{cases}"
    if cases then pure False else startsWith "\\end{"

matchingSubEnvironment
    :: PrefixScanner (Maybe (ByteString, Token, TokenEffect))
matchingSubEnvironment =
    go subEnvironmentTokens
  where
    go = \case
        [] -> pure Nothing
        entry@(literal, _token, _effect) : rest -> do
            matched <- startsWith literal
            if matched then pure (Just entry) else go rest

decodeSpan :: Text -> (Int, Int) -> PrefixScanner Text
decodeSpan operation (start, end) = decodeSlice operation start end

decodedRunEnd
    :: FilePath
    -> Text
    -> ByteString
    -> Int
    -> (Char -> Bool)
    -> Either SourceScanInvariantError Int
decodedRunEnd file operation bytes = go
  where
    go offset predicate = do
        decoded <- decodeScalarAt file operation bytes offset
        case decoded of
            Just (character, width)
                | predicate character -> go (offset + width) predicate
            _ -> pure offset

isWordCharacter :: Char -> Bool
isWordCharacter character =
    isLetter character || character == '\'' || character == '-'

isAsciiDigit :: Char -> Bool
isAsciiDigit character = character >= '0' && character <= '9'

isFormalSymbol :: Char -> Bool
isFormalSymbol character = character `elem` formalSymbols


scanImport :: Int -> PrefixScanner (Located FilePath)
scanImport after = do
    location <- currentPrefixLocation
    consumeToOffset after
    start <- gets scannerOffset
    end <- scanImportPath
    path <- decodeSlice "decoding an import path" start end
    pure (Located location (Text.unpack path) NoSpace)

scanImportPath :: PrefixScanner Int
scanImportPath = do
    scalar <- peekScalar
    case scalar of
        Nothing -> throwUnexpectedEnd
        Just (DecodedScalar '}' _) -> throwUnexpected '}'
        Just (DecodedScalar '\n' _) -> throwUnexpected '\n'
        Just (DecodedScalar '\r' _) -> throwUnexpected '\r'
        Just (DecodedScalar '\0' _) -> throwUnexpected '\0'
        Just value -> consumePeekedScalar value *> scanImportPathNonempty
  where
    scanImportPathNonempty = do
        scalar <- peekScalar
        case scalar of
            Nothing -> throwUnexpectedEnd
            Just value@(DecodedScalar '}' _) -> do
                end <- gets scannerOffset
                consumePeekedScalar value
                pure end
            Just (DecodedScalar '\n' _) -> throwUnexpected '\n'
            Just (DecodedScalar '\r' _) -> throwUnexpected '\r'
            Just (DecodedScalar '\0' _) -> throwUnexpected '\0'
            Just value ->
                consumePeekedScalar value *> scanImportPathNonempty

scanImportTrivia :: PrefixScanner (Maybe PendingProseStart)
scanImportTrivia = go Nothing
  where
    go pending = do
        scalar <- peekScalar
        case scalar of
            Just (DecodedScalar '%' _)
                -> skipComment *> go Nothing
            Just decoded@(DecodedScalar value _)
                | isSpace value -> do
                    start <- case pending of
                        Just retained -> pure retained
                        Nothing -> currentPendingProseStart
                    consumePeekedScalar decoded
                    go (Just start)
            _ -> pure pending


classifyDocumentLead :: ScannerState -> DocumentLead
classifyDocumentLead state =
    case byteAt bytes offset of
        Nothing -> DocumentEnd
        Just byte
            | byte == percent -> DocumentComment
            | byte == backslash -> classifyBackslash
            | otherwise -> DocumentProse
  where
    bytes = scannerBytes state
    offset = scannerOffset state

    classifyBackslash =
        case matchingTopLevelBoundary state of
            Just (MatchedTopLevelBoundary TopLevelBegin after environment) ->
                DocumentTopLevel
                    (MatchedTopLevelEnvironment after environment)
            _ ->
                case matchingImportStart state of
                    Just after -> DocumentImport after
                    Nothing ->
                        case matchingHeadingStart state of
                            Just heading -> DocumentHeading heading
                            Nothing
                                | atRawHeadingStart state ->
                                    DocumentRawHeading
                                | otherwise -> DocumentProse

matchingTopLevelBoundary
    :: ScannerState
    -> Maybe MatchedTopLevelBoundary
matchingTopLevelBoundary state =
    case matchingPrefix of
        Nothing -> Nothing
        Just (boundary, prefixLength) ->
            go boundary (offset + prefixLength) topLevelEnvironmentNames
  where
    bytes = scannerBytes state
    offset = scannerOffset state

    matchingPrefix
        | literalAt bytes offset topLevelEnvironmentStart =
            Just
                ( TopLevelBegin
                , ByteString.length topLevelEnvironmentStart
                )
        | literalAt bytes offset topLevelEnvironmentEnd =
            Just
                ( TopLevelEnd
                , ByteString.length topLevelEnvironmentEnd
                )
        | otherwise = Nothing

    go boundary nameStart = \case
        [] -> Nothing
        (nameBytes, name) : remaining ->
            let nameEnd = nameStart + ByteString.length nameBytes
            in if literalAt bytes nameStart nameBytes
                    && byteAt bytes nameEnd == Just closeBrace
                then Just
                    (MatchedTopLevelBoundary boundary (nameEnd + 1) name)
                else go boundary nameStart remaining

matchingImportStart :: ScannerState -> Maybe Int
matchingImportStart state
    | literalAt bytes offset importStart =
        Just (offset + ByteString.length importStart)
    | otherwise = Nothing
  where
    bytes = scannerBytes state
    offset = scannerOffset state

scanHeadingAtCursor :: MatchedHeadingStart -> PrefixScanner HeadingScan
scanHeadingAtCursor heading = do
    initial <- get
    case runState (runExceptT (scanHeading heading)) initial of
        (Right pending, final) -> do
            put final
            pure (HeadingScanned pending)
        (Left
            (ScanInputAbort
                SourceScanUnexpectedEndOfInput{}), _failed) ->
                    pure HeadingNotRecognized
        (Left failure, _failed) -> throwE failure

matchingHeadingStart :: ScannerState -> Maybe MatchedHeadingStart
matchingHeadingStart state = go headingStarts
  where
    go = \case
        [] -> Nothing
        (literal, level) : remaining
            | literalAt bytes offset literal
                && byteAt bytes afterLiteral == Just openBrace ->
                    Just (MatchedHeadingStart level (afterLiteral + 1))
            | otherwise -> go remaining
          where
            afterLiteral = offset + ByteString.length literal

    bytes = scannerBytes state
    offset = scannerOffset state

atRawHeadingStart :: ScannerState -> Bool
atRawHeadingStart state =
    any
        (\(literal, _level) -> literalAt bytes offset literal)
        headingStarts
  where
    bytes = scannerBytes state
    offset = scannerOffset state

matchHeadingLabel
    :: PrefixScanner (Maybe (Int, Int, Int))
matchHeadingLabel = do
    state <- get
    let bytes = scannerBytes state
        offset = scannerOffset state
        file = scannerLocationPath state
    if not (literalAt bytes offset headingLabelStart)
        then pure Nothing
        else do
            let markerStart = offset + ByteString.length headingLabelStart
            matched <- liftInvariant
                (matchMarker file bytes markerStart)
            pure case matched of
                Just (markerEnd, after)
                    | byteAt bytes markerEnd == Just closeBrace ->
                        Just (markerStart, markerEnd, after)
                _ -> Nothing
  where
    matchMarker file bytes start = do
        initial <- decodeScalarAt
            file "recognizing a heading label" bytes start
        case initial of
            Just (character, width)
                | isPortableIdentifierInitial character ->
                    matchSubsequent file bytes (start + width)
            _ -> Right Nothing

    matchSubsequent file bytes offset = do
        next <- decodeScalarAt
            file "recognizing a heading label" bytes offset
        case next of
            Just (character, width)
                | isPortableIdentifierSubsequent character ->
                    matchSubsequent file bytes (offset + width)
            _ ->
                Right
                    (if byteAt bytes offset == Just closeBrace
                        then Just (offset, offset + 1)
                        else Nothing)


currentPendingProseStart :: PrefixScanner PendingProseStart
currentPendingProseStart = do
    state <- get
    pure
        (PendingProseStart
            (ByteOffset (scannerOffset state))
            (scannerLine state)
            (scannerColumn state))

pendingOffset :: PendingProseStart -> Int
pendingOffset (PendingProseStart (ByteOffset offset) _line _column) =
    offset

pendingByteOffset :: PendingProseStart -> ByteOffset
pendingByteOffset (PendingProseStart offset _line _column) =
    offset

locationAtPending :: PendingProseStart -> PrefixScanner Location
locationAtPending
        (PendingProseStart _offset line column) =
    prefixLocation line column

currentPrefixLocation :: PrefixScanner Location
currentPrefixLocation = do
    line <- gets scannerLine
    column <- gets scannerColumn
    prefixLocation line column

prefixLocation :: Int -> Int -> PrefixScanner Location
prefixLocation line column = do
    state <- get
    let file = scannerLocationPath state
        descriptor = scannerSourceDescriptor state
    case mkLocationChecked descriptor line column of
        Left _failure ->
            throwInput
                (SourceScanLocationOutOfRange file line column)
        Right location ->
            pure location

throwUnexpected :: Char -> PrefixScanner a
throwUnexpected character = do
    location <- currentPrefixLocation
    throwInput
        (SourceScanUnexpectedInput
            location
            (Text.singleton character))

throwUnexpectedEnd :: PrefixScanner a
throwUnexpectedEnd = do
    location <- currentPrefixLocation
    throwInput
        (SourceScanUnexpectedEndOfInput location)

throwExplicit :: Text -> PrefixScanner a
throwExplicit message = do
    location <- currentPrefixLocation
    throwInput (SourceScanExplicitFailure location message)

throwInput :: SourceScanRejection -> PrefixScanner a
throwInput = throwE . ScanInputAbort

throwInvariant :: SourceScanInvariantError -> PrefixScanner a
throwInvariant = throwE . ScanInvariantAbort

liftInvariant
    :: Either SourceScanInvariantError value
    -> PrefixScanner value
liftInvariant = either throwInvariant pure


atEnd :: PrefixScanner Bool
atEnd = do
    state <- get
    pure (scannerOffset state == ByteString.length (scannerBytes state))

peekScalar :: PrefixScanner (Maybe DecodedScalar)
peekScalar = do
    state <- get
    fmap (uncurry DecodedScalar)
        <$> liftInvariant
            (decodeScalarAt
                (scannerLocationPath state)
                "reading source input"
                (scannerBytes state)
                (scannerOffset state))

peekChar :: PrefixScanner (Maybe Char)
peekChar =
    fmap (\(DecodedScalar character _width) -> character) <$> peekScalar

requireChar :: PrefixScanner Char
requireChar =
    peekChar >>= maybe throwUnexpectedEnd pure

consumeExpected :: Char -> PrefixScanner ()
consumeExpected expected = do
    actual <- peekScalar
    case actual of
        Just scalar@(DecodedScalar character _)
            | character == expected -> consumePeekedScalar scalar
            | otherwise -> throwUnexpected character
        Nothing -> throwUnexpectedEnd

consumePeekedScalar :: DecodedScalar -> PrefixScanner ()
consumePeekedScalar scalar = do
    state <- get
    next <- liftInvariant (advanceScannerState scalar state)
    put next

consumeNextScalar :: PrefixScanner Char
consumeNextScalar = do
    scalar@(DecodedScalar character _) <-
        peekScalar >>= maybe throwUnexpectedEnd pure
    consumePeekedScalar scalar
    pure character

consumeIfChar :: Char -> PrefixScanner Bool
consumeIfChar expected = do
    scalar <- peekScalar
    case scalar of
        Just decoded@(DecodedScalar actual _)
            | actual == expected ->
                consumePeekedScalar decoded *> pure True
        _ -> pure False

consumeLiteral :: ByteString -> PrefixScanner ()
consumeLiteral literal = do
    state <- get
    let offset = scannerOffset state
        matched = literalAt (scannerBytes state) offset literal
    unless matched do
        character <- peekChar
        maybe throwUnexpectedEnd throwUnexpected character
    consumeToOffset (offset + ByteString.length literal)

consumeToOffset :: Int -> PrefixScanner ()
consumeToOffset target = do
    initial <- get
    final <- liftInvariant (advanceToOffset target initial)
    put final
  where
    advanceToOffset requested initial
        | requested < initialOffset =
            Left (rangeInvariant requested initialOffset initial)
        | requested > inputLength =
            Left (rangeInvariant initialOffset requested initial)
        | otherwise = go initial
      where
        initialOffset = scannerOffset initial
        inputLength = ByteString.length (scannerBytes initial)

        go !current
            | offset == requested = Right current
            | otherwise = do
                scalar <-
                    if leadingByte < 0x80
                        then Right
                            (DecodedScalar
                                (chr (fromIntegral leadingByte))
                                1)
                        else do
                            decoded <- decodeScalarAt
                                (scannerLocationPath current)
                                "advancing to a known source offset"
                                bytes
                                offset
                            maybe
                                (Left (rangeInvariant offset requested current))
                                (Right . uncurry DecodedScalar)
                                decoded
                let DecodedScalar _ width = scalar
                    nextOffset = offset + width
                if nextOffset > requested
                    then Left (rangeInvariant offset nextOffset current)
                    else do
                        next <- advanceScannerState scalar current
                        go $! next
          where
            bytes = scannerBytes current
            offset = scannerOffset current
            leadingByte = ByteString.index bytes offset

    rangeInvariant start end state =
        SourceScanValidatedUtf8Invariant
            (scannerLocationPath state)
            "advancing to a known source offset"
            start
            end

consumeWhile :: (Char -> Bool) -> PrefixScanner ()
consumeWhile predicate = do
    next <- peekScalar
    case next of
        Just scalar@(DecodedScalar character _)
            | predicate character ->
                consumePeekedScalar scalar *> consumeWhile predicate
        _ -> pure ()

startsWith :: ByteString -> PrefixScanner Bool
startsWith literal = do
    state <- get
    pure (literalAt (scannerBytes state) (scannerOffset state) literal)

consumeIfLiteral :: ByteString -> PrefixScanner Bool
consumeIfLiteral literal = do
    state <- get
    let offset = scannerOffset state
    if literalAt (scannerBytes state) offset literal
        then do
            consumeToOffset (offset + ByteString.length literal)
            pure True
        else pure False


advanceScannerState
    :: DecodedScalar
    -> ScannerState
    -> Either SourceScanInvariantError ScannerState
advanceScannerState (DecodedScalar character width) state = do
    nextOffset <- checkedAdd
        "advancing the source byte cursor"
        state
        offset
        width
    if character == '\n'
        then do
            nextLine <- checkedIncrement
                "advancing a source line"
                state
                (scannerLine state)
            let reversed =
                    maybe id (:)
                        (finishObservedLine bytes offset observation)
                        (scannerPragmaCandidatesReversed state)
            pure
                state
                    { scannerOffset = nextOffset
                    , scannerLine = nextLine
                    , scannerColumn = 1
                    , scannerLineObservation =
                        ObservingLineIndent
                            (ByteOffset nextOffset)
                            nextLine
                    , scannerPragmaCandidatesReversed = reversed
                    }
        else do
            nextColumn <-
                if character == '\t'
                    then do
                        let column = scannerColumn state
                            delta = 8 - ((column - 1) `mod` 8)
                        checkedAdd
                            "advancing a source tab"
                            state
                            column
                            delta
                    else checkedIncrement
                        "advancing a source column"
                        state
                        (scannerColumn state)
            pure
                state
                    { scannerOffset = nextOffset
                    , scannerColumn = nextColumn
                    , scannerLineObservation =
                        observeCharacter
                            bytes
                            offset
                            character
                            observation
                    }
  where
    bytes = scannerBytes state
    offset = scannerOffset state
    observation = scannerLineObservation state

checkedIncrement
    :: Text
    -> ScannerState
    -> Int
    -> Either SourceScanInvariantError Int
checkedIncrement operation state value =
    checkedAdd operation state value 1

checkedAdd
    :: Text
    -> ScannerState
    -> Int
    -> Int
    -> Either SourceScanInvariantError Int
checkedAdd operation state value amount
    | value > maxBound - amount =
        Left
            (SourceScanPositionOverflow
                (scannerLocationPath state)
                operation
                (scannerOffset state))
    | otherwise = Right (value + amount)

observeCharacter
    :: ByteString
    -> Int
    -> Char
    -> LineObservation
    -> LineObservation
observeCharacter bytes offset character = \case
    observing@(ObservingLineIndent lineStart line)
        | character == ' ' || character == '\t' -> observing
        | character == '%'
            && byteAt bytes (offset + 1) == Just exclamation ->
                ObservingPragmaCandidate lineStart line
        | otherwise -> IgnoringPhysicalLine
    candidate@ObservingPragmaCandidate{} -> candidate
    IgnoringPhysicalLine -> IgnoringPhysicalLine

finishObservedLine
    :: ByteString
    -> Int
    -> LineObservation
    -> Maybe PragmaCandidate
finishObservedLine bytes lineFeedOffset = \case
    ObservingPragmaCandidate start line ->
        let hasCarriageReturn =
                lineFeedOffset > unByteOffset start
                    && byteAt bytes (lineFeedOffset - 1)
                        == Just carriageReturn
            end =
                if hasCarriageReturn
                    then lineFeedOffset - 1
                    else lineFeedOffset
            ending =
                if hasCarriageReturn
                    then SyntaxPragmaCrLf
                    else SyntaxPragmaLineFeed
        in Just
            (PragmaCandidate
                line
                ending
                (ByteSpan start (ByteOffset end)))
    _ -> Nothing

finalizeEndOfFileObservation :: PrefixScanner ()
finalizeEndOfFileObservation = do
    state <- get
    unless (scannerEndedAtEof state) do
        let end = ByteOffset (scannerOffset state)
            reversed =
                case scannerLineObservation state of
                    ObservingPragmaCandidate start line ->
                        PragmaCandidate
                            line
                            SyntaxPragmaEndOfFile
                            (ByteSpan start end)
                            : scannerPragmaCandidatesReversed state
                    _ -> scannerPragmaCandidatesReversed state
        modify' \current ->
            current
                { scannerPragmaCandidatesReversed = reversed
                , scannerEndedAtEof = True
                }


decodeSlice
    :: Text
    -> Int
    -> Int
    -> PrefixScanner Text
decodeSlice operation start end = do
    state <- get
    let slice = ByteString.take (end - start)
            (ByteString.drop start (scannerBytes state))
    case Text.decodeUtf8' slice of
        Left _failure ->
            throwInvariant
                (SourceScanValidatedUtf8Invariant
                    (scannerLocationPath state)
                    operation
                    start
                    end)
        Right decoded -> pure decoded

decodeOwnerSpan
    :: ScanOwner
    -> Text
    -> ByteSpan
    -> Either SourceScanInvariantError Text
decodeOwnerSpan owner operation (ByteSpan (ByteOffset start) (ByteOffset end))
    | start < 0 || end < start || end > ByteString.length bytes =
        Left invariant
    | otherwise =
        case Text.decodeUtf8'
                (ByteString.take (end - start) (ByteString.drop start bytes)) of
            Left _failure -> Left invariant
            Right decoded -> Right decoded
  where
    bytes = scanOwnerBytes owner
    invariant =
        SourceScanValidatedUtf8Invariant
            (scanOwnerLocationPath owner)
            operation
            start
            end

decodeScalarAt
    :: FilePath
    -> Text
    -> ByteString
    -> Int
    -> Either SourceScanInvariantError (Maybe (Char, Int))
decodeScalarAt file operation bytes offset
    | offset == ByteString.length bytes = Right Nothing
    | offset < 0 || offset > ByteString.length bytes =
        Left (invariant offset offset)
    | otherwise = do
        let firstByte = ByteString.index bytes offset
        if firstByte < 0x80
            then Right (Just (chr (fromIntegral firstByte), 1))
            else do
                let width = utf8ScalarWidth firstByte
                    remaining = ByteString.length bytes - offset
                if width == 0 || width > remaining
                    then Left (invariant offset (ByteString.length bytes))
                    else
                        let end = offset + width
                        in
                        case Text.decodeUtf8'
                                (ByteString.take width
                                    (ByteString.drop offset bytes)) of
                            Left _failure -> Left (invariant offset end)
                            Right decoded ->
                                case Text.uncons decoded of
                                    Just (character, remainder)
                                        | Text.null remainder ->
                                            Right (Just (character, width))
                                    _ -> Left (invariant offset end)
  where
    invariant start end =
        SourceScanValidatedUtf8Invariant
            file
            operation
            start
            end
{-# INLINE decodeScalarAt #-}

utf8ScalarWidth :: Word8 -> Int
utf8ScalarWidth byte
    | byte < 0x80 = 1
    | byte < 0xe0 = 2
    | byte < 0xf0 = 3
    | byte < 0xf8 = 4
    | otherwise = 0

literalAt :: ByteString -> Int -> ByteString -> Bool
literalAt source offset literal =
    offset >= 0
        && ByteString.length literal
            <= ByteString.length source - offset
        && ByteString.take (ByteString.length literal)
            (ByteString.drop offset source)
            == literal

byteAt :: ByteString -> Int -> Maybe Word8
byteAt bytes offset
    | offset < 0 || offset >= ByteString.length bytes = Nothing
    | otherwise = Just (ByteString.index bytes offset)

scannerBytes :: ScannerState -> ByteString
scannerBytes = scanOwnerBytes . scannerSource

scannerLocationPath :: ScannerState -> FilePath
scannerLocationPath = scanOwnerLocationPath . scannerSource

scannerSourceDescriptor :: ScannerState -> SourceDescriptor
scannerSourceDescriptor = scanOwnerSourceDescriptor . scannerSource

scanOwnerBytes :: ScanOwner -> ByteString
scanOwnerBytes = \case
    PhysicalScanOwner source ->
        loadedBytes (identifiedSourceLoaded source)
    EphemeralScanOwner _descriptor _file bytes ->
        bytes

scanOwnerLocationPath :: ScanOwner -> FilePath
scanOwnerLocationPath = \case
    PhysicalScanOwner source ->
        resolvedSourceLocationPath
            (loadedSource (identifiedSourceLoaded source))
    EphemeralScanOwner _descriptor file _bytes ->
        file

scanOwnerSourceDescriptor :: ScanOwner -> SourceDescriptor
scanOwnerSourceDescriptor = \case
    PhysicalScanOwner source ->
        identifiedSourceDescriptor source
    EphemeralScanOwner descriptor _file _bytes ->
        descriptor

cursorIdentifiedSource :: SourceScanCursor -> IdentifiedLoadedSource
cursorIdentifiedSource
        (SourceScanCursor source _offset _line _column _observation
            _candidates _ended _pending) =
    case source of
        PhysicalScanOwner identified -> identified
        EphemeralScanOwner{} ->
            impossible
                "an ephemeral scanner cursor escaped as a source prefix"

unByteOffset :: ByteOffset -> Int
unByteOffset (ByteOffset offset) = offset

isHeadingGap :: Char -> Bool
isHeadingGap character =
    character == ' '
        || character == '\t'
        || character == '\r'
        || character == '\n'


importStart, sectionStart, subsectionStart, subsubsectionStart :: ByteString
importStart = "\\import{"
sectionStart = "\\section"
subsectionStart = "\\subsection"
subsubsectionStart = "\\subsubsection"

headingStarts :: [(ByteString, DocumentHeadingLevel)]
headingStarts =
    [ (subsubsectionStart, DocumentSubsubsection)
    , (subsectionStart, DocumentSubsection)
    , (sectionStart, DocumentSection)
    ]

headingLabelStart :: ByteString
headingLabelStart = "\\label{"

isFormalSpaceEscapeByte :: Word8 -> Bool
isFormalSpaceEscapeByte = \case
    0x20 -> True
    0x21 -> True
    0x2c -> True
    0x3a -> True
    0x3b -> True
    0x5c -> True
    _ -> False

formalSymbols :: [Char]
formalSymbols = ".,:;!?@=≠+-/|^_><≤≥*&≈⊂⊃⊆⊇∈“”‘’"

subEnvironmentTokens :: [(ByteString, Token, TokenEffect)]
subEnvironmentTokens =
    [ ("\\begin{enumerate}", BeginEnv "enumerate", TokenBegins "enumerate")
    , ("\\end{enumerate}", EndEnv "enumerate", TokenEnds "enumerate")
    , ("\\begin{subproof}", BeginEnv "subproof", TokenBegins "subproof")
    , ("\\end{subproof}", EndEnv "subproof", TokenEnds "subproof")
    , ("\\begin{byCase}", BeginEnv "byCase", TokenBegins "byCase")
    , ("\\end{byCase}", EndEnv "byCase", TokenEnds "byCase")
    ]

topLevelEnvironmentStart, topLevelEnvironmentEnd :: ByteString
topLevelEnvironmentStart = "\\begin{"
topLevelEnvironmentEnd = "\\end{"

topLevelEnvironmentNames :: [(ByteString, Text)]
topLevelEnvironmentNames =
    fmap (\name -> (Text.encodeUtf8 name, name))
        [ "definition"
        , "theorem"
        , "lemma"
        , "axiom"
        , "proof"
        , "corollary"
        , "proposition"
        , "classification"
        , "claim"
        , "abbreviation"
        , "datatype"
        , "recursive-definition"
        , "inductive"
        , "signature"
        , "struct"
        , "instance"
        , "construction"
        , "composition"
        ]

backslash, percent, openBrace, closeBrace, carriageReturn, exclamation :: Word8
backslash = 0x5c
percent = 0x25
openBrace = 0x7b
closeBrace = 0x7d
carriageReturn = 0x0d
exclamation = 0x21
