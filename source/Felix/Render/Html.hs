{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Felix.Render.Html
    ( HtmlRenderIndex
    , withNotationContracts
    , HtmlPagePresentation
    , BlockPresentationKind(..)
    , blockPresentationKind
    , blockPresentationKindLabel
    , HtmlDeclarationPresentation
    , htmlDeclarationMarker
    , htmlDeclarationKind
    , htmlDeclarationTitle
    , htmlDeclarationSource
    , HtmlDocumentPresentation
    , HtmlDocumentDraft
    , resolveHtmlDocument
    , HtmlDocumentProjectionError(..)
    , renderHtmlDocumentProjectionError
    , projectHtmlDocument
    , projectHtmlDocumentWithMathParser
    , StructureSchemaPresentation
    , structureSchemaPresentation
    , structureSchemaPresentationFields
    , buildRenderIndex
    , buildRenderIndexWithStructureSchemas
    , buildRenderIndexWithNavigation
    , buildRenderIndexWithNavigationAndDocuments
    , buildRenderIndexWithConsequences
    , htmlPagePresentationSource
    , HintOccurrenceSite
    , hintOccurrenceSource
    , hintOccurrenceLocation
    , MissingRenderHint
    , missingRenderHintCategory
    , missingRenderHintMarker
    , missingRenderHintArity
    , missingRenderHintSite
    , collectMissingRenderHintsChecked
    , renderMissingRenderHintDiagnostics
    , missingRenderHintDiagnostics
    , renderDocument
    , renderDeclarationIndex
    , stylesheetAssetContents
    , supportScriptAssetContents
    ) where

import Felix.Syntax.Phrase (NativePhraseBinding, nativePhraseBinding, adjectivePhraseEntry, numberedPhraseEntry)
import Felix.Syntax.Interface (CanonicalLexicalEntry(..))
import Felix.Syntax.Abstract
import Felix.Syntax.Adapt
    ( EffectiveSyntaxError
    , renderEffectiveSyntaxError
    )
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Lexicon (builtins, splitOnVariableSlot)

import Base
import Felix.Source
    ( ResolvedSource
    , resolvedSourceMount
    , resolvedSourceRelativePath
    , safeRelativePathFilePath
    , sourceMountIdText
    )
import Felix.Source.Scan
    ( DecodedPresentationSegment(..)
    , DocumentHeadingLevel(..)
    )
import Felix.Source.Scan qualified as SourceScan
import Lucid hiding (Term, for_)
import Lucid.Base (makeAttributes)
import Lucid.Math
import Felix.Render.Html.Assets
    ( stylesheetAssetContents
    , supportScriptAssetContents
    )
import Felix.Render.Html.Context
    ( HtmlRenderContext
    , HtmlRenderContextError
    , htmlCurrentPageLabel
    , htmlCurrentSource
    , htmlSourceFragmentHref
    , htmlSourceLabel
    , htmlSourcePageHref
    , htmlSupportScriptHref
    , htmlStylesheetHref
    , htmlDeclarationIndexHref
    )
import Felix.Render.Html.Contracts qualified as Contracts
import Felix.Render.Html.Consequences qualified as Consequences
import Felix.Checking.Core qualified as Core
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Render.Html.Hints
import Felix.Render.Html.Markup
import Felix.Render.Html.Layout (renderUrlFragment)
import Felix.Report.Diagnostic
import Felix.Report.Location
    ( Locatable(..)
    , Location
    , advanceSourceLocation
    , locLine
    , locColumn
    , pattern Nowhere
    )
import Felix.Syntax.Token
    ( VariableDisplay(..)
    , VariableSuffix(..)
    , displayVariable
    , renderVariableText
    , tokToText
    )

import Control.Monad (foldM, unless, when)
import Data.Char (isAlphaNum, isDigit, isLetter, isSpace, toUpper)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LazyText
import Data.Vector (Vector)



-- | The exact source-level role of a top-level block.  Presentation consumers
-- use this closed classification instead of independently approximating a
-- declaration's kind.
data BlockPresentationKind
    = AxiomPresentation
    | DefinitionPresentation
    | AbbreviationPresentation
    | DatatypePresentation
    | InductivePresentation
    | SignaturePresentation
    | StructurePresentation
    | InstancePresentation
    | ConstructionPresentation
    | PropositionPresentation
    | TheoremPresentation
    | LemmaPresentation
    | CorollaryPresentation
    | ClaimPresentation
    | ProofPresentation
    | ClassificationPresentation
    deriving (Show, Eq, Ord, Enum, Bounded)

blockPresentationKind :: Block -> BlockPresentationKind
blockPresentationKind = \case
    BlockAxiom{} -> AxiomPresentation
    BlockClaim kind _ _ _ _ -> claimPresentationKind kind
    BlockProof{} -> ProofPresentation
    BlockDefn{} -> DefinitionPresentation
    BlockAbbr{} -> AbbreviationPresentation
    BlockRecursive{} -> DefinitionPresentation
    BlockData{} -> DatatypePresentation
    BlockInductive{} -> InductivePresentation
    BlockSig{} -> SignaturePresentation
    BlockStruct{} -> StructurePresentation
    BlockInstance{} -> InstancePresentation
    BlockConstruction{} -> ConstructionPresentation

blockPresentationKindLabel :: BlockPresentationKind -> Text
blockPresentationKindLabel = \case
    AxiomPresentation -> "Axiom"
    DefinitionPresentation -> "Definition"
    AbbreviationPresentation -> "Abbreviation"
    DatatypePresentation -> "Datatype"
    InductivePresentation -> "Inductive"
    SignaturePresentation -> "Signature"
    StructurePresentation -> "Structure"
    InstancePresentation -> "Instance"
    ConstructionPresentation -> "Construction"
    PropositionPresentation -> "Proposition"
    TheoremPresentation -> "Theorem"
    LemmaPresentation -> "Lemma"
    CorollaryPresentation -> "Corollary"
    ClaimPresentation -> "Claim"
    ProofPresentation -> "Proof"
    ClassificationPresentation -> "Classification"

claimPresentationKind :: ClaimKind -> BlockPresentationKind
claimPresentationKind = \case
    Proposition -> PropositionPresentation
    Theorem -> TheoremPresentation
    Lemma -> LemmaPresentation
    Corollary -> CorollaryPresentation
    Composition -> PropositionPresentation
    PlainClaim -> ClaimPresentation
    Classification -> ClassificationPresentation

blockPresentationKindElement :: BlockPresentationKind -> Text
blockPresentationKindElement = \case
    AxiomPresentation -> "axiom-"
    DefinitionPresentation -> "definition-"
    AbbreviationPresentation -> "abbreviation-"
    DatatypePresentation -> "datatype-"
    InductivePresentation -> "inductive-"
    SignaturePresentation -> "signature-"
    StructurePresentation -> "struct-"
    InstancePresentation -> "instance-"
    ConstructionPresentation -> "construction-"
    PropositionPresentation -> "proposition-"
    TheoremPresentation -> "theorem-"
    LemmaPresentation -> "lemma-"
    CorollaryPresentation -> "corollary-"
    ClaimPresentation -> "claim-"
    ProofPresentation -> "proof-"
    ClassificationPresentation -> "classification-"

-- Only resolution constructs a document that may enter indexing and rendering.
data HtmlDocumentDraft = HtmlDocumentDraft ![HtmlDocumentNode] ![Diagnostic]

data HtmlDocumentPresentation = HtmlDocumentPresentation
    ![HtmlDocumentNode]
    deriving (Show, Eq)

data HtmlDocumentNode
    = HtmlDocumentHeading
        !DocumentHeadingLevel
        !Text
        ![HtmlPresentationInline]
    | HtmlDocumentParagraph
        ![HtmlPresentationInline]
    | HtmlDocumentDisplay
        !SourceSlice
        !CommentaryMath
        !(Maybe Text)
    | HtmlDocumentUnsupportedDisplay
        !Text
    | HtmlDocumentFormalSlot
        !Int
    deriving (Show, Eq)

data HtmlPresentationInline
    = HtmlPresentationText !Text
    | HtmlPresentationEmphasis ![HtmlPresentationInline]
    | HtmlPresentationMath !SourceSlice !CommentaryMath
    | HtmlPresentationMembership
    | HtmlPresentationPhrase !SourceSlice !PhraseUse
    | HtmlPresentationReference !(NonEmpty Marker)
    | HtmlPresentationUnsupported !Text
    deriving (Show, Eq)

data HtmlDocumentProjectionError
    = HtmlDocumentScanFailed !Text
    | HtmlDocumentSyntaxFailed !EffectiveSyntaxError
    | HtmlDocumentFormalCountMismatch !Int !Int
    | HtmlDocumentFormalSlotMismatch !Int !Text
    | HtmlDocumentAnchorCollision !Text
    | HtmlDocumentPhraseAmbiguity !Location !(NonEmpty NativePhraseBinding)
    | HtmlDocumentScannerInvariant
        !SourceScan.SourceScanInvariantError
    deriving (Show, Eq)

renderHtmlDocumentProjectionError :: HtmlDocumentProjectionError -> Text
renderHtmlDocumentProjectionError = \case
    HtmlDocumentScanFailed message ->
        "could not segment the source document: " <> message
    HtmlDocumentSyntaxFailed failure ->
        renderEffectiveSyntaxError failure
    HtmlDocumentFormalCountMismatch segments blocks ->
        "HTML document projection found " <> tshow segments
            <> " formal source slots for " <> tshow blocks <> " parsed blocks"
    HtmlDocumentFormalSlotMismatch ordinal message ->
        "HTML document projection slot " <> tshow ordinal
            <> " does not match its parsed block: " <> message
    HtmlDocumentAnchorCollision anchor ->
        "HTML page anchor is used more than once: " <> Text.pack (show anchor)
    HtmlDocumentPhraseAmbiguity location bindings ->
        "ambiguous native phrase at " <> Text.pack (show (locLine location)) <> ":"
            <> Text.pack (show (locColumn location)) <> ": "
            <> tshow (length bindings) <> " distinct lexical bindings"
    HtmlDocumentScannerInvariant failure ->
        "HTML document scanner invariant failed: "
            <> SourceScan.renderSourceScanInvariantError failure
  where
    tshow = Text.pack . show

projectHtmlDocument
    :: Vector DecodedPresentationSegment
    -> [Block]
    -> Either
        HtmlDocumentProjectionError
        HtmlDocumentDraft
projectHtmlDocument segments blocks =
    projectHtmlDocumentWithMathParser
        (prepareMarkupParser builtins)
        segments
        blocks

projectHtmlDocumentWithMathParser
    :: MarkupParser
    -> Vector DecodedPresentationSegment
    -> [Block]
    -> Either
        HtmlDocumentProjectionError
        HtmlDocumentDraft
projectHtmlDocumentWithMathParser mathParser segments blocks = do
    let blockAnchorList =
            concat
            [ renderedAnchorIds index block
            | (index, block) <- zip [1..] blocks
            ]
        blockAnchors = Set.fromList blockAnchorList
        duplicateBlockAnchors =
            blockAnchorList List.\\ Set.toList blockAnchors
        reservedBlockAnchors =
            List.filter isReservedPageAnchor blockAnchorList
    case duplicateBlockAnchors <> reservedBlockAnchors of
        collision : _ -> Left (HtmlDocumentAnchorCollision collision)
        [] -> pure ()
    (nodes, warnings, formalCount, _counters, _lastHeading, _anchors) <-
        foldM
            (projectSegment mathParser blocks)
            ([], [], 0, (0, 0, 0), Nothing, blockAnchors)
            segments
    when (formalCount /= length blocks)
        (Left (HtmlDocumentFormalCountMismatch formalCount (length blocks)))
    pure (HtmlDocumentDraft (reverse nodes) (reverse warnings))

resolveHtmlDocument
    :: RenderHints -> HtmlDocumentDraft -> (HtmlDocumentPresentation, [Diagnostic])
resolveHtmlDocument hints (HtmlDocumentDraft nodes projectionWarnings) =
    let (resolved, warnings) = unzip (resolveNode <$> nodes)
    in (HtmlDocumentPresentation resolved, merge projectionWarnings (concat warnings))
  where
    resolveNode = \case
        HtmlDocumentHeading level anchor inlines ->
            let (resolved, warnings) = resolveInlines inlines
            in (HtmlDocumentHeading level anchor resolved, warnings)
        HtmlDocumentParagraph inlines ->
            let (resolved, warnings) = resolveInlines inlines
            in (HtmlDocumentParagraph resolved, warnings)
        HtmlDocumentDisplay sourceSlice@(SourceSlice location spelling) value punctuation
            | not (boundMath value) ->
                (HtmlDocumentUnsupportedDisplay spelling, [unsupportedMarkupWarning location spelling])
            | otherwise -> (HtmlDocumentDisplay sourceSlice value punctuation, [])
        node -> (node, [])

    resolveInlines inlines =
        let (resolved, warnings) = unzip (resolveInline <$> inlines)
        in (resolved, concat warnings)

    resolveInline = \case
        HtmlPresentationEmphasis nested ->
            let (resolved, warnings) = resolveInlines nested
            in (HtmlPresentationEmphasis resolved, warnings)
        HtmlPresentationPhrase (SourceSlice location spelling) (DisplayPhrase name)
            | not (hasRenderHint PhraseHint (Marker name) 0 hints) ->
                (HtmlPresentationUnsupported spelling, [unsupportedMarkupWarning location spelling])
        HtmlPresentationMath sourceSlice@(SourceSlice location spelling) value
            | not (boundMath value) ->
                (HtmlPresentationUnsupported spelling, [unsupportedMarkupWarning location spelling])
            | otherwise -> (HtmlPresentationMath sourceSlice value, [])
        inline -> (inline, [])

    boundMath = \case
        MathPhrase (DisplayPhrase name) -> hasRenderHint PhraseHint (Marker name) 0 hints
        MathRow values -> all boundMath values
        MathFenced _ value -> boundMath value
        MathScript base scripts -> boundMath base && all boundMath scripts
        NativeMath{} -> True
        MathIdentifier{} -> True
        MathNumber{} -> True
        MathOperator{} -> True
        MathNamedOperator{} -> True
        MathPhrase ScopedPhrase{} -> True

    -- Both inputs follow document order; ties retain the projection diagnostic.
    merge [] right = right
    merge left [] = left
    merge left@(x:xs) right@(y:ys)
        | position x <= position y = x : merge xs right
        | otherwise = y : merge left ys
    position diagnostic =
        (\location -> (locLine location, locColumn location)) <$> diagnosticPrimary diagnostic

renderedAnchorIds :: Int -> Block -> [Text]
renderedAnchorIds index block =
    blockId
        : [ targetAnchorId
          | ReferenceTarget{targetAnchorId} <-
                referenceTargetsOfBlockRenderInfo Map.empty (index, block, blockId)
          , targetAnchorId /= blockId
          ]
  where
    blockId = blockAnchorId index block

isReservedPageAnchor :: Text -> Bool
isReservedPageAnchor anchor =
    anchor `Set.member` staticPageAnchors
        || "reference-preview-" `Text.isPrefixOf` anchor
  where
    staticPageAnchors =
        Set.fromList
            [ "main-content"
            , "theories-heading"
            , "theory-dependencies-heading"
            , "reference-preview-popup"
            ]

projectSegment
    :: MarkupParser
    -> [Block]
    -> ( [HtmlDocumentNode]
       , [Diagnostic]
       , Int
       , (Int, Int, Int)
       , Maybe Int
       , Set Text
       )
    -> DecodedPresentationSegment
    -> Either
        HtmlDocumentProjectionError
        ( [HtmlDocumentNode]
        , [Diagnostic]
        , Int
        , (Int, Int, Int)
        , Maybe Int
        , Set Text
        )
projectSegment mathParser blocks
        (nodes, warnings, formalCount, counters, lastHeading, anchors) = \case
    DecodedPresentationFormal location actualEnvironment -> do
        let ordinal = formalCount + 1
        block <-
            maybe
                (Left
                    (HtmlDocumentFormalCountMismatch
                        ordinal
                        (length blocks)))
                Right
                (zeroBasedIndex formalCount >>= (`nth` blocks))
        when (locate block /= location)
            (Left
                (HtmlDocumentFormalSlotMismatch ordinal
                    "source locations differ"))
        let expectedEnvironment = blockEnvironmentName block
        when (actualEnvironment /= expectedEnvironment)
            (Left
                (HtmlDocumentFormalSlotMismatch ordinal
                    ("expected " <> expectedEnvironment
                        <> ", found " <> actualEnvironment)))
        pure
            ( HtmlDocumentFormalSlot ordinal : nodes
            , warnings
            , ordinal
            , counters
            , lastHeading
            , anchors
            )
    DecodedPresentationProse location prose -> do
        (paragraphNodes, proseWarnings) <-
            projectNarrative mathParser location prose
        pure
            ( reverse paragraphNodes <> nodes
            , reverse proseWarnings <> warnings
            , formalCount
            , counters
            , lastHeading
            , anchors
            )
    DecodedPresentationHeading level location title explicitLabel -> do
        let numericLevel = headingLevelNumber level
            nextCounters = advanceHeadingCounters level counters
            anchor =
                fromMaybe
                    (headingOrdinalAnchor nextCounters numericLevel)
                    explicitLabel
            hierarchyWarnings =
                [ htmlPresentationWarning
                    DiagnosticHtmlSectionHierarchy
                    "section hierarchy is not contiguous"
                    location
                    "The HTML hierarchy should begin with \\section and must not skip a level."
                | maybe
                    (numericLevel /= 1)
                    (\previous -> numericLevel > previous + 1)
                    lastHeading
                ]
            titleLocation =
                advanceSourceLocation
                    location
                    (headingCommand level <> "{")
        (inlineTitle, inlineWarnings) <-
            projectInline mathParser titleLocation title
        when (anchor `Set.member` anchors || isReservedPageAnchor anchor)
            (Left (HtmlDocumentAnchorCollision anchor))
        pure
            ( HtmlDocumentHeading level anchor inlineTitle : nodes
            , reverse inlineWarnings <> hierarchyWarnings <> warnings
            , formalCount
            , nextCounters
            , Just numericLevel
            , Set.insert anchor anchors
            )

blockEnvironmentName :: Block -> Text
blockEnvironmentName = \case
    BlockAxiom{} -> "axiom"
    BlockClaim kind _ _ _ _ -> case kind of
        Proposition -> "proposition"
        Theorem -> "theorem"
        Lemma -> "lemma"
        Corollary -> "corollary"
        Composition -> "composition"
        PlainClaim -> "claim"
        Classification -> "classification"
    BlockProof{} -> "proof"
    BlockDefn{} -> "definition"
    BlockAbbr{} -> "abbreviation"
    BlockRecursive{} -> "recursive-definition"
    BlockData{} -> "datatype"
    BlockInductive{} -> "inductive"
    BlockSig{} -> "signature"
    BlockStruct{} -> "struct"
    BlockInstance{} -> "instance"
    BlockConstruction{} -> "construction"

headingLevelNumber :: DocumentHeadingLevel -> Int
headingLevelNumber = \case
    DocumentSection -> 1
    DocumentSubsection -> 2
    DocumentSubsubsection -> 3

headingCommand :: DocumentHeadingLevel -> Text
headingCommand = \case
    DocumentSection -> "\\section"
    DocumentSubsection -> "\\subsection"
    DocumentSubsubsection -> "\\subsubsection"

advanceHeadingCounters
    :: DocumentHeadingLevel
    -> (Int, Int, Int)
    -> (Int, Int, Int)
advanceHeadingCounters level (sectionNumber, subsectionNumber, subsubsectionNumber) =
    case level of
        DocumentSection -> (sectionNumber + 1, 0, 0)
        DocumentSubsection ->
            (sectionNumber, subsectionNumber + 1, 0)
        DocumentSubsubsection ->
            (sectionNumber, subsectionNumber, subsubsectionNumber + 1)

headingOrdinalAnchor :: (Int, Int, Int) -> Int -> Text
headingOrdinalAnchor (sectionNumber, subsectionNumber, subsubsectionNumber) level =
    "section-" <> Text.intercalate "-"
        (Text.pack . show <$> take level
            [sectionNumber, subsectionNumber, subsubsectionNumber])

projectNarrative
    :: MarkupParser -> Location -> Text
    -> Either HtmlDocumentProjectionError ([HtmlDocumentNode], [Diagnostic])
projectNarrative mathParser initialLocation source = do
    (nodes, warnings, _) <- foldM project ([], [], initialLocation) (splitDisplayEnvelopes source)
    pure (reverse nodes, reverse warnings)
  where
    project (nodes, warnings, location) piece = do
        let spelling = case piece of
                NarrativeProse text -> text
                NarrativeDisplay envelope -> envelopeSource envelope
        (newNodes, newWarnings) <- case piece of
            NarrativeProse prose -> do
                projected <- traverse
                    (\(paragraphLocation, paragraph) -> do
                        (inlines, diagnostics) <- projectInline mathParser paragraphLocation paragraph
                        pure (HtmlDocumentParagraph inlines, diagnostics))
                    (splitNarrativeParagraphs location prose)
                pure (fst <$> projected, concatMap snd projected)
            NarrativeDisplay envelope -> projectDisplay location envelope
        pure (reverse newNodes <> nodes, reverse newWarnings <> warnings,
            advanceSourceLocation location spelling)

    projectDisplay location envelope =
        let spelling = envelopeSource envelope
            unsupported = pure ([HtmlDocumentUnsupportedDisplay spelling],
                [unsupportedMarkupWarning location spelling])
        in case (envelopeKind envelope, envelopeBody envelope) of
            (DisplayEnvelope, Just body) -> case parseDisplayMath mathParser body of
                Right (value, punctuation) ->
                    pure ([HtmlDocumentDisplay (SourceSlice location spelling) value punctuation], [])
                Left MarkupUnsupported{} -> unsupported
                Left MarkupNativeAmbiguity{} -> unsupported
                Left (MarkupPhraseAmbiguity bindings) -> Left (HtmlDocumentPhraseAmbiguity location bindings)
                Left (MarkupScannerInvariant failure) -> Left (HtmlDocumentScannerInvariant failure)
            _ -> unsupported

parseDisplayMath
    :: MarkupParser -> Text
    -> Either MarkupMathFailure (CommentaryMath, Maybe Text)
parseDisplayMath parser source =
    case parseCommentaryMath parser source of
        Right value -> Right (value, Nothing)
        Left failure@MarkupScannerInvariant{} -> Left failure
        Left failure@MarkupNativeAmbiguity{} -> Left failure
        Left failure@MarkupPhraseAmbiguity{} -> Left failure
        Left originalFailure@MarkupUnsupported{} ->
            case stripDisplayPunctuation source of
                Nothing -> Left originalFailure
                Just (body, punctuation) -> case parseCommentaryMath parser body of
                    Right value -> Right (value, Just punctuation)
                    Left failure@MarkupScannerInvariant{} -> Left failure
                    Left failure@MarkupNativeAmbiguity{} -> Left failure
                    Left failure@MarkupPhraseAmbiguity{} -> Left failure
                    Left MarkupUnsupported{} -> Left originalFailure

splitNarrativeParagraphs :: Location -> Text -> [(Location, Text)]
splitNarrativeParagraphs initialLocation initialSource = go initialLocation initialSource
  where
    go location source =
        let leading = Text.takeWhile isSpace source
            paragraphLocation = advanceSourceLocation location leading
            content = Text.drop (Text.length leading) source
        in if Text.null content then [] else
            case breakNarrativeParagraph content of
                Nothing -> [(paragraphLocation, Text.stripEnd content)]
                Just (paragraph, separator, remaining) ->
                    (paragraphLocation, Text.stripEnd paragraph)
                        : go (advanceSourceLocation paragraphLocation (paragraph <> separator)) remaining

breakNarrativeParagraph :: Text -> Maybe (Text, Text, Text)
breakNarrativeParagraph original = search 0 original
  where
    search consumed source =
        case Text.breakOn "\n" source of
            (_, suffix) | Text.null suffix -> Nothing
            (line, suffix) ->
                let afterNewline = Text.drop 1 suffix
                    horizontal = Text.takeWhile (\c -> c == ' ' || c == '\t' || c == '\r') afterNewline
                    afterHorizontal = Text.drop (Text.length horizontal) afterNewline
                in case Text.stripPrefix "\n" afterHorizontal of
                    Just remaining -> Just
                        ( Text.take (consumed + Text.length line) original
                        , "\n" <> horizontal <> "\n"
                        , remaining
                        )
                    Nothing -> search (consumed + Text.length line + 1) afterNewline

projectInline
    :: MarkupParser
    -> Location
    -> Text
    -> Either
        HtmlDocumentProjectionError
        ([HtmlPresentationInline], [Diagnostic])
projectInline mathParser = go
  where
    go location source
        | Text.null source = pure ([], [])
        | Just rest <- Text.stripPrefix "--" source =
            prepend (HtmlPresentationText "–")
                (go (advanceSourceLocation location "--") rest)
        | Just rest <- Text.stripPrefix "\\ " source =
            prepend (HtmlPresentationText " ")
                (go (advanceSourceLocation location "\\ ") rest)
        | Just rest <- Text.stripPrefix "\\in" source
        , maybe True (not . isLetter . fst) (Text.uncons rest) =
            prepend HtmlPresentationMembership
                (go (advanceSourceLocation location "\\in") rest)
        | "\\ref{" `Text.isPrefixOf` source
            || "\\cref{" `Text.isPrefixOf` source
            || "\\obv{" `Text.isPrefixOf` source =
            let (spelling, rest) = takeUnsupportedCommand source
            in case SourceScan.parsePresentationReferenceFragment spelling of
                Left failure ->
                    Left (HtmlDocumentScannerInvariant failure)
                Right (Just markers) ->
                    prepend
                        (HtmlPresentationReference (Marker <$> markers))
                        (go
                            (advanceSourceLocation location spelling)
                            rest)
                Right Nothing ->
                    unsupported location spelling rest
        | Just rest <- Text.stripPrefix "\\emph{" source =
            projectEmphasis location "\\emph{" rest
        | Just rest <- Text.stripPrefix "\\textit{" source =
            projectEmphasis location "\\textit{" rest
        | Just rest <- Text.stripPrefix "\\$" source =
            prepend (HtmlPresentationText "$")
                (go (advanceSourceLocation location "\\$") rest)
        | Just (envelope, rest) <- takeMathEnvelope source =
            projectMath location envelope rest
        | Just (invocation, rest) <- takeCommandInvocation source
        , isBareInvocation invocation =
            let spelling = invocationSource invocation
                name = invocationName invocation
                sourceSlice = SourceSlice location spelling
                continuation = go (advanceSourceLocation location spelling) rest
            in case lookupMarkupPhrase mathParser name of
                Concrete.UniqueNativePhrase binding ->
                    prepend (HtmlPresentationPhrase sourceSlice (ScopedPhrase binding name)) continuation
                Concrete.NoNativePhrase ->
                    prepend (HtmlPresentationPhrase sourceSlice (DisplayPhrase name)) continuation
                Concrete.AmbiguousNativePhrase bindings -> Left (HtmlDocumentPhraseAmbiguity location bindings)
        | Text.isPrefixOf "\\" source =
            let (unsupportedSource, rest) = takeUnsupportedCommand source
                warning = unsupportedMarkupWarning location unsupportedSource
            in do
                (remaining, warnings) <-
                    go (advanceSourceLocation location unsupportedSource) rest
                pure
                    ( HtmlPresentationUnsupported unsupportedSource : remaining
                    , warning : warnings
                    )
        | otherwise =
            let (plain, rest) = Text.break isInlineSpecial source
                consumed = if Text.null plain then Text.take 1 source else plain
                remainingSource = if Text.null plain then Text.drop 1 source else rest
            in prepend (HtmlPresentationText (Text.copy consumed))
                (go (advanceSourceLocation location consumed) remainingSource)

    projectEmphasis location opening rest =
        case takeBalancedContent rest of
            Nothing -> unsupported location (opening <> rest) ""
            Just (content, remaining) -> do
                let nestedLocation = advanceSourceLocation location opening
                    complete = opening <> content <> "}"
                    afterLocation = advanceSourceLocation location complete
                (nested, nestedWarnings) <- go nestedLocation content
                (after, afterWarnings) <- go afterLocation remaining
                pure
                    ( HtmlPresentationEmphasis nested : after
                    , nestedWarnings <> afterWarnings
                    )

    projectMath location envelope remaining =
        let complete = envelopeSource envelope
        in case (envelopeKind envelope, envelopeBody envelope) of
            (InlineEnvelope, Just contents) ->
                case parseCommentaryMath mathParser contents of
                    Right value ->
                        prepend (HtmlPresentationMath (SourceSlice location complete) value)
                            (go (advanceSourceLocation location complete) remaining)
                    Left MarkupUnsupported{} -> unsupported location complete remaining
                    Left MarkupNativeAmbiguity{} -> unsupported location complete remaining
                    Left (MarkupPhraseAmbiguity bindings) -> Left (HtmlDocumentPhraseAmbiguity location bindings)
                    Left (MarkupScannerInvariant failure) -> Left (HtmlDocumentScannerInvariant failure)
            _ -> unsupported location complete remaining

    unsupported location spelling remaining = do
        let warning = unsupportedMarkupWarning location spelling
        (after, warnings) <-
            go (advanceSourceLocation location spelling) remaining
        pure
            ( HtmlPresentationUnsupported spelling : after
            , warning : warnings
            )

    prepend value continuation = do
        (values, warnings) <- continuation
        pure (value : values, warnings)

isInlineSpecial :: Char -> Bool
isInlineSpecial character =
    character == '\\' || character == '$' || character == '-'

takeBalancedContent :: Text -> Maybe (Text, Text)
takeBalancedContent source = takeBalancedGroup ("{" <> source)

takeUnsupportedCommand :: Text -> (Text, Text)
takeUnsupportedCommand source =
    case takeCommandInvocation source of
        Just (invocation, rest) -> (invocationSource invocation, rest)
        Nothing -> (Text.take 2 source, Text.drop 2 source)


unsupportedMarkupWarning :: Location -> Text -> Diagnostic
unsupportedMarkupWarning location spelling =
    htmlPresentationWarning
        DiagnosticHtmlUnsupportedMarkup
        "commentary contains unsupported markup"
        location
        ("The source is shown literally in HTML: " <> spelling)

htmlPresentationWarning
    :: DiagnosticCode
    -> Text
    -> Location
    -> Text
    -> Diagnostic
htmlPresentationWarning code title location message =
    Diagnostic
        { diagnosticSeverity = DiagnosticWarning
        , diagnosticCode = code
        , diagnosticTitle = title
        , diagnosticPrimary = Just location
        , diagnosticMessage = pretty message
        , diagnosticNotes = []
        , diagnosticHelp = []
        }

data RenderEnvironment = RenderEnvironment
    { renderEnvironmentHints :: !RenderHints
    , renderEnvironmentNotationContracts :: !(Maybe Contracts.NotationContracts)
    , renderEnvironmentStructureSchemas
        :: !(Map Marker StructureSchemaPresentation)
    , renderEnvironmentConsequences :: !(Map Marker [Consequences.PublicConsequence])
    }

data StructureSchemaPresentation = StructureSchemaPresentation
    !Text
    ![(StructSymbol, Text)]
    deriving (Show, Eq)

structureSchemaPresentation
    :: Text
    -> [(StructSymbol, Text)]
    -> StructureSchemaPresentation
structureSchemaPresentation = StructureSchemaPresentation

structureSchemaPresentationFields
    :: StructureSchemaPresentation
    -> [StructSymbol]
structureSchemaPresentationFields
        (StructureSchemaPresentation _ fields) =
    fst <$> fields

type AnchorMap = Map Marker Text
type BlockRenderInfo = (Int, Block, Text)
type PreviewMap = Map Marker PreviewEntry

data HtmlRenderIndex = HtmlRenderIndex
    { renderIndexReferenceTargets
        :: !(Map Marker IndexedReferenceTarget)
    , renderIndexRootSource :: !ResolvedSource
    , renderIndexOrderedSources :: !(NonEmpty ResolvedSource)
    , renderIndexImporters
        :: !(Map ResolvedSource [ResolvedSource])
    , renderIndexSourceDeclarations :: ![HtmlDeclarationPresentation]
    }

data HtmlDeclarationPresentation = HtmlDeclarationPresentation
    { htmlDeclarationMarker :: !Text
    , htmlDeclarationKind :: !BlockPresentationKind
    , htmlDeclarationTitle :: !(Maybe Text)
    , htmlDeclarationSource :: !ResolvedSource
    , htmlDeclarationAnchor :: !Text
    }
    deriving (Show, Eq)

data HtmlPagePresentation = HtmlPagePresentation
    { htmlPagePresentationSource :: !ResolvedSource
    , pagePresentationDirectImports :: ![ResolvedSource]
    , pagePresentationBlockInfos :: ![BlockRenderInfo]
    , pagePresentationAnchors :: !AnchorMap
    , pagePresentationReferencedMarkers :: !(Set Marker)
    , pagePresentationStructureSchemas
        :: !(Map Marker StructureSchemaPresentation)
    , pagePresentationConsequences :: !(Map Marker [Consequences.PublicConsequence])
    , pagePresentationNotationContracts :: !(Maybe Contracts.NotationContracts)
    , pagePresentationDocument :: !HtmlDocumentPresentation
    }

withNotationContracts :: Contracts.NotationContracts -> HtmlPagePresentation -> HtmlPagePresentation
withNotationContracts contracts page = page {pagePresentationNotationContracts = Just contracts}

data IndexedReferenceTarget = IndexedReferenceTarget
    !Int
    !ResolvedSource
    !ReferenceTarget

data ReferenceContext = ReferenceContext
    { referenceAnchors :: AnchorMap
    , referencePreviews :: PreviewMap
    }

data PreviewEntry = PreviewEntry
    { previewMarker :: Marker
    , previewKind :: Text
    , previewTitle :: Maybe Text
    , previewSourceLabel :: Text
    , previewSourceHref :: Text
    , previewReferenceHref :: Text
    , previewId :: Text
    , previewBody :: RenderEnvironment -> Html ()
    }

data ReferenceTarget = ReferenceTarget
    { targetMarker :: Marker
    , targetAnchorId :: Text
    , targetKind :: Text
    , targetTitle :: Maybe Text
    , targetBody :: RenderEnvironment -> Html ()
    }

data StmtMathFragment
    = StmtMathProse Text
    | StmtMathNode (Html ())

type StmtMathFragments = [StmtMathFragment]

data HintOccurrenceSite = HintOccurrenceSite
    !ResolvedSource
    !(Maybe Location)
    deriving stock (Show, Eq)

hintOccurrenceSource :: HintOccurrenceSite -> ResolvedSource
hintOccurrenceSource (HintOccurrenceSite source _location) = source

hintOccurrenceLocation :: HintOccurrenceSite -> Maybe Location
hintOccurrenceLocation (HintOccurrenceSite _source location) = location

data MissingRenderHint = MissingRenderHint
    !HintCategory
    !Marker
    !Int
    !HintOccurrenceSite
    deriving stock (Show, Eq)

missingRenderHintCategory :: MissingRenderHint -> HintCategory
missingRenderHintCategory (MissingRenderHint category _marker _arity _site) =
    category

missingRenderHintMarker :: MissingRenderHint -> Marker
missingRenderHintMarker (MissingRenderHint _category marker _arity _site) =
    marker

missingRenderHintArity :: MissingRenderHint -> Int
missingRenderHintArity (MissingRenderHint _category _marker arity _site) =
    arity

missingRenderHintSite :: MissingRenderHint -> HintOccurrenceSite
missingRenderHintSite (MissingRenderHint _category _marker _arity site) =
    site

type MissingRenderHintKey = (HintCategory, Marker, Int)

data MissingHintAccumulator = MissingHintAccumulator
    !(Map MissingRenderHintKey ())
    !(Seq MissingRenderHint)

newtype MissingHintCollection = MissingHintCollection
    { runMissingHintCollection
        :: RenderEnvironment
        -> (Maybe Location -> HintOccurrenceSite)
        -> MissingHintAccumulator
        -> MissingHintAccumulator
    }

instance Semigroup MissingHintCollection where
    left <> right = MissingHintCollection \hints siteFor accumulator ->
        runMissingHintCollection
            right hints siteFor
            (runMissingHintCollection left hints siteFor accumulator)

instance Monoid MissingHintCollection where
    mempty = MissingHintCollection \_hints _siteFor accumulator -> accumulator

proofCollapseThreshold :: Int
proofCollapseThreshold = 10

nestedProofCollapseThreshold :: Int
nestedProofCollapseThreshold = proofCollapseThreshold

referenceGroupThreshold :: Int
referenceGroupThreshold = 5

formalJustificationGroupThreshold :: Int
formalJustificationGroupThreshold = 2

data MarkerReferenceUse
    = CommentaryReference
    | FormalJustificationReference

data MarkerReferencePresentation
    = VisibleMarkerReference
    | CompactMarkerReference


renderDocument
    :: HtmlRenderContext
    -> RenderHints
    -> HtmlRenderIndex
    -> HtmlPagePresentation
    -> Either HtmlRenderContextError Text
renderDocument
        context
        renderHints
        renderIndex
        HtmlPagePresentation
            { pagePresentationDirectImports = directImports
            , pagePresentationBlockInfos = blockInfos
            , pagePresentationAnchors = anchors
            , pagePresentationReferencedMarkers = referencedMarkers
            , pagePresentationNotationContracts = notationContracts
            , pagePresentationStructureSchemas = structureSchemas
            , pagePresentationConsequences = consequences
            , pagePresentationDocument = documentPresentation
            } = do
    let currentSource = htmlCurrentSource context
        rootSource = renderIndexRootSource renderIndex
        isRoot = currentSource == rootSource
        theorySources =
            List.filter
                (/= rootSource)
                (NonEmpty.toList
                    (renderIndexOrderedSources renderIndex))
        directImporters =
            Map.findWithDefault
                []
                currentSource
                (renderIndexImporters renderIndex)
    previews <-
        buildPreviewMap
            context
            referencedMarkers
            anchors
            renderIndex
    theoryLinks <-
        if isRoot
            then traverse (sourceLink context) theorySources
            else pure []
    rootHref <-
        if isRoot
            then pure Nothing
            else Just <$> htmlSourcePageHref context rootSource
    importLinks <-
        if isRoot
            then pure []
            else traverse (sourceLink context) directImports
    importerLinks <-
        if isRoot
            then pure []
            else traverse (sourceLink context) directImporters
    let declarationsHref = htmlDeclarationIndexHref context
    let result = rendered
        hints = RenderEnvironment renderHints notationContracts structureSchemas consequences
        rendered = LazyText.toStrict (renderText (renderPage hints))
        pageLabel = htmlCurrentPageLabel context
        tocOutline = buildDocumentOutline documentPresentation blockInfos
        pageLayoutClass =
            if null tocOutline
                then "page-layout page-layout-without-toc"
                else "page-layout"
        referenceContext = ReferenceContext anchors previews

        renderPage :: RenderEnvironment -> Html ()
        renderPage hintMap = do
            doctype_
            html_ [lang_ "en"] do
                head_ do
                    meta_ [charset_ "utf-8"]
                    meta_
                        [ name_ "viewport"
                        , content_ "width=device-width, initial-scale=1"
                        ]
                    title_ (toHtml pageLabel)
                    link_
                        [ rel_ "stylesheet"
                        , href_ (htmlStylesheetHref context)
                        ]
                body_ do
                    a_
                        [ class_ "skip-link"
                        , href_ "#main-content"
                        ]
                        "Skip to content"
                    div_ [class_ pageLayoutClass] do
                        unless (null tocOutline) do
                            aside_ [class_ "toc-column"] do
                                details_ [class_ "toc-disclosure", open_ ""] do
                                    summary_ [class_ "toc-summary"] "Contents"
                                    nav_
                                        [ class_ "toc"
                                        , makeAttributes "aria-label" "Contents"
                                        ] do
                                        ol_ [class_ "toc-list"] do
                                            traverse_ (renderOutlineEntry hintMap) tocOutline
                        main_
                            [ id_ "main-content"
                            , makeAttributes "tabindex" "-1"
                            ] do
                            renderCollectionNavigation rootHref declarationsHref
                            h1_ (toHtml pageLabel)
                            if isRoot
                                then renderTheoryIndex theoryLinks
                                else
                                    renderTheoryDependencies
                                        importLinks
                                        importerLinks
                            renderDocumentPresentation
                                hintMap
                                referenceContext
                                blockInfos
                                documentPresentation
                    renderPreviewStore hintMap previews
                    div_
                        [ id_ "reference-preview-popup"
                        , class_ "reference-preview-popup"
                        , makeAttributes "role" "tooltip"
                        , makeAttributes "aria-hidden" "true"
                        ]
                        skip
                    script_
                        [src_ (htmlSupportScriptHref context)]
                        ("" :: Text)
    Right result

-- | Render the synthetic source-declaration index.  Its inventory comes only
-- from top-level source blocks; generated inductive facts deliberately remain
-- reference-preview targets rather than declarations.
renderDeclarationIndex
    :: HtmlRenderContext
    -> HtmlRenderIndex
    -> Either HtmlRenderContextError Text
renderDeclarationIndex context renderIndex = do
    rootHref <-
        htmlSourcePageHref context (renderIndexRootSource renderIndex)
    entries <-
        traverse prepareEntry
            (List.sortOn declarationOrder
                (renderIndexSourceDeclarations renderIndex))
    let pageLabel = "Declarations — " <> htmlCurrentPageLabel context
        rendered = LazyText.toStrict (renderText do
            doctype_
            html_ [lang_ "en"] do
                head_ do
                    meta_ [charset_ "utf-8"]
                    meta_
                        [ name_ "viewport"
                        , content_ "width=device-width, initial-scale=1"
                        ]
                    title_ (toHtml pageLabel)
                    link_
                        [ rel_ "stylesheet"
                        , href_ (htmlStylesheetHref context)
                        ]
                body_ do
                    a_ [class_ "skip-link", href_ "#main-content"]
                        "Skip to content"
                    div_ [class_ "page-layout page-layout-without-toc"] do
                        main_ [id_ "main-content", makeAttributes "tabindex" "-1"] do
                            nav_
                                [ class_ "collection-navigation"
                                , makeAttributes "aria-label" "Theory collection"
                                ]
                                (a_ [href_ rootHref] "All theories")
                            h1_ "Declarations"
                            p_ [class_ "declaration-index-introduction"] do
                                toHtml (Text.pack (show (length entries)))
                                toHtml (" source declarations in this export." :: Text)
                            ol_ [class_ "declaration-list"]
                                (traverse_ renderDeclarationEntry entries)
                            p_
                                [ class_ "declaration-no-results"
                                , hidden_ ""
                                ]
                                "No declarations match these filters."
                    script_ [src_ (htmlSupportScriptHref context)] ("" :: Text))
    Right rendered
  where
    declarationOrder declaration =
        ( Text.toCaseFold (htmlDeclarationMarker declaration)
        , htmlDeclarationMarker declaration
        )

    prepareEntry declaration = do
        theoryLabel <- htmlSourceLabel context (htmlDeclarationSource declaration)
        theoryHref <- htmlSourcePageHref context (htmlDeclarationSource declaration)
        declarationHref <-
            htmlSourceFragmentHref
                context
                (htmlDeclarationSource declaration)
                (htmlDeclarationAnchor declaration)
        pure (declaration, theoryLabel, theoryHref, declarationHref)

renderDeclarationEntry
    :: (HtmlDeclarationPresentation, Text, Text, Text)
    -> Html ()
renderDeclarationEntry
        (declaration, theoryLabel, theoryHref, declarationHref) =
    li_
        [ makeAttributes "data-declaration-kind" kindLabel
        , makeAttributes "data-declaration-theory" theoryLabel
        ] do
        a_ [href_ declarationHref, class_ "declaration-marker"]
            (code_ (toHtml (htmlDeclarationMarker declaration)))
        for_ (htmlDeclarationTitle declaration) \title -> do
            toHtml (" — " :: Text)
            span_ [class_ "declaration-title"] (toHtml title)
        span_ [class_ "declaration-metadata"] do
            span_ [class_ "declaration-kind"] (toHtml kindLabel)
            toHtml (" in " :: Text)
            a_ [href_ theoryHref] (code_ (toHtml theoryLabel))
  where
    kindLabel =
        blockPresentationKindLabel (htmlDeclarationKind declaration)

sourceLink
    :: HtmlRenderContext
    -> ResolvedSource
    -> Either HtmlRenderContextError (Text, Text)
sourceLink context source = do
    label <- htmlSourceLabel context source
    href <- htmlSourcePageHref context source
    pure (label, href)

renderCollectionNavigation :: Maybe Text -> Text -> Html ()
renderCollectionNavigation rootHref declarationsHref =
    nav_
        [ class_ "collection-navigation"
        , makeAttributes "aria-label" "Theory collection"
        ] do
        for_ rootHref \href ->
            a_ [href_ href] "All theories"
        a_ [href_ declarationsHref] "All declarations"

renderTheoryIndex :: [(Text, Text)] -> Html ()
renderTheoryIndex theories =
    nav_
        [ class_ "theory-index"
        , makeAttributes "aria-labelledby" "theories-heading"
        ] do
        h2_ [id_ "theories-heading"] "Theories"
        p_ "This is the root theory for this export."
        case theories of
            [] ->
                p_ [class_ "theory-empty"]
                    "This export contains no other theories."
            _ ->
                ol_ [class_ "theory-list"] do
                    traverse_ renderTheoryLink theories

renderTheoryDependencies
    :: [(Text, Text)]
    -> [(Text, Text)]
    -> Html ()
renderTheoryDependencies imports importers =
    nav_
        [ class_ "theory-dependencies"
        , makeAttributes "aria-labelledby" "theory-dependencies-heading"
        ] do
        h2_ [id_ "theory-dependencies-heading"]
            "Theory dependencies"
        renderTheoryRelationship
            "Imports"
            "No direct imports."
            imports
        renderTheoryRelationship
            "Imported by"
            "No importers in this export."
            importers

renderTheoryRelationship
    :: Text
    -> Text
    -> [(Text, Text)]
    -> Html ()
renderTheoryRelationship heading emptyText links =
    section_ [class_ "theory-relationship"] do
        h3_ (toHtml heading)
        case links of
            [] ->
                p_ [class_ "theory-empty"] (toHtml emptyText)
            _ ->
                ul_ [class_ "theory-relationship-list"] do
                    traverse_ renderTheoryLink links

renderTheoryLink :: (Text, Text) -> Html ()
renderTheoryLink (label, href) =
    li_ do
        a_ [href_ href] do
            code_ (toHtml label)

-- | Index every block target and every page's referenced markers once in
-- deterministic source order.  Rendering a page subsequently performs only
-- marker lookups in the shared index.
buildRenderIndex
    :: NonEmpty (ResolvedSource, [Block])
    -> (HtmlRenderIndex, NonEmpty HtmlPagePresentation)
buildRenderIndex sourceBlocks =
    buildRenderIndexWithStructureSchemas
        ((\(source, blocks) -> (source, blocks, Map.empty)) <$> sourceBlocks)

buildRenderIndexWithStructureSchemas
    :: NonEmpty
        ( ResolvedSource
        , [Block]
        , Map Marker StructureSchemaPresentation
        )
    -> (HtmlRenderIndex, NonEmpty HtmlPagePresentation)
buildRenderIndexWithStructureSchemas sourceBlocks =
    buildRenderIndexWithNavigation
        (sourceOf (NonEmpty.last sourceBlocks))
        ((\(source, blocks, schemas) ->
            (source, [], blocks, schemas)) <$> sourceBlocks)
  where
    sourceOf (source, _blocks, _schemas) = source

-- | Build the shared declaration and theory-navigation index for one export.
-- Sources remain in the workspace's imported-before-importer order; only the
-- direct import edges retained by presentation projection are indexed.
buildRenderIndexWithNavigation
    :: ResolvedSource
    -> NonEmpty
        ( ResolvedSource
        , [ResolvedSource]
        , [Block]
        , Map Marker StructureSchemaPresentation
        )
    -> (HtmlRenderIndex, NonEmpty HtmlPagePresentation)
buildRenderIndexWithNavigation rootSource sourceBlocks =
    buildRenderIndexWithNavigationAndDocuments
        rootSource
        ( (\(source, imports, blocks, schemas) ->
            ( source
            , imports
            , blocks
            , schemas
            , defaultDocumentPresentation blocks
            )) <$> sourceBlocks
        )

buildRenderIndexWithNavigationAndDocuments
    :: ResolvedSource
    -> NonEmpty
        ( ResolvedSource
        , [ResolvedSource]
        , [Block]
        , Map Marker StructureSchemaPresentation
        , HtmlDocumentPresentation
        )
    -> (HtmlRenderIndex, NonEmpty HtmlPagePresentation)
buildRenderIndexWithNavigationAndDocuments rootSource sourceBlocks =
    buildRenderIndexWithConsequences Map.empty rootSource sourceBlocks

buildRenderIndexWithConsequences
    :: Map Marker [Consequences.PublicConsequence]
    -> ResolvedSource
    -> NonEmpty (ResolvedSource, [ResolvedSource], [Block], Map Marker StructureSchemaPresentation, HtmlDocumentPresentation)
    -> (HtmlRenderIndex, NonEmpty HtmlPagePresentation)
buildRenderIndexWithConsequences consequences rootSource sourceBlocks =
    ( HtmlRenderIndex
        { renderIndexReferenceTargets =
            Map.fromList
            [ ( targetMarker target
              , IndexedReferenceTarget ordinal source target
              )
            | (ordinal, (source, target)) <-
                zip [1 :: Int ..] orderedTargets
            ]
        , renderIndexRootSource = rootSource
        , renderIndexOrderedSources = orderedSources
        , renderIndexImporters = directImporters
        , renderIndexSourceDeclarations = sourceDeclarations
        }
    , pages
    )
  where
    analysedPages =
        (\(source, imports, blocks, schemas, document) ->
            analysePage source imports blocks schemas document)
            <$> sourceBlocks
    pages =
        fst <$> analysedPages
    orderedSources =
        (\(source, _imports, _blocks, _schemas, _document) -> source)
            <$> sourceBlocks
    directImporters =
        foldl' addImporters Map.empty (NonEmpty.toList sourceBlocks)
    orderedTargets =
        [ (htmlPagePresentationSource page, target)
        | (page, targets) <- NonEmpty.toList analysedPages
        , target <- targets
        ]
    sourceDeclarations =
        [ HtmlDeclarationPresentation
            { htmlDeclarationMarker = marker
            , htmlDeclarationKind = blockPresentationKind block
            , htmlDeclarationTitle = formatBlockTitle (blockTitleOf block)
            , htmlDeclarationSource = source
            , htmlDeclarationAnchor = blockId
            }
        | page <- NonEmpty.toList pages
        , let source = htmlPagePresentationSource page
        , (_index, block, blockId) <- pagePresentationBlockInfos page
        , includeInToc block
        , Just marker <- [formatMarker (blockMarkerOf block)]
        ]

    addImporters importers (importer, imports, _blocks, _schemas, _document) =
        foldl'
            (\current imported ->
                Map.insertWith
                    (\new old -> old <> new)
                    imported
                    [importer]
                    current)
            importers
            imports

    analysePage source imports blocks schemas document =
        ( HtmlPagePresentation
            { htmlPagePresentationSource = source
            , pagePresentationDirectImports = imports
            , pagePresentationBlockInfos = blockInfos
            , pagePresentationAnchors =
                Map.fromList
                    [ (targetMarker, targetAnchorId)
                    | ReferenceTarget
                        { targetMarker
                        , targetAnchorId
                        } <- targets
                    ]
            , pagePresentationReferencedMarkers =
                foldMap
                    (\(_blockInfo, _targets, references) -> references)
                    analysedBlocks
                    <> collectReferencedMarkersOfDocument document
            , pagePresentationNotationContracts = Nothing
            , pagePresentationStructureSchemas = schemas
            , pagePresentationConsequences = consequences
            , pagePresentationDocument = document
            }
        , targets
        )
      where
        analysedBlocks =
            [ ( blockInfo
              , referenceTargetsOfBlockRenderInfo consequences blockInfo
              , collectReferencedMarkersOfBlock block
              )
            | (index, block) <- zip [1 :: Int ..] blocks
            , let blockInfo =
                    (index, block, blockAnchorId index block)
            ]
        blockInfos =
            [ blockInfo
            | (blockInfo, _targets, _references) <- analysedBlocks
            ]
        targets =
            concat
                [ blockTargets
                | (_blockInfo, blockTargets, _references) <- analysedBlocks
                ]

defaultDocumentPresentation :: [Block] -> HtmlDocumentPresentation
defaultDocumentPresentation blocks =
    HtmlDocumentPresentation
        [HtmlDocumentFormalSlot ordinal | ordinal <- [1 .. length blocks]]


collectReferencedMarkersOfBlock :: Block -> Set Marker
collectReferencedMarkersOfBlock =
    collectBlock
  where
        collectBlock :: Block -> Set Marker
        collectBlock = \case
            BlockProof _start proof _end ->
                collectProof proof
            _ ->
                mempty

        collectProof :: Proof -> Set Marker
        collectProof = \case
            Omitted _loc ->
                mempty
            Qed _loc justification ->
                collectJustification justification
            Contradiction _loc justification ->
                collectJustification justification
            ByCase _loc cases ->
                foldMap collectCase cases
            ByContradiction _loc proof ->
                collectProof proof
            BySetInduction _loc _term proof ->
                collectProof proof
            ByOrdInduction _loc proof ->
                collectProof proof
            ByStructuralInduction _loc _focus cases ->
                foldMap (collectProof . namedCaseProof) cases
            Assume _loc _intro _stmt proof ->
                collectProof proof
            Fix _loc _binders _condition proof ->
                collectProof proof
            Calc _loc _maybeQuant calc proof ->
                collectCalc calc <> collectProof proof
            TakeVar _loc _vars _bound _stmt justification proof ->
                collectJustification justification <> collectProof proof
            TakeTyped _loc _vars _coreType _stmt justification proof ->
                collectJustification justification <> collectProof proof
            TakeNoun _loc _np justification proof ->
                collectJustification justification <> collectProof proof
            Have _loc _intro _stmt justification proof ->
                collectJustification justification <> collectProof proof
            Since
                    _premiseLoc _premise premiseJustification
                    _claimLoc _claim claimJustification proof ->
                collectJustification premiseJustification
                    <> collectJustification claimJustification
                    <> collectProof proof
            Suffices _loc _stmt justification proof ->
                collectJustification justification <> collectProof proof
            Subclaim _loc _stmt subproof proof ->
                collectProof subproof <> collectProof proof
            Define _loc _var _expr proof ->
                collectProof proof
            DefineTyped _loc _var _coreType _body proof ->
                collectProof proof
            DefineFunction _loc _fun _arg _value _boundVar _boundExpr proof ->
                collectProof proof
            DefineFunctionLocal _loc _fun _arg _target _domVar _codVar _rules proof ->
                collectProof proof

        collectCase :: Case -> Set Marker
        collectCase Case{caseProof} =
            collectProof caseProof

        collectCalc :: Calc -> Set Marker
        collectCalc = \case
            RelationCalculation _expr steps ->
                foldMap
                    (collectJustification . calcRelationLinkJustification)
                    steps
            Biconditionals _formula steps ->
                foldMap (collectJustification . snd) steps

        collectJustification :: Justification -> Set Marker
        collectJustification = \case
            JustificationAuto markers ->
                foldMap (Set.fromList . toList) markers
            JustificationObviousReferences markers ->
                Set.fromList (toList markers)
            JustificationSetExt ->
                mempty
            JustificationStructureExt ->
                mempty
            JustificationExtensionality ->
                mempty
            JustificationImplicit ->
                mempty
            JustificationAssumption ->
                mempty
            JustificationDefinition ->
                mempty
            JustificationNotion ->
                mempty

collectReferencedMarkersOfDocument
    :: HtmlDocumentPresentation
    -> Set Marker
collectReferencedMarkersOfDocument (HtmlDocumentPresentation nodes) =
    foldMap collectNode nodes
  where
    collectNode = \case
        HtmlDocumentHeading _level _anchor inlines ->
            foldMap collectInline inlines
        HtmlDocumentParagraph inlines ->
            foldMap collectInline inlines
        HtmlDocumentDisplay{} ->
            mempty
        HtmlDocumentUnsupportedDisplay{} ->
            mempty
        HtmlDocumentFormalSlot{} ->
            mempty

    collectInline = \case
        HtmlPresentationEmphasis nested ->
            foldMap collectInline nested
        HtmlPresentationReference markers ->
            Set.fromList (toList markers)
        HtmlPresentationText{} ->
            mempty
        HtmlPresentationMath{} ->
            mempty
        HtmlPresentationMembership ->
            mempty
        HtmlPresentationPhrase{} ->
            mempty
        HtmlPresentationUnsupported{} ->
            mempty

data MissingHintSubject
    = MissingHintPresentationNode !HtmlDocumentNode
    | MissingHintFormalBlock !Block

collectMissingHints :: MissingHintSubject -> MissingHintCollection
collectMissingHints = \case
    MissingHintPresentationNode node -> collectNode node
    MissingHintFormalBlock block -> collectBlock block
    where
        noteMissingHint
            :: HintCategory
            -> Marker
            -> Int
            -> MissingHintCollection
        noteMissingHint category marker arity =
            noteMissingHintAt Nothing category marker arity

        noteMissingHintAt
            :: Maybe Location
            -> HintCategory
            -> Marker
            -> Int
            -> MissingHintCollection
        noteMissingHintAt occurrenceLocation category marker arity =
            MissingHintCollection \hints siteFor accumulator ->
                insertMissingRenderHint
                    (hasRenderHint category marker arity (renderEnvironmentHints hints))
                    category
                    marker
                    arity
                    (siteFor occurrenceLocation)
                    accumulator

        noteNotationHint location notation arity = MissingHintCollection \hints siteFor accumulator ->
            let (marker, present) = case renderEnvironmentNotationContracts hints of
                    Nothing -> (Contracts.notationMarker notation,
                        hasRenderHint (Contracts.notationCategory notation) (Contracts.notationMarker notation) arity (renderEnvironmentHints hints))
                    Just contracts -> (Contracts.notationContractMarker contracts notation,
                        Contracts.hasNotationContract contracts notation arity)
            in insertMissingRenderHint present (Contracts.notationCategory notation) marker arity (siteFor location) accumulator

        collectNode = \case
            HtmlDocumentHeading _level _anchor inlines ->
                foldMap collectInline inlines
            HtmlDocumentParagraph inlines ->
                foldMap collectInline inlines
            HtmlDocumentDisplay _slice value _punctuation ->
                collectPresentationMath value
            HtmlDocumentUnsupportedDisplay{} ->
                mempty
            HtmlDocumentFormalSlot{} ->
                mempty

        collectInline = \case
            HtmlPresentationEmphasis nested ->
                foldMap collectInline nested
            HtmlPresentationMath _slice value ->
                collectPresentationMath value
            HtmlPresentationText{} ->
                mempty
            HtmlPresentationMembership ->
                mempty
            HtmlPresentationPhrase _ phrase -> collectPhrase phrase
            HtmlPresentationReference{} ->
                mempty
            HtmlPresentationUnsupported{} ->
                mempty

        collectPhrase = \case
            ScopedPhrase binding _ -> noteNotationHint Nothing (Contracts.phraseNotation binding) 0
            DisplayPhrase name -> noteMissingHint PhraseHint (Marker name) 0

        collectPresentationMath = \case
            NativeMath value -> case value of
                Concrete.NativeTypedExpression expression -> collectTypedExpression expression
                Concrete.NativeConcreteType{} -> mempty
                Concrete.NativeVariableList{} -> mempty
            MathRow values -> foldMap collectPresentationMath values
            MathFenced _ value -> collectPresentationMath value
            MathScript base scripts ->
                collectPresentationMath base <> foldMap collectPresentationMath scripts
            MathPhrase phrase@ScopedPhrase{} -> collectPhrase phrase
            MathPhrase DisplayPhrase{} -> mempty
            MathIdentifier{} -> mempty
            MathNumber{} -> mempty
            MathOperator{} -> mempty
            MathNamedOperator{} -> mempty

        collectBlock :: Block -> MissingHintCollection
        collectBlock = \case
            BlockAxiom _loc _title _marker axiom ->
                collectAxiom axiom
            BlockClaim _kind _loc _title _marker claim ->
                collectClaim claim
            BlockProof _start proof _end ->
                collectProof proof
            BlockDefn _loc _title _marker defn ->
                collectDefn defn
            BlockAbbr _loc _title _marker abbr ->
                collectAbbreviation abbr
            BlockRecursive _loc _title _marker definition ->
                collectRecursiveDefinition definition
            BlockData _loc _title _marker datatype ->
                collectDatatype datatype
            BlockInductive _loc _title _marker ind ->
                collectInductive ind
            BlockSig _loc _title _marker asms sig ->
                collectAsms asms
                    <> collectSignature sig
            BlockStruct _loc _title _marker structDefn ->
                collectStructDefn structDefn
            BlockInstance _loc _title _marker Instance{..} ->
                foldMap collectTerm
                    (structApplicationArguments instanceApplication)
                    <> collectExpr instanceValue
            BlockConstruction _loc _title _marker Construction{..} ->
                collectAsms constructionAssumptions
                    <> foldMap collectTerm (structApplicationArguments constructionApplication)
                    <> collectSymbolPattern constructionHead
                    <> collectExpr constructionValue

        collectAxiom :: Axiom -> MissingHintCollection
        collectAxiom (Axiom asms stmt) =
            collectAsms asms <> collectStmt stmt

        collectClaim :: Claim -> MissingHintCollection
        collectClaim (Claim asms stmt) =
            collectAsms asms <> collectStmt stmt

        collectDefn :: Defn -> MissingHintCollection
        collectDefn = \case
            Defn asms defnHead stmt ->
                collectAsms asms
                    <> collectDefnHead defnHead
                    <> collectStmt stmt
            DefnFun asms _fun maybeTerm resultTerm maybeResult ->
                collectAsms asms
                    <> foldMap collectTerm maybeTerm
                    <> collectTerm resultTerm
                    <> foldMap collectNounPhraseNameless maybeResult
            DefnOp asms symb expr maybeResult ->
                collectAsms asms
                    <> collectSymbolPattern symb
                    <> collectExpr expr
                    <> foldMap collectNounPhraseNameless maybeResult
            DefnTypedConstant _loc _token _coreType body ->
                collectTypedExpression body

        collectDefnHead :: DefnHead -> MissingHintCollection
        collectDefnHead = \case
            DefnAdj _var _adj ->
                mempty
            DefnVerb _var _verb ->
                mempty
            DefnNoun _var noun ->
                collectVarNoun noun
            DefnSymbolicPredicate predi marker vars ->
                noteNotationHint Nothing (Contracts.predicateNotation predi marker) (length vars)
                    <> foldMap (collectExpr . ExprVar) vars
            DefnRel _x rel params _y ->
                noteNotationHint Nothing (Contracts.relationNotation rel) (length params)

        collectAbbreviation :: Abbreviation -> MissingHintCollection
        collectAbbreviation = \case
            AbbreviationAdj _var _adj stmt ->
                collectStmt stmt
            AbbreviationVerb _var _verb stmt ->
                collectStmt stmt
            AbbreviationNoun _var _noun stmt ->
                collectStmt stmt
            AbbreviationRel _x rel params _y stmt ->
                noteNotationHint Nothing (Contracts.relationNotation rel) (length params)
                    <> collectStmt stmt
            AbbreviationFun _fun bodyTerm ->
                collectTerm bodyTerm
            AbbreviationEq symb expr ->
                collectSymbolPattern symb
                    <> collectExpr expr

        collectRecursiveDefinition RecursiveDefinition{..} =
            collectAsms recursiveAssumptions
                <> either collectSymbolPattern collectDefnHead recursiveHead
                <> collectExpr recursiveDomain
                <> foldMap (either (\(a,b) -> collectExpr a <> collectExpr b)
                    (\(a,b) -> collectFormula a <> collectStmt b) . recursiveClauseEquation) recursiveClauses

        collectDatatype :: Datatype -> MissingHintCollection
        collectDatatype Datatype{..} =
            collectExpr datatypeHeadExpr
                <> foldMap collectDatatypeClause datatypeClauses

        collectDatatypeClause :: DatatypeClause -> MissingHintCollection
        collectDatatypeClause DatatypeClause{..} =
            collectExpr datatypeClauseConstructorExpr
                <> collectExpr datatypeClauseTargetExpr
                <> foldMap (collectExpr . snd) datatypeClausePremises

        collectInductive :: Inductive -> MissingHintCollection
        collectInductive Inductive{..} =
            collectSymbolPattern inductiveSymbolPattern
                <> collectExpr inductiveDomain
                <> foldMap collectIntroRule inductiveIntros

        collectIntroRule :: IntroRule -> MissingHintCollection
        collectIntroRule IntroRule{..} =
            foldMap collectFormula introConditions
                <> collectFormula introResult

        collectSignature :: Signature -> MissingHintCollection
        collectSignature = \case
            SignatureAdj _var adj ->
                collectVarAdj adj
            SignatureVerb _var verb ->
                collectVarVerb verb
            SignatureNoun _var noun ->
                collectVarNoun noun
            SignatureSymbolic symb np ->
                collectSymbolPattern symb
                    <> collectNounPhraseMaybe np
            SignatureTypedConstant{} ->
                mempty

        collectStructDefn :: StructDefn -> MissingHintCollection
        collectStructDefn StructDefn{..} =
            collectAsms structPreamble
                <> foldMap
                    (collectTerms . structApplicationArguments . structParentApplication)
                    structParents
                <> foldMap (collectStmt . snd) structAssumes

        collectProof :: Proof -> MissingHintCollection
        collectProof = \case
            Omitted _loc ->
                mempty
            Qed{} ->
                mempty
            Contradiction{} ->
                mempty
            ByCase _loc cases ->
                foldMap collectCase cases
            ByContradiction _loc proof ->
                collectProof proof
            BySetInduction _loc maybeTerm proof ->
                foldMap collectTerm maybeTerm
                    <> collectProof proof
            ByOrdInduction _loc proof ->
                collectProof proof
            ByStructuralInduction _loc _focus cases ->
                foldMap (collectProof . namedCaseProof) cases
            Assume _loc _intro stmt proof ->
                collectStmt stmt
                    <> collectProof proof
            Fix _loc binders condition proof ->
                foldMap collectFixBinder binders
                    <> foldMap collectStmt condition
                    <> collectProof proof
            Calc _loc maybeQuant calc proof ->
                foldMap collectCalcQuantifier maybeQuant
                    <> collectCalc calc
                    <> collectProof proof
            TakeVar _loc _vars bound stmt _justification proof ->
                collectBound bound
                    <> collectStmt stmt
                    <> collectProof proof
            TakeTyped _loc _vars _coreType stmt _justification proof ->
                collectStmt stmt
                    <> collectProof proof
            TakeNoun _loc np _justification proof ->
                collectNounPhraseList np
                    <> collectProof proof
            Have _loc _intro stmt _justification proof ->
                collectStmt stmt
                    <> collectProof proof
            Since
                    _premiseLoc premise _premiseJustification
                    _claimLoc claim _claimJustification proof ->
                collectStmt premise
                    <> collectStmt claim
                    <> collectProof proof
            Suffices _loc stmt _justification proof ->
                collectStmt stmt
                    <> collectProof proof
            Subclaim _loc stmt subproof proof ->
                collectStmt stmt
                    <> collectProof subproof
                    <> collectProof proof
            Define _loc _var expr proof ->
                collectExpr expr
                    <> collectProof proof
            DefineTyped _loc _var _coreType body proof ->
                collectTypedExpression body
                    <> collectProof proof
            DefineFunction _loc _fun _arg value _boundVar boundExpr proof ->
                collectExpr value
                    <> collectExpr boundExpr
                    <> collectProof proof
            DefineFunctionLocal _loc _fun _arg _target _domVar _codVar rules proof ->
                foldMap collectLocalFunctionRule rules
                    <> collectProof proof

        collectLocalFunctionRule :: (Expr, Formula) -> MissingHintCollection
        collectLocalFunctionRule (ruleTerm, formula) =
            collectExpr ruleTerm
                <> collectFormula formula

        collectCase :: Case -> MissingHintCollection
        collectCase Case{caseOf, caseProof} =
            collectStmt caseOf
                <> collectProof caseProof

        collectCalcQuantifier :: CalcQuantifier -> MissingHintCollection
        collectCalcQuantifier (CalcQuantifier _vars bound maybeStmt) =
            collectBound bound
                <> foldMap collectStmt maybeStmt

        collectFixBinder :: FixBinder -> MissingHintCollection
        collectFixBinder = \case
            FixBinderSymbolic _vars bound ->
                collectBound bound
            FixBinderTyped{} ->
                mempty

        collectCalc :: Calc -> MissingHintCollection
        collectCalc = \case
            RelationCalculation expr steps ->
                collectExpr expr
                    <> foldMap collectCalcRelationLink steps
            Biconditionals phi steps ->
                collectFormula phi
                    <> foldMap (collectFormula . fst) steps

        collectCalcRelationLink :: CalcRelationLink -> MissingHintCollection
        collectCalcRelationLink (CalcRelationLink _sign relation destination _justification) =
            collectCalculationRelation relation
                <> collectExpr destination

        collectCalculationRelation :: Relation -> MissingHintCollection
        collectCalculationRelation = \case
            Relation _location EqSymbol [] ->
                mempty
            relation ->
                collectRelation relation

        collectStmt :: Stmt -> MissingHintCollection
        collectStmt = \case
            StmtFormula phi ->
                collectFormula phi
            StmtVerbPhrase terms verbPhrase ->
                collectTerms terms
                    <> collectVerbPhrase verbPhrase
            StmtNoun _sign terms np ->
                collectTerms terms
                    <> collectNounPhraseMaybe np
            StmtStruct stmtTerm
                    (StructNounPhrase modifiers structure right residual) ->
                collectTerm stmtTerm
                    <> collectAdjLs modifiers
                    <> collectTerms
                        (structApplicationArguments structure)
                    <> collectAdjRs right
                    <> foldMap collectStmt residual
            StmtExactStruct stmtTerm structure ->
                collectTerm stmtTerm
                    <> collectTerms
                        (structApplicationArguments structure)
            StmtNeg _loc stmt ->
                collectStmt stmt
            StmtExists _loc np ->
                collectNounPhraseList np
            StmtConnected _conn _loc stmt1 stmt2 ->
                collectStmt stmt1
                    <> collectStmt stmt2
            StmtQuantPhrase _loc qp stmt ->
                collectQuantPhrase qp
                    <> collectStmt stmt
            SymbolicQuantified _loc _quant _vars bound suchThat stmt ->
                collectBound bound
                    <> foldMap collectStmt suchThat
                    <> collectStmt stmt

        collectQuantPhrase :: QuantPhrase -> MissingHintCollection
        collectQuantPhrase (QuantPhrase _quant np) =
            collectNounPhraseList np

        collectAsm :: Asm -> MissingHintCollection
        collectAsm = \case
            AsmSuppose stmt ->
                collectStmt stmt
            AsmLetNoun _vars np ->
                collectNounPhraseMaybe np
            AsmLetIn _vars expr ->
                collectExpr expr
            AsmLetRelation _vars relation expr ->
                collectRelation relation <> collectExpr expr
            AsmLetThe _var fun ->
                collectFun fun
            AsmLetEq _var expr ->
                collectExpr expr
            AsmLetStruct _variables
                    (StructNounPhrase modifiers structure right residual) ->
                collectAdjLs modifiers
                    <> collectTerms
                    (structApplicationArguments structure)
                    <> collectAdjRs right
                    <> foldMap collectStmt residual

        collectTerm :: Term -> MissingHintCollection
        collectTerm = \case
            TermExpr expr ->
                collectExpr expr
            TermFun fun ->
                collectFun fun
            TermIota _loc _var stmt ->
                collectStmt stmt
            TermQuantified _quant _loc np ->
                collectNounPhraseMaybe np

        collectNounPhraseMaybe :: NounPhrase Maybe -> MissingHintCollection
        collectNounPhraseMaybe (NounPhrase ls noun (NounBinder _maybeName bound) rs maybeSuchThat) =
            collectAdjLs ls
                <> collectNoun noun
                <> collectBound bound
                <> collectAdjRs rs
                <> foldMap collectStmt maybeSuchThat

        collectNounPhraseList :: NounPhrase [] -> MissingHintCollection
        collectNounPhraseList (NounPhrase ls noun (NounBinder _names bound) rs maybeSuchThat) =
            collectAdjLs ls
                <> collectNoun noun
                <> collectBound bound
                <> collectAdjRs rs
                <> foldMap collectStmt maybeSuchThat

        collectNounPhraseNameless
            :: NounPhrase Nameless
            -> MissingHintCollection
        collectNounPhraseNameless
                (NounPhrase ls noun (NounBinder Nameless bound) rs maybeSuchThat) =
            collectAdjLs ls
                <> collectNoun noun
                <> collectBound bound
                <> collectAdjRs rs
                <> foldMap collectStmt maybeSuchThat

        collectAdjL :: AdjLOf Term -> MissingHintCollection
        collectAdjL (AdjL _loc _item args) =
            collectTerms args

        collectAdjR :: AdjROf Term -> MissingHintCollection
        collectAdjR = \case
            AdjR _loc _item args ->
                collectTerms args
            AttrRThat verbPhrase ->
                collectVerbPhrase verbPhrase

        collectAdj :: AdjOf Term -> MissingHintCollection
        collectAdj (Adj _loc _item args) =
            collectTerms args

        collectVarAdj :: AdjOf VarSymbol -> MissingHintCollection
        collectVarAdj _adj =
            mempty

        collectVerb :: VerbOf Term -> MissingHintCollection
        collectVerb (Verb _loc _item args) =
            collectTerms args

        collectVarVerb :: VerbOf VarSymbol -> MissingHintCollection
        collectVarVerb _verb =
            mempty

        collectVerbPhrase :: VerbPhrase -> MissingHintCollection
        collectVerbPhrase = \case
            VPVerb verb ->
                collectVerb verb
            VPAdj adjs ->
                foldMap collectAdj adjs
            VPVerbNot verb ->
                collectVerb verb
            VPAdjNot adjs ->
                foldMap collectAdj adjs

        collectNoun :: NounOf Term -> MissingHintCollection
        collectNoun (Noun _loc _item args) =
            collectTerms args

        collectVarNoun :: NounOf VarSymbol -> MissingHintCollection
        collectVarNoun _noun =
            mempty

        collectFun :: FunOf Term -> MissingHintCollection
        collectFun Fun{funArgs} =
            collectTerms funArgs

        collectBound :: Bound -> MissingHintCollection
        collectBound = \case
            Unbounded ->
                mempty
            Bounded _loc _sign rel expr ->
                collectRelation rel
                    <> collectExpr expr

        collectFormula :: Formula -> MissingHintCollection
        collectFormula = \case
            FormulaChain chain ->
                collectChain chain
            FormulaSetMap _location function domain codomain ->
                collectExpr function
                    <> collectExpr domain
                    <> collectExpr codomain
            FormulaExpression expr ->
                collectExpr expr
            FormulaPredicate loc predi marker exprs ->
                noteNotationHint (Just loc) (Contracts.predicateNotation predi marker) (length exprs)
                    <> collectExprs exprs
            Connected _loc _conn phi psi ->
                collectFormula phi
                    <> collectFormula psi
            FormulaNeg _loc phi ->
                collectFormula phi
            FormulaQuantified _loc _quant _vars bound phi ->
                collectBound bound
                    <> collectFormula phi
            FormulaTypedQuantified _loc _quant _vars _coreType phi ->
                collectFormula phi
            PropositionalConstant{} ->
                mempty

        collectChain :: Chain -> MissingHintCollection
        collectChain = \case
            ChainBase lhs _sign rel rhs ->
                collectExprs lhs
                    <> collectRelation rel
                    <> collectExprs rhs
            ChainCons lhs _sign rel chain ->
                collectExprs lhs
                    <> collectRelation rel
                    <> collectChain chain

        collectRelation :: Relation -> MissingHintCollection
        collectRelation = \case
            Relation loc symbol relParams ->
                noteNotationHint (Just loc) (Contracts.relationNotation symbol) (length relParams)
                    <> collectExprs relParams
            RelationExpr _loc expr ->
                collectExpr expr

        collectExpr :: Expr -> MissingHintCollection
        collectExpr = \case
            ExprVar{} ->
                mempty
            ExprNaturalNumeral{} ->
                mempty
            ExprOpaqueInteger{} ->
                mempty
            ExprTypedConstant{} ->
                mempty
            ExprHigherApply _loc function argument ->
                collectTypedExpression function
                    <> collectTypedExpression argument
            ExprLambda _loc _variables _coreType body ->
                collectTypedExpression body
            ExprSelect _loc _maybeCoreType predicate ->
                collectTypedExpression predicate
            ExprOp loc item args ->
                noteNotationHint (Just loc) (Contracts.operatorNotation item) (length args)
                    <> collectExprs args
            ExprStructOp loc symb maybeExpr ->
                noteNotationHint (Just loc) (Contracts.fieldNotation symb maybeExpr)
                    (length (maybeToList maybeExpr))
                    <> foldMap collectExpr maybeExpr
            ExprFiniteSet _loc exprs ->
                collectExprs exprs
            ExprSep _loc _var boundExpr stmt ->
                collectExpr boundExpr
                    <> collectStmt stmt
            ExprReplace _loc expr bounds maybeStmt ->
                collectExpr expr
                    <> foldMap (collectExpr . snd) bounds
                    <> foldMap collectStmt maybeStmt
            ExprReplacePred _loc _rangeVar _domVar domExpr stmt ->
                collectExpr domExpr
                    <> collectStmt stmt
            ExprStructAggregate _loc maybeSchema entries ->
                foldMap
                    (\(StructApplication _phrase arguments) ->
                        collectExprs arguments)
                    maybeSchema
                    <> foldMap
                        (collectExpr . structAggregateEntryExpression)
                        entries
            ExprStructReduct _loc schema record ->
                let StructApplication _phrase arguments = schema
                in collectExprs arguments <> collectExpr record
            ExprStructReconstruction _loc (StructApplication _ arguments) record entries ->
                collectExprs arguments <> collectExpr record
                    <> foldMap (collectExpr . structAggregateEntryExpression) entries

        collectTypedExpression :: TypedExpression -> MissingHintCollection
        collectTypedExpression = \case
            TypedExpressionExpr expr -> collectExpr expr
            TypedExpressionFormula phi -> collectFormula phi

        collectSymbolPattern :: SymbolPattern -> MissingHintCollection
        collectSymbolPattern (SymbolPattern symbol vars) =
            noteNotationHint Nothing (Contracts.operatorNotation symbol) (length vars)

        collectAsms :: [Asm] -> MissingHintCollection
        collectAsms =
            foldMap collectAsm

        collectTerms :: Foldable t => t Term -> MissingHintCollection
        collectTerms =
            foldMap collectTerm

        collectAdjLs :: [AdjLOf Term] -> MissingHintCollection
        collectAdjLs =
            foldMap collectAdjL

        collectAdjRs :: [AdjROf Term] -> MissingHintCollection
        collectAdjRs =
            foldMap collectAdjR

        collectExprs :: Foldable t => t Expr -> MissingHintCollection
        collectExprs =
            foldMap collectExpr

insertMissingRenderHint
    :: Bool
    -> HintCategory
    -> Marker
    -> Int
    -> HintOccurrenceSite
    -> MissingHintAccumulator
    -> MissingHintAccumulator
insertMissingRenderHint present category marker arity site accumulator
    | present = accumulator
    | Map.member key seen = accumulator
    | otherwise =
        MissingHintAccumulator
            (Map.insert key () seen)
            (ordered Seq.|> MissingRenderHint category marker arity site)
  where
    key = (category, marker, arity)
    MissingHintAccumulator seen ordered = accumulator

collectMissingRenderHintsChecked
    :: RenderHints
    -> [HtmlPagePresentation]
    -> Either
        (ResolvedSource, HtmlDocumentProjectionError)
        [MissingRenderHint]
collectMissingRenderHintsChecked hints pages = do
    MissingHintAccumulator _seen ordered <-
        foldM collectPage emptyAccumulator pages
    pure (toList ordered)
  where
    emptyAccumulator = MissingHintAccumulator Map.empty Seq.empty

    collectPage accumulator HtmlPagePresentation
            { htmlPagePresentationSource = source
            , pagePresentationBlockInfos = blockInfos
            , pagePresentationNotationContracts = contracts
            , pagePresentationStructureSchemas = schemas
            , pagePresentationDocument = HtmlDocumentPresentation nodes
            } =
        foldM (collectNode (RenderEnvironment hints contracts schemas Map.empty) source blockInfos) accumulator nodes

    collectNode environment source blockInfos accumulator node =
        case node of
            HtmlDocumentFormalSlot ordinal -> do
                (blockIndex, block, _blockId) <-
                    maybe
                        (Left
                            ( source
                            , HtmlDocumentFormalSlotMismatch
                                ordinal
                                "the aligned formal block is unavailable during render-hint analysis"
                            ))
                        Right
                        (oneBasedIndex ordinal >>= (`nth` blockInfos))
                unless (blockIndex == ordinal)
                    (Left
                        ( source
                        , HtmlDocumentFormalSlotMismatch
                            ordinal
                            "the aligned formal block has a different ordinal during render-hint analysis"
                        ))
                pure
                    (runMissingHintCollection
                        (collectMissingHints (MissingHintFormalBlock block))
                        environment
                        (\occurrenceLocation ->
                            HintOccurrenceSite
                                source
                                (occurrenceLocation <|> Just (locate block)))
                        accumulator)
            _ ->
                pure
                    (runMissingHintCollection
                        (collectMissingHints
                            (MissingHintPresentationNode node))
                        environment
                        (const (HintOccurrenceSite source Nothing))
                        accumulator)

renderMissingRenderHintDiagnostics
    :: DiagnosticSeverity
    -> [MissingRenderHint]
    -> [Diagnostic]
renderMissingRenderHintDiagnostics severity =
    fmap renderMissing
  where
    renderMissing (MissingRenderHint category marker arity site) =
        Diagnostic
            { diagnosticSeverity = severity
            , diagnosticCode = DiagnosticHtmlMissingRenderHint
            , diagnosticTitle = "HTML render hint is missing"
            , diagnosticPrimary = hintOccurrenceLocation site
            , diagnosticMessage =
                pretty
                    ( "No " <> hintCategoryLabel category
                        <> " render hint is defined for marker \""
                        <> markerText marker
                        <> "\" at arity " <> Text.pack (show arity)
                        <> "; fallback notation is used."
                    )
            , diagnosticNotes =
                case hintOccurrenceLocation site of
                    Just _location -> []
                    Nothing ->
                        [ pretty
                            ("source: "
                                <> renderMissingHintSource
                                    (hintOccurrenceSource site))
                        ]
            , diagnosticHelp = []
            }

renderMissingHintSource :: ResolvedSource -> Text
renderMissingHintSource source =
    sourceMountIdText (resolvedSourceMount source)
        <> ":"
        <> Text.pack
            (safeRelativePathFilePath
                (resolvedSourceRelativePath source))

missingRenderHintDiagnostics
    :: RenderHints
    -> [HtmlPagePresentation]
    -> [Diagnostic]
missingRenderHintDiagnostics hints pages =
    case collectMissingRenderHintsChecked hints pages of
        Right missing ->
            renderMissingRenderHintDiagnostics DiagnosticWarning missing
        Left (source, failure) ->
            impossible
                ( "aligned HTML presentation failed render-hint analysis for "
                    <> Text.unpack (renderMissingHintSource source)
                    <> ": "
                    <> Text.unpack
                        (renderHtmlDocumentProjectionError failure)
                )


renderBlock :: RenderEnvironment -> ReferenceContext -> BlockRenderInfo -> Html ()
renderBlock hints references (_index, block, blockId) = case block of
    BlockAxiom _loc title marker axiom ->
        renderSourceBlock (Just marker) title (renderAxiom hints axiom)
    BlockClaim _kind _loc title marker claim ->
        renderSourceBlock (Just marker) title (renderClaim hints claim)
    BlockProof _start proof _end ->
        renderProofBlock hints references proof
    BlockDefn _loc title marker defn ->
        renderSourceBlock (Just marker) title (renderDefn hints defn)
    BlockAbbr _loc title marker abbr ->
        renderSourceBlock (Just marker) title (renderAbbreviation hints abbr)
    BlockRecursive _loc title marker definition ->
        renderSourceBlock (Just marker) title (renderRecursiveDefinition hints definition)
    BlockData _loc title marker datatype ->
        renderSourceBlock (Just marker) title (renderDatatype hints datatype)
    BlockInductive _loc title marker ind ->
        renderSourceBlock (Just marker) title (renderInductive hints marker ind)
    BlockSig _loc title marker asms sig ->
        renderSourceBlock (Just marker) title (renderSignatureBlock hints asms sig)
    BlockStruct _loc title marker structDefn ->
        renderSourceBlock (Just marker) title (renderStructDefn hints structDefn)
    BlockInstance _loc title marker instanceDefn ->
        renderSourceBlock (Just marker) title do
            renderInstance hints instanceDefn
            renderPublicConsequences hints marker
    BlockConstruction _loc title marker construction ->
        renderSourceBlock (Just marker) title do
            renderConstruction hints construction
            renderPublicConsequences hints marker
  where
    presentationKind = blockPresentationKind block
    kindLabel = blockPresentationKindLabel presentationKind
    renderSourceBlock =
        renderCustomBlock
            blockId
            (blockPresentationKindElement presentationKind)
            kindLabel

data DocumentOutlineEntry = DocumentOutlineEntry
    !DocumentOutlineItem
    ![DocumentOutlineEntry]

data DocumentOutlineItem
    = DocumentOutlineHeading !Text ![HtmlPresentationInline]
    | DocumentOutlineDeclaration !Int !Text !Block

buildDocumentOutline
    :: HtmlDocumentPresentation
    -> [BlockRenderInfo]
    -> [DocumentOutlineEntry]
buildDocumentOutline (HtmlDocumentPresentation nodes) blockInfos =
    foldl' insertFlat [] (snd (mapAccumL flatten Nothing nodes))
  where
    flatten currentLevel = \case
        HtmlDocumentHeading level anchor title ->
            let depth = headingLevelNumber level - 1
            in (Just (headingLevelNumber level),
                Just (depth, DocumentOutlineHeading anchor title))
        HtmlDocumentFormalSlot ordinal ->
            case oneBasedIndex ordinal >>= (`nth` blockInfos) of
                Just (index, block, blockId)
                    | includeInToc block ->
                        (currentLevel,
                            Just
                                ( fromMaybe 0 currentLevel
                                , DocumentOutlineDeclaration index blockId block
                                ))
                _ -> (currentLevel, Nothing)
        _ -> (currentLevel, Nothing)

    insertFlat outline Nothing = outline
    insertFlat outline (Just (depth, item)) =
        insertOutlineEntry depth (DocumentOutlineEntry item []) outline

insertOutlineEntry
    :: Int
    -> DocumentOutlineEntry
    -> [DocumentOutlineEntry]
    -> [DocumentOutlineEntry]
insertOutlineEntry depth entry outline
    | depth <= 0 = outline <> [entry]
    | otherwise =
        case reverse outline of
            [] -> [entry]
            DocumentOutlineEntry parent children : preceding ->
                reverse preceding
                    <> [ DocumentOutlineEntry parent
                            (insertOutlineEntry (depth - 1) entry children)
                       ]

renderOutlineEntry :: RenderEnvironment -> DocumentOutlineEntry -> Html ()
renderOutlineEntry hints (DocumentOutlineEntry item children) =
    li_ do
        case item of
            DocumentOutlineHeading anchor title ->
                a_ [href_ (renderUrlFragment anchor), class_ "toc-section-link"]
                    (renderPresentationInlinesPlain hints title)
            DocumentOutlineDeclaration index blockId block ->
                renderTocEntryContents index blockId block
        unless (null children)
            (ol_ [class_ "toc-list toc-list-nested"]
                (traverse_ (renderOutlineEntry hints) children))

renderTocEntryContents :: Int -> Text -> Block -> Html ()
renderTocEntryContents index blockId block =
    a_ [href_ (renderUrlFragment blockId)] do
        case formatMarker (blockMarkerOf block) of
            Nothing ->
                when (blockNeedsIndexLabel block)
                    (code_ (toHtml (Text.pack (show index))))
            Just marker -> code_ (toHtml marker)
        small_ [class_ "toc-kind"]
            (toHtml (blockPresentationKindLabel
                (blockPresentationKind block)))

renderDocumentPresentation
    :: RenderEnvironment
    -> ReferenceContext
    -> [BlockRenderInfo]
    -> HtmlDocumentPresentation
    -> Html ()
renderDocumentPresentation hints references blockInfos
        (HtmlDocumentPresentation nodes) =
    traverse_ renderNode nodes
  where
    renderNode = \case
        HtmlDocumentHeading level anchor title ->
            case level of
                DocumentSection ->
                    h2_ [id_ anchor]
                        (renderPresentationInlines hints references title)
                DocumentSubsection ->
                    h3_ [id_ anchor]
                        (renderPresentationInlines hints references title)
                DocumentSubsubsection ->
                    h4_ [id_ anchor]
                        (renderPresentationInlines hints references title)
        HtmlDocumentParagraph inlines ->
            p_ [class_ "narrative"]
                (renderPresentationInlines hints references inlines)
        HtmlDocumentDisplay _slice value punctuation ->
            div_ [class_ "narrative-math"]
                (blockMath do
                    renderPresentationMath hints value
                    traverse_ moText punctuation)
        HtmlDocumentUnsupportedDisplay source ->
            pre_ [class_ "unsupported-commentary"] (code_ (toHtml source))
        HtmlDocumentFormalSlot ordinal ->
            case oneBasedIndex ordinal >>= (`nth` blockInfos) of
                Nothing -> impossible "HTML document has an invalid formal slot"
                Just blockInfo -> renderBlock hints references blockInfo

renderPresentationInlines
    :: RenderEnvironment
    -> ReferenceContext
    -> [HtmlPresentationInline]
    -> Html ()
renderPresentationInlines hints references = traverse_ \case
    HtmlPresentationText text -> toHtml text
    HtmlPresentationEmphasis nested ->
        em_ (renderPresentationInlines hints references nested)
    HtmlPresentationMath _slice value ->
        inlineMath (renderPresentationMath hints value)
    HtmlPresentationMembership -> inlineMath (moText "∈")
    HtmlPresentationPhrase _ phrase ->
        renderPresentationPhrase hints phrase
    HtmlPresentationReference markers ->
        renderMarkerReferences
            CommentaryReference
            references
            (toList markers)
    HtmlPresentationUnsupported source ->
        code_ [class_ "unsupported-commentary"] (toHtml source)

renderPresentationInlinesPlain
    :: RenderEnvironment
    -> [HtmlPresentationInline]
    -> Html ()
renderPresentationInlinesPlain hints = traverse_ \case
    HtmlPresentationText text ->
        toHtml text
    HtmlPresentationEmphasis nested ->
        em_ (renderPresentationInlinesPlain hints nested)
    HtmlPresentationMath _slice value ->
        inlineMath (renderPresentationMath hints value)
    HtmlPresentationMembership ->
        inlineMath (moText "∈")
    HtmlPresentationPhrase _ phrase ->
        renderPresentationPhrase hints phrase
    HtmlPresentationReference markers ->
        joinHtml
            (toHtml (", " :: Text))
            (toHtml . markerText <$> toList markers)
    HtmlPresentationUnsupported source ->
        code_ [class_ "unsupported-commentary"] (toHtml source)

renderPresentationMath :: RenderEnvironment -> CommentaryMath -> Html ()
renderPresentationMath hints = \case
    NativeMath value -> renderNativeMath hints value
    MathIdentifier text -> miText text
    MathNumber text -> mn_ (toHtml text)
    MathOperator role text ->
        mo_ [makeAttributes "form" (case role of
            PrefixOperator -> "prefix"
            InfixOperator -> "infix"
            SeparatorOperator -> "infix")] (toHtml text)
    MathRow values -> mrow_ (traverse_ (renderPresentationMath hints) values)
    MathFenced fence value -> mrow_ do
        let (opening, closing) = case fence of
                RoundFence -> ("(", ")")
                SquareFence -> ("[", "]")
                CurlyFence -> ("{", "}")
        moText opening
        renderPresentationMath hints value
        moText closing
    MathScript base scripts ->
        let baseNode = renderPresentationMathNode hints base
            argument = renderPresentationMathNode hints
        in case scripts of
            Subscript lower -> msub_ (baseNode *> argument lower)
            Superscript upper -> msup_ (baseNode *> argument upper)
            SubSuperscript lower upper -> msubsup_ (baseNode *> argument lower *> argument upper)
    MathNamedOperator style name ->
        mi_ [mathvariant_ (case style of
            UprightOperator -> "normal"
            SansSerifOperator -> "sans-serif")] (toHtml name)
    MathPhrase phrase -> renderPhraseMath hints phrase

-- Templates and native rendering may emit siblings even from a single literal.
renderPresentationMathNode :: RenderEnvironment -> CommentaryMath -> Html ()
renderPresentationMathNode hints value = case value of
    NativeMath{} -> mrow_ (renderPresentationMath hints value)
    MathPhrase{} -> mrow_ (renderPresentationMath hints value)
    _ -> renderPresentationMath hints value

renderNativeMath :: RenderEnvironment -> Concrete.NativeMath -> Html ()
renderNativeMath hints = \case
    Concrete.NativeTypedExpression value -> renderTypedExpressionMath hints value
    Concrete.NativeConcreteType coreType -> renderConcreteTypeMath coreType
    Concrete.NativeVariableList variables ->
        joinHtml (moText ",") (renderNamedVariableMath <$> toList variables)

renderPresentationPhrase :: RenderEnvironment -> PhraseUse -> Html ()
renderPresentationPhrase hints phrase = inlineMath (renderPhraseMath hints phrase)

renderPhraseMath :: RenderEnvironment -> PhraseUse -> Html ()
renderPhraseMath hints phrase = case phrase of
    ScopedPhrase binding _ -> renderNotationMath False hints (Contracts.phraseNotation binding) [] fallback
    DisplayPhrase{} -> renderHintedMath hints PhraseHint (phraseMarker phrase) [] fallback
  where
    fallback = merror_ (miText (phraseName phrase))

includeInToc :: Block -> Bool
includeInToc = \case
    BlockProof{} -> False
    _ -> True

renderCustomBlock :: Text -> Text -> Text -> Maybe Marker -> Maybe BlockTitle -> Html () -> Html ()
renderCustomBlock blockId name prefix mmarker mtitle body =
    term name (id_ blockId : previewTargetAttributes prefix mmarker mtitle) do
        renderBlockLead prefix mmarker mtitle True
        body

previewTargetAttributes :: Text -> Maybe Marker -> Maybe BlockTitle -> [Attributes]
previewTargetAttributes prefix mmarker mtitle =
    case formatMarker mmarker of
        Nothing ->
            []
        Just marker ->
            [ makeAttributes "data-preview-kind" prefix
            , makeAttributes "data-preview-label" marker
            ]
            <> case formatBlockTitle mtitle of
                Nothing ->
                    []
                Just title ->
                    [makeAttributes "data-preview-title" title]

renderProofBlock :: RenderEnvironment -> ReferenceContext -> Proof -> Html ()
renderProofBlock hints references proof
    | proofStepCount proof >= proofCollapseThreshold =
        term "proof-" do
            details_ do
                summary_ (renderBlockLead "Proof" Nothing Nothing False)
                renderProof hints references proof
    | otherwise =
        term "proof-" do
            renderBlockLead "Proof" Nothing Nothing True
            renderProof hints references proof

blockAnchorId :: Int -> Block -> Text
blockAnchorId index block =
    case formatMarker (blockMarkerOf block) of
        Just marker -> marker
        Nothing -> sanitizeIdFragment (Text.toLower (blockPrefixText block) <> "-" <> Text.pack (show index))

sanitizeIdFragment :: Text -> Text
sanitizeIdFragment =
    Text.dropWhile (== '-') . Text.map sanitize . Text.toLower
    where
        sanitize c
            | isAlphaNum c = c
            | c == '-' || c == '_' = c
            | otherwise = '-'

blockPrefixText :: Block -> Text
blockPrefixText =
    blockPresentationKindLabel . blockPresentationKind

blockMarkerOf :: Block -> Maybe Marker
blockMarkerOf = \case
    BlockAxiom _ _ marker _ -> Just marker
    BlockClaim _ _ _ marker _ -> Just marker
    BlockProof{} -> Nothing
    BlockDefn _ _ marker _ -> Just marker
    BlockAbbr _ _ marker _ -> Just marker
    BlockRecursive _ _ marker _ -> Just marker
    BlockData _ _ marker _ -> Just marker
    BlockInductive _ _ marker _ -> Just marker
    BlockSig _ _ marker _ _ -> Just marker
    BlockStruct _ _ marker _ -> Just marker
    BlockInstance _ _ marker _ -> Just marker
    BlockConstruction _ _ marker _ -> Just marker

blockTitleOf :: Block -> Maybe BlockTitle
blockTitleOf = \case
    BlockAxiom _ title _ _ -> title
    BlockClaim _ _ title _ _ -> title
    BlockProof{} -> Nothing
    BlockDefn _ title _ _ -> title
    BlockAbbr _ title _ _ -> title
    BlockRecursive _ title _ _ -> title
    BlockData _ title _ _ -> title
    BlockInductive _ title _ _ -> title
    BlockSig _ title _ _ _ -> title
    BlockStruct _ title _ _ -> title
    BlockInstance _ title _ _ -> title
    BlockConstruction _ title _ _ -> title

blockNeedsIndexLabel :: Block -> Bool
blockNeedsIndexLabel block = case (formatMarker (blockMarkerOf block), formatBlockTitle (blockTitleOf block)) of
    (Nothing, Nothing) -> True
    _ -> False

renderBlockLead :: Text -> Maybe Marker -> Maybe BlockTitle -> Bool -> Html ()
renderBlockLead prefix mmarker mtitle withTrailingSpace =
    term "head-" do
        toHtml prefix
        case formatBlockTitle mtitle of
            Just title -> do
                toHtml (" (" :: Text)
                term "title-" (toHtml title)
                toHtml (")." <> suffix)
            Nothing -> do
                case formatMarker mmarker of
                    Nothing -> skip
                    Just marker ->
                        term "id-" (toHtml marker)
                toHtml ("." <> suffix)
    where
        suffix :: Text
        suffix
            | withTrailingSpace = " "
            | otherwise = ""

formatMarker :: Maybe Marker -> Maybe Text
formatMarker = \case
    Nothing -> Nothing
    Just marker ->
        let text = Text.strip (markerText marker)
        in if Text.null text then Nothing else Just text

formatBlockTitle :: Maybe BlockTitle -> Maybe Text
formatBlockTitle =
    fmap capitalizeTitle . nonEmptyTitle
    where
        nonEmptyTitle = \case
            Nothing -> Nothing
            Just toks ->
                let text = Text.strip (Text.unwords (tokToText <$> toks))
                in if Text.null text then Nothing else Just text

capitalizeTitle :: Text -> Text
capitalizeTitle text = case Text.uncons text of
    Nothing -> text
    Just (c, rest) -> Text.cons (toUpper c) rest

renderAxiom :: RenderEnvironment -> Axiom -> Html ()
renderAxiom hints (Axiom asms stmt) =
    renderWithAssumptions hints asms stmt

renderClaim :: RenderEnvironment -> Claim -> Html ()
renderClaim hints (Claim asms stmt) =
    renderWithAssumptions hints asms stmt

renderWithAssumptions :: RenderEnvironment -> [Asm] -> Stmt -> Html ()
renderWithAssumptions hints asms stmt = do
    case asms of
        [] -> renderStmtInline hints stmt
        _ -> do
            traverse_ (renderAsmSentence hints) asms
            toHtml ("Then " :: Text)
            renderStmtInline hints stmt
    toHtml ("." :: Text)

renderAsmSentence :: RenderEnvironment -> Asm -> Html ()
renderAsmSentence hints asm = do
    case asm of
        AsmSuppose stmt -> do
            toHtml ("Suppose " :: Text)
            renderStmtInline hints stmt
        AsmLetIn vars expr -> do
            toHtml ("Let " :: Text)
            inlineMath do
                renderVarListMath vars
                moText "∈"
                renderExprMathRow hints expr
        AsmLetRelation vars relation expr -> do
            toHtml ("Let " :: Text)
            inlineMath
                (renderRelationApplication
                    hints Positive
                    (ExprVar <$> toList vars)
                    relation
                    [expr])
        _ -> do
            toHtml ("Let " :: Text)
            renderAsm hints asm
    toHtml (". " :: Text)

renderDefn :: RenderEnvironment -> Defn -> Html ()
renderDefn hints = \case
    Defn asms headStmt stmt ->
        do
            when (not (null asms)) do
                toHtml ("If " :: Text)
                renderAsmList hints asms
                toHtml (", then " :: Text)
            renderDefnHead hints headStmt
            toHtml (" iff " :: Text)
            renderStmtInline hints stmt
            toHtml ("." :: Text)
    DefnFun asms fun maybeSymbol resultTerm maybeResult ->
        do
            when (not (null asms)) do
                toHtml ("If " :: Text)
                renderAsmList hints asms
                toHtml (", then " :: Text)
            renderFunInline hints renderVarInline fun
            case maybeSymbol of
                Nothing -> skip
                Just symbolicTerm -> do
                    toHtml (", " :: Text)
                    renderTermInline hints symbolicTerm
            toHtml (" is " :: Text)
            renderTermInline hints resultTerm
            traverse_ (renderDefinitionResultPhrase hints) maybeResult
            toHtml ("." :: Text)
    DefnOp asms symb expr maybeResult ->
        do
            when (not (null asms)) do
                toHtml ("If " :: Text)
                renderAsmList hints asms
                toHtml (", then " :: Text)
            inlineMath do
                renderSymbolPatternMath hints symb
                moText "="
                renderExprMathRow hints expr
            traverse_ (renderDefinitionResultPhrase hints) maybeResult
            toHtml ("." :: Text)
    DefnTypedConstant _loc token coreType body ->
        do
            inlineMath do
                renderMathToken token
                moText ":"
                renderConcreteTypeMath coreType
                moText "="
                renderTypedExpressionMath hints body
            toHtml ("." :: Text)

renderDefnHead :: RenderEnvironment -> DefnHead -> Html ()
renderDefnHead hints = \case
    DefnAdj var adj -> do
        renderVarInline var
        toHtml (" is " :: Text)
        renderAdjInline hints renderVarInline adj
    DefnVerb var verb -> do
        renderVarInline var
        toHtml (" " :: Text)
        renderVerbInline hints False renderVarInline verb
    DefnNoun var noun -> do
        renderVarInline var
        toHtml (" is a " :: Text)
        renderNounInline hints False renderVarInline noun
    DefnSymbolicPredicate predi marker vars ->
        inlineMath
            ( renderNotationMath True
                hints
                (Contracts.predicateNotation predi marker)
                (ExprVar <$> toList vars)
                (renderPrefixPredicateFallback predi (renderVarMath <$> toList vars))
            )
    DefnRel x rel params y ->
        inlineMath (renderRelationApplication hints Positive [ExprVar x] (Relation Nowhere rel [ExprVar p | p <- params]) [ExprVar y])

renderAbbreviation :: RenderEnvironment -> Abbreviation -> Html ()
renderAbbreviation hints = \case
    AbbreviationAdj var adj stmt ->
        do
            renderVarInline var
            toHtml (" is " :: Text)
            renderAdjInline hints renderVarInline adj
            toHtml (" stands for " :: Text)
            renderStmtInline hints stmt
            toHtml ("." :: Text)
    AbbreviationVerb var verb stmt ->
        do
            renderVarInline var
            toHtml (" " :: Text)
            renderVerbInline hints False renderVarInline verb
            toHtml (" stands for " :: Text)
            renderStmtInline hints stmt
            toHtml ("." :: Text)
    AbbreviationNoun var noun stmt ->
        do
            renderVarInline var
            toHtml (" is a " :: Text)
            renderNounInline hints False renderVarInline noun
            toHtml (" stands for " :: Text)
            renderStmtInline hints stmt
            toHtml ("." :: Text)
    AbbreviationRel x rel params y stmt ->
        do
            inlineMath (renderRelationApplication hints Positive [ExprVar x] (Relation Nowhere rel [ExprVar p | p <- params]) [ExprVar y])
            toHtml (" stands for " :: Text)
            renderStmtInline hints stmt
            toHtml ("." :: Text)
    AbbreviationFun fun bodyTerm ->
        do
            renderFunInline hints renderVarInline fun
            toHtml (" stands for " :: Text)
            renderTermInline hints bodyTerm
            toHtml ("." :: Text)
    AbbreviationEq symb expr ->
        do
            renderSymbolPatternInline hints symb
            toHtml (" stands for " :: Text)
            inlineMath (renderExprMathRow hints expr)
            toHtml ("." :: Text)

renderRecursiveDefinition :: RenderEnvironment -> RecursiveDefinition -> Html ()
renderRecursiveDefinition hints RecursiveDefinition{..} = do
    traverse_ (renderAsmSentence hints) recursiveAssumptions
    toHtml ("Define " :: Text)
    either (renderSymbolPatternInline hints) (renderDefnHead hints) recursiveHead
    toHtml (" recursively for " :: Text)
    inlineMath (renderRelationApplication hints Positive [ExprVar recursiveVariable]
        (Relation Nowhere ElementSymbol []) [recursiveDomain])
    toHtml (" as follows." :: Text)
    ul_ $ for_ recursiveClauses \RecursiveClause{..} -> li_ do
        for_ recursiveClauseName (\name -> strong_ (toHtml (Text.strip name <> ". ")))
        case recursiveClauseEquation of
            Left (left,right) -> inlineMath do
                renderExprMathRow hints left
                moText "="
                renderExprMathRow hints right
            Right (left,right) -> do
                inlineMath (renderFormulaMath hints left)
                toHtml (" iff " :: Text)
                renderStmtInline hints right
        toHtml ("." :: Text)

renderDatatype :: RenderEnvironment -> Datatype -> Html ()
renderDatatype hints Datatype{..} = do
    toHtml ("Datatype of " :: Text)
    inlineMath (renderExprMathRow hints datatypeHeadExpr)
    toHtml ("." :: Text)
    ul_ do
        traverse_ renderDatatypeClause (toList datatypeClauses)
    -- Derived facts require checked semantic context.
    where
        renderDatatypeClause :: DatatypeClause -> Html ()
        renderDatatypeClause DatatypeClause{..} = li_ do
            for_ datatypeClauseName \name -> strong_ (toHtml (Text.strip name <> ". "))
            inlineMath do
                renderRelationApplication hints Positive [datatypeClauseConstructorExpr] (Relation Nowhere ElementSymbol []) [datatypeClauseTargetExpr]
            case datatypeClausePremises of
                [] ->
                    toHtml ("." :: Text)
                premises -> do
                    toHtml (" for " :: Text)
                    joinHtml (toHtml (" and " :: Text)) (renderDatatypePremise <$> premises)
                    toHtml ("." :: Text)

        renderDatatypePremise :: (VarSymbol, Expr) -> Html ()
        renderDatatypePremise (x, domain) =
            inlineMath (renderRelationApplication hints Positive [ExprVar x] (Relation Nowhere ElementSymbol []) [domain])

exprVar :: Expr -> Maybe VarSymbol
exprVar = \case
    ExprVar x ->
        Just x
    _ ->
        Nothing


elementOfFormula :: Expr -> Expr -> Formula
elementOfFormula left right =
    FormulaChain (ChainBase (left :| []) Positive (Relation Nowhere ElementSymbol []) (right :| []))

semanticSubsetFormula :: Set VarSymbol -> Expr -> Expr -> Formula
semanticSubsetFormula reserved left right =
    forallIfNeeded [witnessVar]
        (impliesFormula
            (elementOfFormula (ExprVar witnessVar) left)
            (elementOfFormula (ExprVar witnessVar) right))
    where
        witnessVar = freshNamedVar (reserved <> Set.fromList (exprVars left <> exprVars right)) "x"

equalsFormula :: Expr -> Expr -> Formula
equalsFormula left right =
    FormulaChain (ChainBase (left :| []) Positive (Relation Nowhere EqSymbol []) (right :| []))

impliesFormula :: Formula -> Formula -> Formula
impliesFormula left right =
    Connected Nowhere Implication left right

formulaConjunction :: [Formula] -> Formula
formulaConjunction = \case
    [] ->
        PropositionalConstant Nowhere IsTop
    phi : rest ->
        foldl' (\left right -> Connected Nowhere Conjunction left right) phi rest

formulaDisjunction :: [Formula] -> Formula
formulaDisjunction = \case
    [] ->
        PropositionalConstant Nowhere IsBottom
    phi : rest ->
        foldl' (\left right -> Connected Nowhere Disjunction left right) phi rest

forallIfNeeded :: [VarSymbol] -> Formula -> Formula
forallIfNeeded [] phi = phi
forallIfNeeded vars phi =
    FormulaQuantified Nowhere Universally (NonEmpty.fromList vars) Unbounded phi

existsIfNeeded :: [VarSymbol] -> Formula -> Formula
existsIfNeeded [] phi = phi
existsIfNeeded vars phi =
    FormulaQuantified Nowhere Existentially (NonEmpty.fromList vars) Unbounded phi

impliesFrom :: [Formula] -> Formula -> Formula
impliesFrom [] conclusion = conclusion
impliesFrom premises conclusion = impliesFormula (formulaConjunction premises) conclusion

renderInductive :: RenderEnvironment -> Marker -> Inductive -> Html ()
renderInductive hints marker Inductive{..} = do
    toHtml ("Inductive definition of " :: Text)
    renderSymbolPatternInline hints inductiveSymbolPattern
    toHtml (" over " :: Text)
    inlineMath (renderExprMathRow hints inductiveDomain)
    toHtml ("." :: Text)
    ul_ do
        traverse_ renderIntro (toList inductiveIntros)
    case inductiveDerivedFacts marker Inductive{..} of
        [] ->
            skip
        derivedFacts ->
            details_ do
                summary_ (toHtml ("Derived facts" :: Text))
                ul_ [class_ "inductive-derived-facts"] do
                    traverse_ (renderInductiveDerivedFact hints) derivedFacts
    where
        renderIntro :: IntroRule -> Html ()
        renderIntro IntroRule{..} = li_ do
            case introConditions of
                [] -> skip
                _ -> do
                    toHtml ("If " :: Text)
                    joinHtml (toHtml (" and " :: Text)) (inlineMath . renderFormulaMath hints <$> introConditions)
                    toHtml (", then " :: Text)
            inlineMath (renderFormulaMath hints introResult)
            toHtml ("." :: Text)

renderInductiveDerivedFact :: RenderEnvironment -> InductiveDerivedFact -> Html ()
renderInductiveDerivedFact hints InductiveDerivedFact{inductiveDerivedFactMarker, inductiveDerivedFactFormula} =
    li_ (id_ (markerText inductiveDerivedFactMarker) : previewTargetAttributes "Inductive Fact" (Just inductiveDerivedFactMarker) Nothing) do
        term "head-" do
            code_ (toHtml (markerText inductiveDerivedFactMarker))
            toHtml (": " :: Text)
        inlineMath (renderFormulaMath hints inductiveDerivedFactFormula)
        toHtml ("." :: Text)

data InductiveDerivedFact = InductiveDerivedFact
    { inductiveDerivedFactMarker :: Marker
    , inductiveDerivedFactFormula :: Formula
    }

data InductiveRenderInfo = InductiveRenderInfo
    { inductiveFactBaseMarker :: Marker
    , inductiveRenderParams :: [VarSymbol]
    , inductiveRenderCarrierExpr :: Expr
    , inductiveRenderDomainExpr :: Expr
    , inductiveRenderClauses :: NonEmpty InductiveRenderClause
    }

data InductiveRenderClause = InductiveRenderClause
    { inductiveRenderClauseVars :: [VarSymbol]
    , inductiveRenderClauseConditions :: [InductiveRenderCondition]
    , inductiveRenderClauseResultExpr :: Expr
    }

data InductiveRenderCondition
    = InductiveRenderSideCondition Formula
    | InductiveRenderRecursiveCondition Expr InductiveCarrierContext

inductiveDerivedFacts :: Marker -> Inductive -> [InductiveDerivedFact]
inductiveDerivedFacts marker inductive = case inductiveRenderInfo marker inductive of
    Nothing ->
        []
    Just info ->
        inductiveIntroFacts info
            <> [ InductiveDerivedFact (inductiveDomSubsetMarker info) (inductiveDomSubsetFormula info)
               , InductiveDerivedFact (inductiveCasesMarker info) (inductiveCasesFormula info)
               , InductiveDerivedFact (inductiveInductMarker info) (inductiveInductFormula info)
               ]

inductiveRenderInfo :: Marker -> Inductive -> Maybe InductiveRenderInfo
inductiveRenderInfo marker Inductive{inductiveSymbolPattern = SymbolPattern inductiveSymbol inductiveParams, inductiveDomain, inductiveIntros} = do
    inductiveRenderClauses <- traverse (inductiveRenderClause inductiveSymbol inductiveParams) inductiveIntros
    pure InductiveRenderInfo
        { inductiveFactBaseMarker = marker
        , inductiveRenderParams = inductiveParams
        , inductiveRenderCarrierExpr = ExprOp Nowhere inductiveSymbol (ExprVar <$> inductiveParams)
        , inductiveRenderDomainExpr = inductiveDomain
        , inductiveRenderClauses
        }
    where
        inductiveRenderClause :: MixfixItem -> [VarSymbol] -> IntroRule -> Maybe InductiveRenderClause
        inductiveRenderClause symbol params IntroRule{introConditions, introResult} = do
            inductiveRenderClauseResultExpr <- inductiveRenderResultExpr symbol params introResult
            inductiveRenderClauseConditions <- traverse (inductiveRenderCondition symbol params) introConditions
            let paramSet = Set.fromList params
                inductiveRenderClauseVars =
                    List.filter (`Set.notMember` paramSet)
                        (nubOrd (concatMap formulaVars introConditions <> exprVars inductiveRenderClauseResultExpr))
            pure InductiveRenderClause
                { inductiveRenderClauseVars
                , inductiveRenderClauseConditions
                , inductiveRenderClauseResultExpr
                }

inductiveRenderResultExpr :: MixfixItem -> [VarSymbol] -> Formula -> Maybe Expr
inductiveRenderResultExpr symbol params = \case
    FormulaChain (ChainBase (resultExpr :| []) Positive (Relation _ ElementSymbol []) (carrierExpr :| []))
        | sameInductiveCarrierExpr symbol params carrierExpr ->
            Just resultExpr
    _ ->
        Nothing

inductiveRenderCondition :: MixfixItem -> [VarSymbol] -> Formula -> Maybe InductiveRenderCondition
inductiveRenderCondition symbol params phi
    | not (formulaMentionsFunction symbol phi) =
        Just (InductiveRenderSideCondition phi)
    | otherwise = case phi of
        FormulaChain (ChainBase (recursiveTerm :| []) Positive (Relation _ ElementSymbol []) (recursiveCarrier :| []))
            | not (exprMentionsFunction symbol recursiveTerm) ->
                InductiveRenderRecursiveCondition recursiveTerm
                    <$> prepareInductiveCarrierContext symbol params recursiveCarrier
        _ ->
            Nothing

inductiveIntroFacts :: InductiveRenderInfo -> [InductiveDerivedFact]
inductiveIntroFacts info =
    [ InductiveDerivedFact (inductiveIntroMarker info index) (inductiveIntroFormula info clause)
    | (index, clause) <- zip [(1 :: Int) ..] (NonEmpty.toList (inductiveRenderClauses info))
    ]

inductiveIntroMarker :: InductiveRenderInfo -> Int -> Marker
inductiveIntroMarker info index =
    Marker (markerText (inductiveFactBaseMarker info) <> "_intro_" <> Text.pack (show index))

inductiveDomSubsetMarker :: InductiveRenderInfo -> Marker
inductiveDomSubsetMarker info =
    Marker (markerText (inductiveFactBaseMarker info) <> "_dom_subset")

inductiveCasesMarker :: InductiveRenderInfo -> Marker
inductiveCasesMarker info =
    Marker (markerText (inductiveFactBaseMarker info) <> "_cases")

inductiveInductMarker :: InductiveRenderInfo -> Marker
inductiveInductMarker info =
    Marker (markerText (inductiveFactBaseMarker info) <> "_induct")

inductiveIntroFormula :: InductiveRenderInfo -> InductiveRenderClause -> Formula
inductiveIntroFormula info clause =
    forallIfNeeded (nubOrd (inductiveRenderParams info <> inductiveRenderClauseVars clause))
        (impliesFrom premises conclusion)
    where
        premises = inductiveRenderConditionFormula info <$> inductiveRenderClauseConditions clause
        conclusion = elementOfFormula (inductiveRenderClauseResultExpr clause) (inductiveRenderCarrierExpr info)

inductiveDomSubsetFormula :: InductiveRenderInfo -> Formula
inductiveDomSubsetFormula info =
    forallIfNeeded (inductiveRenderParams info)
        (semanticSubsetFormula (inductiveUsedVars info) (inductiveRenderCarrierExpr info) (inductiveRenderDomainExpr info))

inductiveCasesFormula :: InductiveRenderInfo -> Formula
inductiveCasesFormula info =
    forallIfNeeded (nubOrd (inductiveRenderParams info <> [witnessVar]))
        (impliesFormula (elementOfFormula (ExprVar witnessVar) (inductiveRenderCarrierExpr info)) (formulaDisjunction disjuncts))
    where
        witnessVar = freshNamedVar (inductiveUsedVars info) "x"
        disjuncts = inductiveCaseDisjunct witnessVar <$> NonEmpty.toList (inductiveRenderClauses info)
        inductiveCaseDisjunct x clause =
            existsIfNeeded (inductiveRenderClauseVars clause)
                (formulaConjunction (premises <> [equalsFormula (ExprVar x) (inductiveRenderClauseResultExpr clause)]))
            where
                premises = inductiveRenderConditionFormula info <$> inductiveRenderClauseConditions clause

inductiveInductFormula :: InductiveRenderInfo -> Formula
inductiveInductFormula info =
    forallIfNeeded (nubOrd (inductiveRenderParams info <> [subsetVar]))
        (impliesFrom closures conclusion)
    where
        subsetVar = freshNamedVar (inductiveUsedVars info) "S"
        closures = inductiveInductionClosure subsetVar <$> NonEmpty.toList (inductiveRenderClauses info)
        conclusion =
            semanticSubsetFormula
                (Set.insert subsetVar (inductiveUsedVars info))
                (inductiveRenderCarrierExpr info)
                (ExprVar subsetVar)

inductiveInductionClosure :: VarSymbol -> InductiveRenderClause -> Formula
inductiveInductionClosure subsetVar clause =
    forallIfNeeded (inductiveRenderClauseVars clause) (impliesFrom premises conclusion)
    where
        premises = inductiveRenderConditionFormulaAt (ExprVar subsetVar) <$> inductiveRenderClauseConditions clause
        conclusion = elementOfFormula (inductiveRenderClauseResultExpr clause) (ExprVar subsetVar)

inductiveRenderConditionFormula :: InductiveRenderInfo -> InductiveRenderCondition -> Formula
inductiveRenderConditionFormula info =
    inductiveRenderConditionFormulaAt (inductiveRenderCarrierExpr info)

inductiveRenderConditionFormulaAt :: Expr -> InductiveRenderCondition -> Formula
inductiveRenderConditionFormulaAt replacement = \case
    InductiveRenderSideCondition phi ->
        phi
    InductiveRenderRecursiveCondition recursiveTerm recursiveCarrierTemplate ->
        elementOfFormula recursiveTerm (recursiveCarrierTemplate replacement)

inductiveUsedVars :: InductiveRenderInfo -> Set VarSymbol
inductiveUsedVars info =
    Set.fromList
        ( inductiveRenderParams info
            <> [ var
               | clause <- NonEmpty.toList (inductiveRenderClauses info)
               , var <- inductiveRenderClauseVars clause
               ]
        )

sameInductiveCarrierExpr :: MixfixItem -> [VarSymbol] -> Expr -> Bool
sameInductiveCarrierExpr symbol params = \case
    ExprOp _ symbol' args ->
        symbol == symbol'
            && length params == length args
            && and (zipWith (\param arg -> exprVar arg == Just param) params args)
    _ ->
        False

-- A prepared presentation context distinguishes carrier holes from real names.
type InductiveCarrierContext = Expr -> Expr

prepareInductiveCarrierContext
    :: MixfixItem -> [VarSymbol] -> Expr -> Maybe InductiveCarrierContext
prepareInductiveCarrierContext symbol params = go
    where
        go = \case
            original@ExprVar{} -> Just (const original)
            original@ExprNaturalNumeral{} -> Just (const original)
            original@ExprOpaqueInteger{} -> Just (const original)
            ExprTypedConstant{} -> Nothing
            ExprHigherApply{} -> Nothing
            ExprLambda{} -> Nothing
            ExprSelect{} -> Nothing
            original@(ExprOp loc symbol' args)
                | sameInductiveCarrierExpr symbol params original ->
                    Just id
                | symbol == symbol' ->
                    Nothing
                | otherwise -> do
                    children <- traverse go args
                    pure (\replacement -> ExprOp loc symbol'
                        (map ($ replacement) children))
            ExprStructOp loc structSymbol expr -> do
                child <- traverse go expr
                pure (\replacement -> ExprStructOp loc structSymbol
                    (($ replacement) <$> child))
            ExprFiniteSet loc exprs -> do
                children <- traverse go exprs
                pure (\replacement -> ExprFiniteSet loc
                    (($ replacement) <$> children))
            ExprSep{} -> Nothing
            ExprReplace{} -> Nothing
            ExprReplacePred{} -> Nothing
            ExprStructAggregate{} -> Nothing
            ExprStructReduct{} -> Nothing
            ExprStructReconstruction{} -> Nothing

formulaMentionsFunction :: MixfixItem -> Formula -> Bool
formulaMentionsFunction symbol = \case
    FormulaChain chain ->
        chainMentionsFunction symbol chain
    FormulaSetMap _location function domain codomain ->
        symbol == FunsSymbol
            || any (exprMentionsFunction symbol) [function, domain, codomain]
    FormulaExpression expr ->
        exprMentionsFunction symbol expr
    FormulaPredicate _loc _predicate _marker exprs ->
        any (exprMentionsFunction symbol) exprs
    Connected _loc _conn left right ->
        formulaMentionsFunction symbol left || formulaMentionsFunction symbol right
    FormulaNeg _loc phi ->
        formulaMentionsFunction symbol phi
    FormulaQuantified _loc _quant _vars _bound phi ->
        formulaMentionsFunction symbol phi
    FormulaTypedQuantified _loc _quant _vars _coreType phi ->
        formulaMentionsFunction symbol phi
    PropositionalConstant{} ->
        False

chainMentionsFunction :: MixfixItem -> Chain -> Bool
chainMentionsFunction symbol = \case
    ChainBase left _sign relation right ->
        any (exprMentionsFunction symbol) left || relationMentionsFunction symbol relation || any (exprMentionsFunction symbol) right
    ChainCons left _sign relation rest ->
        any (exprMentionsFunction symbol) left || relationMentionsFunction symbol relation || chainMentionsFunction symbol rest

relationMentionsFunction :: MixfixItem -> Relation -> Bool
relationMentionsFunction symbol = \case
    Relation _loc _relationSymbol exprs ->
        any (exprMentionsFunction symbol) exprs
    RelationExpr _loc expr ->
        exprMentionsFunction symbol expr

exprMentionsFunction :: MixfixItem -> Expr -> Bool
exprMentionsFunction symbol = \case
    ExprVar{} ->
        False
    ExprNaturalNumeral{} ->
        False
    ExprOpaqueInteger{} ->
        False
    ExprTypedConstant{} ->
        False
    ExprHigherApply _loc function argument ->
        typedExpressionMentionsFunction symbol function
            || typedExpressionMentionsFunction symbol argument
    ExprLambda _loc _variables _coreType body ->
        typedExpressionMentionsFunction symbol body
    ExprSelect _loc _maybeCoreType predicate ->
        typedExpressionMentionsFunction symbol predicate
    ExprOp _loc symbol' args ->
        symbol == symbol' || any (exprMentionsFunction symbol) args
    ExprStructOp _loc _structSymbol expr ->
        maybe False (exprMentionsFunction symbol) expr
    ExprFiniteSet _loc exprs ->
        any (exprMentionsFunction symbol) exprs
    ExprSep _loc _var bound _stmt ->
        exprMentionsFunction symbol bound
    ExprReplace _loc expr bounds _maybeStmt ->
        exprMentionsFunction symbol expr || any (exprMentionsFunction symbol . snd) bounds
    ExprReplacePred _loc _x _y expr _stmt ->
        exprMentionsFunction symbol expr
    ExprStructAggregate _loc maybeSchema entries ->
        maybe False
            (\(StructApplication _phrase arguments) ->
                any (exprMentionsFunction symbol) arguments)
            maybeSchema
            || any
                (exprMentionsFunction symbol
                    . structAggregateEntryExpression)
                entries
    ExprStructReduct _loc schema record ->
        let StructApplication _phrase arguments = schema
        in any (exprMentionsFunction symbol) arguments
            || exprMentionsFunction symbol record
    ExprStructReconstruction _loc (StructApplication _ arguments) record entries ->
        any (exprMentionsFunction symbol) arguments
            || exprMentionsFunction symbol record
            || any (exprMentionsFunction symbol . structAggregateEntryExpression) entries

typedExpressionMentionsFunction
    :: MixfixItem
    -> TypedExpression
    -> Bool
typedExpressionMentionsFunction symbol = \case
    TypedExpressionExpr expr ->
        exprMentionsFunction symbol expr
    TypedExpressionFormula phi ->
        formulaMentionsFunction symbol phi

formulaVars :: Formula -> [VarSymbol]
formulaVars = \case
    FormulaChain chain ->
        chainVars chain
    FormulaSetMap _location function domain codomain ->
        concatMap exprVars [function, domain, codomain]
    FormulaExpression expr ->
        exprVars expr
    FormulaPredicate _loc _predicate _marker exprs ->
        concatMap exprVars exprs
    Connected _loc _conn left right ->
        formulaVars left <> formulaVars right
    FormulaNeg _loc phi ->
        formulaVars phi
    FormulaQuantified _loc _quant vars _bound phi ->
        List.filter (`notElem` toList vars) (formulaVars phi)
    FormulaTypedQuantified _loc _quant vars _coreType phi ->
        List.filter (`notElem` toList vars) (formulaVars phi)
    PropositionalConstant{} ->
        []

chainVars :: Chain -> [VarSymbol]
chainVars = \case
    ChainBase left _sign relation right ->
        concatMap exprVars (toList left) <> relationVars relation <> concatMap exprVars (toList right)
    ChainCons left _sign relation rest ->
        concatMap exprVars (toList left) <> relationVars relation <> chainVars rest

relationVars :: Relation -> [VarSymbol]
relationVars = \case
    Relation _loc _relationSymbol exprs ->
        concatMap exprVars exprs
    RelationExpr _loc expr ->
        exprVars expr

exprVars :: Expr -> [VarSymbol]
exprVars = \case
    ExprVar x ->
        [x]
    ExprNaturalNumeral{} ->
        []
    ExprOpaqueInteger{} ->
        []
    ExprTypedConstant{} ->
        []
    ExprHigherApply _loc function argument ->
        typedExpressionVars function <> typedExpressionVars argument
    ExprLambda _loc variables _coreType body ->
        List.filter
            (`notElem` toList variables)
            (typedExpressionVars body)
    ExprSelect _loc _maybeCoreType predicate ->
        typedExpressionVars predicate
    ExprOp _loc _symbol args ->
        concatMap exprVars args
    ExprStructOp _loc _structSymbol expr ->
        maybe [] exprVars expr
    ExprFiniteSet _loc exprs ->
        concatMap exprVars exprs
    ExprSep _loc x bound _stmt ->
        List.filter (/= x) (exprVars bound)
    ExprReplace _loc expr bounds _maybeStmt ->
        let boundVars = fst <$> toList bounds
            free = exprVars expr <> concatMap (exprVars . snd) (toList bounds)
        in List.filter (`notElem` boundVars) free
    ExprReplacePred _loc x y expr _stmt ->
        List.filter (\var -> var /= x && var /= y) (exprVars expr)
    ExprStructAggregate _loc maybeSchema entries ->
        foldMap
            (\(StructApplication _phrase arguments) ->
                concatMap exprVars arguments)
            maybeSchema
            <> concatMap
                (exprVars . structAggregateEntryExpression)
                entries
    ExprStructReduct _loc schema record ->
        let StructApplication _phrase arguments = schema
        in concatMap exprVars arguments <> exprVars record
    ExprStructReconstruction _loc (StructApplication _ arguments) record entries ->
        concatMap exprVars arguments <> exprVars record
            <> concatMap (exprVars . structAggregateEntryExpression) entries

typedExpressionVars :: TypedExpression -> [VarSymbol]
typedExpressionVars = \case
    TypedExpressionExpr expr -> exprVars expr
    TypedExpressionFormula phi -> formulaVars phi

renderSignatureBlock :: RenderEnvironment -> [Asm] -> Signature -> Html ()
renderSignatureBlock hints asms sig = do
    case asms of
        [] -> skip
        _ -> do
            toHtml ("Assumptions: " :: Text)
            renderAsmList hints asms
            toHtml ("." :: Text)
    when (not (null asms)) do
        p_ do
            renderSignature hints sig
            toHtml ("." :: Text)
    when (null asms) do
        renderSignature hints sig
        toHtml ("." :: Text)

renderSignature :: RenderEnvironment -> Signature -> Html ()
renderSignature hints = \case
    SignatureAdj var adj -> do
        renderVarInline var
        toHtml (" can be " :: Text)
        renderAdjInline hints renderVarInline adj
    SignatureVerb var verb -> do
        renderVarInline var
        toHtml (" can " :: Text)
        renderVerbInline hints True renderVarInline verb
    SignatureNoun var noun -> do
        renderVarInline var
        toHtml (" is a " :: Text)
        renderNounInline hints False renderVarInline noun
    SignatureSymbolic symb np -> do
        renderSymbolPatternInline hints symb
        toHtml (" is a " :: Text)
        renderNounPhraseMaybe hints np
    SignatureTypedConstant _location token coreType ->
        inlineMath do
            renderMathToken token
            moText ":"
            renderConcreteTypeMath coreType

renderConcreteTypeMath :: ConcreteType -> Html ()
renderConcreteTypeMath = go False
  where
    go _ ConcreteSet = miText "Set"
    go _ ConcreteProp = miText "Prop"
    go parenthesize (ConcreteArrow domain codomain) = do
        when parenthesize (moText "(")
        go True domain
        moText "→"
        go False codomain
        when parenthesize (moText ")")

renderInstance :: RenderEnvironment -> Instance -> Html ()
renderInstance hints Instance{..} = p_ do
    inlineMath (renderMathToken instanceNameToken)
    toHtml (" is a " :: Text)
    renderStructApplicationInline hints instanceApplication
    toHtml (" defined by " :: Text)
    inlineMath do
        renderMathToken instanceNameToken
        moText "="
        renderExprMathRowWithImmediateStructure
            hints instanceApplication instanceValue
    toHtml ("." :: Text)

renderConstruction :: RenderEnvironment -> Construction -> Html ()
renderConstruction hints Construction{..} = do
    unless (null constructionAssumptions) do
        p_ (traverse_ (renderAsmSentence hints) constructionAssumptions)
    p_ do
        toHtml ("The " :: Text)
        renderStructApplicationInline hints constructionApplication
        toHtml (" " :: Text)
        inlineMath do
            renderSymbolPatternMath hints constructionHead
            moText "="
            renderExprMathRowWithImmediateStructure hints constructionApplication constructionValue
        toHtml ("." :: Text)

renderStructDefn :: RenderEnvironment -> StructDefn -> Html ()
renderStructDefn hints StructDefn{..} = do
    when (not (null structPreamble)) do
        p_ do
            toHtml ("Parameters: " :: Text)
            renderAsmList hints structPreamble
            toHtml ("." :: Text)
    toHtml ("Structure phrase: " :: Text)
    renderStructureDeclarationPhraseInline hints
        structPhrase
        structParameters
    toHtml ("." :: Text)
    p_ do
        toHtml ("Label: " :: Text)
        renderVarInline structLabel
        toHtml ("." :: Text)
    when (not (null structParents)) do
        p_ do
            toHtml ("Parents: " :: Text)
            joinHtml
                (toHtml (", " :: Text))
                [do
                    traverse_ (\marker -> toHtml (markerText marker) >> toHtml (": " :: Text)) label
                    renderStructApplicationInline hints application
                | StructParent application label <- structParents]
            toHtml ("." :: Text)
    when (not (null structFields)) do
        toHtml ("Fields:" :: Text)
        ul_ do
            for_ structFields \StructField{..} -> li_ do
                traverse_
                    (\marker -> do
                        toHtml (markerText marker)
                        toHtml (": " :: Text))
                    structFieldMarker
                unless (null structFieldDescription) do
                    joinHtml
                        (toHtml (" " :: Text))
                        (tokenTextHtml <$> structFieldDescription)
                    toHtml (" " :: Text)
                case structFieldSpecification of
                    Just specification ->
                        renderStmtInline hints specification
                    Nothing ->
                        inlineMath
                            (renderStructSymbolName structFieldSymbol)
    when (not (null structAssumes)) do
        ul_ do
            for_ structAssumes \(marker, stmt) -> li_ do
                toHtml (markerText marker)
                toHtml (": " :: Text)
                renderStmtInline hints stmt
                toHtml ("." :: Text)


buildPreviewMap
    :: HtmlRenderContext
    -> Set Marker
    -> AnchorMap
    -> HtmlRenderIndex
    -> Either HtmlRenderContextError PreviewMap
buildPreviewMap
        context
        referencedMarkers
        anchors
        HtmlRenderIndex
            { renderIndexReferenceTargets = targetIndex
            } =
    Map.fromList <$> traverse makePreviewEntry indexedTargets
  where
    targets =
        List.sortOn targetOrdinal
            [ indexed
            | marker <- Set.toList referencedMarkers
            , marker `Map.notMember` anchors
            , Just indexed@(IndexedReferenceTarget _ source _target) <-
                [Map.lookup marker targetIndex]
            , source /= htmlCurrentSource context
            ]
    targetOrdinal (IndexedReferenceTarget ordinal _source _target) =
        ordinal
    sourceTarget (IndexedReferenceTarget _ordinal source target) =
        (source, target)
    indexedTargets =
        zip [1 :: Int ..] (sourceTarget <$> targets)

    makePreviewEntry (index, (source, target)) = do
        previewSourceLabel <-
            htmlSourceLabel context source
        previewSourceHref <-
            htmlSourcePageHref context source
        previewReferenceHref <-
            htmlSourceFragmentHref
                context
                source
                (targetAnchorId target)
        let marker = targetMarker target
            previewMarker = marker
            previewKind = targetKind target
            previewTitle = targetTitle target
            previewId =
                "reference-preview-" <> Text.pack (show index)
            previewBody = targetBody target
        Right (marker, PreviewEntry{..})

renderPreviewStore :: RenderEnvironment -> PreviewMap -> Html ()
renderPreviewStore hints previews =
    div_ [class_ "reference-preview-store", makeAttributes "aria-hidden" "true"] do
        traverse_ (renderPreviewEntry hints) (Map.elems previews)

renderPreviewEntry :: RenderEnvironment -> PreviewEntry -> Html ()
renderPreviewEntry hints PreviewEntry{..} =
    div_ [id_ previewId, class_ "reference-preview-template"] do
        div_ [class_ "reference-preview-heading"] do
            toHtml previewKind
            toHtml (" " :: Text)
            code_ (toHtml (markerText previewMarker))
            case previewTitle of
                Nothing ->
                    skip
                Just title -> do
                    toHtml (" (" :: Text)
                    toHtml title
                    toHtml (")" :: Text)
        div_ [class_ "reference-preview-source"] do
            toHtml ("from " :: Text)
            a_ [href_ previewSourceHref] do
                code_ (toHtml previewSourceLabel)
        div_ [class_ "reference-preview-body"] do
            previewBody hints

renderPreviewBlockBody :: RenderEnvironment -> Block -> Html ()
renderPreviewBlockBody hints = \case
    BlockAxiom _loc _title _marker axiom ->
        previewStatement (renderAxiom hints axiom)
    BlockClaim _kind _loc _title _marker claim ->
        previewStatement (renderClaim hints claim)
    BlockDefn _loc _title _marker defn ->
        previewStatement (renderDefn hints defn)
    BlockAbbr _loc _title _marker abbr ->
        previewStatement (renderAbbreviation hints abbr)
    BlockRecursive _loc _title _marker definition ->
        renderRecursiveDefinition hints definition
    BlockData _loc _title _marker datatype ->
        renderDatatype hints datatype
    BlockInductive _loc _title marker ind ->
        renderInductive hints marker ind
    BlockSig _loc _title _marker asms sig ->
        renderSignatureBlock hints asms sig
    BlockStruct _loc _title _marker structDefn ->
        renderStructDefn hints structDefn
    BlockInstance _loc _title _marker instanceDefn ->
        previewStatement (renderInstance hints instanceDefn)
    BlockConstruction _loc _title _marker construction ->
        renderConstruction hints construction
    BlockProof{} ->
        skip

previewStatement :: Html () -> Html ()
previewStatement =
    p_ [class_ "reference-preview-statement"]

referenceTargetsOfBlockRenderInfo :: Map Marker [Consequences.PublicConsequence] -> BlockRenderInfo -> [ReferenceTarget]
referenceTargetsOfBlockRenderInfo consequences (_index, block, blockId) =
    maybeToList blockTarget <> recordTargets <> inductiveTargets
    where
        blockTarget = do
            marker <- blockMarkerOf block
            pure ReferenceTarget
                { targetMarker = marker
                , targetAnchorId = blockId
                , targetKind = blockPrefixText block
                , targetTitle = formatBlockTitle (blockTitleOf block)
                , targetBody = \hints -> case List.find ((== marker) . Consequences.consequenceLabel) entries of
                    Just consequence -> renderPublicConsequence hints consequence
                    Nothing -> renderPreviewBlockBody hints block
                }

        recordTargets =
            [ ReferenceTarget
                { targetMarker = Consequences.consequenceLabel consequence
                , targetAnchorId = blockId
                , targetKind = "Construction consequence"
                , targetTitle = Nothing
                , targetBody = \hints -> renderPublicConsequence hints consequence
                }
            | consequence <- entries
            , Just (Consequences.consequenceLabel consequence) /= blockMarkerOf block
            ]
        entries = maybe [] (\marker -> Map.findWithDefault [] marker consequences) (blockMarkerOf block)

        inductiveTargets = case block of
            BlockInductive _loc _title marker inductive ->
                [ ReferenceTarget
                    { targetMarker = inductiveDerivedFactMarker
                    , targetAnchorId = markerText inductiveDerivedFactMarker
                    , targetKind = "Inductive Fact"
                    , targetTitle = Nothing
                    , targetBody = \hints -> previewStatement (inlineMath (renderFormulaMath hints inductiveDerivedFactFormula))
                    }
                | InductiveDerivedFact{inductiveDerivedFactMarker, inductiveDerivedFactFormula} <- inductiveDerivedFacts marker inductive
                ]
            _ ->
                []


renderPublicConsequences :: RenderEnvironment -> Marker -> Html ()
renderPublicConsequences hints marker =
    case Map.findWithDefault [] marker (renderEnvironmentConsequences hints) of
        [] -> skip
        entries -> details_ [class_ "construction-consequences"] do
            summary_ "Public consequences"
            for_ entries (renderPublicConsequence hints)

renderPublicConsequence :: RenderEnvironment -> Consequences.PublicConsequence -> Html ()
renderPublicConsequence hints consequence = div_ [class_ "public-consequence"] do
    code_ (toHtml (markerText (Consequences.consequenceLabel consequence)))
    p_ [class_ "reference-preview-statement"] do
        unless (null (Consequences.consequenceBinders consequence)) do
            toHtml ("For all sets " :: Text)
            inlineMath (joinHtml (moText ",") (renderVarMath <$> Consequences.consequenceBinders consequence))
            toHtml (", " :: Text)
        unless (null (Consequences.consequenceHeaders consequence)) do
            toHtml (if null (Consequences.consequenceBinders consequence) then "If " else "if " :: Text)
            joinHtml (toHtml (" and " :: Text))
                [inlineMath (renderConsequenceMath hints header) | header <- Consequences.consequenceHeaders consequence]
            toHtml (", then " :: Text)
        inlineMath (renderConsequenceMath hints (Consequences.consequenceConclusion consequence))
        toHtml ("." :: Text)

renderConsequenceMath :: RenderEnvironment -> Consequences.ConsequenceMath -> Html ()
renderConsequenceMath hints = render
  where
    render = \case
        Consequences.ConsequenceVariable variable -> renderVarMath variable
        Consequences.ConsequenceInteger value -> mn_ (toHtml (show value))
        Consequences.ConsequenceSeparation variable domain body -> surround "{" "}" do
            renderVarMath variable
            moText "∈"
            render domain
            moText "|"
            render body
        Consequences.ConsequenceField field subject ->
            notation (Contracts.fieldNotation field (Just ())) [subject] do
                renderStructSymbolName field
                moText "["
                render subject
                moText "]"
        Consequences.ConsequenceStructure phrase subject parameters -> do
            render subject
            mtextText (" is " <> article (Schema.structurePhraseSingular phrase))
            words' (Schema.structurePhraseSingular phrase) parameters
        Consequences.ConsequenceExactFields fields subject -> do
            render subject
            mtextText (if null fields then " has no fields" else " has exactly the fields ")
            joinHtml (moText ",") (renderStructSymbolName <$> fields)
        Consequences.ConsequenceGlobal key marker arguments -> global key marker arguments
        Consequences.ConsequenceIntrinsic intrinsic arguments -> case (intrinsic, arguments) of
            (Core.Empty, []) -> moText "∅"
            (Core.Member, [left, right]) -> infix' "∈" left right
            (Core.OrderedPair, [left, right]) -> surround "(" ")" (joinHtml (moText ",") [render left, render right])
            (Core.PairSet, values) -> surround "{" "}" (joinHtml (moText ",") (render <$> values))
            (Core.PowerSet, [value]) -> moText "𝒫" >> surround "(" ")" (render value)
            (Core.FamilyUnion, [value]) -> moText "⋃" >> surround "(" ")" (render value)
            _ -> do
                miText (Text.pack (show intrinsic))
                surround "(" ")" (joinHtml (moText ",") (render <$> arguments))
        Consequences.ConsequenceBinary symbol left right -> infix' symbol left right
        Consequences.ConsequenceUnary symbol body -> moText symbol >> surround "(" ")" (render body)
        Consequences.ConsequenceQuantified quantifier variable body -> do
            moText quantifier
            renderVarMath variable
            moText "."
            surround "(" ")" (render body)
        Consequences.ConsequenceTruth value -> moText (if value then "⊤" else "⊥")
    infix' symbol left right = surround "(" ")" do
        render left
        moText symbol
        render right
    surround left right body = mrow_ (moText left >> body >> moText right)
    notation contract arguments fallback =
        case renderEnvironmentNotationContracts hints >>= \contracts ->
                Contracts.applyNotationContract contracts contract (render <$> arguments) of
            Just pieces -> mrow_ (traverse_ (either toHtmlRaw id) pieces)
            Nothing -> fallback
    words' pattern' arguments = case applyPattern (patternToHoley pattern') arguments of
        Left failure -> merror_ (mtextText (patternApplicationMessage failure))
        Right pieces -> joinHtml (mtextText " ") (either (mtextText . tokToText) render <$> pieces)
    article (TokenCons token _) = case Text.uncons (Text.toLower (tokToText token)) of
        Just (initial, _) | initial `elem` ("aeiou" :: String) -> "an "
        _ -> "a "
    article _ = "a "
    global key marker arguments = case (key, arguments) of
        (Semantic.SemanticNoun singular _, subject : parameters) -> do
            render subject
            mtextText (" is " <> article singular)
            words' singular parameters
        (Semantic.SemanticLeftAdjective _ pattern', subject : parameters) -> adjective pattern' subject parameters
        (Semantic.SemanticRightAdjective _ pattern', subject : parameters) -> adjective pattern' subject parameters
        (Semantic.SemanticRelation token arity, left : right : parameters) -> do
            render left
            notation (Contracts.relationNotation (RelationSymbol token arity marker)) parameters (renderMathToken token)
            render right
        _ -> case Contracts.notationForKey key marker of
            Just contract -> notation contract arguments fallback
            Nothing -> fallback
      where
        adjective pattern' subject parameters = render subject >> mtextText " is " >> words' pattern' parameters
        fallback = do
            miText (markerText marker)
            unless (null arguments) (surround "(" ")" (joinHtml (moText ",") (render <$> arguments)))

renderAssumeIntro :: AssumeIntro -> Html ()
renderAssumeIntro = \case
    AssumeIntroAssume ->
        toHtml ("Assume " :: Text)
    AssumeIntroSuppose ->
        toHtml ("Suppose " :: Text)

renderProof :: RenderEnvironment -> ReferenceContext -> Proof -> Html ()
renderProof hints references = \case
    Omitted _loc ->
        p_ "Omitted."
    Qed mloc justification ->
        renderProofTerminal mloc justification
    Contradiction _loc justification ->
        p_ do
            toHtml ("Contradiction" :: Text)
            renderJustificationSuffix references justification
            toHtml ("." :: Text)
    ByCase _loc cases -> do
        p_ "Proof by cases."
        term "proof-" (traverse_ (renderCase hints references) cases)
    ByContradiction _loc proof -> do
        p_ "Proof by contradiction."
        term "proof-" (renderProof hints references proof)
    BySetInduction _loc maybeTerm proof -> do
        p_ do
            toHtml ("Proof by set induction" :: Text)
            case maybeTerm of
                Nothing -> skip
                Just targetTerm -> do
                    toHtml (" on " :: Text)
                    renderTermInline hints targetTerm
            toHtml ("." :: Text)
        term "proof-" (renderProof hints references proof)
    ByOrdInduction _loc proof -> do
        p_ "Proof by ordinal induction."
        term "proof-" (renderProof hints references proof)
    ByStructuralInduction _loc focus cases -> do
        p_ do
            toHtml ("Proof by structural induction on " :: Text)
            renderVarInline focus
            toHtml ("." :: Text)
        for_ cases \named -> do
            p_ (strong_ (toHtml (Text.strip (namedCaseName named) <> ".")))
            term "proof-" (renderProof hints references (namedCaseProof named))
    Assume _loc intro stmt proof -> do
        p_ do
            renderAssumeIntro intro
            renderStmtInline hints stmt
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    Fix _loc binders condition proof -> do
        p_ do
            toHtml ("Fix " :: Text)
            renderFixBinderList hints binders
            for_ condition \stmt -> do
                toHtml (" such that " :: Text)
                renderStmtInline hints stmt
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    Calc _loc maybeQuant calc proof -> do
        renderCalc hints references maybeQuant calc
        renderProofContinuation hints references proof
    TakeVar _loc vars bound stmt justification proof -> do
        p_ do
            toHtml ("Take " :: Text)
            renderVarListInline vars
            renderBoundInline hints vars bound
            toHtml (" such that " :: Text)
            renderStmtInline hints stmt
            renderJustificationSuffix references justification
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    TakeTyped _loc vars coreType stmt justification proof -> do
        p_ do
            toHtml ("Take " :: Text)
            inlineMath do
                renderVarListMath vars
                moText ":"
                renderConcreteTypeMath coreType
            toHtml (" such that " :: Text)
            renderStmtInline hints stmt
            renderJustificationSuffix references justification
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    TakeNoun _loc np justification proof -> do
        p_ do
            toHtml ("Take " :: Text)
            renderNounPhraseList hints np
            renderJustificationSuffix references justification
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    Have _loc intro stmt justification proof -> do
        p_ do
            renderHaveIntro intro proof
            renderStmtInline hints stmt
            renderJustificationSuffix references justification
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    Since
            _premiseLoc premise premiseJustification
            _claimLoc claim claimJustification proof -> do
        p_ do
            toHtml ("Since " :: Text)
            renderStmtInline hints premise
            renderJustificationSuffix references premiseJustification
            toHtml (", we have " :: Text)
            renderStmtInline hints claim
            renderJustificationSuffix references claimJustification
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    Suffices _loc stmt justification proof -> do
        p_ do
            toHtml ("It suffices to show that " :: Text)
            renderStmtInline hints stmt
            renderJustificationSuffix references justification
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    Subclaim _loc stmt subproof proof -> do
        if proofStepCount subproof >= nestedProofCollapseThreshold
            then term "proof-" do
                details_ do
                    summary_ (renderShowLead hints stmt)
                    renderProof hints references subproof
            else do
                p_ (renderShowLead hints stmt)
                term "proof-" (renderProof hints references subproof)
        renderProofContinuation hints references proof
    Define _loc var expr proof -> do
        p_ do
            toHtml ("Let " :: Text)
            renderVarEqInline hints var expr
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    DefineTyped _loc var coreType body proof -> do
        p_ do
            toHtml ("Let " :: Text)
            inlineMath do
                renderVarMath var
                moText ":"
                renderConcreteTypeMath coreType
                moText "="
                renderTypedExpressionMath hints body
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    DefineFunction _loc fun arg value boundVar boundExpr proof -> do
        p_ do
            toHtml ("Let " :: Text)
            renderFunctionEqInline hints fun arg value
            toHtml (" for " :: Text)
            renderVarInline boundVar
            toHtml (" in " :: Text)
            inlineMath (renderExprMathRow hints boundExpr)
            toHtml ("." :: Text)
        renderProofContinuation hints references proof
    DefineFunctionLocal _loc fun arg _target domVar codVar rules proof -> do
        p_ do
            toHtml ("Let " :: Text)
            renderFunctionCallInline fun arg
            toHtml (" be locally defined from " :: Text)
            renderVarInline domVar
            toHtml (" to " :: Text)
            renderVarInline codVar
            toHtml ("." :: Text)
        ul_ do
            for_ (toList rules) \(ruleTerm, formula) -> li_ do
                inlineMath (renderExprMathRow hints ruleTerm)
                toHtml (" if " :: Text)
                inlineMath (renderFormulaMath hints formula)
                toHtml ("." :: Text)
        renderProofContinuation hints references proof

    where
        renderProofTerminal :: Maybe Location -> Justification -> Html ()
        renderProofTerminal mloc justification = case (mloc, justification) of
            (Nothing, JustificationImplicit) ->
                skip
            (Just _, JustificationImplicit) ->
                p_ "Follows."
            _ ->
                p_ do
                    toHtml ("Follows" :: Text)
                    renderJustificationSuffix references justification
                    toHtml ("." :: Text)

renderHaveIntro :: HaveIntro -> Proof -> Html ()
renderHaveIntro intro proof = case intro of
    HaveNoIntro ->
        unless (isImplicitProofEnd proof) $ toHtml ("We have " :: Text)
    HaveWeHave ->
        toHtml ("We have " :: Text)
    HaveThus ->
        toHtml ("Thus " :: Text)
    HaveHence ->
        toHtml ("Hence " :: Text)
    HaveThen ->
        toHtml ("Then " :: Text)
    HaveNext ->
        toHtml ("Next " :: Text)
    HaveNow ->
        toHtml ("Now " :: Text)
    HaveFirst ->
        toHtml ("First " :: Text)
    HaveFinally ->
        toHtml ("Finally " :: Text)
    HaveSubsequently ->
        toHtml ("Subsequently " :: Text)
    HaveUltimately ->
        toHtml ("Ultimately " :: Text)
    HaveTherefore ->
        toHtml ("Therefore " :: Text)
    HaveParticularly ->
        toHtml ("Particularly, " :: Text)
    HaveInParticular ->
        toHtml ("In particular, " :: Text)

renderProofContinuation :: RenderEnvironment -> ReferenceContext -> Proof -> Html ()
renderProofContinuation hints references proof =
    unless (isImplicitProofEnd proof) (renderProof hints references proof)

isImplicitProofEnd :: Proof -> Bool
isImplicitProofEnd = \case
    Qed Nothing JustificationImplicit -> True
    _ -> False

proofStepCount :: Proof -> Int
proofStepCount = \case
    Omitted _loc -> 1
    Qed{} -> 1
    Contradiction{} -> 1
    ByCase _loc cases -> 1 + sum (caseStepCount <$> cases)
    ByContradiction _loc proof -> 1 + proofStepCount proof
    BySetInduction _loc _maybeTerm proof -> 1 + proofStepCount proof
    ByOrdInduction _loc proof -> 1 + proofStepCount proof
    ByStructuralInduction _loc _focus cases -> 1 + sum (proofStepCount . namedCaseProof <$> cases)
    Assume _loc _intro _stmt proof -> 1 + proofStepCount proof
    Fix _loc _binders _condition proof -> 1 + proofStepCount proof
    Calc _loc _maybeQuant calc proof -> 1 + calcStepCount calc + proofStepCount proof
    TakeVar _loc _vars _bound _stmt _justification proof -> 1 + proofStepCount proof
    TakeTyped _loc _vars _coreType _stmt _justification proof -> 1 + proofStepCount proof
    TakeNoun _loc _np _justification proof -> 1 + proofStepCount proof
    Have _loc _intro _stmt _justification proof -> 1 + proofStepCount proof
    Since
            _premiseLoc _premise _premiseJustification
            _claimLoc _claim _claimJustification proof ->
        1 + proofStepCount proof
    Suffices _loc _stmt _justification proof -> 1 + proofStepCount proof
    Subclaim _loc _stmt subproof proof -> 1 + proofStepCount subproof + proofStepCount proof
    Define _loc _var _expr proof -> 1 + proofStepCount proof
    DefineTyped _loc _var _coreType _body proof -> 1 + proofStepCount proof
    DefineFunction _loc _fun _arg _value _boundVar _boundExpr proof -> 1 + proofStepCount proof
    DefineFunctionLocal _loc _fun _arg _target _domVar _codVar rules proof ->
        1 + length rules + proofStepCount proof

renderFixBinderList :: RenderEnvironment -> NonEmpty FixBinder -> Html ()
renderFixBinderList hints binders =
    case NonEmpty.toList binders of
        [binder] ->
            renderFixBinder hints binder
        [firstBinder, secondBinder] -> do
            renderFixBinder hints firstBinder
            toHtml (" and " :: Text)
            renderFixBinder hints secondBinder
        firstBinder : secondBinder : remaining -> do
            renderFixBinder hints firstBinder
            toHtml (", " :: Text)
            renderFixBinderListWithFinal hints (secondBinder : remaining)
        [] ->
            impossible "empty Fix binder list"

renderFixBinderListWithFinal
    :: RenderEnvironment
    -> [FixBinder]
    -> Html ()
renderFixBinderListWithFinal hints = \case
    [firstBinder, lastBinder] -> do
        renderFixBinder hints firstBinder
        toHtml (", and " :: Text)
        renderFixBinder hints lastBinder
    firstBinder : remaining -> do
        renderFixBinder hints firstBinder
        toHtml (", " :: Text)
        renderFixBinderListWithFinal hints remaining
    [] ->
        impossible "missing final Fix binder"

renderFixBinder :: RenderEnvironment -> FixBinder -> Html ()
renderFixBinder hints = \case
    FixBinderSymbolic vars bound -> do
        renderVarListInline vars
        renderBoundInline hints vars bound
    FixBinderTyped vars coreType ->
        inlineMath do
            renderVarListMath vars
            moText ":"
            renderConcreteTypeMath coreType

caseStepCount :: Case -> Int
caseStepCount Case{caseProof} = 1 + proofStepCount caseProof

calcStepCount :: Calc -> Int
calcStepCount = \case
    RelationCalculation _ steps -> length steps
    Biconditionals _ steps -> length steps

renderCase :: RenderEnvironment -> ReferenceContext -> Case -> Html ()
renderCase hints references Case{..} =
    term "proof-" do
        if proofStepCount caseProof >= nestedProofCollapseThreshold
            then details_ do
                summary_ (renderCaseLead hints caseOf)
                renderProof hints references caseProof
            else do
                p_ (renderCaseLead hints caseOf)
                renderProof hints references caseProof

renderShowLead :: RenderEnvironment -> Stmt -> Html ()
renderShowLead hints stmt = do
    toHtml ("Show " :: Text)
    renderStmtInline hints stmt
    toHtml ("." :: Text)

renderCaseLead :: RenderEnvironment -> Stmt -> Html ()
renderCaseLead hints stmt = do
    toHtml ("Case " :: Text)
    renderStmtInline hints stmt
    toHtml ("." :: Text)

renderCalc :: RenderEnvironment -> ReferenceContext -> Maybe CalcQuantifier -> Calc -> Html ()
renderCalc hints references maybeQuant calc = do
    p_ do
        toHtml ("Calculation" :: Text)
        case maybeQuant of
            Nothing -> skip
            Just quant -> do
                toHtml (" for " :: Text)
                renderCalcQuantifierInline hints quant
        toHtml ("." :: Text)
    renderCalculationRows hints references calc

renderCalcQuantifierInline :: RenderEnvironment -> CalcQuantifier -> Html ()
renderCalcQuantifierInline hints (CalcQuantifier vars bound maybeStmt) = do
    renderVarListInline vars
    renderBoundInline hints vars bound
    case maybeStmt of
        Nothing -> skip
        Just stmt -> do
            toHtml (" such that " :: Text)
            renderStmtInline hints stmt

renderCalculationRows
    :: RenderEnvironment
    -> ReferenceContext
    -> Calc
    -> Html ()
renderCalculationRows hints references = \case
    RelationCalculation initial links ->
        ol_ [class_ "calculation-chain"]
            (renderRelationRows initial (toList links))
    Biconditionals initial links ->
        ol_ [class_ "calculation-chain"]
            (renderBiconditionalRows initial (toList links))
  where
    renderRelationRows _left [] = skip
    renderRelationRows left
            (CalcRelationLink sign relation right justification : rest) = do
        renderCalculationRow
            (renderExprMathRow hints left)
            (renderCalculationRelationOperator hints sign relation)
            (renderExprMathRow hints right)
            justification
        renderRelationRows right rest

    renderBiconditionalRows _left [] = skip
    renderBiconditionalRows left ((right, justification) : rest) = do
        renderCalculationRow
            (renderFormulaMath hints left)
            (moText "⇔")
            (renderFormulaMath hints right)
            justification
        renderBiconditionalRows right rest

    renderCalculationRow left relation right justification =
        li_ [class_ "calculation-row"] do
            span_ [class_ "calculation-left"] (inlineMath left)
            span_ [class_ "calculation-relation"] (inlineMath relation)
            span_ [class_ "calculation-right"] (inlineMath right)
            case justification of
                JustificationImplicit -> skip
                _ -> span_ [class_ "calculation-reason"] do
                    renderJustification references justification
                    toHtml ("." :: Text)

calcRelationLinkJustification :: CalcRelationLink -> Justification
calcRelationLinkJustification
        (CalcRelationLink _sign _relation _destination justification) =
    justification

renderCalculationRelationOperator
    :: RenderEnvironment
    -> Sign
    -> Relation
    -> Html ()
renderCalculationRelationOperator hints sign relation = do
    applySign sign (renderCalculationRelationOperatorCore hints relation)
    where
        renderCalculationRelationOperatorCore _hints
                (Relation _location EqSymbol []) =
            moText "="
        renderCalculationRelationOperatorCore renderHints
                (Relation _location symbol parameters) =
            renderRelationSymbolCore renderHints symbol parameters
        renderCalculationRelationOperatorCore renderHints
                (RelationExpr _location expression) =
            renderExprMath renderHints expression


renderStmtInline :: RenderEnvironment -> Stmt -> Html ()
renderStmtInline = proseStatement inlineProse


quantifierWord :: Quantifier -> Text
quantifierWord = \case
    Universally -> "for every"
    Existentially -> "there exists"
    Nonexistentially -> "there exists no"

connectiveWord :: Connective -> Text
connectiveWord = \case
    Conjunction -> "and"
    Disjunction -> "or"
    Implication -> "implies"
    Equivalence -> "iff"
    ExclusiveOr -> "xor"
    NegatedDisjunction -> "nor"

renderAsmList :: RenderEnvironment -> [Asm] -> Html ()
renderAsmList hints asms =
    joinHtml (toHtml ("; " :: Text)) (renderAsm hints <$> asms)

renderAsm :: RenderEnvironment -> Asm -> Html ()
renderAsm hints = \case
    AsmSuppose stmt ->
        renderStmtInline hints stmt
    AsmLetNoun vars np -> do
        renderVarListInline vars
        toHtml (" be " :: Text)
        renderNounPhraseMaybeNumber hints (NonEmpty.length vars > 1) np
    AsmLetIn vars expr -> do
        renderVarListInline vars
        toHtml (" be in " :: Text)
        inlineMath (renderExprMathRow hints expr)
    AsmLetRelation vars relation expr ->
        inlineMath
            (renderRelationApplication
                hints Positive
                (ExprVar <$> toList vars)
                relation
                [expr])
    AsmLetThe var fun -> do
        renderVarInline var
        toHtml (" be " :: Text)
        renderFunInline hints renderTermInline' fun
            where renderTermInline' = renderTermInline hints
    AsmLetEq var expr -> do
        renderVarEqInline hints var expr
    AsmLetStruct variables
            (StructNounPhrase modifiers structure right residual) -> do
        let isPlural = NonEmpty.length variables > 1
        renderVarListInline variables
        toHtml (if isPlural then " be " else " be a " :: Text)
        renderAdjListInline hints (renderTermInline hints) modifiers
        renderStructApplicationNumberInline hints isPlural structure
        renderAdjRListInline hints isPlural right
        for_ residual \statement -> do
            toHtml (" such that " :: Text)
            renderStmtInline hints statement


renderTermInline :: RenderEnvironment -> Term -> Html ()
renderTermInline = proseTerm inlineProse

termQuantifierWord :: Quantifier -> Text
termQuantifierWord = \case
    Universally -> "every"
    Existentially -> "some"
    Nonexistentially -> "no"


renderNounPhraseMaybe :: RenderEnvironment -> NounPhrase Maybe -> Html ()
renderNounPhraseMaybe hints = proseNounPhrase inlineProse hints False

renderNounPhraseMaybeNumber
    :: RenderEnvironment
    -> Bool
    -> NounPhrase Maybe
    -> Html ()
renderNounPhraseMaybeNumber = proseNounPhrase inlineProse

renderNounPhraseList :: RenderEnvironment -> NounPhrase [] -> Html ()
renderNounPhraseList = proseNounPhraseList inlineProse

renderDefinitionResultPhrase
    :: RenderEnvironment
    -> DefinitionResultPhrase
    -> Html ()
renderDefinitionResultPhrase hints
        (NounPhrase ls noun (NounBinder Nameless _bound) rs maybeSuchThat) = do
    toHtml (", which is a " :: Text)
    renderAdjListInline hints renderTermInline' ls
    renderNounInline hints False renderTermInline' noun
    renderAdjRListInline hints False rs
    case maybeSuchThat of
        Nothing -> skip
        Just stmt -> do
            toHtml (" such that " :: Text)
            renderStmtInline hints stmt
  where
    renderTermInline' = renderTermInline hints

renderAdjListInline :: RenderEnvironment -> (a -> Html ()) -> [AdjLOf a] -> Html ()
renderAdjListInline = proseLeftAdjectives inlineProse

renderAdjRListInline :: RenderEnvironment -> Bool -> [AdjROf Term] -> Html ()
renderAdjRListInline = proseRightAdjectives inlineProse

renderAdjInline :: RenderEnvironment -> (a -> Html ()) -> AdjOf a -> Html ()
renderAdjInline = proseAdjective inlineProse

renderVerbInline :: RenderEnvironment -> Bool -> (a -> Html ()) -> VerbOf a -> Html ()
renderVerbInline = proseVerb inlineProse


-- Use the parser's lexical name slot, including nouns with arguments before
-- the slot (such as a hyphenated adjective) and trailing parameters.
nounPatternWithBinder
    :: LexicalPhrase -> [a] -> ([Maybe Token], [Maybe a])
nounPatternWithBinder phrase arguments =
    (before <> [Nothing] <> after, map Just leading <> [Nothing] <> map Just trailing)
  where
    (before, after) = splitOnVariableSlot phrase
    (leading, trailing) = List.splitAt (length (List.filter isNothing before)) arguments

renderNounInline :: RenderEnvironment -> Bool -> (a -> Html ()) -> NounOf a -> Html ()
renderNounInline = proseNoun inlineProse

renderFunInline :: RenderEnvironment -> (a -> Html ()) -> FunOf a -> Html ()
renderFunInline = proseFunction inlineProse

renderStructureDeclarationPhraseInline
    :: RenderEnvironment
    -> StructPhrase
    -> [VarSymbol]
    -> Html ()
renderStructureDeclarationPhraseInline hints item parameters =
    renderLexicalItemSgPlInline CanonicalStructureNoun
        hints
        False
        renderVarInline
        item
        parameters

renderStructApplicationInline
    :: RenderEnvironment
    -> StructApplication Term
    -> Html ()
renderStructApplicationInline hints = proseStructure inlineProse hints False

renderStructApplicationNumberInline
    :: RenderEnvironment
    -> Bool
    -> StructApplication Term
    -> Html ()
renderStructApplicationNumberInline = proseStructure inlineProse


renderLexicalItemSgPlInline
    :: (Pattern -> Pattern -> Marker -> CanonicalLexicalEntry)
    -> RenderEnvironment
    -> Bool
    -> (a -> Html ())
    -> LexicalItemSgPl
    -> [a]
    -> Html ()
renderLexicalItemSgPlInline = proseLexicalItem inlineProse


-- Optional symbolic presentation of an otherwise total native phrase. Both
-- inline prose and statement fragments consume this same resolved association.
symbolicPhraseRendering :: RenderEnvironment -> CanonicalLexicalEntry -> Maybe (Html ())
symbolicPhraseRendering environment entry = do
    binding <- nativePhraseBinding entry
    let notation = Contracts.phraseNotation binding
    pieces <- case renderEnvironmentNotationContracts environment of
        Just contracts -> Contracts.applyNotationContract contracts notation ([] :: [Html ()])
        Nothing -> do
            hint <- resolveRenderHint PhraseHint (Contracts.notationMarker notation) 0
                (renderEnvironmentHints environment)
            applyResolvedRenderHint hint ([] :: [Html ()])
    pure (foldMap (either toHtmlRaw id) pieces)

symbolicPhrasePattern :: [Maybe Token] -> Bool
symbolicPhrasePattern = \case
    [Just Command{}] -> True
    _ -> False

data PatternApplicationError = PatternApplicationError
    { patternHoleCount :: !Int
    , patternArgumentCount :: !Int
    } deriving (Show, Eq)

applyPattern
    :: [Maybe token]
    -> [value]
    -> Either PatternApplicationError [Either token value]
applyPattern parts values
    | holeCount /= valueCount =
        Left (PatternApplicationError holeCount valueCount)
    | otherwise = Right (go parts values)
  where
    holeCount = length (List.filter isNothing parts)
    valueCount = length values

    go [] _remaining = []
    go (Just token : rest) remaining =
        Left token : go rest remaining
    go (Nothing : rest) (value : remaining) =
        Right value : go rest remaining
    go (Nothing : rest) [] =
        -- The count check makes this branch unreachable, but keeping the
        -- traversal total avoids rebuilding that invariant into a partial
        -- zipper.
        go rest []

patternApplicationMessage :: PatternApplicationError -> Text
patternApplicationMessage PatternApplicationError{..} =
    "internal render-pattern mismatch: expected "
        <> Text.pack (show patternHoleCount)
        <> " arguments, received "
        <> Text.pack (show patternArgumentCount)


tokensJoin :: Maybe Token -> Maybe Token -> Bool
tokensJoin (Just left) (Just right) =
    Text.isSuffixOf "-" (tokToText left)
        || Text.isPrefixOf "-" (tokToText right)
tokensJoin _ _ = False

renderStmtMath :: RenderEnvironment -> Stmt -> Html ()
renderStmtMath hints =
    renderStmtMathFragments . stmtMathFragments hints

renderStmtMathFragments :: StmtMathFragments -> Html ()
renderStmtMathFragments =
    go ""
    where
        go :: Text -> StmtMathFragments -> Html ()
        go pending = \case
            [] ->
                flush pending
            StmtMathProse text : rest ->
                go (pending <> text) rest
            StmtMathNode node : rest -> do
                flush pending
                node
                go "" rest

        flush :: Text -> Html ()
        flush text =
            let renderedText = preserveBoundarySpaces text
            in unless (Text.null renderedText) (mtextText renderedText)

        preserveBoundarySpaces :: Text -> Text
        preserveBoundarySpaces text =
            Text.replicate leadingCount nbsp
                <> middleText
                <> Text.replicate trailingCount nbsp
            where
                leadingCount = Text.length (Text.takeWhile (== ' ') text)
                textAfterLeading = Text.drop leadingCount text
                trailingCount = Text.length (Text.takeWhileEnd (== ' ') textAfterLeading)
                middleText = Text.dropEnd trailingCount textAfterLeading
                nbsp = Text.singleton '\160'

stmtMathProse :: Text -> StmtMathFragments
stmtMathProse text
    | Text.null text = []
    | otherwise = [StmtMathProse text]

stmtMathNode :: Html () -> StmtMathFragments
stmtMathNode html =
    [StmtMathNode html]


-- One wording policy, with separate inline envelopes and MathML prose nodes.
data ProseOutput result = ProseOutput
    { proseText :: Text -> result
    , proseMath :: Html () -> result
    , proseToken :: Token -> result
    , prosePatternError :: PatternApplicationError -> result
    }

inlineProse :: ProseOutput (Html ())
inlineProse = ProseOutput toHtml inlineMath tokenTextHtml
    (\failure -> span_ [class_ "renderer-invariant-error"]
        (toHtml (patternApplicationMessage failure)))

mathProse :: ProseOutput StmtMathFragments
mathProse = ProseOutput stmtMathProse stmtMathNode token
    (stmtMathProse . patternApplicationMessage)
  where
    token = \case
        Word word -> stmtMathProse word
        Command "in" -> stmtMathNode (moText "∈")
        other -> stmtMathNode (renderMathToken other)

joinProse :: Monoid result => result -> [result] -> result
joinProse _ [] = mempty
joinProse separator (initial : rest) =
    initial <> foldMap (separator <>) rest

stmtMathFragments :: RenderEnvironment -> Stmt -> StmtMathFragments
stmtMathFragments = proseStatement mathProse

proseStatement :: Monoid result => ProseOutput result -> RenderEnvironment -> Stmt -> result
proseStatement output hints = \case
    StmtFormula phi ->
        proseMath output (renderFormulaMath hints phi)
    StmtVerbPhrase ts vp ->
        proseTermList output hints ts
            <> proseText output " "
            <> proseVerbPhrase output hints (length ts > 1) vp
    StmtNoun sign ts np ->
        proseTermList output hints ts
            <> proseText output
                (case (length ts > 1, sign) of
                    (False, Positive) -> " is a "
                    (False, Negative) -> " is not a "
                    (True, Positive) -> " are "
                    (True, Negative) -> " are not ")
            <> proseNounPhrase output hints (length ts > 1) np
    StmtStruct t (StructNounPhrase modifiers structure right residual) ->
        proseTermWithImmediateStructure output hints structure t
            <> proseText output " is a "
            <> proseLeftAdjectives output hints (proseTerm output hints) modifiers
            <> proseStructure output hints False structure
            <> proseRightAdjectives output hints False right
            <> foldMap
                (\statement ->
                    proseText output " such that "
                        <> proseStatement output hints statement)
                residual
    StmtExactStruct t structure ->
        proseTermWithImmediateStructure output hints structure t
            <> proseText output " is an exact "
            <> proseStructure output hints False structure
    StmtNeg _loc stmt ->
        case stmt of
            StmtExists _existsLoc np ->
                proseText output "there exists no "
                    <> proseNounPhraseList output hints np
            StmtQuantPhrase phraseLoc
                    (QuantPhrase Existentially np) body ->
                proseStatement output hints
                    (StmtQuantPhrase phraseLoc
                        (QuantPhrase Nonexistentially np) body)
            SymbolicQuantified quantifiedLoc Existentially
                    vars bound suchThat body ->
                proseStatement output hints
                    (SymbolicQuantified quantifiedLoc Nonexistentially
                        vars bound suchThat body)
            _ ->
                proseText output "it is not the case that "
                    <> proseStatement output hints stmt
    StmtExists _loc np ->
        proseText output "there exists "
            <> proseNounPhraseList output hints np
    StmtConnected conn _loc stmt1 stmt2 ->
        proseConnectedStatement output hints conn stmt1 stmt2
    StmtQuantPhrase _loc qp stmt ->
        proseQuantPhrase output hints qp
            <> proseText output " "
            <> proseStatement output hints stmt
    SymbolicQuantified _loc quant vars bound suchThat stmt ->
        proseText output (quantifierWord quant <> " ")
            <> proseBoundSubject output hints vars bound
            <> proseQuantifiedTail output hints quant suchThat stmt

proseQuantPhrase :: Monoid result => ProseOutput result -> RenderEnvironment -> QuantPhrase -> result
proseQuantPhrase output hints (QuantPhrase quant np) =
    proseText output (quantifierWord quant <> " ")
        <> proseNounPhraseList output hints np

proseConnectedStatement :: Monoid result => ProseOutput result -> RenderEnvironment -> Connective -> Stmt -> Stmt -> result
proseConnectedStatement output hints conn stmt1 stmt2 = case conn of
    ExclusiveOr ->
        proseText output "either "
            <> proseStatement output hints stmt1
            <> proseText output " or "
            <> proseStatement output hints stmt2
    NegatedDisjunction ->
        proseText output "neither "
            <> proseStatement output hints stmt1
            <> proseText output " nor "
            <> proseStatement output hints stmt2
    _ ->
        proseStatement output hints stmt1
            <> proseText output (" " <> connectiveWord conn <> " ")
            <> proseStatement output hints stmt2

proseQuantifiedTail :: Monoid result => ProseOutput result -> RenderEnvironment -> Quantifier -> Maybe Stmt -> Stmt -> result
proseQuantifiedTail output hints quant suchThat stmt =
    case quant of
        Universally ->
            foldMap
                (\suchStmt -> proseText output " such that " <> proseStatement output hints suchStmt)
                suchThat
                <> proseText output " we have "
                <> proseStatement output hints stmt
        Existentially ->
            proseExistentialTail output hints suchThat stmt
        Nonexistentially ->
            proseExistentialTail output hints suchThat stmt

proseExistentialTail :: Monoid result => ProseOutput result -> RenderEnvironment -> Maybe Stmt -> Stmt -> result
proseExistentialTail output hints suchThat stmt =
    proseText output " such that "
        <> case suchThat of
            Nothing ->
                proseStatement output hints stmt
            Just suchStmt ->
                proseStatement output hints suchStmt
                    <> proseText output " and "
                    <> proseStatement output hints stmt

proseTerm :: Monoid result => ProseOutput result -> RenderEnvironment -> Term -> result
proseTerm output hints = \case
    TermExpr expr ->
        proseMath output (renderExprMathRow hints expr)
    TermFun fun ->
        proseText output "the "
            <> proseFunction output hints (proseTerm output hints) fun
    TermIota _loc var stmt ->
        proseText output "the "
            <> proseMath output (renderVarMath var)
            <> proseText output " such that "
            <> proseStatement output hints stmt
    TermQuantified quant _loc np ->
        proseText output (termQuantifierWord quant <> " ")
            <> proseNounPhrase output hints False np

proseTermList :: Monoid result => ProseOutput result -> RenderEnvironment -> NonEmpty Term -> result
proseTermList output hints =
    joinProse (proseText output " and ") . fmap (proseTerm output hints) . toList

-- A Maybe binder inherits the subject's number; list binders supply their own.
proseNounPhrase
    :: (Monoid result, Foldable names)
    => ProseOutput result
    -> RenderEnvironment
    -> Bool
    -> NounPhrase names
    -> result
proseNounPhrase output hints isPlural
        (NounPhrase ls noun (NounBinder names bound) rs maybeSuchThat) =
    proseLeftAdjectives output hints (proseTerm output hints) ls
        <> proseNamedNoun output hints isPlural noun (toList names) bound
        <> proseRightAdjectives output hints isPlural rs
        <> foldMap (\stmt -> proseText output " such that " <> proseStatement output hints stmt) maybeSuchThat

proseNounPhraseList :: Monoid result => ProseOutput result -> RenderEnvironment -> NounPhrase [] -> result
proseNounPhraseList output hints phrase@(NounPhrase _ _ (NounBinder names _) _ _) =
    proseNounPhrase output hints (length names > 1) phrase

proseLeftAdjectives
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> (a -> result)
    -> [AdjLOf a]
    -> result
proseLeftAdjectives output hints renderArg adjs =
    if null adjs
        then mempty
        else joinProse
                (proseText output " ")
                (proseLeftAdjective output hints renderArg <$> adjs)
            <> proseText output " "

proseRightAdjectives
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> Bool
    -> [AdjROf Term]
    -> result
proseRightAdjectives output hints isPlural adjs =
    if null adjs
        then mempty
        else proseText output " "
            <> joinProse
                (proseText output " and ")
                (proseRightAdjective output hints isPlural <$> adjs)

proseLeftAdjective
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> (a -> result)
    -> AdjLOf a
    -> result
proseLeftAdjective output hints renderArg (AdjL _loc item args) =
    proseAdjectiveLexicalItem output hints renderArg item args

proseRightAdjective
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> Bool
    -> AdjROf Term
    -> result
proseRightAdjective output hints isPlural = \case
    AdjR _loc item args ->
        proseAdjectiveLexicalItem output
            hints
            (proseTerm output hints)
            item
            args
    AttrRThat verbPhrase ->
        proseText output "that "
            <> proseVerbPhrase output hints isPlural verbPhrase

proseAdjective
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> (a -> result)
    -> AdjOf a
    -> result
proseAdjective output hints renderArg (Adj _loc item args) =
    proseAdjectiveLexicalItem output hints renderArg item args

proseVerb
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> Bool
    -> (a -> result)
    -> VerbOf a
    -> result
proseVerb output hints isPlural renderArg (Verb _loc item args) =
    proseLexicalPattern output
        hints
        (CanonicalVerb (verbLexicalSurfaces item) (verbLexicalMarker item))
        renderArg
        (if isPlural
            then verbSurfaceBase (verbLexicalSurfaces item)
            else verbSurfaceSingular (verbLexicalSurfaces item))
        args

proseVerbPhrase :: Monoid result => ProseOutput result -> RenderEnvironment -> Bool -> VerbPhrase -> result
proseVerbPhrase output hints isPlural = \case
    VPVerb verb ->
        proseVerb output hints isPlural (proseTerm output hints) verb
    VPAdj adjs ->
        proseText output (if isPlural then "are " else "is ")
            <> joinProse
                (proseText output " and ")
                (proseAdjective output hints (proseTerm output hints)
                    <$> toList adjs)
    VPVerbNot verb ->
        proseText output (if isPlural then "do not " else "does not ")
            <> proseVerb output hints True (proseTerm output hints) verb
    VPAdjNot adjs ->
        proseText output (if isPlural then "are not " else "is not ")
            <> joinProse
                (proseText output " and ")
                (proseAdjective output hints (proseTerm output hints)
                    <$> toList adjs)

proseNoun
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> Bool
    -> (a -> result)
    -> NounOf a
    -> result
proseNoun output hints isPlural renderArg (Noun _loc item args) =
    proseLexicalItem output CanonicalNoun hints isPlural renderArg item args

proseFunction
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> (a -> result)
    -> FunOf a
    -> result
proseFunction output hints renderArg Fun{phrase, funArgs} =
    proseLexicalItem output CanonicalFunctionPhrase hints False renderArg phrase funArgs

proseStructure
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> Bool
    -> StructApplication Term
    -> result
proseStructure output hints isPlural
        (StructApplication item arguments) =
    proseLexicalItem output CanonicalStructureNoun
        hints
        isPlural
        (proseTerm output hints)
        item
        arguments

proseAdjectiveLexicalItem
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> (a -> result)
    -> AdjectiveLexicalItem
    -> [a]
    -> result
proseAdjectiveLexicalItem output hints renderArg item args =
    proseLexicalPattern output hints (adjectivePhraseEntry item) renderArg
        (adjectiveLexicalPhrase item) args

proseLexicalItem
    :: Monoid result => ProseOutput result -> (Pattern -> Pattern -> Marker -> CanonicalLexicalEntry)
    -> RenderEnvironment
    -> Bool
    -> (a -> result)
    -> LexicalItemSgPl
    -> [a]
    -> result
proseLexicalItem output constructor hints isPlural renderArg item args =
    proseLexicalPattern output
        hints
        (numberedPhraseEntry constructor item)
        renderArg
        phrase
        args
    where
        phrase = if isPlural then pl (lexicalItemSgPlPhrase item) else sg (lexicalItemSgPlPhrase item)

proseLexicalPattern
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> CanonicalLexicalEntry
    -> (a -> result)
    -> [Maybe Token]
    -> [a]
    -> result
proseLexicalPattern output hints entry renderArg patternParts args
    | symbolicPhrasePattern patternParts
    , null args
    , Just rendered <- symbolicPhraseRendering hints entry = proseMath output rendered
    | otherwise = prosePattern output renderArg patternParts args

prosePattern :: Monoid result => ProseOutput result -> (a -> result) -> [Maybe Token] -> [a] -> result
prosePattern output renderArg patternParts args =
    case applyPattern patternParts args of
        Left failure ->
            prosePatternError output failure
        Right pieces ->
            joinPatternFragments (toStatementPiece <$> pieces)
    where
        toStatementPiece = \case
            Left token -> (Just token, proseToken output token)
            Right value -> (Nothing, renderArg value)

        joinPatternFragments [] = mempty
        joinPatternFragments ((firstToken, initial) : rest) =
            initial <> joinRest firstToken rest

        joinRest _previous [] = mempty
        joinRest previous ((next, fragments) : rest) =
            (if tokensJoin previous next then mempty else proseText output " ")
                <> fragments
                <> joinRest next rest

proseNamedNoun
    :: Monoid result => ProseOutput result -> RenderEnvironment -> Bool -> Noun -> [VarSymbol] -> Bound -> result
proseNamedNoun output hints isPlural noun@(Noun _ item arguments) names bound =
    case NonEmpty.nonEmpty names of
        Nothing -> proseNoun output hints isPlural (proseTerm output hints) noun
        Just variables
            | symbolicPhrasePattern phrase ->
                proseNoun output hints isPlural (proseTerm output hints) noun
                    <> proseText output " " <> proseBoundSubject output hints variables bound
            | otherwise ->
                let (patternParts, values) = nounPatternWithBinder phrase arguments
                in prosePattern output
                    (maybe (proseBoundSubject output hints variables bound) (proseTerm output hints))
                    patternParts values
  where
    phrase = (if isPlural then pl else sg) (lexicalItemSgPlPhrase item)

proseTermWithImmediateStructure
    :: Monoid result => ProseOutput result -> RenderEnvironment
    -> StructApplication Term
    -> Term
    -> result
proseTermWithImmediateStructure output hints structure = \case
    TermExpr expression ->
        proseMath output
            (renderExprMathRowWithImmediateStructure
                hints structure expression)
    candidate ->
        proseTerm output hints candidate

proseBoundSubject :: ProseOutput result -> RenderEnvironment -> NonEmpty VarSymbol -> Bound -> result
proseBoundSubject output hints vars bound =
    proseMath output (renderBoundSubjectMath hints vars bound)


renderFormulaMath :: RenderEnvironment -> Formula -> Html ()
renderFormulaMath hints = \case
    FormulaChain chain ->
        renderChainMathRow hints chain
    FormulaSetMap _location function domain codomain -> do
        renderExprMath hints function
        moText ":"
        renderExprMath hints domain
        moText "→"
        renderExprMath hints codomain
    FormulaExpression expr ->
        renderExprMath hints expr
    FormulaPredicate _loc predi marker exprs ->
        renderNotationMath True hints (Contracts.predicateNotation predi marker) (toList exprs) (renderPrefixPredicateFallback predi (renderExprMath hints <$> toList exprs))
    Connected _loc conn phi psi -> do
        renderFormulaMath hints phi
        moText (connectiveSymbol conn)
        renderFormulaMath hints psi
    FormulaNeg _loc phi -> do
        moText "¬"
        renderFormulaMath hints phi
    FormulaQuantified _loc quant vars bound phi -> do
        moText (quantifierSymbol quant)
        renderVarListMath vars
        renderBoundMath hints vars bound
        moText "."
        renderFormulaMath hints phi
    FormulaTypedQuantified _loc quant vars coreType phi -> do
        moText (quantifierSymbol quant)
        renderVarListMath vars
        moText ":"
        renderConcreteTypeMath coreType
        moText "."
        renderFormulaMath hints phi
    PropositionalConstant _loc pc ->
        moText (propositionalConstantSymbol pc)

connectiveSymbol :: Connective -> Text
connectiveSymbol = \case
    Conjunction -> "∧"
    Disjunction -> "∨"
    Implication -> "⇒"
    Equivalence -> "⇔"
    ExclusiveOr -> "⊕"
    NegatedDisjunction -> "↓"

quantifierSymbol :: Quantifier -> Text
quantifierSymbol = \case
    Universally -> "∀"
    Existentially -> "∃"
    Nonexistentially -> "∄"

propositionalConstantSymbol :: PropositionalConstant -> Text
propositionalConstantSymbol = \case
    IsBottom -> "⊥"
    IsTop -> "⊤"

renderChainMathRow :: RenderEnvironment -> Chain -> Html ()
renderChainMathRow hints chain =
    joinHtml (moText "∧") (renderLink <$> splatChain chain)
    where
        renderLink (lhs, sign, rel, rhs) =
            renderRelationApplication hints sign (toList lhs) rel (toList rhs)

        splatChain :: Chain -> [(NonEmpty Expr, Sign, Relation, NonEmpty Expr)]
        splatChain = \case
            ChainBase es sign rel es' ->
                [(es, sign, rel, es')]
            ChainCons es sign rel ch'@(ChainBase es' _ _ _) ->
                (es, sign, rel, es') : splatChain ch'
            ChainCons es sign rel ch'@(ChainCons es' _ _ _) ->
                (es, sign, rel, es') : splatChain ch'

renderBoundMath :: RenderEnvironment -> NonEmpty VarSymbol -> Bound -> Html ()
renderBoundMath hints vars = \case
    Unbounded -> skip
    Bounded _loc sign rel expr -> do
        moText ","
        renderRelationApplication hints sign (ExprVar <$> toList vars) rel [expr]

renderRelationApplication :: RenderEnvironment -> Sign -> [Expr] -> Relation -> [Expr] -> Html ()
renderRelationApplication hints sign lhs rel rhs = case (sign, rel) of
    (Negative, Relation _loc symbol [])
        | Just negated <- negatedRelationSymbol (relationSymbolToken symbol) -> do
            renderExprListMath hints lhs
            moText negated
            renderExprListMath hints rhs
    _ ->
        applySign sign (renderRelationCore hints lhs rel rhs)

applySign :: Sign -> Html () -> Html ()
applySign sign html = case sign of
    Positive -> html
    Negative -> do
        mo_ "¬"
        html

renderRelationCore :: RenderEnvironment -> [Expr] -> Relation -> [Expr] -> Html ()
renderRelationCore hints lhs rel rhs = case rel of
    Relation _loc symbol relParams -> do
        renderExprListMath hints lhs
        renderRelationSymbolCore hints symbol relParams
        renderExprListMath hints rhs
    RelationExpr _loc expr -> do
        renderExprListMath hints lhs
        renderExprMath hints expr
        renderExprListMath hints rhs

renderRelationSymbolCore :: RenderEnvironment -> RelationSymbol -> [Expr] -> Html ()
renderRelationSymbolCore hints symbol relParams =
    renderNotationMath True
        hints
        (Contracts.relationNotation symbol)
        relParams
        (renderRelationFallback hints symbol relParams)

renderRelationFallback :: RenderEnvironment -> RelationSymbol -> [Expr] -> Html ()
renderRelationFallback hints symbol relParams =
    merror_ (renderRelationFallbackCore hints symbol relParams)

renderRelationFallbackCore :: RenderEnvironment -> RelationSymbol -> [Expr] -> Html ()
renderRelationFallbackCore hints symbol relParams
    | null relParams = renderRelationToken (relationSymbolToken symbol)
    | otherwise = msub_ do
        renderRelationToken (relationSymbolToken symbol)
        mrow_ (renderExprListMath hints relParams)

renderRelationToken :: Token -> Html ()
renderRelationToken = \case
    Command "in" -> moText "∈"
    Command "ni" -> moText "∋"
    Command "notin" -> moText "∉"
    Command "meets" -> moText "⋈"
    Command "notmeets" -> moText "⋈̸"
    Command "subset" -> moText "⊂"
    Command "subseteq" -> moText "⊆"
    Command "supset" -> moText "⊃"
    Command "supseteq" -> moText "⊇"
    Command "neq" -> moText "≠"
    tok -> renderMathToken tok

negatedRelationSymbol :: Token -> Maybe Text
negatedRelationSymbol = \case
    Command "in" -> Just "∉"
    Command "ni" -> Just "∌"
    Command "subset" -> Just "⊄"
    Command "subseteq" -> Just "⊈"
    Command "supset" -> Just "⊅"
    Command "supseteq" -> Just "⊉"
    Command "meets" -> Just "⋈̸"
    Symbol "=" -> Just "≠"
    Symbol "<" -> Just "≮"
    Symbol ">" -> Just "≯"
    Symbol "≤" -> Just "≰"
    Symbol "≥" -> Just "≱"
    _ -> Nothing


renderExprMath :: RenderEnvironment -> Expr -> Html ()
renderExprMath hints expr = case expr of
    ExprVar var ->
        renderVarMath var
    ExprNaturalNumeral _loc n ->
        mnText (Text.pack (show n))
    ExprOpaqueInteger _loc n ->
        renderOpaqueInteger n
    ExprTypedConstant _loc constantToken _coreType ->
        renderMathToken constantToken
    ExprHigherApply{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprLambda{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprSelect{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprOp _loc item args ->
        renderNotationMath False hints (Contracts.operatorNotation item) args (renderPatternFallback (mixfixPattern item) (renderExprMath hints <$> args))
    ExprStructOp _loc symb maybeExpr ->
        let args = maybeToList maybeExpr
        in renderNotationMath False hints (Contracts.fieldNotation symb maybeExpr) args (renderStructFallback symb (renderExprMath hints <$> args))
    ExprFiniteSet{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprSep{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprReplace{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprReplacePred{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprStructAggregate{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprStructReduct{} ->
        mrow_ (renderExprMathRow hints expr)
    ExprStructReconstruction{} ->
        mrow_ (renderExprMathRow hints expr)

renderOpaqueInteger :: Integer -> Html ()
renderOpaqueInteger integer =
    mtextText ("\\opaqueInteger{" <> Text.pack (show integer) <> "}")

renderExprMathRow :: RenderEnvironment -> Expr -> Html ()
renderExprMathRow hints = \case
    ExprVar var ->
        renderVarMath var
    ExprNaturalNumeral _loc n ->
        mnText (Text.pack (show n))
    ExprOpaqueInteger _loc n ->
        renderOpaqueInteger n
    ExprTypedConstant _loc constantToken _coreType ->
        renderMathToken constantToken
    expression@ExprHigherApply{} -> do
        let (function, arguments) = flattenHigherApplication expression
        renderTypedExpressionMath hints function
        moText "("
        joinHtml
            (moText ",")
            (renderTypedExpressionMath hints <$> arguments)
        moText ")"
    ExprLambda _loc variables coreType body -> do
        moText "λ"
        renderVarListMath variables
        moText ":"
        renderConcreteTypeMath coreType
        moText "."
        renderTypedExpressionMath hints body
    ExprSelect _loc maybeCoreType predicate -> do
        miText "Select"
        for_ maybeCoreType \coreType -> do
            moText "["
            renderConcreteTypeMath coreType
            moText "]"
        moText "("
        renderTypedExpressionMath hints predicate
        moText ")"
    ExprOp _loc item args ->
        renderNotationMath True hints (Contracts.operatorNotation item) args (renderPatternFallback (mixfixPattern item) (renderExprMath hints <$> args))
    ExprStructOp _loc symb maybeExpr ->
        let args = maybeToList maybeExpr
        in renderNotationMath True hints (Contracts.fieldNotation symb maybeExpr) args (renderStructFallback symb (renderExprMath hints <$> args))
    ExprFiniteSet _loc exprs ->
        renderFiniteSetMath hints (toList exprs)
    ExprSep _loc var bound stmt -> do
        moText "{"
        renderVarMath var
        moText "∈"
        renderExprMathRow hints bound
        moText "|"
        renderStmtMath hints stmt
        moText "}"
    ExprReplace _loc expr bounds maybeStmt -> do
        moText "{"
        renderExprMathRow hints expr
        moText "|"
        renderReplaceBoundsMath hints (toList bounds)
        for_ maybeStmt \stmt -> do
            moText "|"
            renderStmtMath hints stmt
        moText "}"
    ExprReplacePred _loc rangeVar domVar domExpr stmt -> do
        moText "{"
        renderVarMath rangeVar
        moText "|"
        moText "∃"
        renderVarMath domVar
        moText "∈"
        renderExprMathRow hints domExpr
        moText "."
        renderStmtMath hints stmt
        moText "}"
    ExprStructAggregate _loc maybeSchema entries ->
        renderStructureAggregate hints Nothing maybeSchema entries
    ExprStructReduct _loc schema record -> do
        miText "reduct"
        moText "["
        renderStructApplicationMath hints schema
        moText "]"
        moText "("
        renderExprMathRow hints record
        moText ")"
    ExprStructReconstruction _loc schema record entries ->
        renderStructureReconstruction hints schema record entries

flattenHigherApplication :: Expr -> (TypedExpression, [TypedExpression])
flattenHigherApplication = go []
  where
    go arguments = \case
        ExprHigherApply _location function argument ->
            case function of
                TypedExpressionExpr nested@ExprHigherApply{} ->
                    go (argument : arguments) nested
                _ ->
                    (function, argument : arguments)
        expression ->
            (TypedExpressionExpr expression, arguments)

renderStructApplicationMath
    :: RenderEnvironment
    -> StructApplication Expr
    -> Html ()
renderStructApplicationMath hints
        (StructApplication item arguments) =
    case applyPattern (patternToHoley (sg (lexicalItemSgPlPattern item))) arguments of
        Left failure -> merror_ (mtextText (patternApplicationMessage failure))
        Right pieces -> renderPieces Nothing pieces
  where
    renderPieces _ [] = skip
    renderPieces previous (piece : remaining) = do
        let token = either Just (const Nothing) piece
        when (isJust previous && not (tokensJoin (fromMaybe Nothing previous) token))
            (mtextText " ")
        either (mtextText . tokToText) (renderExprMath hints) piece
        renderPieces (Just token) remaining

renderStructAggregateEntryMath
    :: RenderEnvironment
    -> StructAggregateEntry
    -> Html ()
renderStructAggregateEntryMath hints = \case
    StructAggregatePositional expression ->
        renderExprMathRow hints expression
    StructAggregateNamed _location symbol expression -> do
        renderStructSymbolName symbol
        moText "="
        renderExprMathRow hints expression

renderExprMathRowWithImmediateStructure
    :: RenderEnvironment
    -> StructApplication Term
    -> Expr
    -> Html ()
renderExprMathRowWithImmediateStructure hints structure = \case
    ExprStructAggregate _location maybeSchema entries ->
        renderStructureAggregate
            hints
            (Just (termStructureApplicationPresentation structure))
            maybeSchema
            entries
    expression ->
        renderExprMathRow hints expression



renderStructureReconstruction
    :: RenderEnvironment -> StructApplication Expr -> Expr -> [StructAggregateEntry]
    -> Html ()
renderStructureReconstruction hints schema record entries =
    case Map.lookup marker (renderEnvironmentStructureSchemas hints) of
        Nothing -> body
        Just (StructureSchemaPresentation identity fields) ->
            mrow_
                [ class_ "structure-reconstruction has-schema-tooltip"
                , makeAttributes "data-structure-id" identity
                , makeAttributes "title" ("Exact record for " <> label
                    <> "; schema " <> identity <> "; field mapping: "
                    <> Text.intercalate ", " (mapping <$> fields)
                    <> "; field specifications and laws require the structure predicate")
                , makeAttributes "tabindex" "0"
                ] body
  where
    (marker, label) = exprStructureApplicationPresentation schema
    mapping (symbol, identity) = structSymbolText symbol <> " [" <> identity <> "] ← "
        <> case List.findIndex (\case
                StructAggregateNamed _ candidate _ -> candidate == symbol
                StructAggregatePositional{} -> False) entries of
            Just index -> "replacement " <> Text.pack (show (index + 1))
            Nothing -> "base"
    body = do
        moText "("
        renderStructApplicationMath hints schema
        mtextText " based on "
        renderExprMath hints record
        for_ (zip [0 :: Int ..] entries) \(index, entry) -> do
            mtextText (if index == 0 then " with " else " and ")
            case entry of
                StructAggregateNamed _ (StructSymbol name) value -> do
                    miText name
                    moText "="
                    renderExprMath hints value
                StructAggregatePositional value -> renderExprMath hints value
        moText ")"

renderStructureAggregate
    :: RenderEnvironment
    -> Maybe (Marker, Text)
    -> Maybe (StructApplication Expr)
    -> [StructAggregateEntry]
    -> Html ()
renderStructureAggregate hints contextualSchema annotatedSchema entries =
    case presentation of
        Nothing -> renderAggregateBody
        Just (schemaLabel, schemaPresentation) ->
            mrow_
                [ class_ "structure-aggregate has-schema-tooltip"
                , makeAttributes "title"
                    (aggregatePresentationText
                        schemaLabel schemaPresentation entries)
                , makeAttributes "tabindex" "0"
                ]
                renderAggregateBody
  where
    selectedSchema =
        case annotatedSchema of
            Just application ->
                Just (exprStructureApplicationPresentation application)
            Nothing -> contextualSchema
    presentation = do
        (marker, schemaLabel) <- selectedSchema
        schemaPresentation <-
            Map.lookup marker (renderEnvironmentStructureSchemas hints)
        pure (schemaLabel, schemaPresentation)

    renderAggregateBody = do
        moText "⟨"
        joinHtml
            (moText ",")
            (renderStructAggregateEntryMath hints <$> entries)
        moText "⟩"

aggregatePresentationText
    :: Text
    -> StructureSchemaPresentation
    -> [StructAggregateEntry]
    -> Text
aggregatePresentationText schemaLabel schemaPresentation entries =
    "Exact record for " <> schemaLabel
        <> mappingText
        <> "; field specifications and laws require the structure predicate"
  where
    fields = structureSchemaPresentationFields schemaPresentation
    positions =
        case entries of
            [] -> []
            StructAggregatePositional{} : _ ->
                zip fields [1 :: Int ..]
            StructAggregateNamed{} : _ ->
                [ (field, index)
                | field <- fields
                , Just index <-
                    [ (+ 1) <$> List.findIndex
                        (entryNames field)
                        entries
                    ]
                ]
    entryNames field = \case
        StructAggregateNamed _location candidate _value ->
            candidate == field
        StructAggregatePositional{} -> False
    mappingText =
        case positions of
            [] -> ""
            _ ->
                "; field mapping: "
                    <> Text.intercalate ", "
                        [ structSymbolText field
                            <> " ← entry " <> Text.pack (show position)
                        | (field, position) <- positions
                        ]

structSymbolText :: StructSymbol -> Text
structSymbolText (StructSymbol name) = name

exprStructureApplicationPresentation
    :: StructApplication Expr
    -> (Marker, Text)
exprStructureApplicationPresentation
        (StructApplication phrase arguments) =
    ( lexicalItemSgPlMarker phrase
    , structureApplicationText phrase
        (expressionPresentationText <$> arguments)
    )

termStructureApplicationPresentation
    :: StructApplication Term
    -> (Marker, Text)
termStructureApplicationPresentation
        (StructApplication phrase arguments) =
    ( lexicalItemSgPlMarker phrase
    , structureApplicationText phrase
        (termPresentationText <$> arguments)
    )

structureApplicationText
    :: LexicalItemSgPl
    -> [Text]
    -> Text
structureApplicationText phrase arguments =
    Text.unwords (go (sg (lexicalItemSgPlPhrase phrase)) arguments)
  where
    go [] [] = []
    go [] (_ : _) = ["…"]
    go (Nothing : rest) (argument : remaining) =
        argument : go rest remaining
    go (Nothing : rest) [] =
        "…" : go rest []
    go (Just token : rest) remaining =
        tokToText token : go rest remaining

termPresentationText :: Term -> Text
termPresentationText = \case
    TermExpr expression -> expressionPresentationText expression
    _ -> "…"

expressionPresentationText :: Expr -> Text
expressionPresentationText = \case
    ExprVar (NamedVarAt _location name) ->
        renderVariableText name
    ExprVar (FreshVarAt _location index) ->
        "_" <> Text.pack (show index)
    ExprNaturalNumeral _location integer ->
        Text.pack (show integer)
    ExprOpaqueInteger _location integer ->
        "\\opaqueInteger{" <> Text.pack (show integer) <> "}"
    ExprTypedConstant _location token _coreType ->
        tokToText token
    _ -> "…"

renderTypedExpressionMath :: RenderEnvironment -> TypedExpression -> Html ()
renderTypedExpressionMath hints = \case
    TypedExpressionExpr expr -> renderExprMath hints expr
    TypedExpressionFormula phi -> renderFormulaMath hints phi

renderReplaceBoundsMath :: RenderEnvironment -> [(VarSymbol, Expr)] -> Html ()
renderReplaceBoundsMath hints =
    joinHtml (moText ",") . fmap renderBound
    where
        renderBound (var, expr) = do
            renderVarMath var
            moText "∈"
            renderExprMathRow hints expr

renderExprListMath :: RenderEnvironment -> [Expr] -> Html ()
renderExprListMath hints =
    joinHtml (moText ",") . fmap (renderExprMath hints)

renderFiniteSetMath :: RenderEnvironment -> [Expr] -> Html ()
renderFiniteSetMath hints exprs =
    do
        moText "{"
        renderExprListMath hints exprs
        moText "}"

-- Checked pages consume the resolved binding contract. Parse-only/synthetic
-- pages deliberately retain the raw notation path.
renderNotationMath :: Bool -> RenderEnvironment -> Contracts.Notation -> [Expr] -> Html () -> Html ()
renderNotationMath row hints notation args fallback =
    case pieces of
        Nothing -> fallback
        Just values | row -> traverse_ renderPiece values
        Just [value] -> renderPiece value
        Just values -> mrow_ (traverse_ renderPiece values)
  where
    renderedArguments = renderExprMath hints <$> args
    pieces = case renderEnvironmentNotationContracts hints of
        Nothing -> applyRenderHint (Contracts.notationCategory notation) (Contracts.notationMarker notation) renderedArguments (renderEnvironmentHints hints)
        Just contracts -> Contracts.applyNotationContract contracts notation renderedArguments
    renderPiece = either toHtmlRaw id

renderHintedMath :: RenderEnvironment -> HintCategory -> Marker -> [Expr] -> Html () -> Html ()
renderHintedMath hints category marker args fallback =
    case applyRenderHint
            category
            marker
            renderedArgs
            (renderEnvironmentHints hints) of
        Nothing ->
            fallback
        Just pieces ->
            renderTemplateAsNode pieces
    where
        renderedArgs = renderExprMath hints <$> args

        renderTemplateAsNode :: [Either Text (Html ())] -> Html ()
        renderTemplateAsNode = \case
            [piece] ->
                renderPiece piece
            pieces ->
                mrow_ (traverse_ renderPiece pieces)

        renderPiece :: Either Text (Html ()) -> Html ()
        renderPiece = \case
            Left text -> toHtmlRaw text
            Right html -> html

renderPatternFallback :: Pattern -> [Html ()] -> Html ()
renderPatternFallback patternParts renderedArgs =
    merror_ (renderPatternMath patternParts renderedArgs)

renderPatternMath :: Pattern -> [Html ()] -> Html ()
renderPatternMath patternParts renderedArgs =
    case applyPattern (patternToHoley patternParts) renderedArgs of
        Left failure ->
            merror_ (mtextText (patternApplicationMessage failure))
        Right pieces ->
            traverse_ (either renderMathToken id) pieces

renderPrefixPredicateFallback :: PrefixPredicate -> [Html ()] -> Html ()
renderPrefixPredicateFallback (PrefixPredicate command _arity) renderedArgs =
        merror_ do
        miText command
        when (not (null renderedArgs)) do
            moText "("
            joinHtml (moText ",") renderedArgs
            moText ")"

renderStructFallback :: StructSymbol -> [Html ()] -> Html ()
renderStructFallback symb renderedArgs =
    merror_ do
        renderStructSymbolName symb
        when (not (null renderedArgs)) do
            moText "("
            joinHtml (moText ",") renderedArgs
            moText ")"

renderStructSymbolName :: StructSymbol -> Html ()
renderStructSymbolName (StructSymbol name) = miText name

renderMathToken :: Token -> Html ()
renderMathToken = \case
    NamedItem name -> mtextText name
    CaseHeading _ -> miText "caseOf"
    Word w -> miText w
    Variable v -> renderNamedVariableMath v
    Symbol s -> moText s
    Integer n -> mnText (Text.pack (show n))
    Command cmd -> miText cmd
    CommandReference command references ->
        mtextText
            ( command <> ":"
                <> Text.intercalate "," (toList references)
            )
    Label m -> mtextText ("label:" <> m)
    Ref ms -> mtextText ("ref:" <> Text.intercalate "," (toList ms))
    BeginEnv env -> mtextText ("begin:" <> env)
    EndEnv env -> mtextText ("end:" <> env)
    ParenL -> moText "("
    ParenR -> moText ")"
    BracketL -> moText "["
    BracketR -> moText "]"
    VisibleBraceL -> moText "{"
    VisibleBraceR -> moText "}"
    InvisibleBraceL -> moText "("
    InvisibleBraceR -> moText ")"


inlineMath :: Html () -> Html ()
inlineMath inner = math_ inner

blockMath :: Html () -> Html ()
blockMath inner = math_ [displayblock_] inner

renderVarInline :: VarSymbol -> Html ()
renderVarInline = inlineMath . renderVarMath

renderVarMath :: VarSymbol -> Html ()
renderVarMath = \case
    NamedVarAt _loc name ->
        renderNamedVariableMath name
    FreshVarAt _loc n ->
        miText ("_" <> Text.pack (show n))

renderNamedVariableMath :: Text -> Html ()
renderNamedVariableMath rawName =
    case displayVariable rawName of
        VariableDisplay baseText Nothing ->
            miText baseText
        VariableDisplay baseText (Just (VariableTicks tickCount)) ->
            msup_ do
                miText baseText
                renderPrimeSuperscript tickCount
        VariableDisplay baseText (Just (VariableSubscript subscriptText)) ->
            msub_ do
                miText baseText
                renderVariableSubscriptMath subscriptText

renderPrimeSuperscript :: Int -> Html ()
renderPrimeSuperscript tickCount
    | tickCount <= 1 =
        moText "′"
    | otherwise =
        mrow_ (foldMap (const (moText "′")) [1 .. tickCount])

renderVariableSubscriptMath :: Text -> Html ()
renderVariableSubscriptMath subscriptText
    | Text.all isDigit subscriptText =
        mnText subscriptText
    | otherwise =
        miText subscriptText

renderVarEqInline :: RenderEnvironment -> VarSymbol -> Expr -> Html ()
renderVarEqInline hints var expr =
    inlineMath do
        renderVarMath var
        moText "="
        renderExprMathRow hints expr

renderFunctionCallInline :: VarSymbol -> VarSymbol -> Html ()
renderFunctionCallInline fun arg =
    inlineMath (renderFunctionCallMath fun arg)

renderFunctionEqInline :: RenderEnvironment -> VarSymbol -> VarSymbol -> Expr -> Html ()
renderFunctionEqInline hints fun arg expr =
    inlineMath do
        renderFunctionCallMath fun arg
        moText "="
        renderExprMathRow hints expr

renderFunctionCallMath :: VarSymbol -> VarSymbol -> Html ()
renderFunctionCallMath fun arg = do
    renderVarMath fun
    moText "("
    renderVarMath arg
    moText ")"

renderVarListInline :: NonEmpty VarSymbol -> Html ()
renderVarListInline vars =
    inlineMath (renderVarListMath vars)

renderVarListMath :: NonEmpty VarSymbol -> Html ()
renderVarListMath vars =
    joinHtml (moText ",") (renderVarMath <$> toList vars)

renderBoundInline :: RenderEnvironment -> NonEmpty VarSymbol -> Bound -> Html ()
renderBoundInline hints vars = \case
    Unbounded -> skip
    bound -> do
        toHtml (" with " :: Text)
        inlineMath (renderBoundPhraseMath hints vars bound)


renderBoundPhraseMath :: RenderEnvironment -> NonEmpty VarSymbol -> Bound -> Html ()
renderBoundPhraseMath hints vars = \case
    Unbounded -> mrow_ skip
    Bounded _loc sign rel expr ->
        renderRelationApplication hints sign (ExprVar <$> toList vars) rel [expr]

renderBoundSubjectMath :: RenderEnvironment -> NonEmpty VarSymbol -> Bound -> Html ()
renderBoundSubjectMath hints vars = \case
    Unbounded ->
        renderVarListMath vars
    Bounded _loc sign rel expr ->
        renderRelationApplication hints sign (ExprVar <$> toList vars) rel [expr]


renderSymbolPatternInline :: RenderEnvironment -> SymbolPattern -> Html ()
renderSymbolPatternInline hints =
    inlineMath . renderSymbolPatternMath hints

renderSymbolPatternMath :: RenderEnvironment -> SymbolPattern -> Html ()
renderSymbolPatternMath hints (SymbolPattern symbol vars) =
    renderNotationMath True hints (Contracts.operatorNotation symbol) (ExprVar <$> vars) (renderPatternFallback (mixfixPattern symbol) (renderVarMath <$> vars))

renderJustification :: ReferenceContext -> Justification -> Html ()
renderJustification references = \case
    JustificationAuto markers ->
        renderAutomationJustification references "auto" markers
    JustificationObviousReferences markers ->
        renderAutomationJustification references "obvious" (Just markers)
    JustificationSetExt ->
        toHtml ("by set extensionality" :: Text)
    JustificationStructureExt ->
        toHtml ("by structure extensionality" :: Text)
    JustificationExtensionality ->
        toHtml ("by extensionality" :: Text)
    JustificationImplicit ->
        skip
    JustificationAssumption ->
        toHtml ("by assumption" :: Text)
    JustificationDefinition ->
        toHtml ("by definition" :: Text)
    JustificationNotion ->
        toHtml ("by notion" :: Text)

renderAutomationJustification
    :: ReferenceContext
    -> Text
    -> Maybe (NonEmpty Marker)
    -> Html ()
renderAutomationJustification references method markers = do
    toHtml ("by " <> method)
    for_ markers \selected -> do
        toHtml (" using " :: Text)
        renderMarkerReferences
            FormalJustificationReference
            references
            (toList selected)

renderJustificationSuffix :: ReferenceContext -> Justification -> Html ()
renderJustificationSuffix _ JustificationImplicit = skip
renderJustificationSuffix references justification = do
    toHtml (" " :: Text)
    renderJustification references justification

renderMarkerReferences
    :: MarkerReferenceUse
    -> ReferenceContext
    -> [Marker]
    -> Html ()
renderMarkerReferences FormalJustificationReference references [marker] =
    renderMarkerReferenceWith CompactMarkerReference references marker
renderMarkerReferences use references markers
    | length markers >= markerReferenceGroupThreshold use =
        renderMarkerReferenceGroup references markers
    | otherwise =
        joinHtml (toHtml (", " :: Text)) (renderMarkerReference references <$> markers)

markerReferenceGroupThreshold :: MarkerReferenceUse -> Int
markerReferenceGroupThreshold = \case
    CommentaryReference -> referenceGroupThreshold
    FormalJustificationReference -> formalJustificationGroupThreshold

renderMarkerReferenceGroup :: ReferenceContext -> [Marker] -> Html ()
renderMarkerReferenceGroup references markers =
    span_ groupAttributes do
        toHtml ("[...]" :: Text)
        span_ [class_ "reference-preview-group-items", makeAttributes "hidden" "hidden"] do
            traverse_ (renderMarkerReferenceGroupItem references) markers
    where
        referenceCountLabel = Text.pack (show (length markers)) <> " references"

        groupAttributes =
            [ class_ "ref-badge has-preview ref-badge-group"
            , makeAttributes "data-preview-group" "true"
            , makeAttributes "data-reference-label" referenceCountLabel
            , makeAttributes "aria-describedby" "reference-preview-popup"
            , makeAttributes "tabindex" "0"
            , makeAttributes "role" "button"
            , makeAttributes "aria-label" ("Show " <> referenceCountLabel)
            ]

renderMarkerReferenceGroupItem :: ReferenceContext -> Marker -> Html ()
renderMarkerReferenceGroupItem ReferenceContext{..} marker =
    span_ itemAttributes skip
    where
        label = markerText marker
        baseAttributes =
            [ class_ "reference-preview-group-item"
            , makeAttributes "data-reference-label" label
            ]

        itemAttributes =
            baseAttributes <> case Map.lookup marker referenceAnchors of
                Just anchor ->
                    [ makeAttributes
                        "data-preview-link"
                        (renderUrlFragment anchor)
                    , makeAttributes "data-preview-target-id" anchor
                    ]
                Nothing ->
                    case Map.lookup marker referencePreviews of
                        Nothing ->
                            []
                        Just preview ->
                            [ makeAttributes
                                "data-preview-link"
                                (previewReferenceHref preview)
                            , makeAttributes "data-preview-id" (previewId preview)
                            ]

renderMarkerReference :: ReferenceContext -> Marker -> Html ()
renderMarkerReference = renderMarkerReferenceWith VisibleMarkerReference

renderMarkerReferenceWith
    :: MarkerReferencePresentation
    -> ReferenceContext
    -> Marker
    -> Html ()
renderMarkerReferenceWith presentation ReferenceContext{..} marker =
    case Map.lookup marker referenceAnchors of
        Just anchor ->
            a_
                ( href_ (renderUrlFragment anchor)
                    : referenceAttributes
                        True
                        (Just (currentPreviewAttributes anchor))
                )
                (toHtml (resolvedLabel presentation))
        Nothing ->
            case Map.lookup marker referencePreviews of
                Nothing ->
                    span_ (referenceAttributes False Nothing) (toHtml label)
                Just preview ->
                    a_
                        ( href_ (previewReferenceHref preview)
                        : referenceAttributes
                            True
                            (Just (importedPreviewAttributes preview))
                        )
                        (toHtml (resolvedLabel presentation))
    where
        label = markerText marker

        referenceAttributes resolved preview =
            [ class_ (if hasPreview preview then "ref-badge has-preview" else "ref-badge")
            , makeAttributes "data-reference-label" label
            ]
            <> foldMap id preview
            <> compactAccessibilityAttributes resolved

        compactAccessibilityAttributes resolved =
            case presentation of
                CompactMarkerReference
                    | resolved ->
                        [makeAttributes "aria-label" ("1 reference: " <> label)]
                _ -> []

        resolvedLabel = \case
            CompactMarkerReference -> "[...]"
            VisibleMarkerReference -> label

        hasPreview =
            \case
                Nothing -> False
                Just _ -> True

        currentPreviewAttributes anchor =
            [ makeAttributes "data-preview-target-id" anchor
            , makeAttributes "aria-describedby" "reference-preview-popup"
            ]

        importedPreviewAttributes entry =
            [ makeAttributes "data-preview-id" (previewId entry)
            , makeAttributes "aria-describedby" "reference-preview-popup"
            ]


markerText :: Marker -> Text
markerText (Marker text) = text

tokenTextHtml :: Token -> Html ()
tokenTextHtml = \case
    Command "in" -> inlineMath (moText "∈")
    token -> toHtml (tokToText token)

joinHtml :: Html () -> [Html ()] -> Html ()
joinHtml _ [] = mempty
joinHtml separator (x : xs) = x <> foldMap (separator <>) xs

miText :: Text -> Html ()
miText = mi_ . toHtml

moText :: Text -> Html ()
moText = mo_ . toHtml

mnText :: Text -> Html ()
mnText = mn_ . toHtml

mtextText :: Text -> Html ()
mtextText = mtext_ . toHtml
