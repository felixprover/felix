{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.Html (unitTests) where

import Base
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Source
import Felix.Source.Graph
import Felix.Source.Scan qualified as SourceScan
import Felix.Workspace qualified as Workspace
import Felix.Render.Html qualified as Html
import Felix.Render.Html.Contracts qualified as Contracts
import Felix.Render.Html.Context
import Felix.Render.Html.Hints qualified as Hints
import Felix.Render.Html.Layout
import Felix.Report.Diagnostic
import Felix.Report.Render.Terminal qualified as Terminal
import Felix.Report.Location
    ( SourceDescriptor
    , Location
    , anonymousSourceDescriptor
    , advanceSourceLocation
    , locColumn
    , locLine
    , mkLocation
    , pattern Nowhere
    )
import Felix.Syntax.Abstract
import Felix.Render.Html.Markup qualified as Markup
import Felix.Syntax.Lexicon (Lexicon(..), builtins)

import Data.Text qualified as Text
import Data.Text.IO qualified as TextIO
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import System.Directory qualified as Directory
import Numeric.Natural (Natural)
import Text.Megaparsec (Parsec, chunk, getSourcePos, runParser)
import Text.Megaparsec.Pos
    ( SourcePos
    , sourceColumn
    , sourceLine
    , unPos
    )
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "HTML renderer"
    [ testCase "resolves commentary phrases from one retained draft" resolvesCommentaryDraft
    , testCase "math envelope failures retain source locations and formal slots" reportsMathEnvelopeLocations
    , testCase "one shared index resolves local and cross-page previews" referencePreviews
    , testCase "missing reference preview data falls back to readable text" missingReferenceFallback
    , testCase "datatype rendering omits unchecked derived facts" datatypeDerivedFactsAreOmitted
    , testCase "recursive definitions render their domain and equations" recursiveDefinitionRendering
    , testCase "inductive carrier contexts do not capture named variables"
        inductiveCarrierContexts
    , testCase "set-map assertions retain textbook arrow notation" setMapRetainsArrowNotation
    , testCase "logical applications render as comma-separated arguments"
        logicalApplicationsRenderAsArgumentList
    , testCase "renders naturals and opaque integers distinctly"
        integerExpressionsRenderDistinctly
    , testCase "grouped Fix binders render as one readable sentence"
        groupedFixBindersRenderAsOneSentence
    , testCase "bounded noun names render at the lexical slot" boundedNounPlacement
    , testCase "prose interpretations preserve exact markup seams" proseMarkupSeams
    , testCase "parameterized structure phrases render their arguments"
        parameterizedStructuresRenderArguments
    , testCase "renders the record phrase with number agreement"
        recordPhraseRenders
    , testCase "structure aggregates render as angle-bracket records"
        structureAggregatesRenderAsRecords
    , testCase "structure reducts retain their mandatory schema"
        structureReductsRenderTheirSchema
    , testCase "structure reconstructions retain their base and replacements"
        structureReconstructionsRenderTheirClauses
    , testCase "exact structure predicates render explicitly"
        exactStructurePredicatesRenderExplicitly
    , testCase "predicate rendering follows structural number"
        predicateRenderingFollowsStructuralNumber
    , testCase "source headings and disciplined prose retain document order"
        rendersDocumentPresentation
    , testCase "classifications retain a distinct public presentation"
        classificationPresentation
    , testCase "heading anchors cannot collide with declaration anchors"
        rejectsDocumentAnchorCollisions
    , testCase "unsupported heading markup has an exact source location"
        reportsHeadingMarkupLocation
    , testCase "malformed commentary references retain their source location"
        reportsMalformedReferenceLocation
    , testCase "source advancement agrees with Megaparsec"
        sourceAdvancementMatchesMegaparsec
    , testCase "render hints validate their complete row contract"
        validatesRenderHints
    , testCase "render hint numbers cannot wrap before validation"
        rejectsOverflowingRenderHints
    , testCase "validated render hints apply slots totally"
        appliesRenderHintSlots
    , testCase "ambiguous native phrases cannot degrade to warnings" rejectsAmbiguousNativePhrases
    , testCase "checked rendering consumes the bound operand pattern" rendersBoundOperators
    , testCase "formal phrases cannot borrow an unbound template" rendersBoundFormalPhrases
    , testCase "collects missing render hints in exact document order"
        collectsMissingHintsInDocumentOrder
    , testCase
        "Have introductions render their canonical wording"
        haveIntroductionsRenderCanonicalWording
    , testCase
        "ordinary assumptions render their source wording"
        assumptionIntroductionsRenderSourceWording
    , testCase
        "notion justifications render their source wording"
        notionJustificationsRenderSourceWording
    , testCase
        "definition result annotations render their source wording"
        definitionResultAnnotationsRenderSourceWording
    , testCase
        "claim preambles preserve Let and Suppose sentences"
        claimPreamblesPreserveAssumptionKinds
    , testCase
        "symbolic relation Let headers retain grouped and parameterized syntax"
        symbolicRelationLetHeadersRenderSymbolically
    , testCase
        "nested proof disclosures use the body threshold"
        nestedProofDisclosuresUseBodyThreshold
    ]

classificationPresentation :: Assertion
classificationPresentation = do
    let block = BlockClaim Classification Nowhere Nothing "classification"
            (Claim [] (StmtFormula (PropositionalConstant Nowhere IsTop)))
        kind = Html.blockPresentationKind block
    assertEqual "classification presentation kind"
        Html.ClassificationPresentation kind
    assertEqual "classification presentation label"
        "Classification" (Html.blockPresentationKindLabel kind)

integerExpressionsRenderDistinctly :: Assertion
integerExpressionsRenderDistinctly = do
    let equality expression =
            StmtFormula
                (FormulaChain
                    (ChainBase
                        (expression :| [])
                        Positive
                        (Relation Nowhere EqSymbol [])
                        (expression :| [])))
        block =
            BlockClaim Proposition Nowhere Nothing "integer-rendering"
                (Claim
                    [ AsmLetEq "n0" (ExprNaturalNumeral Nowhere 0)
                    , AsmLetEq "n1" (ExprNaturalNumeral Nowhere 1)
                    , AsmLetEq "n1024" (ExprNaturalNumeral Nowhere 1024)
                    , AsmLetEq "i0" (ExprOpaqueInteger Nowhere 0)
                    , AsmLetEq "i37" (ExprOpaqueInteger Nowhere 37)
                    , AsmLetEq "ineg" (ExprOpaqueInteger Nowhere (-2))
                    ]
                    (equality (ExprVar "n0")))
    html <- renderSynthetic [block]
    for_ [0, 1, 1024 :: Natural] \magnitude ->
        assertContains
            ("natural numeral " <> show magnitude
                <> " uses mathematical number markup")
            ("<mn>" <> Text.pack (show magnitude) <> "</mn>")
            html
    for_ [0, 37, -2 :: Integer] \integer ->
        assertContains
            ("opaque integer " <> show integer
                <> " retains its explicit source surface")
            ("\\opaqueInteger{" <> Text.pack (show integer) <> "}")
            html
    assertNotContains "opaque integer is not rendered as a numeral"
        "<mn>-2</mn>" html

sourceAdvancementMatchesMegaparsec :: Assertion
sourceAdvancementMatchesMegaparsec =
    for_ prefixes \prefix -> do
        parserLocation <-
            case runParser
                    (chunk prefix *> getSourcePos
                        :: Parsec Void Text SourcePos)
                    "location.tex"
                    prefix of
                Left failure ->
                    assertFailure
                        ("position parser failed: " <> show failure)
                Right position -> pure position
        let advanced =
                advanceSourceLocation
                    (mkLocation anonymousSourceDescriptor 1 1)
                    prefix
        assertEqual
            ("line after " <> show prefix)
            (unPos (sourceLine parserLocation))
            (locLine advanced)
        assertEqual
            ("column after " <> show prefix)
            (unPos (sourceColumn parserLocation))
            (locColumn advanced)
  where
    prefixes =
        [ "\t"
        , "a\t"
        , "abcdefg\t"
        , "abcdefgh\t"
        , "\t\t"
        , "a\nb"
        , "a\r\nb"
        , "a\n\tb"
        , "\955\t\946"
        ]

validatesRenderHints :: Assertion
validatesRenderHints = do
    let source = Text.unlines
            [ "operator\tonly-three\t1"
            , "mystery\tunknown_category\t0\t<mi>u</mi>"
            , "operator\tbad-marker!\t0\t<mi>b</mi>"
            , "operator\tbad_arity\tminus\t<mi>a</mi>"
            , "operator\tbad_slot\t1\t<x/>"
            , "operator\tlarge_slot\t1\t<x2/>"
            , "operator\tduplicate\t0\t<mi>d</mi>"
            , "operator\tduplicate\t0\t<mi>D</mi>"
            ]
    case Hints.parseRenderHints source of
        Left failures ->
            fmap hintFailureKind (NonEmpty.toList failures)
                @?= [ "columns"
                    , "category"
                    , "marker"
                    , "arity"
                    , "slot"
                    , "bounds"
                    , "duplicate"
                    ]
        Right _ ->
            assertFailure "invalid render hints were accepted"
  where
    hintFailureKind :: Hints.RenderHintError -> Text
    hintFailureKind = \case
        Hints.RenderHintWrongColumnCount{} -> "columns"
        Hints.RenderHintUnknownCategory{} -> "category"
        Hints.RenderHintInvalidMarker{} -> "marker"
        Hints.RenderHintInvalidArity{} -> "arity"
        Hints.RenderHintCategoryArity{} -> "category-arity"
        Hints.RenderHintInvalidSlot{} -> "slot"
        Hints.RenderHintSlotOutOfBounds{} -> "bounds"
        Hints.RenderHintDuplicateKey{} -> "duplicate"

rejectsOverflowingRenderHints :: Assertion
rejectsOverflowingRenderHints = do
    for_ [("phrase", Hints.PhraseHint, 1), ("structop", Hints.StructOpHint, 2)] \(category, kind, arity) -> do
        let row = category <> "\tunused\t" <> Text.pack (show arity) <> "\t<mi>literal</mi>"
        Hints.parseRenderHints row @?= Left (Hints.RenderHintCategoryArity 1 kind arity :| [])
    valid <- expectRight (Hints.parseRenderHints
        "phrase\tphrase\t0\t<mi>P</mi>\nstructop\tfield\t0\t<mi>f</mi>\nstructop\tfield\t1\t<x1/>")
    assertBool "both explicit receiver conventions remain available"
        (Hints.hasRenderHint Hints.StructOpHint "field" 0 valid
            && Hints.hasRenderHint Hints.StructOpHint "field" 1 valid)

    let largest = Text.pack (show (maxBound :: Int))
        excessive = Text.pack (show (toInteger (maxBound :: Int) + 1))
        row arity slot = "operator\tbounded\t" <> arity <> "\t<x" <> slot <> "/>"
    accepted <- expectRight (Hints.parseRenderHints (row largest largest))
    Hints.hasRenderHint Hints.OperatorHint "bounded" maxBound accepted @?= True
    for_ [excessive, "18446744073709551617", "-1"] \arity ->
        case Hints.parseRenderHints (row arity "1") of
            Left (Hints.RenderHintInvalidArity 1 actual :| []) -> actual @?= arity
            other -> assertFailure ("invalid arity was not classified: " <> show other)
    for_ [excessive, "18446744073709551617", "0"] \slot ->
        case Hints.parseRenderHints (row largest slot) of
            Left (Hints.RenderHintInvalidSlot 1 _ :| []) -> pure ()
            other -> assertFailure ("invalid slot was not classified: " <> show other)

appliesRenderHintSlots :: Assertion
appliesRenderHintSlots = do
    hints <- expectRight
        (Hints.parseRenderHints
            "operator\tswap\t2\t<x2/><mo>:</mo><x1/>\n")
    Hints.applyRenderHint
        Hints.OperatorHint
        "swap"
        (["first", "second"] :: [Text])
        hints
        @?= Just [Right "second", Left "<mo>:</mo>", Right "first"]
    case Hints.resolveRenderHint Hints.OperatorHint "swap" 2 hints of
        Nothing -> assertFailure "the validated template could not be resolved"
        Just contract -> do
            Hints.applyResolvedRenderHint contract (["first"] :: [Text]) @?= Nothing
            Hints.applyResolvedRenderHint contract (["first", "second", "extra"] :: [Text]) @?= Nothing

rejectsAmbiguousNativePhrases :: Assertion
rejectsAmbiguousNativePhrases = do
    let item side = intrinsicAdjectiveLexicalItem side (TokenCons (Command "scoped") End) "shared"
        parser = Markup.prepareMarkupParser builtins
            {lexiconAdjLs = [item LeftAdjectiveSide], lexiconAdjRs = [item RightAdjectiveSide]}
    for_ ["\\scoped", "$\\scoped$", "\\[\\scoped\\]"] \source -> do
        segments <- expectRight (SourceScan.scanCompletePresentationText anonymousSourceDescriptor "phrase.tex" source)
        case Html.projectHtmlDocumentWithMathParser parser segments [] of
            Left (Html.HtmlDocumentPhraseAmbiguity _ bindings) -> length bindings @?= 2
            Left other -> assertFailure ("wrong phrase failure: " <> show other)
            Right _ -> assertFailure ("ambiguous phrase bypassed presentation validation: " <> Text.unpack source)

rendersBoundOperators :: Assertion
rendersBoundOperators = do
    hints <- expectRight (Hints.parseRenderHints "operator\temptyset\t0\t<mi>bound-empty</mi>")
    bindings <- expectRight (Contracts.checkedNotationBindings [])
    let contracts = Contracts.resolveNotationContracts hints bindings
        blocks command = [BlockClaim Proposition Nowhere Nothing "operator_contract"
            (Claim [AsmLetEq "X" (ExprOp Nowhere
                (MixfixItem (TokenCons (Command command) End) "emptyset" NonAssoc) [])]
                (StmtFormula (PropositionalConstant Nowhere IsTop)))]
    valid <- renderSyntheticWith hints (Html.withNotationContracts contracts) (blocks "emptyset")
    assertContains "intrinsic contract renders its resolved template" "<mi>bound-empty</mi>" valid
    mismatched <- renderSyntheticWith hints (Html.withNotationContracts contracts) (blocks "different")
    assertNotContains "a marker lookalike cannot reuse the resolved template" "<mi>bound-empty</mi>" mismatched
    assertContains "an unmatched binding retains the explicit rendering failure" "<merror>" mismatched

rendersBoundFormalPhrases :: Assertion
rendersBoundFormalPhrases = do
    hints <- expectRight (Hints.parseRenderHints "phrase\tlookalike\t0\t<mi>borrowed-template</mi>")
    bindings <- expectRight (Contracts.checkedNotationBindings [])
    let item = mkLexicalItemSgPl
            (SgPl [Just (Command "unboundPhrase")] [Just (Command "unboundPhrase")]) "lookalike"
        statement = StmtExists Nowhere (NounPhrase [] (Noun Nowhere item [])
            (NounBinder ["x"] Unbounded) [] Nothing)
        block value = BlockClaim Proposition Nowhere Nothing "formal_phrase" (Claim [] value)
        contracts = Contracts.resolveNotationContracts hints bindings
    for_ [statement, StmtFormula (FormulaExpression (ExprSep Nowhere "z" (ExprVar "Z") statement))] \value -> do
        parsed <- renderSyntheticWith hints id [block value]
        assertContains "parsed fixtures retain their optional symbolic template" "borrowed-template" parsed
        checked <- renderSyntheticWith hints (Html.withNotationContracts contracts) [block value]
        assertNotContains "formal phrases require the actual checked binding" "borrowed-template" checked
        assertContains "native phrases retain total literal rendering" "unboundPhrase" checked

collectsMissingHintsInDocumentOrder :: Assertion
collectsMissingHintsInDocumentOrder = do
    hints <- expectRight (Hints.parseRenderHints "")
    let descriptor = anonymousSourceDescriptor
        blockLocation = mkLocation descriptor 3 1
        definitionLocation = mkLocation descriptor 7 1
        predicateLocation = mkLocation descriptor 4 9
        formalFirstLocation = mkLocation descriptor 4 13
        sharedBinaryLocation = mkLocation descriptor 4 17
        alphabeticalFirstLocation = mkLocation descriptor 4 21
        relationLocation = mkLocation descriptor 4 25
        structureLocation = mkLocation descriptor 4 29
        beforeSymbol = unaryWithMarker "before" "shared"
        zebraSymbol = unaryWithMarker "zebra" "z-key"
        formalAgainSymbol = unaryWithMarker "formalAgain" "formal-first"
        sharedSymbol = unaryWithMarker "unusedShared" "shared"
        alphabeticalFirstSymbol = unaryWithMarker "unusedA" "a-key"
        headSymbol = unaryWithMarker "unusedHead" "head-key"
        customRelation =
            RelationSymbol
                (Command "unusedRelation")
                zeroParameterArity
                "relation-key"
        variable = ExprVar "x"
        propositionBlock =
            BlockClaim Proposition blockLocation Nothing "ordered_hints"
                (Claim []
                    (StmtFormula
                        (Connected blockLocation Conjunction
                            (FormulaPredicate
                                predicateLocation
                                (PrefixPredicate "unusedPredicate" 1)
                                "predicate-key"
                                (variable :| []))
                            (Connected blockLocation Conjunction
                                (FormulaExpression
                                    (ExprOp
                                        formalFirstLocation
                                        formalAgainSymbol
                                        [variable]))
                                (FormulaChain
                                    (ChainBase
                                        (ExprOp
                                            sharedBinaryLocation
                                            sharedSymbol
                                            [ ExprOp
                                                alphabeticalFirstLocation
                                                alphabeticalFirstSymbol
                                                [variable]
                                            , variable
                                            ] :| [])
                                        Positive
                                        (Relation
                                            relationLocation
                                            customRelation
                                            [])
                                        (ExprStructOp
                                            structureLocation
                                            (StructSymbol "structure-key")
                                            Nothing :| [])))))))
        definitionBlock =
            BlockDefn definitionLocation Nothing "head_definition"
                (DefnOp
                    []
                    (SymbolPattern headSymbol ["x"])
                    variable
                    Nothing)
        blocks = [propositionBlock, definitionBlock]
        sourceText = Text.unlines
            [ "Scoped \\scoped. Before $\\before{x}$ and $\\zebra{x}$."
            , ""
            , "\\begin{proposition}\\label{ordered_hints}"
            , "    $x=x$."
            , "\\end{proposition}"
            , ""
            , "\\begin{definition}\\label{head_definition}"
            , "    $x=x$."
            , "\\end{definition}"
            , ""
            , "After $\\formalAgain{x}$."
            ]
        presentationLexicon =
            builtins
                { lexiconAdjLs = [intrinsicAdjectiveLexicalItem LeftAdjectiveSide
                    (TokenCons (Command "scoped") End) "scoped-key"]
                , lexiconMixfixTable =
                    Seq.adjust
                        (\table ->
                            foldl'
                                (\items item ->
                                    Map.insert (mixfixPattern item) item items)
                                table
                                [beforeSymbol, zebraSymbol, formalAgainSymbol])
                        9
                        (lexiconMixfixTable builtins)
                }
    segments <- case SourceScan.scanCompletePresentationText
            descriptor "ordered-hints.tex" sourceText of
        Left failure ->
            assertFailure ("presentation scan failed: " <> show failure)
                >> fail "unreachable"
        Right decoded -> pure decoded
    (document, projectionDiagnostics) <- expectRight
        (Html.resolveHtmlDocument hints <$> Html.projectHtmlDocumentWithMathParser
            (Markup.prepareMarkupParser presentationLexicon)
            segments
            blocks)
    assertBool "ordered collector fixture projects without warnings"
        (null projectionDiagnostics)
    graph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/root-preview.tex"
    let source = sourceGraphRootSource graph
        (_renderIndex, pages) =
            Html.buildRenderIndexWithNavigationAndDocuments
                source
                ((source, [], blocks, Map.empty, document) :| [])
    missing <- expectRight
        (Html.collectMissingRenderHintsChecked
            hints
            (NonEmpty.toList pages))
    let key missingHint =
            ( Html.missingRenderHintCategory missingHint
            , Html.missingRenderHintMarker missingHint
            , Html.missingRenderHintArity missingHint
            )
        occurrenceLocation =
            Html.hintOccurrenceLocation . Html.missingRenderHintSite
    fmap key missing @?=
        [ (Hints.PhraseHint, "scoped-key", 0)
        , (Hints.OperatorHint, "shared", 1)
        , (Hints.OperatorHint, "z-key", 1)
        , (Hints.PredicateHint, "predicate-key", 1)
        , (Hints.OperatorHint, "formal-first", 1)
        , (Hints.OperatorHint, "shared", 2)
        , (Hints.OperatorHint, "a-key", 1)
        , (Hints.RelationHint, "relation-key", 0)
        , (Hints.StructOpHint, "structure-key", 0)
        , (Hints.OperatorHint, "head-key", 1)
        ]
    fmap occurrenceLocation missing @?=
        [ Nothing
        , Nothing
        , Nothing
        , Just predicateLocation
        , Just formalFirstLocation
        , Just sharedBinaryLocation
        , Just alphabeticalFirstLocation
        , Just relationLocation
        , Just structureLocation
        , Just definitionLocation
        ]
    let diagnostics =
            Html.renderMissingRenderHintDiagnostics DiagnosticError missing
    assertBool "requested diagnostic severity applies to every record"
        (all ((== DiagnosticError) . diagnosticSeverity) diagnostics)
    fmap diagnosticPrimary diagnostics
        @?= fmap occurrenceLocation missing
    case diagnostics of
        _phraseDiagnostic : firstDiagnostic : _ -> do
            let rendered = Terminal.renderTerminalDiagnostic firstDiagnostic
            assertContains "diagnostic renders exact arity" "arity 1" rendered
            assertContains
                "locationless diagnostic renders canonical source"
                "project:test/html-fixtures/root-preview.tex"
                rendered
        _ -> assertFailure "ordered collector returned too few diagnostics"
  where
    unaryWithMarker commandName marker =
        mkMixfixItem
            [ Just (Command commandName)
            , Just InvisibleBraceL
            , Nothing
            , Just InvisibleBraceR
            ]
            marker
            NonAssoc

resolvesCommentaryDraft :: Assertion
resolvesCommentaryDraft = do
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <- expectRight =<< Workspace.prepareDefaultSourceGraph
        "test/html-fixtures/root-preview.tex"
    layout <- expectRight
        (layoutHtmlSourceGraph (Workspace.workspaceHtmlMountPrefixes environment) graph)
    let source = sourceGraphRootSource graph
        sourceText = Text.unlines
            [ "\\section{Names \\teeone and \\obv{one_two}}"
            , "A \\emph{\\teeone{}}-space. \\teeone{X}{Y} \\teeoneExtra"
            , "A citation \\obv{one_two, second}. Bad \\obv{one,}."
            , "Math $\\teeone_\\teeone$ and $2^{-n}$."
            , "Native $\\exp{2}{\\neg{n}}$."
            , "Whole $\\pow{A}+\\unconfigured$."
            , "Source <script> and $x<y$; \\unsafe{<script>}."
            ]
    segments <- case SourceScan.scanCompletePresentationText
            anonymousSourceDescriptor "draft.tex" sourceText of
        Right value -> pure value
        Left _ -> assertFailure "draft fixture did not scan" >> fail "unreachable"
    draft <- expectRight (Html.projectHtmlDocument segments [])
    context <- expectRight (htmlRenderContext layout source)
    for_ [("", 8, "\\teeone"), ("<mi>T</mi><mi>S</mi>", 5, "<mi>T</mi><mi>S</mi>"),
            ("<mi>U</mi>", 5, "<mi>U</mi>")] \(template, count, expected) -> do
        hints <- expectRight (Hints.parseRenderHints
            (if Text.null template then "" else "phrase\tteeone\t0\t" <> template))
        let (document, diagnostics) = Html.resolveHtmlDocument hints draft
            (index, pages) = Html.buildRenderIndexWithNavigationAndDocuments source
                ((source, [], [], Map.empty, document) :| [])
        length diagnostics @?= count
        let positions =
                [ (locLine location, locColumn location)
                | diagnostic <- diagnostics
                , Just location <- [diagnosticPrimary diagnostic]
                ]
        assertBool "deferred diagnostics remain in source order"
            (and (zipWith (<=) positions (drop 1 positions)))
        html <- expectRight (Html.renderDocument context hints index (NonEmpty.head pages))
        assertContains "hint changes affect the same retained draft" expected html
        assertContains "malformed invocation stays whole" "\\teeone{X}{Y}" html
        assertContains "a different control word stays whole" "\\teeoneExtra" html
        assertContains "ordinary underscores survive commentary citations" "one_two" html
        assertContains "malformed citation stays source" "\\obv{one,}" html
        assertContains "commentary source is escaped" "Source &lt;script&gt;" html
        assertContains "layout operators are escaped" "<mo form=\"infix\">&lt;</mo>" html
        assertContains "unsupported source is escaped"
            "<code class=\"unsupported-commentary\">\\unsafe{&lt;script&gt;}</code>" html
        assertContains "a failed mathematical phrase retains the whole envelope"
            "<code class=\"unsupported-commentary\">$\\pow{A}+\\unconfigured$</code>" html
        if Text.null template then pure () else
            assertContains "template siblings form one script base and argument"
                ("<msub><mrow>" <> template <> "</mrow><mrow>" <> template <> "</mrow></msub>") html
        missing <- expectRight (Html.collectMissingRenderHintsChecked hints (toList pages))
        fmap (\item -> (Html.missingRenderHintMarker item, Html.missingRenderHintArity item)) missing
            @?= [("exp", 2), ("neg", 1)]
        assertBool "native commentary hints remain locationless"
            (all (isNothing . Html.hintOccurrenceLocation . Html.missingRenderHintSite) missing)
    emptyHints <- expectRight (Hints.parseRenderHints "")
    (layoutOnly, diagnostics) <- expectRight
        (projectHtmlDocumentSource emptyHints anonymousSourceDescriptor "layout.tex" "$2^{-n}$" [])
    assertBool "layout does not need native hints" (null diagnostics)
    let (_, layoutPages) = Html.buildRenderIndexWithNavigationAndDocuments source
            ((source, [], [], Map.empty, layoutOnly) :| [])
    layoutMissing <- expectRight (Html.collectMissingRenderHintsChecked emptyHints (toList layoutPages))
    assertBool "conventional scripts do not manufacture exp/neg dependencies" (null layoutMissing)

reportsMathEnvelopeLocations :: Assertion
reportsMathEnvelopeLocations = do
    hints <- expectRight (Hints.parseRenderHints "")
    for_
        [ ("α\t\\unknown{<script>}", [(1, 9)])
        , ("before \\[x\n\n+\\unknown\\] after", [(1, 8)])
        , ("before $$x$$ after", [(1, 8)])
        , ("\\emph{inline \\[x\\] text}", [(1, 14)])
        , ("\\section{α\t\\unknown{x}}", [(1, 17)])
        ] \(sourceText, positions) -> do
            (_, diagnostics) <- expectRight
                (projectHtmlDocumentSource hints anonymousSourceDescriptor "envelopes.tex" sourceText [])
            [(locLine location, locColumn location)
                | diagnostic <- diagnostics, Just location <- [diagnosticPrimary diagnostic]]
                @?= positions
    let sourceText = Text.unlines
            [ "Before \\[x"
            , "\\begin{proposition}\\label{after_math}"
            , "    $x=x$."
            , "\\end{proposition}"
            , "After $y$."
            ]
        block = BlockClaim Proposition (mkLocation anonymousSourceDescriptor 2 1) Nothing "after_math"
            (Claim [] (StmtFormula (FormulaChain
                (ChainBase (ExprVar "x" :| []) Positive (Relation Nowhere EqSymbol [])
                    (ExprVar "x" :| [])))))
    (_, diagnostics) <- expectRight
        (projectHtmlDocumentSource hints anonymousSourceDescriptor "segment.tex" sourceText [block])
    [(locLine location, locColumn location)
        | diagnostic <- diagnostics, Just location <- [diagnosticPrimary diagnostic]] @?= [(1, 8)]

projectHtmlDocumentSource
    :: Hints.RenderHints
    -> SourceDescriptor
    -> FilePath
    -> Text
    -> [Block]
    -> Either
        Html.HtmlDocumentProjectionError
        (Html.HtmlDocumentPresentation, [Diagnostic])
projectHtmlDocumentSource hints descriptor file source blocks = do
    segments <- case SourceScan.scanCompletePresentationText
            descriptor file source of
        Left (SourceScan.SourceInputFailure failure) ->
            Left
                (Html.HtmlDocumentScanFailed
                    (SourceScan.renderPresentationScanError failure))
        Left (SourceScan.SourceScannerInvariantFailure failure) ->
            Left
                (Html.HtmlDocumentScannerInvariant failure)
        Right decoded -> Right decoded
    Html.resolveHtmlDocument hints <$> Html.projectHtmlDocument segments blocks

rendersDocumentPresentation :: Assertion
rendersDocumentPresentation = do
    hints <- expectRight (Hints.parseRenderHints "")
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <-
        expectRight =<<
            Workspace.prepareDefaultSourceGraph
                "test/html-fixtures/document-presentation.tex"
    workspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
    layout <-
        expectRight
            (layoutHtmlSourceGraph
                (Workspace.workspaceHtmlMountPrefixes environment)
                graph)
    let parsedModule = Parsed.parsedWorkspaceRootModule workspace
        source = Parsed.parsedModuleResolved parsedModule
        blocks = Parsed.parsedModuleBlocks parsedModule
        loaded = Parsed.parsedModuleLoaded parsedModule
    (document, diagnostics) <-
        expectRight
            (projectHtmlDocumentSource hints
                (Parsed.parsedModuleSourceDescriptor parsedModule)
                (canonicalPathFilePath (resolvedSourceCanonicalPath source))
                (loadedText loaded)
                blocks)
    let (renderIndex, pages) =
            Html.buildRenderIndexWithNavigationAndDocuments
                source
                ((source, [], blocks, Map.empty, document) :| [])
        page = NonEmpty.head pages
    context <- expectRight (htmlRenderContext layout source)
    html <-
        expectRight
            (Html.renderDocument context hints renderIndex page)
    assertOrdered
        "headings, prose, and formal blocks retain source order"
        [ "<h2 id=\"introduction\">Readable <math><mo>∈</mo></math>-theory about <a href=\"#no_set\""
        , ">no_set</a></h2>"
        , "<p class=\"narrative\">Plain &lt;source&gt; with <em>emphasized <math><mrow><mi>x</mi><mo form=\"infix\">,</mo><mi>y</mi></mrow></math></em> – in source order.</p>"
        , "class=\"narrative-math\""
        , "<math display=\"block\""
        , "id=\"no_set\""
        , "<h3 id=\"section-1-1\">Fallbacks</h3>"
        , "<code class=\"unsupported-commentary\">\\unknown{source}</code>"
        ]
        html
    assertContains
        "heading references stay plain inside the enclosing TOC link"
        "class=\"toc-section-link\">Readable <math><mo>∈</mo></math>-theory about no_set</a>"
        html
    assertCount
        "the variable-list display is rendered once"
        1
        "class=\"narrative-math\""
        html
    assertContains
        "structural existential negation is idiomatic"
        "there exists no set"
        html
    case diagnostics of
        [diagnostic] -> do
            assertEqual "warning severity"
                DiagnosticWarning (diagnosticSeverity diagnostic)
            assertEqual "warning code"
                DiagnosticHtmlUnsupportedMarkup (diagnosticCode diagnostic)
            assertEqual "warning line"
                (Just 15) (locLine <$> diagnosticPrimary diagnostic)
        _ ->
            assertFailure
                ("expected one presentation diagnostic, got "
                    <> show (length diagnostics))

rejectsDocumentAnchorCollisions :: Assertion
rejectsDocumentAnchorCollisions = do
    hints <- expectRight (Hints.parseRenderHints "")
    let declarationSource = Text.unlines
            [ "\\section{Collision}\\label{same}"
            , "\\begin{proposition}\\label{same}"
            , "  $x = x$."
            , "\\end{proposition}"
            ]
    assertCollision hints "same" declarationSource [referenceClaimBlock "same"]
  where
    assertCollision hints anchor source blocks =
        case projectHtmlDocumentSource hints
                anonymousSourceDescriptor
                "anchor-collision.tex"
                source
                blocks of
            Left (Html.HtmlDocumentAnchorCollision actual) ->
                assertEqual "colliding anchor" anchor actual
            Left other ->
                assertFailure
                    ("unexpected document projection failure: " <> show other)
            Right _ ->
                assertFailure
                    ("a heading reused rendered block anchor "
                        <> Text.unpack anchor)

reportsHeadingMarkupLocation :: Assertion
reportsHeadingMarkupLocation = do
    hints <- expectRight (Hints.parseRenderHints "")
    (_document, diagnostics) <-
        expectRight
            (projectHtmlDocumentSource hints
                anonymousSourceDescriptor
                "heading-warning.tex"
                "\\section{Bad \\unknown{x}}\n"
                [])
    case diagnostics of
        [diagnostic] -> do
            assertEqual "warning line"
                (Just 1) (locLine <$> diagnosticPrimary diagnostic)
            assertEqual "warning column"
                (Just 14) (locColumn <$> diagnosticPrimary diagnostic)
        _ ->
            assertFailure
                ("expected one heading warning, got "
                    <> show (length diagnostics))

reportsMalformedReferenceLocation :: Assertion
reportsMalformedReferenceLocation = do
    hints <- expectRight (Hints.parseRenderHints "")
    (_document, diagnostics) <-
        expectRight
            (projectHtmlDocumentSource hints
                anonymousSourceDescriptor
                "reference-warning.tex"
                "A malformed reference: \\cref{one,}.\n"
                [])
    case diagnostics of
        [diagnostic] -> do
            assertEqual "warning line"
                (Just 1) (locLine <$> diagnosticPrimary diagnostic)
            assertEqual "warning column"
                (Just 24) (locColumn <$> diagnosticPrimary diagnostic)
        _ ->
            assertFailure
                ("expected one malformed-reference warning, got "
                    <> show (length diagnostics))

referencePreviews :: Assertion
referencePreviews = do
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <-
        expectRight =<<
            Workspace.prepareDefaultSourceGraph
                "test/html-fixtures/root-preview.tex"
    workspace <-
        expectRight =<< Parse.parseResolvedSourceGraph graph
    hints <- TextIO.readFile "library/lexicon.tsv"
    renderHints <- expectRight (Hints.parseRenderHints hints)
    layout <-
        expectRight
            (layoutHtmlSourceGraph
                (Workspace.workspaceHtmlMountPrefixes environment)
                graph)
    let nodes = Parsed.parsedWorkspaceImportedBeforeImporter workspace
        sourceByAddress =
            Map.fromList
                [ (Parsed.parsedModuleAddress node, Parsed.parsedModuleResolved node)
                | node <- toList nodes
                ]
    sourcePresentations <- for nodes \node -> do
        let source = Parsed.parsedModuleResolved node
            loaded = Parsed.parsedModuleLoaded node
            blocks = Parsed.parsedModuleBlocks node
        imports <- for (Parsed.parsedModuleImports node) \parsedImport ->
            case Map.lookup
                    (Parsed.parsedImportedAddress parsedImport)
                    sourceByAddress of
                Just imported -> pure imported
                Nothing -> assertFailure "fixture import has no parsed source"
        (document, diagnostics) <-
            expectRight
                (projectHtmlDocumentSource renderHints
                    (Parsed.parsedModuleSourceDescriptor node)
                    (canonicalPathFilePath
                        (resolvedSourceCanonicalPath source))
                    (loadedText loaded)
                    blocks)
        assertBool "preview fixture has no markup warnings" (null diagnostics)
        pure (source, imports, blocks, Map.empty, document)
    let
        (renderIndex, pages) =
            Html.buildRenderIndexWithNavigationAndDocuments
                (Parsed.parsedWorkspaceRoot workspace)
                sourcePresentations
        rootPage = NonEmpty.last pages
    context <-
        expectRight
            (htmlRenderContext
                layout
                (Html.htmlPagePresentationSource rootPage))
    html <-
        expectRight
            (Html.renderDocument
                context
                renderHints
                renderIndex
                rootPage)
    assertContains "local references keep page anchors" "href=\"#local_prop\"" html
    assertContains "local references point previews at the visible target block" "data-reference-label=\"local_prop\" data-preview-target-id=\"local_prop\"" html
    assertNotContains "local references do not use hidden preview ids" "data-reference-label=\"local_prop\" data-preview-id=\"" html
    assertContains "titled declarations use title-first visible leads" "<head->Proposition (<title->Local proposition</title->)." html
    assertElementContentNotContains
        "titled declaration leads omit the machine marker"
        "<head->Proposition (<title->Local proposition</title->)."
        "</head->"
        "local_prop"
        html
    assertContains
        "untitled declarations retain marker-first visible leads"
        "<head->Proposition<id->uses_refs</id->."
        html
    assertContains
        "visible target blocks preserve titled preview metadata"
        "id=\"local_prop\" data-preview-kind=\"Proposition\" data-preview-label=\"local_prop\" data-preview-title=\"Local proposition\""
        html
    assertContains "imported references get preview metadata" "data-reference-label=\"imported_prop\"" html
    assertContains "imported references link to their relative encoded theory route" "href=\"imported-preview#imported_prop\"" html
    assertContains "imported references still use hidden preview templates" "data-reference-label=\"imported_prop\" data-preview-id=\"reference-preview-" html
    assertNotContains "imported references do not get broken page anchors" "href=\"#imported_prop\"" html
    assertNotContains "imported references are not non-clickable spans" "<span class=\"ref-badge has-preview\" data-reference-label=\"imported_prop\"" html
    assertCount "hidden preview store only contains the imported fixture preview" 1 "class=\"reference-preview-template\"" html
    assertContains "page grid is scoped to an explicit shell" "class=\"page-layout\"" html
    assertNotContains "page grid does not apply to every body div" "body > div" html
    assertContains
        "one open native disclosure contains the local contents"
        "<details class=\"toc-disclosure\" open=\"\"><summary class=\"toc-summary\">Contents</summary>"
        html
    assertOrdered
        "TOC entries put the marker before the exact declaration kind"
        [ "href=\"#local_prop\""
        , "<code>local_prop</code>"
        , "<small class=\"toc-kind\">Proposition</small>"
        ]
        html
    assertContains "page heading uses the selected mounted source" "<h1>project:test/html-fixtures/root-preview.tex</h1>" html
    assertContains "imported preview records its mounted source" "project:test/html-fixtures/imported-preview.tex" html
    assertContains "imported preview source links to the same route" "href=\"imported-preview\"><code>project:test/html-fixtures/imported-preview.tex</code>" html
    assertContains "imported source renders on its own line" "class=\"reference-preview-source\"" html
    assertContains "multi-reference rendering preserves the comma separator" ", <a href=\"imported-preview#imported_prop\" class=\"ref-badge has-preview\" data-reference-label=\"imported_prop\"" html
    assertContains
        "commentary references share formal local and imported links"
        "Commentary cites <a href=\"#local_prop\" class=\"ref-badge has-preview\""
        html
    assertNotContains
        "two commentary references remain ungrouped"
        "Commentary cites <span class=\"ref-badge has-preview ref-badge-group\" data-preview-group=\"true\" data-reference-label=\"2 references\""
        html
    assertContains
        "two formal references use the grouped reference badge"
        "Follows by auto using <span class=\"ref-badge has-preview ref-badge-group\" data-preview-group=\"true\" data-reference-label=\"2 references\""
        html
    assertContains
        "two-reference groups preserve local preview metadata"
        "data-reference-label=\"local_prop\" data-preview-link=\"#local_prop\" data-preview-target-id=\"local_prop\""
        html
    assertContains
        "two-reference groups preserve imported preview metadata"
        "data-reference-label=\"imported_prop\" data-preview-link=\"imported-preview#imported_prop\" data-preview-id=\"reference-preview-"
        html
    assertContains
        "calculations render as ordered relation rows"
        "<ol class=\"calculation-chain\"><li class=\"calculation-row\">"
        html
    assertContains
        "calculation justifications stay in their relation row"
        "class=\"calculation-reason\">by auto using <a href=\"#local_prop\" class=\"ref-badge has-preview\" data-reference-label=\"local_prop\" data-preview-target-id=\"local_prop\""
        html
    assertContains
        "resolved singleton formal references use an accessible compact label"
        "aria-label=\"1 reference: local_prop\">[...]</a>"
        html
    assertOrdered
        "calculation rows keep endpoints, relation, and reason in source order"
        [ "<li class=\"calculation-row\">"
        , "class=\"calculation-left\""
        , "class=\"calculation-relation\""
        , "class=\"calculation-right\""
        , "class=\"calculation-reason\""
        ]
        html
    assertCount
        "the fixture renders every calculation link as one row"
        6
        "class=\"calculation-row\""
        html
    assertCount
        "implicit calculation links keep rows without empty reasons"
        3
        "class=\"calculation-reason\""
        html
    assertContains
        "ordinary calculation relations remain visible"
        "<mo>∈</mo>"
        html
    assertContains
        "biconditional calculation relations remain visible"
        "<mo>⇔</mo>"
        html
    assertNotContains
        "calculation rows replace numbered step labels"
        "Step 2:"
        html
    assertNotContains
        "singleton justifications do not use the grouped badge"
        "class=\"calculation-reason\">by auto using <span class=\"ref-badge has-preview ref-badge-group\""
        html
    assertContains
        "commentary references retain the five-reference group threshold"
        "Commentary cites five references <span class=\"ref-badge has-preview ref-badge-group\" data-preview-group=\"true\" data-reference-label=\"5 references\""
        html
    assertContains "large reference lists collapse to an ellipsis trigger" "Follows by auto using <span class=\"ref-badge has-preview ref-badge-group\" data-preview-group=\"true\" data-reference-label=\"5 references\"" html
    assertOrdered
        "five-reference groups preserve every hidden item in citation order"
        [ "Follows by auto using <span class=\"ref-badge has-preview ref-badge-group\" data-preview-group=\"true\" data-reference-label=\"5 references\""
        , "data-reference-label=\"local_prop\" data-preview-link=\"#local_prop\" data-preview-target-id=\"local_prop\""
        , "data-reference-label=\"uses_refs\" data-preview-link=\"#uses_refs\" data-preview-target-id=\"uses_refs\""
        , "data-reference-label=\"calc_refs\" data-preview-link=\"#calc_refs\" data-preview-target-id=\"calc_refs\""
        , "data-reference-label=\"group_source\" data-preview-link=\"#group_source\" data-preview-target-id=\"group_source\""
        , "data-reference-label=\"imported_prop\" data-preview-link=\"imported-preview#imported_prop\" data-preview-id=\"reference-preview-"
        ]
        html
    assertContains
        "group triggers retain keyboard and preview accessibility attributes"
        "data-reference-label=\"2 references\" aria-describedby=\"reference-preview-popup\" tabindex=\"0\" role=\"button\" aria-label=\"Show 2 references\""
        html
    assertContains "collapsed references keep current-page item metadata" "data-reference-label=\"group_source\" data-preview-link=\"#group_source\" data-preview-target-id=\"group_source\"" html
    assertContains "collapsed references keep imported item metadata" "data-reference-label=\"imported_prop\" data-preview-link=\"imported-preview#imported_prop\" data-preview-id=\"reference-preview-" html
    assertNotContains "collapsed references do not inline the long list" "Follows by auto using <a href=\"#local_prop\" class=\"ref-badge has-preview\" data-reference-label=\"local_prop\" data-preview-target-id=\"local_prop\" aria-describedby=\"reference-preview-popup\">local_prop</a>, <a href=\"#uses_refs\"" html
    assertContains "page links the shared stylesheet" "href=\"../../_static/naproche-html.css\"" html
    assertNotContains "page has no inline stylesheet" "<style" html
    assertContains "behaviour loads from the shared external script asset" "src=\"../../_static/naproche-html.js\"" html
    assertNotContains "inline script bundles are not emitted" "<script type=\"text/javascript\">" html
    assertContains "preview statements use a full-width paragraph" "class=\"reference-preview-statement\"" html
    assertContains "preview popup is emitted once" "id=\"reference-preview-popup\"" html

missingReferenceFallback :: Assertion
missingReferenceFallback = do
    let proof =
            Qed (Just Nowhere)
                (JustificationAuto (Just ("missing_ref" :| [])))
        blocks = [BlockProof Nowhere proof Nowhere]
    html <- renderSynthetic blocks
    assertContains "missing references remain visible" "missing_ref" html
    assertNotContains "missing references do not collapse to an ellipsis" "[...]" html
    assertNotContains "missing references do not claim preview content" "data-preview-id=" html

inductiveCarrierContexts :: Assertion
inductiveCarrierContexts = do
    let carrier = ExprOp Nowhere (constSymbol "carrier") []
        member left right = FormulaChain
            (ChainBase (left :| []) Positive (Relation Nowhere ElementSymbol []) (right :| []))
        context = ExprFiniteSet Nowhere (carrier :| [ExprVar "__inductive"])
        block recursive = BlockInductive Nowhere Nothing "carrier"
            (Inductive (SymbolPattern (constSymbol "carrier") []) (ExprVar "D")
                (IntroRule [member (ExprVar "x") carrier, member (ExprVar "S") recursive]
                    (member (ExprVar "x") carrier) :| []))
        references = [referenceClaimBlock "uses_carrier", referenceProofBlock "carrier_induct"]
    html <- renderSynthetic (block context : references)
    for_ ["carrier_intro_1", "carrier_dom_subset", "carrier_cases", "carrier_induct"] \label ->
        assertContains "generated facts retain their preview targets"
            ("data-preview-label=\"" <> label <> "\"") html
    assertContains "induction references point to the generated fact"
        "data-preview-target-id=\"carrier_induct\"" html
    assertContains "the cases witness avoids the supplied x variable"
        "<msub><mi>x</mi><mn>1</mn></msub>"
        (snd (Text.breakOn "id=\"carrier_cases\"" html))
    -- Inspect the generated induction fact, not just the unchanged source clause.
    let induction = snd (Text.breakOn "id=\"carrier_induct\"" html)
    assertContains "the ordinary placeholder-like variable survives in the context"
        "<mo>{</mo><msub><mi>S</mi><mn>1</mn></msub><mo>,</mo><msub><mi>_</mi>" induction
    assertContains "the subset binder avoids the supplied S variable" "<msub><mi>S</mi>" induction
    unsupported <- renderSynthetic [block (ExprSep Nowhere "z" carrier
        (StmtFormula (PropositionalConstant Nowhere IsTop)))]
    assertNotContains "unsupported recursive contexts have no derived preview"
        "data-preview-label=\"carrier_induct\"" unsupported

datatypeDerivedFactsAreOmitted :: Assertion
datatypeDerivedFactsAreOmitted = do
    let blocks =
            [ propformDatatypeBlock Nowhere
            , referenceClaimBlock "uses_datatype_fact"
            , referenceProofBlock "propform_induct"
            , referenceClaimBlock "structural_example"
            , BlockProof Nowhere (ByStructuralInduction Nowhere "p"
                (NamedCase Nowhere " Falsity " (Qed Nothing JustificationImplicit) :| [])) Nowhere
            ]
    html <- renderSynthetic blocks
    assertContains "datatype declarations remain visible" "Datatype of " html
    assertContains "datatype case names retain their spelling" "<strong>Falsity. </strong>" html
    assertContains "derived fact references remain readable" "propform_induct" html
    assertContains "structural induction retains its proof header" "Proof by structural induction on " html
    assertContains "structural induction retains case names" "<strong>Falsity.</strong>" html
    assertNotContains "unchecked datatype facts are not rendered" "<summary>Derived facts</summary>" html
    assertNotContains "unchecked datatype facts do not become preview targets" "data-preview-label=\"propform_induct\"" html

recursiveDefinitionRendering :: Assertion
recursiveDefinitionRendering = do
    let symbol = mkMixfixItem [Just (Command "copy"),Nothing] "recursive_copy" NonAssoc
        zero = ExprOp Nowhere (mkMixfixItem [Just (Command "zero")] "zero" NonAssoc) []
        call = ExprOp Nowhere symbol [zero]
        body = RecursiveDefinition [] (Left (SymbolPattern symbol ["p"])) "p" (ExprVar "D")
            (RecursiveClause (Just "Zero") (Left (call,zero)) :| [])
    html <- renderSynthetic [BlockRecursive Nowhere Nothing "recursive_copy" body]
    assertContains "explicit structural domain" " recursively for " html
    assertContains "constructor heading" "<strong>Zero. </strong>" html
    assertContains "source equation" "=" html
    assertNotContains "implementation support stays private" "recursor" html

setMapRetainsArrowNotation :: Assertion
setMapRetainsArrowNotation = do
    let proposition =
            FormulaSetMap
                Nowhere
                (ExprVar "f")
                (ExprVar "A")
                (ExprVar "B")
        blocks =
            [ BlockAxiom
                Nowhere
                Nothing
                "set_map_render"
                (Axiom [] (StmtFormula proposition))
            ]
    html <- renderSynthetic blocks
    assertContains "set-map source renders with the standard arrow" "→" html
    assertNotContains "set-map rendering does not expose its lowering" "funs" html

logicalApplicationsRenderAsArgumentList :: Assertion
logicalApplicationsRenderAsArgumentList = do
    let blocks =
            [ renderApplication "nested_application_render"
            , renderApplication "compact_application_render"
            ]
    html <- renderSynthetic blocks
    assertCount
        "both equivalent application trees retain the function symbol"
        2
        "<mi>P</mi>"
        html
    assertContains
        "logical application renders its curried arguments in one list"
        "<mi>P</mi><mo>(</mo><mi>a</mi><mo>,</mo><mi>b</mi><mo>,</mo><mi>d</mi><mo>)</mo>"
        html
  where
    renderApplication marker =
        BlockAxiom
            Nowhere
            Nothing
            marker
            (Axiom [] (StmtFormula (FormulaExpression application)))

    application =
        ExprHigherApply
            Nowhere
            (TypedExpressionExpr
                (ExprHigherApply
                    Nowhere
                    (TypedExpressionExpr
                        (ExprHigherApply
                            Nowhere
                            (TypedExpressionExpr (ExprVar "P"))
                            (TypedExpressionExpr (ExprVar "a"))))
                    (TypedExpressionExpr (ExprVar "b"))))
            (TypedExpressionExpr (ExprVar "d"))

groupedFixBindersRenderAsOneSentence :: Assertion
groupedFixBindersRenderAsOneSentence = do
    let bound =
            Bounded
                Nowhere
                Positive
                (Relation Nowhere ElementSymbol [])
                (ExprVar "A")
        proof =
            Fix
                Nowhere
                ( FixBinderSymbolic ("A" :| []) Unbounded
                    :| [FixBinderSymbolic ("x" :| []) bound]
                )
                (Just (StmtFormula (FormulaExpression (ExprVar "P"))))
                (Qed (Just Nowhere) JustificationImplicit)
    html <- renderSynthetic [BlockProof Nowhere proof Nowhere]
    assertContains
        "grouped Fix binders retain the conjunction wording"
        "Fix <math><mi>A</mi></math> and <math><mi>x</mi></math> with "
        html
    assertContains
        "grouped Fix retains its final condition"
        " such that <math><mi>P</mi></math>."
        html
    commaHtml <- renderSynthetic
        [ BlockProof
            Nowhere
            ( Fix
                Nowhere
                (FixBinderSymbolic ("x" :| ["y"]) bound :| [])
                (Just (StmtFormula (FormulaExpression (ExprVar "P"))))
                (Qed (Just Nowhere) JustificationImplicit)
            )
            Nowhere
        ]
    assertContains
        "comma-grouped bounded Fix binders retain compact source wording"
        "Fix <math><mi>x</mi><mo>,</mo><mi>y</mi></math> with "
        commaHtml

recordPhraseRenders :: Assertion
recordPhraseRenders = do
    let recordPhrase = mkLexicalItemSgPl
            (lexicalPhraseSgPl ((Just "record", Just "records") :| []))
            "record"
        recordNoun = StructNounPhrase [] (StructApplication recordPhrase []) [] Nothing
        block = BlockClaim Proposition Nowhere Nothing "record_phrase_render"
            (Claim
                [AsmLetStruct ("R" :| ["S"]) recordNoun]
                (StmtStruct (TermExpr (ExprVar "R")) recordNoun))
    html <- renderSynthetic [block]
    assertContains "plural record introduction" "be records" html
    assertContains "singular record conclusion" "is a record" html

parameterizedStructuresRenderArguments :: Assertion
parameterizedStructuresRenderArguments = do
    let application =
            StructApplication
                parameterizedStructurePhrase
                [TermExpr (ExprVar "R")]
        blocks =
            [ BlockAxiom
                Nowhere
                Nothing
                "parameterized_structure_render"
                (Axiom
                    [ AsmLetStruct ("M" :| ["N"])
                        (StructNounPhrase
                            []
                            application
                            [AttrRThat
                                (VPAdj
                                    (Adj Nowhere renderedRigid [] :| []))]
                            (Just
                                (StmtFormula
                                    (FormulaExpression (ExprVar "P")))))
                    ]
                    (StmtStruct
                        (TermExpr (ExprVar "M"))
                        (StructNounPhrase [] application [] Nothing)))
            ]
    parentHtml <- renderSynthetic
        [BlockStruct Nowhere Nothing "labeled_child"
            (StructDefn [] parameterizedStructurePhrase ["R"]
                [StructParent application (Just "left_parent")] "M" [] [])]
    assertContains "explicit parent labels remain visible" "left_parent: action over" parentHtml
    html <- renderSynthetic blocks
    assertCount
        "grouped assumptions render the plural structure phrase once"
        1
        "actions over"
        html
    assertCount
        "singular conclusions retain the singular structure phrase"
        1
        "action over"
        html
    assertContains
        "grouped structure subjects render as one variable list"
        "<math><mi>M</mi><mo>,</mo><mi>N</mi></math> be actions over"
        html
    assertContains
        "grouped structure right attributes retain plural agreement"
        "that are rendered rigid"
        html
    assertContains
        "grouped structure residuals render once"
        "such that <math><mi>P</mi></math>"
        html
    assertNotContains
        "structure arguments are not rendered as placeholders"
        "action over ?"
        html
  where
    renderedRigid =
        userAdjectiveLexicalItem
            RightAdjectiveSide
            (TokenCons (Word "rendered")
                (TokenCons (Word "rigid") End))

    parameterizedStructurePhrase =
        LexicalItemSgPl
            (SgPl
                (TokenCons (Word "action")
                    (TokenCons (Word "over")
                        (HoleCons End)))
                (TokenCons (Word "actions")
                    (TokenCons (Word "over")
                        (HoleCons End))))
            "parameterized_structure_render"

structureAggregatesRenderAsRecords :: Assertion
structureAggregatesRenderAsRecords = do
    let schema =
            LexicalItemSgPl
                (SgPl
                    (TokenCons (Word "rendered")
                        (TokenCons (Word "structure") End))
                    (TokenCons (Word "rendered")
                        (TokenCons (Word "structures") End)))
                "rendered_structure"
        aggregate =
            ExprStructAggregate
                Nowhere
                (Just (StructApplication schema []))
                [ StructAggregateNamed
                    Nowhere CarrierSymbol (ExprVar "X")
                , StructAggregateNamed
                    Nowhere (StructSymbol "point") (ExprVar "x")
                ]
        proposition =
            FormulaChain
                (ChainBase
                    (aggregate :| [])
                    Positive
                    (Relation Nowhere EqSymbol [])
                    (ExprVar "T" :| []))
    html <-
        renderSynthetic
            [ BlockAxiom
                Nowhere
                Nothing
                "structure_aggregate_render"
                (Axiom [] (StmtFormula proposition))
            ]
    assertContains "aggregate uses a left angle bracket" "⟨" html
    assertContains "aggregate uses a right angle bracket" "⟩" html
    assertContains "named fields remain legible" "point" html
    assertNotContains
        "schema annotations are not nominal term labels"
        "rendered structure"
        html
    assertNotContains
        "raw parse-only rendering does not claim a checked schema"
        "has-schema-tooltip"
        html

structureReductsRenderTheirSchema :: Assertion
structureReductsRenderTheirSchema = do
    let schema =
            LexicalItemSgPl
                (SgPl
                    (TokenCons (Word "rendered")
                        (TokenCons (Word "structure") End))
                    (TokenCons (Word "rendered")
                        (TokenCons (Word "structures") End)))
                "rendered_structure_reduct"
        reduct =
            ExprStructReduct
                Nowhere
                (StructApplication schema [])
                (ExprVar "T")
        proposition =
            FormulaChain
                (ChainBase
                    (reduct :| [])
                    Positive
                    (Relation Nowhere EqSymbol [])
                    (ExprVar "R" :| []))
    html <-
        renderSynthetic
            [ BlockAxiom
                Nowhere
                Nothing
                "structure_reduct_render"
                (Axiom [] (StmtFormula proposition))
            ]
    assertContains "reduct operation remains visible" "reduct" html
    assertContains "reduct schema remains visible" "rendered" html
    assertContains "reduct schema remains visible in full" "structure" html

structureReconstructionsRenderTheirClauses :: Assertion
structureReconstructionsRenderTheirClauses = do
    let schema = mkLexicalItemSgPl
            (lexicalPhraseSgPl ((Just "coordinate", Just "coordinate")
                :| [(Just "datum", Just "data")])) "rendered_coordinate"
        value = ExprStructReconstruction Nowhere (StructApplication schema [])
            (ExprVar "R")
            [StructAggregateNamed Nowhere (StructSymbol "atlas") (ExprVar "A")]
        proposition = FormulaChain (ChainBase (value :| []) Positive
            (Relation Nowhere EqSymbol []) (ExprVar "Q" :| []))
    html <- renderSynthetic [BlockAxiom Nowhere Nothing "reconstruction_render"
        (Axiom [] (StmtFormula proposition))]
    assertContains "target is visible" "coordinate" html
    assertContains "base clause is visible" "based on" html
    assertContains "replacement clause is visible" "with" html
    assertContains "replacement field is named" "atlas" html
    assertNotContains "reconstruction is not expanded to a graph" "⟨" html
    let nested = ExprStructReconstruction Nowhere (StructApplication schema []) value
            [StructAggregateNamed Nowhere (StructSymbol "atlas") (ExprVar "B")]
        nestedEquation = FormulaChain (ChainBase (nested :| []) Positive
            (Relation Nowhere EqSymbol []) (ExprVar "Q" :| []))
    grouped <- renderSynthetic [BlockAxiom Nowhere Nothing "nested_reconstruction_render"
        (Axiom [] (StmtFormula nestedEquation))]
    assertOrdered "nested clauses and surrounding equality keep their grouping"
        [ "<mo>(</mo>", " based on ", "<mo>(</mo>", " based on ", " with ",
          "<mi>A</mi>", "<mo>)</mo>", " with ", "<mi>B</mi>", "<mo>)</mo>",
          "<mo>=</mo>", "<mi>Q</mi>" ] grouped

exactStructurePredicatesRenderExplicitly :: Assertion
exactStructurePredicatesRenderExplicitly = do
    let schema =
            LexicalItemSgPl
                (SgPl
                    (TokenCons (Word "rendered")
                        (TokenCons (Word "structure") End))
                    (TokenCons (Word "rendered")
                        (TokenCons (Word "structures") End)))
                "rendered_exact_structure"
        proposition =
            StmtExactStruct
                (TermExpr (ExprVar "T"))
                (StructApplication schema [])
    html <-
        renderSynthetic
            [ BlockAxiom
                Nowhere
                Nothing
                "exact_structure_render"
                (Axiom [] proposition)
            ]
    assertContains
        "exactness is not hidden in the ordinary structure noun"
        "is an exact rendered structure"
        html

predicateRenderingFollowsStructuralNumber :: Assertion
predicateRenderingFollowsStructuralNumber = do
    html <- renderSynthetic
        [ axiom "verb_singular" singularVerb
        , axiom "verb_plural" pluralVerb
        , axiom "verb_negative_plural" negativePluralVerb
        , axiom "noun_singular" singularNoun
        , axiom "noun_plural" pluralNoun
        , axiom "noun_negative_singular" (StmtNoun Negative (term "X" :| []) memberNounPhrase)
        , axiom "noun_negative_plural" (StmtNoun Negative (term "X" :| [term "Y"]) memberNounPhrase)
        , axiom "noun_sentence_negation" (StmtNeg Nowhere pluralNoun)
        , axiom
            "noun_plural_in_math"
            (StmtFormula
                (FormulaExpression
                    (ExprSep Nowhere "z" (ExprVar "A") pluralNoun)))
        , BlockSig
            Nowhere
            Nothing
            "verb_signature"
            []
            (SignatureVerb "X" (Verb Nowhere clopenBasisVerb []))
        ]
    assertContains "singular verbs retain their finite surface"
        "has a clopen basis" html
    assertContains "plural verbs use their base surface"
        "have a clopen basis" html
    assertContains "negated plural verbs use the base surface"
        "do not have a clopen basis" html
    assertContains "singular noun copulas retain their article"
        "is a member" html
    assertContains "plural noun copulas omit the singular article"
        "are members" html
    assertContains "negative singular noun predicates retain their article"
        "is not a member" html
    assertContains "negative plural noun predicates retain their scope"
        "are not members" html
    assertContains "sentence negation retains its explicit scope"
        "it is not the case that <math><mi>X</mi></math> and <math><mi>Y</mi></math> are members"
        html
    assertContains "statement-math fragments retain plural noun rendering"
        ("<mtext>" <> mathSpace <> "are members</mtext>")
        html
    assertNotContains "plural noun copulas never retain the singular article"
        "are a members" html
    assertContains "verb signatures use the base surface after can"
        "can have a clopen basis" html
    assertNotContains "verb signatures never use the finite surface after can"
        "can has a clopen basis" html
  where
    mathSpace = Text.singleton '\160'

    axiom marker statement =
        BlockAxiom Nowhere Nothing marker (Axiom [] statement)

    singularVerb =
        StmtVerbPhrase
            (term "X" :| [])
            (VPVerb (Verb Nowhere clopenBasisVerb []))
    pluralVerb =
        StmtVerbPhrase
            (term "X" :| [term "Y"])
            (VPVerb (Verb Nowhere clopenBasisVerb []))
    negativePluralVerb =
        StmtVerbPhrase
            (term "X" :| [term "Y"])
            (VPVerbNot (Verb Nowhere clopenBasisVerb []))
    singularNoun = StmtNoun Positive (term "X" :| []) memberNounPhrase
    pluralNoun = StmtNoun Positive (term "X" :| [term "Y"]) memberNounPhrase

    term name = TermExpr (ExprVar name)

    memberNounPhrase =
        NounPhrase
            []
            (Noun
                Nowhere
                (mkLexicalItemSgPl
                    (SgPl
                        [Just (Word "member")]
                        [Just (Word "members")])
                    "member_render")
                [])
            (unboundedNounBinder Nothing)
            []
            Nothing

    clopenBasisVerb =
        VerbLexicalItem
            (case checkVerbSurfaces
                    [ Just (Word "has")
                    , Just (Word "a")
                    , Just (Word "clopen")
                    , Just (Word "basis")
                    ]
                    [ Just (Word "have")
                    , Just (Word "a")
                    , Just (Word "clopen")
                    , Just (Word "basis")
                    ] of
                Right surfaces -> surfaces
                Left failure ->
                    impossible
                        ("invalid render-test verb: " <> show failure))
            "clopen_basis_render"

haveIntroductionsRenderCanonicalWording :: Assertion
haveIntroductionsRenderCanonicalWording = do
    let statement =
            StmtFormula
                (FormulaExpression (ExprVar "x"))
        render intro =
            BlockProof
                Nowhere
                (Have
                    Nowhere
                    intro
                    statement
                    JustificationAssumption
                    (Qed Nothing JustificationImplicit))
                Nowhere
        introductions =
            [ (HaveHence, "Hence ")
            , (HaveThen, "Then ")
            , (HaveThus, "Thus ")
            , (HaveTherefore, "Therefore ")
            , (HaveInParticular, "In particular, ")
            , (HaveWeHave, "We have ")
            ]
    html <- renderSynthetic (render . fst <$> introductions)
    for_ introductions \(intro, expected) ->
        assertContains
            ("canonical rendering for " <> show intro)
            expected
            html
    bare <- renderSynthetic [render HaveNoIntro]
    assertNotContains
        "an implicit final claim remains bare"
        "We have "
        bare

assumptionIntroductionsRenderSourceWording :: Assertion
assumptionIntroductionsRenderSourceWording = do
    let statement =
            StmtFormula
                (FormulaExpression (ExprVar "x"))
        render intro =
            BlockProof
                Nowhere
                (Assume
                    Nowhere
                    intro
                    statement
                    (Qed (Just Nowhere) JustificationAssumption))
                Nowhere
    html <-
        renderSynthetic
            [ render AssumeIntroSuppose
            , render AssumeIntroAssume
            ]
    assertContains
        "Suppose is rendered for the suppose spelling"
        "Suppose"
        html
    assertContains
        "Assume is rendered for the assume spelling"
        "Assume"
        html
    assertContains
        "the shared continuation remains rendered"
        "Follows by assumption."
        html

notionJustificationsRenderSourceWording :: Assertion
notionJustificationsRenderSourceWording = do
    html <-
        renderSynthetic
            [ BlockProof
                Nowhere
                (Qed (Just Nowhere) JustificationNotion)
                Nowhere
            ]
    assertContains
        "the explicit notion method is rendered"
        "Follows by notion."
        html

definitionResultAnnotationsRenderSourceWording :: Assertion
definitionResultAnnotationsRenderSourceWording = do
    hints <- expectRight (Hints.parseRenderHints "")
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <- expectRight =<< Workspace.prepareDefaultSourceGraph
        "test/html-fixtures/definition-result.tex"
    workspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
    layout <- expectRight
        (layoutHtmlSourceGraph
            (Workspace.workspaceHtmlMountPrefixes environment)
            graph)
    let parsedModule = Parsed.parsedWorkspaceRootModule workspace
        source = Parsed.parsedModuleResolved parsedModule
        blocks = Parsed.parsedModuleBlocks parsedModule
        loaded = Parsed.parsedModuleLoaded parsedModule
    (document, diagnostics) <- expectRight
        (projectHtmlDocumentSource hints
            (Parsed.parsedModuleSourceDescriptor parsedModule)
            (canonicalPathFilePath (resolvedSourceCanonicalPath source))
            (loadedText loaded)
            blocks)
    assertBool "result fixture has no presentation diagnostics"
        (null diagnostics)
    let (renderIndex, pages) =
            Html.buildRenderIndexWithNavigationAndDocuments
                source
                ((source, [], blocks, Map.empty, document) :| [])
    context <- expectRight (htmlRenderContext layout source)
    html <- expectRight
        (Html.renderDocument
            context
            hints
            renderIndex
            (NonEmpty.head pages))
    assertOrdered
        "definition result clause keeps its natural attachment"
        [ "clone"
        , ", which is a "
        , "special"
        , "notable"
        , "set"
        ]
        html

claimPreamblesPreserveAssumptionKinds :: Assertion
claimPreamblesPreserveAssumptionKinds = do
    let proposition expression =
            StmtFormula (FormulaExpression expression)
        claim =
            Claim
                [ AsmLetEq "x" (ExprNaturalNumeral Nowhere 0)
                , AsmSuppose (proposition (ExprVar "x"))
                , AsmLetIn ("y" :| []) (ExprVar "A")
                ]
                (proposition (ExprVar "y"))
        block =
            BlockClaim Proposition Nowhere Nothing "mixed_preamble" claim
    html <- renderSynthetic [block]
    assertOrdered
        "claim assumptions remain complete source-order sentences"
        [ "Let "
        , "<mo>=</mo>"
        , ". Suppose "
        , ". Let "
        , "<mo>∈</mo>"
        , ". Then "
        ]
        html
    assertCount
        "only source Let assumptions receive Let introductions"
        2
        "Let "
        html

symbolicRelationLetHeadersRenderSymbolically :: Assertion
symbolicRelationLetHeadersRenderSymbolically = do
    let proposition expression =
            StmtFormula (FormulaExpression expression)
        relation = Relation
            Nowhere
            (RelationSymbol (Command "indexed") (ParameterArity 1) "indexed")
            [ExprVar "P"]
        claim = Claim
            [AsmLetRelation ("A" :| ["B"]) relation (ExprVar "C")]
            (proposition (ExprVar "A"))
        block = BlockClaim Proposition Nowhere Nothing "relation_let" claim
    html <- renderSynthetic [block]
    assertOrdered
        "relation Let is one symbolic sentence in exact source order"
        [ "Let "
        , "<mi>A</mi>"
        , "<mi>B</mi>"
        , "indexed"
        , "<mi>P</mi>"
        , "<mi>C</mi>"
        , ". Then "
        ]
        html

nestedProofDisclosuresUseBodyThreshold :: Assertion
nestedProofDisclosuresUseBodyThreshold = do
    shortSubclaim <- renderSynthetic [proofBlock (subclaim 9)]
    longSubclaim <- renderSynthetic [proofBlock (subclaim 10)]
    assertCount
        "a nine-step subproof only has the top-level disclosure"
        1 "<details>" shortSubclaim
    assertCount
        "a ten-step subproof adds one nested disclosure"
        2 "<details>" longSubclaim
    assertOrdered
        "the complete Show summary precedes its body and continuation"
        [ "<summary>Show "
        , "</math>.</summary>"
        , "</details></proof->"
        , "Then "
        ]
        longSubclaim

    shortCase <- renderSynthetic [proofBlock (byCase 9)]
    longCase <- renderSynthetic [proofBlock (byCase 10)]
    assertCount
        "a nine-step case only has the top-level disclosure"
        1 "<details>" shortCase
    assertCount
        "a ten-step case adds one nested disclosure"
        2 "<details>" longCase
    assertOrdered
        "a collapsed case retains its complete summary"
        [ "<summary>Case "
        , "</math>.</summary>"
        ]
        longCase
  where
    statement name =
        StmtFormula (FormulaExpression (ExprVar name))

    proofOfSize :: Int -> Proof
    proofOfSize size
        | size <= 1 = Qed Nothing JustificationImplicit
        | otherwise =
            Have Nowhere HaveThen (statement "body")
                JustificationImplicit (proofOfSize (size - 1))

    continuation =
        Have Nowhere HaveThen (statement "after")
            JustificationImplicit (Qed Nothing JustificationImplicit)

    subclaim :: Int -> Proof
    subclaim size =
        Subclaim Nowhere (statement "claim")
            (proofOfSize size) continuation

    byCase :: Int -> Proof
    byCase size =
        ByCase Nowhere [Case (statement "case") (proofOfSize size)]

    proofBlock proof = BlockProof Nowhere proof Nowhere

renderSynthetic :: [Block] -> IO Text
renderSynthetic blocks = do
    hints <- expectRight (Hints.parseRenderHints "")
    renderSyntheticWith hints id blocks

renderSyntheticWith :: Hints.RenderHints -> (Html.HtmlPagePresentation -> Html.HtmlPagePresentation) -> [Block] -> IO Text
renderSyntheticWith hints configure blocks = do
    currentDirectory <- Directory.getCurrentDirectory
    mounts <-
        expectRight =<<
            prepareSourceMounts
                [(sourceMountId "project", currentDirectory)]
    request <-
        expectRight
            (searchedRoot "test/html-fixtures/root-preview.tex")
    graph <-
        expectRight =<<
            buildResolvedSourceGraph mounts request
    layout <-
        expectRight
            (layoutHtmlSourceGraph
                [(sourceMountId "project", [])]
                graph)
    context <-
        expectRight
            (htmlRenderContext
                layout
                (sourceGraphRootSource graph))
    let (renderIndex, page :| _remainingPages) =
            Html.buildRenderIndex
                ((sourceGraphRootSource graph, blocks) :| [])
    expectRight
        (Html.renderDocument
            context
            hints
            renderIndex
            (configure page))

expectRight :: (Show e, HasCallStack) => Either e a -> IO a
expectRight = \case
    Left err ->
        assertFailure ("expected Right, got Left " <> show err)
    Right value ->
        pure value

propformDatatypeBlock :: Location -> Block
propformDatatypeBlock blockLoc =
    BlockData blockLoc Nothing "propform" propformDatatype

propformDatatype :: Datatype
propformDatatype =
    Datatype
        { datatypeHeadExpr = ExprOp Nowhere (constSymbol "propform") []
        , datatypeClauses =
            DatatypeClause (Just "Falsity") (ExprOp Nowhere (constSymbol "propbot") []) (ExprOp Nowhere (constSymbol "propform") []) [] :|
                [ DatatypeClause Nothing (ExprOp Nowhere (unarySymbol "propvar") [ExprVar "n"]) (ExprOp Nowhere (constSymbol "propform") []) [("n", ExprOp Nowhere (constSymbol "naturals") [])]
                , DatatypeClause Nothing
                    (ExprOp Nowhere (infixSymbol "propto") [ExprVar "p", ExprVar "q"])
                    (ExprOp Nowhere (constSymbol "propform") [])
                    [ ("p", ExprOp Nowhere (constSymbol "propform") [])
                    , ("q", ExprOp Nowhere (constSymbol "propform") [])
                    ]
                ]
        }

referenceClaimBlock :: Marker -> Block
referenceClaimBlock marker =
    BlockClaim Proposition Nowhere Nothing marker
        (Claim []
            (StmtFormula (PropositionalConstant Nowhere IsTop)))

referenceProofBlock :: Marker -> Block
referenceProofBlock marker =
    BlockProof Nowhere
        (Qed (Just Nowhere) (JustificationAuto (Just (marker :| []))))
        Nowhere

constSymbol :: Text -> FunctionSymbol
constSymbol name =
    mkMixfixItem [Just (Command name)] (Marker name) NonAssoc

unarySymbol :: Text -> FunctionSymbol
unarySymbol name =
    mkMixfixItem [Just (Command name), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] (Marker name) NonAssoc

infixSymbol :: Text -> FunctionSymbol
infixSymbol name =
    mkMixfixItem [Nothing, Just (Command name), Nothing] (Marker name) NonAssoc

assertContains :: HasCallStack => String -> Text -> Text -> Assertion
assertContains label needle haystack =
    assertBool
        (label <> "\nExpected to find: " <> Text.unpack needle)
        (needle `Text.isInfixOf` haystack)

assertNotContains :: HasCallStack => String -> Text -> Text -> Assertion
assertNotContains label needle haystack =
    assertBool
        (label <> "\nDid not expect to find: " <> Text.unpack needle)
        (not (needle `Text.isInfixOf` haystack))

assertCount :: HasCallStack => String -> Int -> Text -> Text -> Assertion
assertCount label expected needle haystack =
    assertEqual
        (label <> "\nExpected count for: " <> Text.unpack needle)
        expected
        (Text.count needle haystack)

assertOrdered :: HasCallStack => String -> [Text] -> Text -> Assertion
assertOrdered description = go
  where
    go [] _text = pure ()
    go (needle : remaining) text =
        case Text.breakOn needle text of
            (_before, suffix)
                | Text.null suffix ->
                    assertFailure
                        (description <> ": missing or out of order: "
                            <> Text.unpack needle)
                | otherwise ->
                    go remaining (Text.drop (Text.length needle) suffix)

assertElementContentNotContains
    :: HasCallStack
    => String
    -> Text
    -> Text
    -> Text
    -> Text
    -> Assertion
assertElementContentNotContains label opening closing needle html =
    case elementContent opening closing html of
        Nothing ->
            assertFailure
                (label <> "\nCould not find element beginning with: "
                    <> Text.unpack opening)
        Just content ->
            assertNotContains label needle content

elementContent :: Text -> Text -> Text -> Maybe Text
elementContent opening closing html =
    case Text.breakOn opening html of
        (_before, suffix)
            | Text.null suffix ->
                Nothing
            | otherwise ->
                let afterOpening = Text.drop (Text.length opening) suffix
                    (content, afterClosing) = Text.breakOn closing afterOpening
                in if Text.null afterClosing
                    then Nothing
                    else Just content

proseMarkupSeams :: Assertion
proseMarkupSeams = do
    let nounPhrase parts = NounPhrase []
            (Noun Nowhere (mkLexicalItemSgPl (SgPl parts parts) "codec") [])
            (NounBinder [] Unbounded) [] Nothing
        member = nounPhrase [Just (Word "member")]
        body = StmtFormula (FormulaExpression (ExprVar "R"))
        mathR = "<mi>R</mi>"
        inlineR = "<math>" <> mathR <> "</math>"
        inlineX = "<math><mi>x</mi></math>"
        prose value = "<mtext>" <> value <> "</mtext>"
        space = Text.singleton '\160'
        errorText = "internal render-pattern mismatch: expected 1 arguments, received 0"
        rows =
            [ ("negative existence", StmtNeg Nowhere (StmtExists Nowhere member),
                "there exists no member", prose "there exists no member")
            , ("negative phrase", StmtNeg Nowhere
                    (StmtQuantPhrase Nowhere (QuantPhrase Existentially member) body),
                "there exists no member " <> inlineR,
                prose ("there exists no member" <> space) <> mathR)
            , ("negative symbolic", StmtNeg Nowhere
                    (SymbolicQuantified Nowhere Existentially ("x" :| []) Unbounded Nothing body),
                "there exists no " <> inlineX <> " such that " <> inlineR,
                prose ("there exists no" <> space) <> "<mi>x</mi>"
                    <> prose (space <> "such that" <> space) <> mathR)
            , ("universal tail", SymbolicQuantified Nowhere Universally ("x" :| [])
                    Unbounded (Just body) body,
                "for every " <> inlineX <> " such that " <> inlineR <> " we have " <> inlineR,
                prose ("for every" <> space) <> "<mi>x</mi>"
                    <> prose (space <> "such that" <> space) <> mathR
                    <> prose (space <> "we have" <> space) <> mathR)
            , ("joined tokens", StmtExists Nowhere
                    (nounPhrase [Just (Word "well-"), Just (Word "ordered"), Just (Command "in")]),
                "there exists well-ordered <math><mo>∈</mo></math>",
                prose ("there exists well-ordered" <> space) <> "<mo>∈</mo>")
            , ("symbolic token", StmtExists Nowhere (nounPhrase [Just (Command "codec")]),
                "there exists \\codec", prose ("there exists" <> space) <> "<mi>codec</mi>")
            , ("pattern failure", StmtExists Nowhere (nounPhrase [Nothing]),
                "there exists <span class=\"renderer-invariant-error\">" <> errorText <> "</span>",
                prose ("there exists " <> errorText))
            ]
    for_ rows \(label, statement, inlineExpected, mathExpected) -> do
        let block value = BlockAxiom Nowhere Nothing "prose" (Axiom [] value)
        inline <- renderSynthetic [block statement]
        fragments <- renderSynthetic [block (StmtFormula (FormulaExpression
            (ExprSep Nowhere "z" (ExprVar "Z") statement)))]
        assertContains (label <> " inline markup") inlineExpected inline
        assertContains (label <> " fragment markup") mathExpected fragments
        assertCount (label <> " inline envelopes") (Text.count "<math>" inlineExpected) "<math>" inline
        assertCount (label <> " single enclosing mathematical envelope") 1 "<math>" fragments

boundedNounPlacement :: Assertion
boundedNounPlacement = do
    let item = mkLexicalItemSgPl
            (SgPl [Just (Word "element"), Just (Word "of"), Nothing]
                [Just (Word "elements"), Just (Word "of"), Nothing]) "elem"
        nounPhrase = NounPhrase [] (Noun Nowhere item [TermExpr (ExprVar "A")])
            (NounBinder ["x", "y"] (Bounded Nowhere Negative
                (Relation Nowhere ElementSymbol []) (ExprVar "F"))) [] Nothing
        statement = StmtExists Nowhere nounPhrase
        inlineBlock = BlockClaim Proposition Nowhere Nothing "bounded_inline" (Claim [] statement)
        expression = ExprSep Nowhere "z" (ExprVar "Z") statement
        mathBlock = BlockClaim Proposition Nowhere Nothing "bounded_math"
            (Claim [] (StmtFormula (FormulaExpression expression)))
    for_ [("inline noun", inlineBlock), ("noun in mathematical separation", mathBlock)] \(label, block) -> do
        html <- renderSynthetic [block]
        assertOrdered (label <> " keeps names and bound before trailing parameters")
            ["elements", "<mi>x</mi>", "<mi>y</mi>", "∉", "<mi>F</mi>", "of", "<mi>A</mi>"] html
        assertNotContains (label <> " has no rendering invariant failure") "renderer-invariant-error" html
