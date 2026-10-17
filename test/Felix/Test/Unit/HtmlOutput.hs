{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.HtmlOutput (unitTests) where

import Base
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Prelude qualified as Prelude
import Felix.Source
import Felix.Source.Graph qualified as SourceGraph
import Felix.Source.Scan qualified as SourceScan
import Felix.Render.Html qualified as Html
import Felix.Render.Html.Export
import Felix.Render.Html.Layout qualified as HtmlLayout
import Felix.Render.Html.Output
import Felix.Report.Diagnostic
import Felix.Store qualified as Store
import Felix.Syntax.Interface qualified as Syntax
import Felix.Test.Temp (withTemporaryDirectory)
import Felix.Workspace qualified as Workspace

import Control.Monad (unless, when)
import Data.ByteString qualified as ByteString
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import Prettyprinter (defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.Text (renderStrict)
import System.Directory qualified as Directory
import System.FilePath.Posix ((</>))
import System.Posix.Files qualified as PosixFiles
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "HTML output"
        [ testCase
            "publishes a mounted multi-page UTF-8 export"
            publishesMountedExport
        , testCase
            "renders complete direct theory navigation"
            rendersTheoryNavigation
        , testCase
            "writes prepared strict bytes"
            writesPreparedBytes
        , testCase
            "attaches bytes only to reserved routes"
            attachesBytesToReservedRoutes
        , testCase
            "rejects a symbolic-link output root before publication"
            rejectsOutputRootSymlink
        , testCase
            "replaces hard-linked targets without changing peers"
            replacesHardLinkedTarget
        , testCase
            "rejects a non-directory output root before publication"
            rejectsNonDirectoryRoot
        , testCase
            "leaves the previous snapshot unchanged after rendering failure"
            preservesSnapshotAfterRenderingFailure
        , testCase
            "leaves the previous snapshot unchanged after staging failure"
            preservesSnapshotAfterStagingFailure
        , testCase
            "restores the previous snapshot after installation failure"
            restoresSnapshotAfterInstallationFailure
        , testCase
            "reports installation and rollback failure"
            reportsSnapshotRollbackFailure
        , testCase
            "reports cleanup failure after successful installation"
            reportsSnapshotCleanupFailure
        , testCase
            "recovers an interrupted snapshot before publication"
            recoversInterruptedSnapshot
        , testCase
            "preserves unrelated prefix-named publication siblings"
            preservesPublicationSiblings
        , testCase "refuses unowned and symlinked publication workspaces"
            refusesPublicationWorkspaces
        , testCase "serializes overlapping publications without replacing the lock"
            serializesPublications
        , testCase
            "renders commentary mathematics with each theory's visible syntax"
            rendersSourceAwarePresentationMath
        , testCase
            "returns missing render hints as deduplicated diagnostics"
            reportsMissingRenderHints
        , testCase
            "injects analysis and artefact failures into composed exports"
            distinguishesComposedExportFailures
        , testCase
            "does not request an equality hint for calculation links"
            doesNotReportCalculationEqualityHint
        , testCase
            "reports an unresolved parsed import during assembly"
            reportsUnresolvedParsedImport
        , testCase
            "reports presentation sidecar length disagreement"
            reportsPresentationLengthMismatch
        , testCase
            "selects source completion from demand and cache state"
            selectsSourceCompletionMode
        ]

reportsPresentationLengthMismatch :: Assertion
reportsPresentationLengthMismatch = do
    graph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/root-preview.tex"
    (workspace, entries) <-
        parseHtmlWorkspace Parse.UncachedParsedArtefacts graph (const [])
    shortened <- case NonEmpty.nonEmpty (NonEmpty.init entries) of
        Just value -> pure value
        Nothing ->
            assertFailure "HTML fixture has only one source"
                >> fail "unreachable"
    case htmlPresentationFromParsedWorkspaceWithSyntaxInputs
            (const []) workspace shortened of
        Left (HtmlPresentationSidecarLengthMismatch modules supplied) -> do
            modules @?= length (Parsed.parsedWorkspaceModules workspace)
            supplied @?= NonEmpty.length shortened
        Left failure ->
            assertFailure
                ("unexpected HTML assembly failure: " <> show failure)
        Right _presentation ->
            assertFailure "short presentation sidecar was accepted"

selectsSourceCompletionMode :: Assertion
selectsSourceCompletionMode =
    withTemporaryDirectory "felix-presentation-completion" \temp -> do
        graph <- expectRight =<<
            Workspace.prepareDefaultSourceGraph
                "test/html-fixtures/calculation-equality.tex"
        let sourceCount = fromIntegral
                (NonEmpty.length
                    (SourceGraph.sourceGraphImportedBeforeImporter graph))
            parseWith access demand =
                expectRight =<<
                    Parse.parseResolvedSourceGraphExecution
                        access demand graph (const []) (const (Right ()))
        semantic <- parseWith
            Parse.UncachedParsedArtefacts Parse.NoPresentation
        case Parse.parseExecutionPresentation semantic of
            Parse.ParseWithoutPresentation -> pure ()
            Parse.ParseWithPresentation{} ->
                assertFailure "semantic-only parse retained presentation"
        assertCompletionCounts sourceCount 0 semantic

        foundation <- expectRight Foundation.checkedFoundation
        (_startup, store) <- expectRight =<<
            Store.openStore
                (temp </> "completion.sqlite")
                (Identity.theoryId foundation)
        fresh <- parseWith
            (Parse.PersistentParsedArtefacts store)
            Parse.HtmlPresentationRequested
        warm <- parseWith
            (Parse.PersistentParsedArtefacts store)
            Parse.HtmlPresentationRequested
        Store.closeStore store
        assertHasPresentation fresh
        assertHasPresentation warm
        assertCompletionCounts sourceCount 0 fresh
        assertCompletionCounts 0 sourceCount warm
  where
    assertHasPresentation execution =
        case Parse.parseExecutionPresentation execution of
            Parse.ParseWithPresentation{} -> pure ()
            Parse.ParseWithoutPresentation ->
                assertFailure "HTML parse returned no presentation"

    assertCompletionCounts verification presentation execution = do
        let measurements = Parse.parseExecutionMeasurements execution
        Parse.verificationCompletionCount measurements @?= verification
        Parse.presentationOnlyCompletionCount measurements @?= presentation
        Parse.sourceBodyScanCount measurements
            @?= verification + presentation

reportsUnresolvedParsedImport :: Assertion
reportsUnresolvedParsedImport = do
    graph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/root-preview.tex"
    (workspace, scannedEntries) <-
        parseHtmlWorkspace Parse.UncachedParsedArtefacts graph (const [])
    let root = Parsed.parsedWorkspaceRootModule workspace
    imported <- case Parsed.parsedModuleImports root of
        [] ->
            assertFailure "HTML fixture root has no parsed import"
                >> fail "unreachable"
        parsedImport : _ ->
            pure (Parsed.parsedImportedAddress parsedImport)
    let brokenWorkspace =
            Parsed.parsedSourceWorkspace (root :| [])
        rootEntry = NonEmpty.last scannedEntries :| []
    case htmlPresentationFromParsedWorkspaceWithSyntaxInputs
            (const []) brokenWorkspace rootEntry of
        Left (HtmlPresentationUnresolvedParsedImport importer missing) -> do
            importer @?= Parsed.parsedModuleAddress root
            missing @?= imported
        Left failure ->
            assertFailure
                ("unexpected HTML assembly failure: " <> show failure)
        Right _presentation ->
            assertFailure "unresolved parsed import was accepted"

reportsMissingRenderHints :: Assertion
reportsMissingRenderHints = do
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/root-preview.tex"
    (workspace, entries) <-
        parseHtmlWorkspace Parse.UncachedParsedArtefacts graph (const [])
    presentation <- expectRight
        (htmlPresentationFromParsedWorkspaceWithSyntaxInputs
            (const []) workspace entries)
    prepared <- expectRight
        (prepareHtmlExport
            (Workspace.workspaceHtmlMountPrefixes environment)
            presentation
            "")
    let missing =
            [ diagnostic
            | diagnostic <- preparedHtmlExportDiagnostics prepared
            , diagnosticCode diagnostic == DiagnosticHtmlMissingRenderHint
            ]
        messages = renderDiagnosticMessage <$> missing
    assertBool "the fixture exercises missing render hints" (not (null messages))
    List.nub messages @?= messages

distinguishesComposedExportFailures :: Assertion
distinguishesComposedExportFailures = do
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/root-preview.tex"
    (workspace, entries) <-
        parseHtmlWorkspace Parse.UncachedParsedArtefacts graph (const [])
    presentation <- expectRight
        (htmlPresentationFromParsedWorkspaceWithSyntaxInputs
            (const []) workspace entries)
    case prepareHtmlExport
            (Workspace.workspaceHtmlMountPrefixes environment)
            presentation
            "invalid-render-hint-row" of
        Left wrapper@(HtmlExportAnalysisFailed failure) ->
            renderHtmlExportError wrapper
                @?= renderPresentationAnalysisError failure
        Left failure ->
            assertFailure
                ("invalid hints produced the wrong composed error: "
                    <> show failure)
        Right _prepared ->
            assertFailure "invalid hints produced an HTML export"

    unrelatedGraph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/calculation-equality.tex"
    unrelatedLayout <- expectRight
        (HtmlLayout.layoutHtmlSourceGraph
            (Workspace.workspaceHtmlMountPrefixes environment)
            unrelatedGraph)
    case prepareHtmlExportWithLayout unrelatedLayout presentation "" of
        Left wrapper@(HtmlExportArtefactFailed failure) ->
            renderHtmlExportError wrapper
                @?= renderHtmlArtefactError failure
        Left failure ->
            assertFailure
                ("unrouted source produced the wrong composed error: "
                    <> show failure)
        Right _prepared ->
            assertFailure "an unrelated layout produced an HTML export"

doesNotReportCalculationEqualityHint :: Assertion
doesNotReportCalculationEqualityHint = do
    environment <- expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
    graph <- expectRight =<<
        Workspace.prepareDefaultSourceGraph
            "test/html-fixtures/calculation-equality.tex"
    (workspace, entries) <-
        parseHtmlWorkspace Parse.UncachedParsedArtefacts graph (const [])
    presentation <- expectRight
        (htmlPresentationFromParsedWorkspaceWithSyntaxInputs
            (const []) workspace entries)
    prepared <- expectRight
        (prepareHtmlExport
            (Workspace.workspaceHtmlMountPrefixes environment)
            presentation
            "")
    let missing =
            [ diagnostic
            | diagnostic <- preparedHtmlExportDiagnostics prepared
            , diagnosticCode diagnostic == DiagnosticHtmlMissingRenderHint
            ]
    assertBool
        "equality calculations must not request the built-in eq render hint"
        (all
            (not . Text.isInfixOf "marker \"eq\"" . renderDiagnosticMessage)
            missing)

renderDiagnosticMessage :: Diagnostic -> Text
renderDiagnosticMessage diagnostic =
    renderStrict
        (layoutPretty defaultLayoutOptions (diagnosticMessage diagnostic))

rendersSourceAwarePresentationMath :: Assertion
rendersSourceAwarePresentationMath =
    withTemporaryDirectory "felix-presentation-math" \temp -> do
        environment <-
            expectRight =<< Workspace.prepareDefaultWorkspaceEnvironment
        graph <-
            expectRight =<<
                Workspace.prepareDefaultSourceGraph
                    "test/html-fixtures/presentation/root.tex"
        preludeSource <- expectRight =<< Prelude.loadReservedPreludeSourceInput
        parsedPrelude <-
            expectRight =<< Prelude.parseReservedPreludeSource preludeSource
        let preludeSyntax =
                Parsed.identifiedParsedModuleSyntaxInterface
                    (Prelude.reservedParsedPreludeModule parsedPrelude)
        (workspace, entries) <-
            parseHtmlWorkspace
                Parse.UncachedParsedArtefacts
                graph
                (const [preludeSyntax])
        foundation <- expectRight Foundation.checkedFoundation
        (_startup, store) <-
            expectRight =<<
                Store.openStore
                    (temp </> "presentation.sqlite")
                    (Identity.theoryId foundation)
        _storedFresh <-
            expectRight =<<
                Parse.parseResolvedSourceGraphWithStoreAndSyntaxInputsAndGraphValidation
                    store
                    graph
                    (const [preludeSyntax])
                    (const (Right ()))
        (cachedWorkspace, cachedEntries) <-
            parseHtmlWorkspace
                (Parse.PersistentParsedArtefacts store)
                graph
                (const [preludeSyntax])
        Store.closeStore store
        let syntaxBefore =
                Parsed.parsedModuleSyntaxInterface
                    <$> Parsed.parsedWorkspaceImportedBeforeImporter workspace
            blocksBefore =
                Parsed.parsedModuleBlocks
                    <$> Parsed.parsedWorkspaceImportedBeforeImporter workspace
            hints = Text.unlines
                [ "operator\temptyset\t0\t<mi>∅</mi>"
                , "operator\tpresentation_imported\t1\t<mi>I</mi><mo>(</mo><x1/><mo>)</mo>"
                , "operator\tpresentation_local\t1\t<mi>L</mi><mo>(</mo><x1/><mo>)</mo>"
                , "operator\tpresentation_warning_local\t1\t<mi>W</mi><mo>(</mo><x1/><mo>)</mo>"
                , "operator\tpresentation_sibling\t1\t<mi>S</mi><mo>(</mo><x1/><mo>)</mo>"
                , "operator\ttimes\t2\t<x1/><mo>×</mo><x2/>"
                , "operator\tpow\t1\t<mi>P</mi><mo>(</mo><x1/><mo>)</mo>"
                , "operator\texp\t2\t<msup><x1/><x2/></msup>"
                , "operator\tneg\t1\t<mo>−</mo><x1/>"
                , "operator\tapply\t2\t<x1/><mo>(</mo><x2/><mo>)</mo>"
                , "operator\tpair\t2\t<mo>(</mo><x1/><mo>,</mo><x2/><mo>)</mo>"
                , "operator\tadd\t2\t<x1/><mo>+</mo><x2/>"
                , "operator\tminus\t2\t<x1/><mo>−</mo><x2/>"
                , "relation\teq\t0\t<mo>=</mo>"
                , "phrase\tteezero\t0\t<msub><mi>T</mi><mn>0</mn></msub>"
                , "phrase\tteeone\t0\t<msub><mi>T</mi><mn>1</mn></msub>"
                , "phrase\tteetwo\t0\t<msub><mi>T</mi><mn>2</mn></msub>"
                , "phrase\tteethree\t0\t<msub><mi>T</mi><mn>3</mn></msub>"
                , "phrase\tteefour\t0\t<msub><mi>T</mi><mn>4</mn></msub>"
                ]
        presentation <- expectRight
            (htmlPresentationFromParsedWorkspaceWithSyntaxInputs
                (const [preludeSyntax])
                workspace
                entries)
        cachedPresentation <- expectRight
            (htmlPresentationFromParsedWorkspaceWithSyntaxInputs
                (const [preludeSyntax])
                cachedWorkspace
                cachedEntries)
        prepared <-
            expectRight
                (prepareHtmlExport
                    (Workspace.workspaceHtmlMountPrefixes environment)
                    presentation
                    hints)
        cachedPrepared <-
            expectRight
                (prepareHtmlExport
                    (Workspace.workspaceHtmlMountPrefixes environment)
                    cachedPresentation
                    hints)
        assertEqual
            "only malformed, non-imported, unknown, and malformed-adapter notation warn"
            4
            (length (preparedHtmlExportDiagnostics prepared))
        assertEqual
            "cached projection reports the same warnings"
            (length (preparedHtmlExportDiagnostics prepared))
            (length (preparedHtmlExportDiagnostics cachedPrepared))
        assertEqual
            "cached parsing retains module identities"
            (Parsed.parsedModuleId
                <$> Parsed.parsedWorkspaceImportedBeforeImporter workspace)
            (Parsed.parsedModuleId
                <$> Parsed.parsedWorkspaceImportedBeforeImporter cachedWorkspace)
        assertEqual
            "HTML projection does not alter parsed blocks"
            blocksBefore
            (Parsed.parsedModuleBlocks
                <$> Parsed.parsedWorkspaceImportedBeforeImporter workspace)
        assertEqual
            "HTML projection does not alter syntax interfaces"
            syntaxBefore
            (Parsed.parsedModuleSyntaxInterface
                <$> Parsed.parsedWorkspaceImportedBeforeImporter workspace)

        let outputRoot = temp </> "html"
        plan <-
            requirePlan =<<
                planHtmlOutput
                    outputRoot
                    (preparedHtmlExportArtefacts prepared)
        requirePublication =<< writeHtmlOutput plan
        page <-
            readUtf8
                (outputRoot
                    </> "test"
                    </> "html-fixtures"
                    </> "presentation"
                    </> "used.html")
        let cachedOutputRoot = temp </> "cached-html"
        cachedPlan <-
            requirePlan =<<
                planHtmlOutput
                    cachedOutputRoot
                    (preparedHtmlExportArtefacts cachedPrepared)
        requirePublication =<< writeHtmlOutput cachedPlan
        cachedPage <-
            readUtf8
                (cachedOutputRoot
                    </> "test"
                    </> "html-fixtures"
                    </> "presentation"
                    </> "used.html")
        assertEqual
            "fresh and cached presentations are byte-identical"
            page
            cachedPage
        importedPage <-
            readUtf8
                (outputRoot
                    </> "test"
                    </> "html-fixtures"
                    </> "presentation"
                    </> "imported.html")
        assertContains
            "symbolic adjective occurrences use the phrase template"
            "is <math><msub><mi>T</mi><mn>0</mn></msub></math>"
            importedPage
        assertContains
            "fixed notation"
            "<math><mi>∅</mi></math>"
            page
        assertContains
            "imported notation"
            "<mi>I</mi><mo>(</mo><mi>A</mi><mo>)</mo>"
            page
        assertContains
            "local notation"
            "<mi>L</mi><mo>(</mo><mi>A</mi><mo>)</mo>"
            page
        assertContains
            "complete formula"
            "</mrow><mo form=\"infix\">=</mo><mrow><mi>L</mi>"
            page
        assertContains
            "commentary variable list"
            "<math><mrow><mi>x</mi><mo form=\"infix\">,</mo><mi>y</mi></mrow></math>"
            page
        assertContains
            "concrete type"
            "<mi>Set</mi><mo form=\"infix\">→</mo><mi>Set</mi><mo form=\"infix\">→</mo><mi>Set</mi>"
            page
        assertContains
            "display punctuation stays inside mathematics"
            "<mo>.</mo></math>"
            page
        for_ ([0..4] :: [Int]) \number ->
            assertContains
                "configured separation phrases render in commentary"
                ("<msub><mi>T</mi><mn>" <> Text.pack (show number) <> "</mn></msub>")
                page
        assertContains
            "unknown prose commands remain visible"
            "<code class=\"unsupported-commentary\">\\presentationUnknown</code>"
            page
        assertContains
            "sans-serif named operator"
            "<mi mathvariant=\"sans-serif\">cons</mi>"
            page
        assertContains
            "schematic tuple holes"
            "<math><mrow><mo>(</mo><mrow><mo form=\"prefix\">−</mo><mo form=\"infix\">,</mo><mo form=\"prefix\">−</mo></mrow><mo>)</mo></mrow></math>"
            page
        assertContains
            "anonymous textbook arrow"
            "<mo form=\"infix\">→</mo><mi>B</mi></mrow></math>"
            page
        assertContains
            "conventional superscript"
            "<msup><mn>2</mn><mrow><mo form=\"prefix\">−</mo><mi>n</mi></mrow></msup>"
            page
        assertContains
            "conventional function application"
            "<mi>g</mi><mrow><mo>(</mo><mrow><mi>u</mi><mo form=\"infix\">,</mo><mi>y</mi></mrow><mo>)</mo></mrow>"
            page
        assertContains
            "multiline conventional display"
            "<math display=\"block\"><mrow><mrow><mi>g</mi>"
            page
        assertContains
            "prose before a display without blank-line delimiters"
            "<p class=\"narrative\">The displayed identity</p>"
            page
        assertContains
            "prose after consecutive embedded displays"
            "<p class=\"narrative\">and ordinary prose.</p>"
            page
        assertContains
            "proper-class product"
            "<mi mathvariant=\"normal\">ON</mi><mo form=\"infix\">×</mo><mi mathvariant=\"normal\">ON</mi>"
            page
        assertContains
            "malformed adapters retain their complete span"
            "<code class=\"unsupported-commentary\">$\\operatorname{\\textsf{}}$</code>"
            page
        assertContains
            "malformed mathematics remains visible"
            "<code class=\"unsupported-commentary\">$\\presentationImported{A}+$</code>"
            page
        assertContains
            "a rendered sibling does not leak syntax"
            "<code class=\"unsupported-commentary\">$\\presentationSibling{A}$</code>"
            page

        warningPage <- readUtf8
            (outputRoot </> "test" </> "html-fixtures" </> "presentation" </> "warnings.html")
        assertBool "every warning-family fixture renders successfully"
            (not ("unsupported-commentary" `Text.isInfixOf` warningPage))
        for_
            [ "<msub><mn>1</mn><mi>R</mi></msub>"
            , "<mo form=\"infix\">↦</mo>"
            , "<msup><mi>a</mi><mrow><mo form=\"prefix\">−</mo><mn>1</mn></mrow></msup>"
            , "<math><mrow><mi>a</mi><mi>H</mi></mrow></math>"
            , "<mi>φ</mi><mi>ψ</mi>"
            , "<mo>[</mo><mrow><mi>x</mi><mo form=\"infix\">,</mo><mi>y</mi></mrow><mo>]</mo>"
            , "<mo>(</mo><mrow><mi>f</mi><mi>g</mi></mrow><mo>)</mo>"
            , "<mo form=\"prefix\">−</mo><mi>x</mi>"
            , "<math><mrow><mi>R</mi><mo form=\"infix\">/</mo><mi>I</mi></mrow></math>"
            ] \expected -> assertContains "reported notation retains its structure" expected warningPage
        for_ ([0..4] :: [Int]) \number ->
            assertContains "all reported separation phrases render"
                ("<msub><mi>T</mi><mn>" <> Text.pack (show number) <> "</mn></msub>") warningPage
        Text.count "data-reference-label=\"presentation_warning_local\"" warningPage @?= 2
        Text.count "data-reference-label=\"presentation_imported\"" warningPage @?= 2
        assertContains "obv keeps local links and visible-block previews"
            "href=\"#presentation_warning_local\"" warningPage
        assertContains "obv keeps local preview targets"
            "data-preview-target-id=\"presentation_warning_local\"" warningPage
        assertContains "obv keeps imported links"
            "href=\"imported#presentation_imported\"" warningPage
        assertContains "obv keeps imported preview templates"
            "data-reference-label=\"presentation_imported\" data-preview-id=\"reference-preview-" warningPage


publishesMountedExport :: Assertion
publishesMountedExport =
    withTemporaryDirectory "felix-html-export" \temp -> do
        let projectRoot = temp </> "project"
            libraryRoot = temp </> "library"
            projectDirectory = projectRoot </> "docs"
            libraryDirectory = libraryRoot </> "shared"
            rootSource = projectDirectory </> "über #.tex"
            importedSource =
                libraryDirectory </> "sets #.tex"
            outputRoot = temp </> "html"
            rootPage = outputRoot </> "docs" </> "über #.html"
            importedPage =
                outputRoot
                    </> "library"
                    </> "shared"
                    </> "sets #.html"
            supportAsset =
                outputRoot
                    </> "_static"
                    </> "naproche-html.js"
            stylesheetAsset =
                outputRoot </> "_static" </> "naproche-html.css"
            declarationPage =
                outputRoot </> "docs" </> "über #" </> "declarations.html"
            configuration =
                [ (sourceMountId "project", [])
                , (sourceMountId "library", ["library"])
                ]
            hints =
                "relation\teq\t0\t<mo>=</mo>\n"
        Directory.createDirectory projectRoot
        Directory.createDirectory libraryRoot
        Directory.createDirectory projectDirectory
        Directory.createDirectory libraryDirectory
        writeImportedTheory importedSource
        writeRootTheory rootSource
        mounts <-
            expectRight =<<
                prepareSourceMounts
                    [ (sourceMountId "project", projectRoot)
                    , (sourceMountId "library", libraryRoot)
                    ]
        searched <-
            expectRight
                (searchedRoot "docs/über #.tex")
        exact <-
            expectRight =<< existingRoot rootSource
        searchedExport <-
            expectRight =<<
                prepareTestHtmlExport
                    configuration
                    mounts
                    searched
                    hints
        exactExport <-
            expectRight =<<
                prepareTestHtmlExport
                    configuration
                    mounts
                    exact
                    hints
        assertEqual
            "root-form-independent destinations"
            (preparedHtmlArtefactDestination <$> searchedExport)
            (preparedHtmlArtefactDestination <$> exactExport)

        let artefacts = searchedExport
        replacesSnapshotWithoutFollowingArtefactSymlinks temp artefacts

        plan <-
            requirePlan =<<
                planHtmlOutput outputRoot artefacts
        outputExistsBeforePublication <-
            Directory.doesPathExist outputRoot
        assertBool
            "preflight created the output root"
            (not outputExistsBeforePublication)
        requirePublication =<< writeHtmlOutput plan

        rootText <- readUtf8 rootPage
        importedText <- readUtf8 importedPage
        supportText <- readUtf8 supportAsset
        stylesheetText <- readUtf8 stylesheetAsset
        declarationText <- readUtf8 declarationPage
        assertContains
            "root heading"
            "<h1>project:docs/über #.tex</h1>"
            rootText
        assertContains
            "imported heading"
            "<h1>library:shared/sets #.tex</h1>"
            importedText
        assertContains
            "encoded imported reference"
            "href=\"../library/shared/sets%20%23#imported_prop\""
            rootText
        assertContains
            "encoded imported source link"
            "href=\"../library/shared/sets%20%23\"><code>library:shared/sets #.tex</code>"
            rootText
        assertContains
            "root support route"
            "src=\"../_static/naproche-html.js\""
            rootText
        assertContains
            "imported support route"
            "src=\"../../_static/naproche-html.js\""
            importedText
        for_ [rootText, importedText] \document ->
            assertContains
                "UTF-8 declaration"
                "<meta charset=\"utf-8\">"
                document
        assertEqual
            "support asset"
            Html.supportScriptAssetContents
            supportText
        assertEqual
            "stylesheet asset"
            Html.stylesheetAssetContents
            stylesheetText
        assertNotContains "pages contain no inline styles" "<style" rootText
        assertContains
            "root links its relative stylesheet"
            "href=\"../_static/naproche-html.css\""
            rootText
        assertContains
            "declaration index contains source declarations"
            "data-declaration-kind=\"Proposition\""
            declarationText
        assertContains
            "declaration index links an imported marker"
            "href=\"../../library/shared/sets%20%23#imported_prop\""
            declarationText
        assertNotContains
            "declaration index excludes proof blocks"
            "data-declaration-kind=\"Proof\""
            declarationText
        assertOrdered
            "declarations use deterministic marker ordering"
            [ "<code>imported_prop</code>"
            , "<code>local_prop</code>"
            , "<code>uses_import</code>"
            ]
            declarationText
        assertNotContains
            "declaration filters require progressive script initialization"
            "class=\"declaration-filter-controls\""
            declarationText
        assertContains
            "the static declaration index has a no-results state"
            "class=\"declaration-no-results\" hidden=\"\""
            declarationText
        assertContains
            "declaration filtering inserts labelled controls"
            "controls.append(labelledControl('Find declarations', search), labelledControl('Kind', kind), labelledControl('Theory', theory));"
            supportText
        assertContains
            "declaration filtering reports the visible result count"
            "status.textContent = `${visible} of ${entries.length} declarations`;"
            supportText
        assertContains
            "declaration filtering toggles the no-results state"
            "noResults.hidden = visible !== 0;"
            supportText

rendersTheoryNavigation :: Assertion
rendersTheoryNavigation =
    withTemporaryDirectory "felix-html-navigation" \temp -> do
        let projectRoot = temp </> "project"
            outputRoot = temp </> "html"
            rootSource = projectRoot </> "root.tex"
            sharedSource = projectRoot </> "shared.tex"
            leftSource = projectRoot </> "left.tex"
            rightSource = projectRoot </> "right.tex"
        Directory.createDirectory projectRoot
        writeFile rootSource
            (unlines
                [ "\\import{left.tex}"
                , "\\import{right.tex}"
                ])
        writeFile leftSource
            (unlines
                [ "\\import{shared.tex}"
                , "\\import{shared.tex}"
                ])
        writeFile rightSource "\\import{shared.tex}\n"
        writeFile sharedSource ""
        mounts <-
            expectRight =<<
                prepareSourceMounts
                    [(sourceMountId "project", projectRoot)]
        request <- expectRight (searchedRoot "root.tex")
        artefacts <-
            expectRight =<<
                prepareTestHtmlExport
                    [(sourceMountId "project", [])]
                    mounts
                    request
                    ""
        publishArtefacts outputRoot artefacts

        rootText <- readUtf8 (outputRoot </> "root.html")
        sharedText <- readUtf8 (outputRoot </> "shared.html")
        leftText <- readUtf8 (outputRoot </> "left.html")
        supportText <-
            readUtf8
                (outputRoot
                    </> "_static"
                    </> "naproche-html.js")

        assertContains
            "document language"
            "<html lang=\"en\">"
            rootText
        assertContains
            "device viewport"
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
            rootText
        assertContains
            "skip link"
            "class=\"skip-link\" href=\"#main-content\""
            rootText
        assertContains
            "labelled theory index"
            "class=\"theory-index\" aria-labelledby=\"theories-heading\""
            rootText
        assertContains
            "declaration-free root uses the full-width shell"
            "class=\"page-layout page-layout-without-toc\""
            rootText
        assertNotContains
            "declaration-free root omits an empty contents landmark"
            "class=\"toc\" aria-label=\"Contents\""
            rootText
        assertCount
            "root theory is represented by its page heading once"
            1
            "<h1>project:root.tex</h1>"
            rootText
        assertNotContains
            "root index does not link to itself"
            "href=\"root\"><code>project:root.tex</code>"
            rootText
        assertCount
            "shared theory occurs once in the root index"
            1
            "href=\"shared\"><code>project:shared.tex</code>"
            rootText
        assertCount
            "left theory occurs once in the root index"
            1
            "href=\"left\"><code>project:left.tex</code>"
            rootText
        assertCount
            "right theory occurs once in the root index"
            1
            "href=\"right\"><code>project:right.tex</code>"
            rootText
        assertOrdered
            "theory index preserves imported-before-importer order"
            [ "project:shared.tex"
            , "project:left.tex"
            , "project:right.tex"
            ]
            rootText
        assertNotContains
            "root has no redundant dependency panel"
            "class=\"theory-dependencies\""
            rootText
        assertNotContains
            "theory routes omit HTML extensions"
            "href=\"shared.html\""
            rootText
        assertNotContains
            "theory filter is absent without script execution"
            "<input class=\"theory-filter\""
            rootText
        assertNotContains
            "contents filter is absent without script execution"
            "<input class=\"toc-filter\""
            rootText

        assertContains
            "leaf links back to the root relatively"
            "href=\"root\">All theories</a>"
            sharedText
        assertContains
            "dependencies are labelled navigation"
            "aria-labelledby=\"theory-dependencies-heading\""
            sharedText
        assertContains
            "leaf import empty state"
            "No direct imports."
            sharedText
        assertOrdered
            "reverse imports use collection order"
            [ "project:left.tex"
            , "project:right.tex"
            ]
            sharedText
        assertNotContains
            "reverse imports contain no transitive root edge"
            "project:root.tex</code>"
            sharedText

        assertCount
            "repeated direct imports are suppressed"
            1
            "href=\"shared\"><code>project:shared.tex</code>"
            leftText
        assertContains
            "direct importer is shown"
            "href=\"root\"><code>project:root.tex</code>"
            leftText
        assertNotContains
            "dependency navigation contains no unrelated sibling"
            "project:right.tex"
            leftText

        assertContains
            "theory filter is progressively inserted"
            "filterInput.className = 'theory-filter';"
            supportText
        assertContains
            "contents filter is progressively inserted"
            "filterInput.className = 'toc-filter';"
            supportText

replacesSnapshotWithoutFollowingArtefactSymlinks
    :: FilePath
    -> [PreparedHtmlArtefact]
    -> Assertion
replacesSnapshotWithoutFollowingArtefactSymlinks temp artefacts = do
    let outputRoot = temp </> "escape-html"
        outsideRoot = temp </> "outside"
        outsideMarker = outsideRoot </> "unchanged"
    Directory.createDirectory outputRoot
    Directory.createDirectory outsideRoot
    ByteString.writeFile outsideMarker "outside"
    Directory.createDirectoryLink
        outsideRoot
        (outputRoot </> "docs")
    publishArtefacts outputRoot artefacts
    outsideBytes <- ByteString.readFile outsideMarker
    assertEqual
        "snapshot replacement followed an old artefact symlink"
        "outside"
        outsideBytes
    supportExists <- Directory.doesPathExist (outputRoot </> "_static")
    assertBool
        "replacement omitted the new support assets"
        supportExists

writesPreparedBytes :: Assertion
writesPreparedBytes =
    withTemporaryDirectory "felix-html-output-bytes" \temp -> do
        let outputRoot = temp </> "html"
            pageText = "∀ café"
            supportText = "const π = 3;"
            expectedPageBytes =
                ByteString.pack
                    [ 0xe2, 0x88, 0x80
                    , 0x20
                    , 0x63, 0x61, 0x66
                    , 0xc3, 0xa9
                    ]
        artefacts <-
            makeArtefacts
                [ ( "nested/über.html"
                  , TextEncoding.encodeUtf8 pageText
                  )
                , ( "_static/naproche-html.js"
                  , TextEncoding.encodeUtf8 supportText
                  )
                ]
        Directory.createDirectory outputRoot
        ByteString.writeFile (outputRoot </> "stale.html") "stale"
        publishArtefacts outputRoot artefacts
        pageBytes <-
            ByteString.readFile
                (outputRoot </> "nested" </> "über.html")
        supportBytes <-
            ByteString.readFile
                (outputRoot
                    </> "_static"
                    </> "naproche-html.js")
        assertEqual
            "exact page UTF-8 bytes"
            expectedPageBytes
            pageBytes
        assertEqual
            "exact support bytes"
            (TextEncoding.encodeUtf8 supportText)
            supportBytes
        staleExists <- Directory.doesPathExist (outputRoot </> "stale.html")
        assertBool "stale snapshot artefact remains" (not staleExists)

attachesBytesToReservedRoutes :: Assertion
attachesBytesToReservedRoutes =
    withTemporaryDirectory "felix-html-output-routes" \temp -> do
        let outputRoot = temp </> "html"
        reserved <- expectRight
            (traverse safeRelativePath
                ["page.html", "_static/naproche-html.js"])
        routes <- requireRoutePlan =<<
            planHtmlRoutes outputRoot reserved
        matching <- makeArtefacts
            [ ("page.html", "page")
            , ("_static/naproche-html.js", "support")
            ]
        case planHtmlOutputAgainst routes matching of
            Right _ ->
                pure ()
            Left failure ->
                assertFailure (show failure)
        mismatched <- makeArtefacts
            [ ("other.html", "other")
            , ("_static/naproche-html.js", "support")
            ]
        case planHtmlOutputAgainst routes mismatched of
            Left HtmlOutputRouteMismatch{} ->
                pure ()
            Left failure ->
                assertFailure
                    ("unexpected route mismatch: " <> show failure)
            Right _ ->
                assertFailure "unreserved HTML route was accepted"

rejectsOutputRootSymlink :: Assertion
rejectsOutputRootSymlink =
    withTemporaryDirectory "felix-html-output-final-link" \temp -> do
        let outputRoot = temp </> "html"
            outsideRoot = temp </> "outside"
            outsidePage = outsideRoot </> "page.html"
        Directory.createDirectory outsideRoot
        ByteString.writeFile outsidePage "outside page"
        Directory.createDirectoryLink outsideRoot outputRoot
        artefacts <- makeArtefacts [("page.html", "new page")]
        result <- planHtmlOutput outputRoot artefacts
        case result of
            Left (HtmlOutputRootIsSymbolicLink target) ->
                assertEqual "rejected root" outputRoot target
            other ->
                assertFailure
                    ("expected output-root symlink rejection, got "
                        <> showPlanResult other)
        outsideBytes <- ByteString.readFile outsidePage
        outputIsLink <- Directory.pathIsSymbolicLink outputRoot
        assertEqual "symlink referent changed" "outside page" outsideBytes
        assertBool "output symlink was replaced" outputIsLink

replacesHardLinkedTarget :: Assertion
replacesHardLinkedTarget =
    withTemporaryDirectory "felix-html-output-hard-link" \temp -> do
        let outputRoot = temp </> "html"
            page = outputRoot </> "page.html"
            outsidePage = temp </> "outside.html"
        Directory.createDirectory outputRoot
        ByteString.writeFile outsidePage "outside page"
        PosixFiles.createLink outsidePage page
        artefacts <-
            makeArtefacts [("page.html", "new page")]
        publishArtefacts outputRoot artefacts
        outsideBytes <- ByteString.readFile outsidePage
        pageBytes <- ByteString.readFile page
        assertEqual
            "outside hard-link peer changed"
            "outside page"
            outsideBytes
        assertEqual "page was not replaced" "new page" pageBytes

rejectsNonDirectoryRoot :: Assertion
rejectsNonDirectoryRoot =
    withTemporaryDirectory "felix-html-output-fifo" \temp -> do
        let outputRoot = temp </> "html"
        PosixFiles.createNamedPipe outputRoot PosixFiles.ownerModes
        artefacts <-
            makeArtefacts [("page.html", "page")]
        result <- planHtmlOutput outputRoot artefacts
        case result of
            Left (HtmlOutputRootNotDirectory target) ->
                assertEqual "rejected root" outputRoot target
            other ->
                assertFailure
                    ("expected non-directory root rejection, got "
                        <> showPlanResult other)
        rootStatus <- PosixFiles.getSymbolicLinkStatus outputRoot
        assertBool
            "FIFO root was replaced"
            (PosixFiles.isNamedPipe rootStatus)

preservesSnapshotAfterRenderingFailure :: Assertion
preservesSnapshotAfterRenderingFailure =
    withTemporaryDirectory "felix-html-output-incomplete" \temp -> do
        let outputRoot = temp </> "html"
            oldPage = outputRoot </> "old.html"
        Directory.createDirectory outputRoot
        ByteString.writeFile oldPage "old snapshot"
        good <- expectRight (safeRelativePath "new.html")
        failed <- expectRight (safeRelativePath "failed.html")
        let artefacts =
                [ preparedHtmlArtefact good (Right "new snapshot")
                , preparedHtmlArtefact failed (Left "renderer failed")
                ]
        plan <-
            requirePlan =<<
                planHtmlOutput outputRoot artefacts
        result <- writeHtmlOutput plan
        case result of
            Left (HtmlArtefactRenderingFailed destination reason) -> do
                assertEqual "failed destination" failed destination
                assertEqual "rendering reason" "renderer failed" reason
            Left other ->
                assertFailure
                    ("unexpected publication failure: " <> show other)
            Right () ->
                assertFailure
                    "expected rendering failure"
        oldBytes <- ByteString.readFile oldPage
        newExists <- Directory.doesPathExist (outputRoot </> "new.html")
        entries <- Directory.listDirectory temp
        assertEqual "previous snapshot changed" "old snapshot" oldBytes
        assertBool "new artefact was published" (not newExists)
        assertBool
            "staging directory remains after rendering failure"
            (not
                (any
                    (List.isInfixOf ".staging.")
                    entries))

preservesSnapshotAfterStagingFailure :: Assertion
preservesSnapshotAfterStagingFailure =
    withTemporaryDirectory "felix-html-output-staging" \temp -> do
        let outputRoot = temp </> "html"
            oldPage = outputRoot </> "old.html"
        Directory.createDirectory outputRoot
        ByteString.writeFile oldPage "old snapshot"
        artefacts <-
            makeArtefacts
                [ ("conflict", "file")
                , ("conflict/nested.html", "nested")
                ]
        plan <- requirePlan =<< planHtmlOutput outputRoot artefacts
        result <- writeHtmlOutput plan
        case result of
            Left (HtmlArtefactStagingFailed _staging destination _reason) -> do
                expected <- expectRight (safeRelativePath "conflict/nested.html")
                assertEqual "failed staging destination" expected destination
            Left other ->
                assertFailure ("unexpected staging failure: " <> show other)
            Right () ->
                assertFailure "conflicting staging paths were published"
        oldBytes <- ByteString.readFile oldPage
        assertEqual "previous snapshot changed" "old snapshot" oldBytes
        assertBool
            "failed staging directory remains"
            . not =<< Directory.doesPathExist (outputRoot <> ".felix-publication/staging")

restoresSnapshotAfterInstallationFailure :: Assertion
restoresSnapshotAfterInstallationFailure =
    withTemporaryDirectory "felix-html-output-rollback" \temp -> do
        let outputRoot = temp </> "html"
            supplied = temp </> "html.staging.current"
            staging = outputRoot <> ".felix-publication/staging"
            backup = outputRoot <> ".felix-publication/backup"
            operations =
                defaultHtmlSnapshotOperations
                    { htmlSnapshotRenameDirectory = \source destination ->
                        if source == staging && destination == outputRoot
                            then ioError (userError "installation failed")
                            else Directory.renameDirectory source destination
                    }
        writeSnapshot outputRoot "page.html" "old snapshot"
        writeSnapshot supplied "page.html" "new snapshot"
        result <- replaceHtmlSnapshotWith operations outputRoot supplied
        case result of
            Left (HtmlSnapshotInstallationFailedRestored
                    target retained reportedBackup reason) -> do
                target @?= outputRoot
                retained @?= staging
                reportedBackup @?= backup
                assertContains
                    "installation failure"
                    "installation failed"
                    reason
            other ->
                assertFailure
                    ("expected restored installation failure, got "
                        <> show other)
        ByteString.readFile (outputRoot </> "page.html")
            >>= assertEqual "restored snapshot" "old snapshot"
        assertBool "completed staging snapshot was removed"
            =<< Directory.doesDirectoryExist staging
        assertBool "restored backup remains"
            . not
            =<< Directory.doesPathExist backup

reportsSnapshotRollbackFailure :: Assertion
reportsSnapshotRollbackFailure =
    withTemporaryDirectory "felix-html-output-rollback-failure" \temp -> do
        let outputRoot = temp </> "html"
            supplied = temp </> "html.staging.current"
            staging = outputRoot <> ".felix-publication/staging"
            backup = outputRoot <> ".felix-publication/backup"
            operations =
                defaultHtmlSnapshotOperations
                    { htmlSnapshotRenameDirectory = \source destination ->
                        if source == staging && destination == outputRoot
                            then ioError (userError "installation failed")
                        else if source == backup && destination == outputRoot
                            then ioError (userError "rollback failed")
                            else Directory.renameDirectory source destination
                    }
        writeSnapshot outputRoot "page.html" "old snapshot"
        writeSnapshot supplied "page.html" "new snapshot"
        result <- replaceHtmlSnapshotWith operations outputRoot supplied
        case result of
            Left (HtmlSnapshotRollbackFailed
                    target retained reportedBackup installReason rollbackReason) -> do
                target @?= outputRoot
                retained @?= staging
                reportedBackup @?= backup
                assertContains
                    "installation failure"
                    "installation failed"
                    installReason
                assertContains
                    "rollback failure"
                    "rollback failed"
                    rollbackReason
            other ->
                assertFailure
                    ("expected rollback failure, got " <> show other)
        assertBool "failed installation published an output"
            . not
            =<< Directory.doesPathExist outputRoot
        ByteString.readFile (backup </> "page.html")
            >>= assertEqual "retained old snapshot" "old snapshot"
        ByteString.readFile (staging </> "page.html")
            >>= assertEqual "retained staged snapshot" "new snapshot"

reportsSnapshotCleanupFailure :: Assertion
reportsSnapshotCleanupFailure =
    withTemporaryDirectory "felix-html-output-cleanup-failure" \temp -> do
        let outputRoot = temp </> "html"
            staging = temp </> "html.staging.current"
            backup = outputRoot <> ".felix-publication/backup"
            operations =
                defaultHtmlSnapshotOperations
                    { htmlSnapshotRemovePath = \artefact ->
                        if artefact == backup
                            then ioError (userError "cleanup failed")
                            else Directory.removePathForcibly artefact
                    }
        writeSnapshot outputRoot "page.html" "old snapshot"
        writeSnapshot staging "page.html" "new snapshot"
        result <- replaceHtmlSnapshotWith operations outputRoot staging
        case result of
            Left (HtmlSnapshotCleanupFailed target artefact reason) -> do
                target @?= outputRoot
                artefact @?= backup
                assertContains "cleanup failure" "cleanup failed" reason
            other ->
                assertFailure
                    ("expected cleanup failure, got " <> show other)
        ByteString.readFile (outputRoot </> "page.html")
            >>= assertEqual "installed snapshot" "new snapshot"
        ByteString.readFile (backup </> "page.html")
            >>= assertEqual "retained backup" "old snapshot"

recoversInterruptedSnapshot :: Assertion
recoversInterruptedSnapshot = for_
    [(False, True, True), (True, False, True), (False, True, False),
     (True, True, False), (True, True, True), (True, False, False)]
    \(hasRoot, hasStaging, hasBackup) ->
    withTemporaryDirectory "felix-html-output-recovery" \temp -> do
        let outputRoot = temp </> "html"
            orphanedStaging = outputRoot <> ".felix-publication/staging"
            orphanedBackup = outputRoot <> ".felix-publication/backup"
            staging = temp </> "html.staging.current"
        publishArtefacts outputRoot =<< makeArtefacts [("page.html", "old snapshot")]
        unless hasRoot (Directory.removePathForcibly outputRoot)
        when hasStaging (writeSnapshot orphanedStaging "page.html" "abandoned snapshot")
        when hasBackup (writeSnapshot orphanedBackup "page.html" "old snapshot")
        writeSnapshot staging "page.html" "new snapshot"
        renames <- newIORef []
        let operations =
                defaultHtmlSnapshotOperations
                    { htmlSnapshotRenameDirectory = \source destination -> do
                        modifyIORef' renames (<> [(source, destination)])
                        Directory.renameDirectory source destination
                    }
        result <- replaceHtmlSnapshotWith operations outputRoot staging
        if hasRoot && hasStaging && hasBackup then do
            case result of
                Left HtmlPublicationWorkspaceFailed{} -> pure ()
                other -> assertFailure ("expected inconsistent workspace refusal: " <> show other)
            readIORef renames >>= (@?= [])
            for_ [outputRoot, orphanedBackup, orphanedStaging, staging] \path ->
                assertBool "recovery removed a recoverable copy" =<< Directory.doesDirectoryExist path
        else do
            result @?= Right ()
            observedRenames <- readIORef renames
            when (not hasRoot && hasBackup) case observedRenames of
                firstRename : _ -> firstRename @?= (orphanedBackup, outputRoot)
                [] -> assertFailure "snapshot recovery performed no rename"
            ByteString.readFile (outputRoot </> "page.html")
                >>= assertEqual "published snapshot" "new snapshot"
            for_ [orphanedStaging, orphanedBackup] \path ->
                assertBool "abandoned owned slot remains" . not =<< Directory.doesPathExist path

preservesPublicationSiblings :: Assertion
preservesPublicationSiblings =
    withTemporaryDirectory "felix-html-output-stale" \temp -> do
        let outputRoot = temp </> "html"
            staleStaging = temp </> "html.staging.stale"
            staleBackup = staleStaging <> ".backup"
            staging = temp </> "html.staging.current"
        writeSnapshot outputRoot "page.html" "old snapshot"
        writeSnapshot staleStaging "page.html" "stale staging"
        writeSnapshot staleBackup "page.html" "stale backup"
        ByteString.writeFile (temp </> "html.staging.store.sqlite") "unrelated store"
        ByteString.writeFile (temp </> "html.staging.store.sqlite.lock") "unrelated lock"
        writeSnapshot staging "page.html" "new snapshot"
        result <-
            replaceHtmlSnapshotWith
                defaultHtmlSnapshotOperations
                outputRoot
                staging
        result @?= Right ()
        ByteString.readFile (outputRoot </> "page.html")
            >>= assertEqual "published snapshot" "new snapshot"
        ByteString.readFile (staleStaging </> "page.html") >>= (@?= "stale staging")
        ByteString.readFile (staleBackup </> "page.html") >>= (@?= "stale backup")
        ByteString.readFile (temp </> "html.staging.store.sqlite") >>= (@?= "unrelated store")
        ByteString.readFile (temp </> "html.staging.store.sqlite.lock") >>= (@?= "unrelated lock")

refusesPublicationWorkspaces :: Assertion
refusesPublicationWorkspaces = for_ ["unmarked", "symlink", "owner", "lock", "staging", "backup", "unexpected"] \kind ->
    withTemporaryDirectory "felix-html-output-unowned" \temp -> do
        let outputRoot = temp </> "html"
            workspace = outputRoot <> ".felix-publication"
            unrelated = temp </> "unrelated"
        writeSnapshot unrelated "keep" "unrelated"
        artefacts <- makeArtefacts [("page.html", "new snapshot")]
        case kind of
            "unmarked" -> writeSnapshot workspace "keep" "unowned"
            "symlink" -> PosixFiles.createSymbolicLink unrelated workspace
            _ -> do
                publishArtefacts outputRoot artefacts
                case kind of
                    "owner" -> ByteString.writeFile (workspace </> "owner") "wrong root"
                    "lock" -> do
                        Directory.removeFile (workspace </> "lock")
                        PosixFiles.createSymbolicLink (unrelated </> "keep") (workspace </> "lock")
                    "unexpected" -> ByteString.writeFile (workspace </> "keep") "unowned"
                    _ -> PosixFiles.createSymbolicLink unrelated (workspace </> kind)
        planned <- planHtmlOutput outputRoot artefacts
        case planned of
            Left HtmlOutputPathInspectionFailed{} -> pure ()
            Left other -> assertFailure ("unexpected planning failure: " <> show other)
            Right plan -> writeHtmlOutput plan >>= \case
                Left HtmlPublicationWorkspaceFailed{} -> pure ()
                other -> assertFailure ("expected publication refusal: " <> show other)
        ByteString.readFile (unrelated </> "keep") >>= (@?= "unrelated")
        when (kind == "unmarked" || kind == "unexpected") do
            ByteString.readFile (workspace </> "keep") >>= (@?= "unowned")

serializesPublications :: Assertion
serializesPublications =
    withTemporaryDirectory "felix-html-output-lease" \temp -> do
        let outputRoot = temp </> "html"
            workspace = outputRoot <> ".felix-publication"
            firstStage = temp </> "first"
            secondStage = temp </> "second"
            lock = workspace </> "lock"
        publishArtefacts outputRoot =<< makeArtefacts [("page.html", "old snapshot")]
        before <- PosixFiles.fileID <$> PosixFiles.getFileStatus lock
        writeSnapshot firstStage "page.html" "first snapshot"
        writeSnapshot secondStage "page.html" "second snapshot"
        let operations = defaultHtmlSnapshotOperations
                { htmlSnapshotRenameDirectory = \source destination -> do
                    when (source == workspace </> "staging") do
                        nested <- replaceHtmlSnapshotWith defaultHtmlSnapshotOperations outputRoot secondStage
                        nested @?= Left (HtmlPublicationBusy workspace)
                    Directory.renameDirectory source destination
                }
        replaceHtmlSnapshotWith operations outputRoot firstStage >>= (@?= Right ())
        ByteString.readFile (outputRoot </> "page.html") >>= (@?= "first snapshot")
        replaceHtmlSnapshotWith defaultHtmlSnapshotOperations outputRoot secondStage >>= (@?= Right ())
        ByteString.readFile (outputRoot </> "page.html") >>= (@?= "second snapshot")
        lockAfter <- PosixFiles.fileID <$> PosixFiles.getFileStatus lock
        lockAfter @?= before

writeSnapshot :: FilePath -> FilePath -> ByteString.ByteString -> IO ()
writeSnapshot root relative bytes = do
    Directory.createDirectory root
    ByteString.writeFile (root </> relative) bytes


publishArtefacts
    :: FilePath
    -> [PreparedHtmlArtefact]
    -> IO ()
publishArtefacts outputRoot artefacts = do
    plan <-
        requirePlan =<< planHtmlOutput outputRoot artefacts
    requirePublication =<< writeHtmlOutput plan

makeArtefacts
    :: [(FilePath, ByteString.ByteString)]
    -> IO [PreparedHtmlArtefact]
makeArtefacts artefacts =
    for artefacts \(path, bytes) -> do
        relative <- expectRight (safeRelativePath path)
        pure (preparedHtmlArtefact relative (Right bytes))

requirePlan
    :: Either HtmlOutputError HtmlOutputPlan
    -> IO HtmlOutputPlan
requirePlan =
    expectRight

requireRoutePlan
    :: Either HtmlOutputError HtmlRoutePlan
    -> IO HtmlRoutePlan
requireRoutePlan =
    expectRight

requirePublication
    :: Either HtmlPublicationError ()
    -> IO ()
requirePublication =
    expectRight

showPlanResult
    :: Either HtmlOutputError HtmlOutputPlan
    -> String
showPlanResult = \case
    Left err ->
        show err
    Right _plan ->
        "successful output plan"

readUtf8 :: FilePath -> IO Text
readUtf8 path = do
    bytes <- ByteString.readFile path
    case TextEncoding.decodeUtf8' bytes of
        Left err ->
            assertFailure
                ("invalid UTF-8 output: " <> show err)
        Right text ->
            pure text

prepareTestHtmlExport
    :: [(SourceMountId, [Text])]
    -> SourceMounts
    -> RootRequest
    -> Text
    -> IO (Either HtmlExportError [PreparedHtmlArtefact])
prepareTestHtmlExport configuration mounts request hints = do
    graph <-
        expectRight =<<
            SourceGraph.buildResolvedSourceGraph mounts request
    (workspace, entries) <-
        parseHtmlWorkspace Parse.UncachedParsedArtefacts graph (const [])
    presentation <- expectRight
        (htmlPresentationFromParsedWorkspaceWithSyntaxInputs
            (const []) workspace entries)
    pure
        ( preparedHtmlExportArtefacts
            <$> prepareHtmlExport
                configuration
                presentation
                hints
        )

parseHtmlWorkspace
    :: Parse.ParsedArtefactAccess
    -> SourceGraph.ResolvedSourceGraph
    -> (ResolvedSource -> [Syntax.ModuleSyntaxInterface])
    -> IO
        ( Parsed.ParsedSourceWorkspace
        , NonEmpty SourceScan.SourcePresentationEntry
        )
parseHtmlWorkspace artefactAccess graph syntaxInputs = do
    execution <- expectRight =<<
        Parse.parseResolvedSourceGraphExecution
            artefactAccess
            Parse.HtmlPresentationRequested
            graph
            syntaxInputs
            (const (Right ()))
    entries <- case Parse.parseExecutionPresentation execution of
        Parse.ParseWithPresentation sidecar -> pure sidecar
        Parse.ParseWithoutPresentation ->
            assertFailure "HTML parse returned no presentation"
                >> fail "unreachable"
    pure (Parse.parseExecutionWorkspace execution, entries)

writeImportedTheory :: FilePath -> IO ()
writeImportedTheory path =
    writeFile path
        (unlines
            [ "\\begin{proposition}\\label{imported_prop}"
            , "  $i = i$."
            , "\\end{proposition}"
            ])

writeRootTheory :: FilePath -> IO ()
writeRootTheory path =
    writeFile path
        (unlines
            [ "\\import{shared/sets #.tex}"
            , "\\begin{proposition}\\label{local_prop}"
            , "  $a = a$."
            , "\\end{proposition}"
            , "\\begin{proposition}\\label{uses_import}"
            , "  $b = b$."
            , "\\end{proposition}"
            , "\\begin{proof}"
            , "  Follows by \\auto{imported_prop}."
            , "\\end{proof}"
            ])

assertContains
    :: String
    -> Text
    -> Text
    -> Assertion
assertContains description needle haystack =
    assertBool
        (description <> ": missing " <> show needle)
        (needle `Text.isInfixOf` haystack)

assertNotContains
    :: String
    -> Text
    -> Text
    -> Assertion
assertNotContains description needle haystack =
    assertBool
        (description <> ": unexpectedly found " <> show needle)
        (not (needle `Text.isInfixOf` haystack))

assertCount
    :: String
    -> Int
    -> Text
    -> Text
    -> Assertion
assertCount description expected needle haystack =
    assertEqual
        (description <> ": count for " <> show needle)
        expected
        (Text.count needle haystack)

assertOrdered
    :: String
    -> [Text]
    -> Text
    -> Assertion
assertOrdered description needles haystack =
    go haystack needles
  where
    go _remaining [] =
        pure ()
    go remaining (needle : rest) =
        case Text.breakOn needle remaining of
            (_before, suffix)
                | Text.null suffix ->
                    assertFailure
                        (description <> ": missing " <> show needle)
                | otherwise ->
                    go (Text.drop (Text.length needle) suffix) rest

expectRight
    :: (Show e, HasCallStack)
    => Either e a
    -> IO a
expectRight = \case
    Left err ->
        assertFailure
            ("expected Right, got Left " <> show err)
    Right value ->
        pure value
