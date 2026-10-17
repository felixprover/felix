{-# LANGUAGE RankNTypes #-}

module Main where

import Base
import Fixtures
import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.IORef (newIORef, readIORef)
import Data.List qualified as List
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Felix.Math.Codec (hashBlake2b256, mathematicalDigestHex)
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Parsed.Payload qualified as Payload
import Felix.Prelude qualified as Prelude
import Felix.Report.Diagnostic
import Felix.Report.Location
import Felix.Render.Html.Markup qualified as Markup
import Felix.Render.Html qualified as Html
import Felix.Render.Html.Context (htmlRenderContext)
import Felix.Render.Html.Layout (layoutHtmlSourceGraph)
import Felix.Render.Html.Hints qualified as Hints
import Felix.Source
import Felix.Source.Graph qualified as Graph
import Felix.Source.Scan qualified as Scan
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Adapt qualified as Adapt
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Interface qualified as Interface
import Felix.Syntax.Lexicon
import Felix.Syntax.Phrase (nativePhraseEntry)
import Felix.Syntax.Prepared qualified as Prepared
import Felix.Syntax.Token
import Felix.Test.SourceScan.Adapter (scanTestSource)
import Felix.Test.SourceScan.Observation
import Felix.Workspace qualified as Workspace
import GHC.Conc (getAllocationCounter)
import System.Environment (getArgs)
import Text.Earley qualified as Earley
import Text.Read (readMaybe)

type BlockParser = Earley.Parser Text [Located Token] (Either Concrete.ConcreteSyntaxError Raw.Block)

main :: IO ()
main = getArgs >>= \case
    ["cases"] -> traverse_ (putStrLn . fixtureName) allFixtures
    ["observe", name] -> findFixture name >>= observeFixture
    ["controls"] -> observeControls
    ["corpus", root] -> measure "corpus" 0 do
        blocks <- Workspace.parse root
        evaluate (rnf blocks)
    ["manifest", root] -> observeCorpus root
    ["observe-workspace", root] -> observeWorkspace root
    ["html", name] -> do
        fixture <- findFixture name
        measure "html" 0 (renderHtmlFixture fixture >>= evaluate . rnf)
    ["observe-html", name] -> findFixture name >>= renderHtmlFixture >>= print
    ["materialize", countText] -> do
        count <- maybe (fail "invalid materialization size") pure (readMaybe countText)
        unless (count >= 0 && count <= 128) (fail "materialization size must be 0..128")
        let entries = [Interface.CanonicalTypedConstant (Command (nameAt i)) Raw.ConcreteSet (Raw.Marker (nameAt i)) | i <- [1..count]]
        evaluate (rnf entries)
        measure "canonical-validation-and-materialization" 0 do
            delta <- either (fail . show) pure (Interface.canonicalSyntaxDelta entries)
            inventory <- either (fail . show) pure (Adapt.materializeSyntaxDelta delta)
            evaluate (forceLexicon inventory)
    ["measure", name, mode, countText] -> do
        count <- case readMaybe countText of
            Just n | n >= 1 && n <= 10000 -> pure n
            _ -> fail "COUNT must be between 1 and 10000"
        fixture <- findFixture name
        measureFixture fixture mode count
    _ -> fail "usage: parser-bench cases | observe CASE | controls | corpus ROOT | manifest ROOT | measure CASE {parse|report|rebuild|native|markup} COUNT"

findFixture :: String -> IO Fixture
findFixture name = maybe (fail ("unknown fixture: " <> name)) pure
    (List.find ((== name) . fixtureName) allFixtures)

scanFixture :: Fixture -> IO [[Located Token]]
scanFixture fixture = do
    let path = "parser-bench/" <> fixtureName fixture <> ".tex"
    let descriptor = sourceDescriptorForPath path
    chunks <- either fail (pure . snd)
        (scanTestSource descriptor path (fixtureSource fixture))
    -- Empty input is a concrete parser fixture as well as a scanner outcome.
    let result
            | fixtureName fixture == "partial" = map (\tokens -> take (length tokens - 3) tokens) chunks
            | null chunks = [[]]
            | otherwise = chunks
    evaluate (Scan.forceSourceTokenChunksHandoff result)
    pure result

measure :: String -> Int -> IO () -> IO ()
measure = measureValue

measureValue :: String -> Int -> IO a -> IO a
measureValue stage iteration action = do
    started <- getMonotonicTimeNSec
    allocated <- getAllocationCounter
    value <- action
    remaining <- getAllocationCounter
    ended <- getMonotonicTimeNSec
    putStrLn (intercalate "\t"
        [stage, show iteration, show (ended - started), show (allocated - remaining)])
    pure value

measureFixture :: Fixture -> String -> Int -> IO ()
measureFixture fixture mode count = do
    -- This IORef is a benchmark input barrier, not a parser cache. Every call
    -- reads its inputs afresh, preventing the optimizer from sharing a result
    -- thunk across repetitions of the same pure application.
    sourceRef <- newIORef fixture
    if mode == "rebuild" then
        for_ [0 .. count - 1] \iteration -> measure mode iteration do
            fresh <- readIORef sourceRef
            chunks <- scanFixture fresh
            evaluate (forceLexicon (fixtureLexicon fresh))
            let prepared :: BlockParser
                prepared = Earley.parser (Concrete.grammar (fixtureLexicon fresh))
            traverse_ (evaluate . forceSelected . Parse.parsePreparedTokenChunk prepared) chunks
    else do
        chunks <- scanFixture fixture
        measure "lexical-data" 0 (evaluate (forceLexicon (fixtureLexicon fixture)))
        let preparedLexicon = Prepared.prepareLexicon (fixtureLexicon fixture)
        if mode == "parse" || mode == "report" then
            measure "prepare-lexicon" 0 (evaluate (Prepared.forcePreparedLexicon preparedLexicon))
        else pure ()
        -- WHNF of these functions is not a measurement of Earley setup.
        let lexicon = fixtureLexicon fixture
            prepared :: BlockParser
            prepared = Earley.parser (Concrete.grammarPrepared preparedLexicon)
            native = Concrete.prepareNativeMathParser lexicon
            markup = Markup.prepareMarkupParser lexicon
        inputs <- newIORef (chunks, nativeSnippets, markupSnippets)
        for_ [0 .. count - 1] \iteration -> measure mode iteration do
            (freshChunks, snippets, presentation) <- readIORef inputs
            case mode of
                "parse" -> traverse_ (evaluate . forceSelected . Parse.parsePreparedTokenChunk prepared) freshChunks
                "report" -> traverse_ (evaluate . forceReport . Earley.report prepared) freshChunks
                "native" -> traverse_ (evaluate . forceNativeResult . Concrete.parseNativeMath native) snippets
                "markup" -> traverse_ (evaluate . forceMarkupResult . Markup.parseCommentaryMath markup) presentation
                _ -> fail ("unknown mode: " <> mode)

forceSelected :: Either Parse.ParseException Raw.Block -> ()
forceSelected = either forceParseFailure rnf

-- Failure timings explicitly include the selected diagnostic text, matching
-- the CLI's reporting demand; raw expectations are forced as well.
forceParseFailure :: Parse.ParseException -> ()
forceParseFailure failure = case failure of
    Parse.UnconsumedTokens expectations tokens -> rnf expectations `seq` Scan.forceSourceTokenChunksHandoff [toList tokens] `seq` rendered
    _ -> rendered
  where
    rendered = rnf (show failure, diagnosticObservation failure)

forceReport :: Earley.Report Text [Located Token] -> ()
forceReport (Earley.Report position expected remaining) = rnf (position, expected) `seq` Scan.forceSourceTokenChunksHandoff [remaining]

forceNative :: Concrete.NativeMath -> ()
forceNative = \case
    Concrete.NativeTypedExpression value -> rnf value
    Concrete.NativeConcreteType value -> rnf value
    Concrete.NativeVariableList value -> rnf value

forceNativeResult :: Either Concrete.NativeMathFailure Concrete.NativeMath -> ()
forceNativeResult = either (rnf . show) forceNative

forceMarkupResult :: Either Markup.MarkupMathFailure Markup.CommentaryMath -> ()
forceMarkupResult = either (rnf . show) forceMarkup

forceMarkup :: Markup.CommentaryMath -> ()
forceMarkup = \case
    Markup.NativeMath value -> forceNative value
    Markup.MathIdentifier value -> rnf value
    Markup.MathNumber value -> rnf value
    Markup.MathOperator role value -> role `seq` rnf value
    Markup.MathRow values -> foldr (\value rest -> forceMarkup value `seq` rest) () values
    Markup.MathFenced fence value -> fence `seq` forceMarkup value
    Markup.MathScript value scripts -> forceMarkup value `seq` foldr (\s rest -> forceMarkup s `seq` rest) () scripts
    Markup.MathNamedOperator style value -> style `seq` rnf value
    Markup.MathPhrase (Markup.ScopedPhrase binding name) -> rnf (nativePhraseEntry binding, name)
    Markup.MathPhrase (Markup.DisplayPhrase name) -> rnf name

diagnosticObservation :: Parse.ParseException -> String
diagnosticObservation failure = case Parse.parseExceptionDiagnostic failure of
    Nothing -> "none"
    Just diagnostic -> show
        ( diagnosticSeverity diagnostic, diagnosticCode diagnostic
        , diagnosticTitle diagnostic, diagnosticPrimary diagnostic
        , show (diagnosticMessage diagnostic), map show (diagnosticNotes diagnostic)
        , map show (diagnosticHelp diagnostic))

observeChunk :: BlockParser -> [Located Token] -> IO (Int, Int)
observeChunk prepared tokens = do
    let (results, report) = Earley.fullParses prepared tokens
        successes = [block | Right block <- results]
        distinct = nubOrd successes
        selected = Parse.parsePreparedTokenChunk prepared tokens
    -- Serialize before deduplication: some Raw Eq/Ord instances intentionally
    -- ignore locations or lexical markers. The oracle must retain both.
    print ("successful-values" :: String, Set.toAscList (Set.fromList (blockObservation <$> successes)))
    print ("concrete-failures-in-order" :: String, [concreteFailureObservation failure | Left failure <- results])
    print ("report" :: String, report)
    print ("selected" :: String, either parseFailureObservation (show . blockObservation) selected)
    case selected of
        Left failure -> print ("diagnostic" :: String, diagnosticObservation failure)
        Right _ -> pure ()
    print ("counts" :: String, length results, length distinct)
    pure (length results, length distinct)

-- The canonical payload codec retains every location, including VarSymbol's
-- coordinates that its Show instance omits. It encodes line/column rather than
-- process-local SourceDescriptors. Each observation's fixture/module supplies its owner.
blockObservation :: Raw.Block -> (String, Text)
blockObservation block = (show block, mathematicalDigestHex (hashBlake2b256 bytes))
  where
    delta = either (error . show) id (Interface.canonicalSyntaxDelta [])
    syntax = Interface.moduleSyntaxAssertedId (either (error . show) id (Interface.moduleSyntaxInterface [] delta))
    bytes = Payload.canonicalParsedPayloadBytes (Payload.canonicalParsedPayload [] [block] [] syntax)

nativeObservation :: Either Concrete.NativeMathFailure Concrete.NativeMath -> String
nativeObservation outcome = show outcome <> case outcome of
    Right (Concrete.NativeTypedExpression expression) -> show (blockObservation
        (Raw.BlockClaim Raw.Proposition Nowhere Nothing "observation" (Raw.Claim [] (Raw.StmtFormula (formula expression)))))
    _ -> ""
  where
    formula (Raw.TypedExpressionFormula value) = value
    formula (Raw.TypedExpressionExpr value) = Raw.FormulaPredicate Nowhere (Raw.PrefixPredicate "observation" 1) "observation" (value :| [])

concreteFailureObservation :: Concrete.ConcreteSyntaxError -> String
concreteFailureObservation failure@(Concrete.OwnedStructureFieldReceiverMismatch location receiver owner) =
    show failure <> show (blockObservation (Raw.BlockClaim Raw.Proposition location Nothing "observation"
        (Raw.Claim [] (Raw.StmtFormula (Raw.FormulaPredicate location
            (Raw.PrefixPredicate "observation" 2) "observation" (Raw.ExprVar receiver :| [owner]))))))
concreteFailureObservation failure@Concrete.InvalidFieldEnvelope{} = show failure
concreteFailureObservation failure@Concrete.InvalidFieldContents{} = show failure

parseFailureObservation :: Parse.ParseException -> String
parseFailureObservation (Parse.ConcreteSyntaxFailure failure) = concreteFailureObservation failure
parseFailureObservation failure = show failure

markupObservation :: Either Markup.MarkupMathFailure Markup.CommentaryMath -> (String, [String])
markupObservation result = (show result, either (const []) nativeValues result)
  where
    nativeValues = \case
        Markup.NativeMath value -> [nativeObservation (Right value)]
        Markup.MathRow values -> concatMap nativeValues (toList values)
        Markup.MathFenced _ value -> nativeValues value
        Markup.MathScript value scripts -> nativeValues value <> concatMap nativeValues (toList scripts)
        _ -> []

observeFixture :: Fixture -> IO ()
observeFixture fixture = do
    chunks <- scanFixture fixture
    let lexicon = fixtureLexicon fixture
        prepared :: BlockParser
        prepared = Earley.parser (Concrete.grammar lexicon)
    print (fixtureName fixture, lexiconCounts lexicon, map length chunks)
    counts <- traverse (observeChunk prepared) chunks
    case fixtureName fixture of
        "short" -> requireCounts [(1, 1)] counts
        "duplicate-relation" -> requireCounts [(2, 1)] counts
        "ambiguous-relation" -> requireCounts [(2, 2)] counts
        "owned-field-failure" -> requireCounts [(1, 0)] counts
        "owned-field-success" -> requireCounts [(1, 1)] counts
        _ -> pure ()
    unless (not ("-match" `List.isSuffixOf` fixtureName fixture)
        || "-0-" `List.isInfixOf` fixtureName fixture || counts == [(1, 1)])
        (fail "nonempty scaling fixture must match its target uniquely")
    case List.stripPrefix "derivations-" (fixtureName fixture) of
        Just suffix -> case readMaybe (takeWhile (/= '-') suffix) of
            Just n -> requireCounts [(n, if "-equal" `List.isSuffixOf` suffix then 1 else n)] counts
            Nothing -> fail "invalid derivation fixture name"
        Nothing -> pure ()
    let native = Concrete.prepareNativeMathParser lexicon
        markup = Markup.prepareMarkupParser lexicon
    for_ nativeSnippets \snippet -> print ("native" :: String, snippet, nativeObservation (Concrete.parseNativeMath native snippet))
    for_ markupSnippets \snippet -> print ("markup" :: String, snippet, markupObservation (Markup.parseCommentaryMath markup snippet))
    for_ ["set", "benchab", "common benchab"] \phrase ->
        print ("phrase" :: String, phrase, Concrete.lookupNativePhrase native phrase)
    whenAmbiguous fixture native markup
  where
    requireCounts intended actual = unless (actual == intended)
        (fail ("fixture counts: wanted " <> show intended <> "; got " <> show actual))
    whenAmbiguous f native markup
        | fixtureName f == "native-ambiguous" = do
            unless (Concrete.parseNativeMath native "\\Set" == Left (Concrete.NativeMathRejected (Concrete.NativeMathAmbiguous 2)))
                (fail "native ambiguity fixture no longer ambiguous")
            unless (Markup.parseCommentaryMath markup "\\Set" == Left (Markup.MarkupNativeAmbiguity 2))
                (fail "HTML ambiguity must remain decisive")
        | otherwise = pure ()

observeControls :: IO ()
observeControls = do
    -- Earley diagnostic feasibility control, independent of Felix's grammar.
    let old :: Earley.Parser Text String Char
        old = Earley.parser (pure ((Earley.satisfy (== 'a') Earley.<?> "a") <|> (Earley.satisfy (== 'b') Earley.<?> "b") Earley.<?> "category"))
        lookupOnly :: Earley.Parser Text String Char
        lookupOnly = Earley.parser (pure (Earley.terminal (\c -> if c `elem` ['a', 'b'] then Just c else Nothing) Earley.<?> "category"))
        namedLookup :: Earley.Parser Text String Char
        namedLookup = Earley.parser (pure (((Earley.terminal (\c -> if c `elem` ['a', 'b'] then Just c else Nothing) Earley.<?> "b") Earley.<?> "a") Earley.<?> "category"))
    print ("labelled-alternatives" :: String, Earley.fullParses old "x")
    print ("category-only" :: String, Earley.fullParses lookupOnly "x")
    print ("named-lookup" :: String, Earley.fullParses namedLookup "x")
    unless (show (Earley.fullParses old "x") == show (Earley.fullParses namedLookup "x"))
        (fail "lookup diagnostic control changed")
    f <- findFixture "short"
    chunks <- scanFixture f
    seed <- case chunks of
        [tokens] -> either (fail . show) pure (Parse.parsePreparedTokenChunk (Earley.parser (Concrete.grammar builtins)) tokens)
        _ -> fail "one seed block expected"
    let first = Concrete.OwnedStructureFieldReceiverMismatch Nowhere (Raw.NamedVar "x") (Raw.ExprVar (Raw.NamedVar "y"))
        second = Concrete.OwnedStructureFieldReceiverMismatch Nowhere (Raw.NamedVar "x") (Raw.ExprVar (Raw.NamedVar "z"))
        controls =
            [ ("unique" :: String, [Right seed], (1, 1))
            , ("duplicates" :: String, replicate 4 (Right seed), (4, 1))
            , ("mixed" :: String, [Left first, Right seed, Left second], (3, 1))
            , ("competing-failures" :: String, [Left first, Left second, Left first], (3, 0))
            , ("empty" :: String, [], (0, 0))
            ]
    for_ controls \(name, values, intended) -> do
        print ("toy-selection" :: String, name)
        observed <- observeChunk (Earley.parser (pure (asum (pure <$> values)))) []
        unless (observed == intended) (fail "toy raw/distinct count mismatch")
    -- A partial result must still lose to unconsumed input.
    print ("toy-unconsumed" :: String, either show show
        (Parse.parsePreparedTokenChunk (Earley.parser (pure (pure (Right seed)))) (concat chunks)))

observeCorpus :: FilePath -> IO ()
observeCorpus root = do
    environment <- Workspace.prepareDefaultWorkspaceEnvironment >>= either (fail . show) pure
    request <- Workspace.prepareWorkspaceRoot environment root >>= either (fail . show) pure
    graph <- Workspace.prepareSourceGraph environment request >>= either (fail . show) pure
    preludeSource <- Prelude.loadReservedPreludeSourceInput >>= either (fail . show) pure
    prelude <- Prelude.parseReservedPreludeSource preludeSource >>= either (fail . show) pure
    either (fail . show) pure (Prelude.rejectOrdinaryPreludeSourceGraph preludeSource graph)
    let preludeModule = Prelude.reservedParsedPreludeModule prelude
        preludeSyntax = Parsed.identifiedParsedModuleSyntaxInterface preludeModule
    workspace <- Parse.parseResolvedSourceGraphWithSyntaxInputs graph (const [preludeSyntax]) >>= either (fail . show) pure
    let modules = Parsed.parsedWorkspaceModules workspace
        interfaces = preludeSyntax : map Parsed.parsedModuleSyntaxInterface modules
        interfaceMap = Map.fromList [(Interface.moduleSyntaxAssertedId i, i) | i <- interfaces]
        logical source = LogicalSourceAddress
            (sourceMountIdText (resolvedSourceMount source))
            (Text.pack (safeRelativePathFilePath (resolvedSourceRelativePath source)))
        sourceInput node = ManifestSourceInput
            (logical (Graph.sourceNodeResolved node))
            (canonicalPathFilePath (resolvedSourceCanonicalPath (Graph.sourceNodeResolved node)))
            (loadedBytes (Graph.sourceNodeLoaded node))
        inputs = ManifestSourceInput (LogicalSourceAddress "reserved" "prelude.tex")
            "library/prelude.tex" (Prelude.reservedPreludeSourceBytes preludeSource)
            : map sourceInput (toList (Graph.sourceGraphImportedBeforeImporter graph))
        manifest = makeCorpusManifest (logical (Graph.sourceGraphRootSource graph))
            [sourceMountIdText (sourceMountIdentifier mount) | mount <- sourceMountList (Workspace.workspaceSourceMounts environment)] inputs
    putStrLn (Text.unpack (renderCorpusManifest manifest))
    print ("prelude-blocks" :: String, map blockObservation (Parsed.identifiedParsedModuleBlocks preludeModule))
    preludeLexicon <- either (fail . show) pure (Adapt.materializeEffectiveSyntax interfaceMap preludeSyntax)
    preludeChunks <- scanFixture (Fixture "reserved-prelude" preludeLexicon (Prelude.reservedPreludeSourceText preludeSource))
    print ("prelude-counts" :: String, lexiconCounts preludeLexicon, map length preludeChunks)
    traverse_ (observeChunk (Earley.parser (Concrete.grammar preludeLexicon))) preludeChunks
    for_ modules \m -> do
        lexicon <- either (fail . show) pure
            (Adapt.materializeEffectiveSyntax interfaceMap (Parsed.parsedModuleSyntaxInterface m))
        chunks <- either (fail . show) pure (Scan.scanCompleteSourceTokens (Parsed.parsedModuleIdentifiedSource m))
        print ("module" :: String, logical (Parsed.parsedModuleResolved m), lexiconCounts lexicon, map length chunks)
        print ("module-blocks" :: String, map blockObservation (Parsed.parsedModuleBlocks m))
        -- Complete semantic sets, independent of production's selected block.
        traverse_ (observeChunk (Earley.parser (Concrete.grammar lexicon))) chunks

-- Complete production handoffs, without the much larger per-derivation oracle.
-- The canonical codec preserves markers, variable locations, syntax and
-- occurrence associations. This command never runs inside a performance trial.
observeWorkspace :: FilePath -> IO ()
observeWorkspace root = do
    preludeSource <- Prelude.loadReservedPreludeSourceInput >>= either (fail . show) pure
    prelude <- Prelude.parseReservedPreludeSource preludeSource >>= either (fail . show) pure
    let reserved = Prelude.reservedParsedPreludeModule prelude
    print ("reserved" :: String, Parsed.identifiedParsedModuleId reserved)
    graph <- Workspace.prepareDefaultSourceGraph root >>= either (fail . show) pure
    either (fail . show) pure (Prelude.rejectOrdinaryPreludeSourceGraph preludeSource graph)
    workspace <- Parse.parseResolvedSourceGraphWithSyntaxInputs graph
        (const [Parsed.identifiedParsedModuleSyntaxInterface reserved]) >>= either (fail . show) pure
    for_ (Parsed.parsedWorkspaceModules workspace) \m -> do
        let payload = Payload.canonicalParsedPayloadBytes (Parsed.parsedModulePayload m)
            path = safeRelativePathFilePath (resolvedSourceRelativePath (Parsed.parsedModuleResolved m))
        evaluate (rnf (Parsed.parsedModuleBlocks m))
        print (path, length (Parsed.parsedModuleBlocks m), Parsed.parsedModuleSourceContentId m,
            mathematicalDigestHex (hashBlake2b256 payload))

-- Actual presentation projection, native math, navigation, and HTML rendering.
-- This uses a maintained presentation fixture and no verification/store path.
-- Source discovery, parsing, file I/O, and rendering are included in the timer.
renderHtmlFixture :: Fixture -> IO (Text, [String])
renderHtmlFixture fixture = do
    environment <- Workspace.prepareDefaultWorkspaceEnvironment >>= either (fail . show) pure
    graph <- Workspace.prepareDefaultSourceGraph "test/html-fixtures/document-presentation.tex" >>= either (fail . show) pure
    workspace <- Parse.parseResolvedSourceGraph graph >>= either (fail . show) pure
    layout <- either (fail . show) pure (layoutHtmlSourceGraph (Workspace.workspaceHtmlMountPrefixes environment) graph)
    hints <- either (fail . show) pure (Hints.parseRenderHints "")
    let m = Parsed.parsedWorkspaceRootModule workspace
        source = Parsed.parsedModuleResolved m
        blocks = Parsed.parsedModuleBlocks m
    segments <- either (fail . show) pure (Scan.scanCompletePresentationText
        (Parsed.parsedModuleSourceDescriptor m) "test/html-fixtures/document-presentation.tex" (loadedText (Parsed.parsedModuleLoaded m)))
    draft <- either (fail . show) pure (Html.projectHtmlDocumentWithMathParser
        (Markup.prepareMarkupParser (fixtureLexicon fixture)) segments blocks)
    let (document, diagnostics) = Html.resolveHtmlDocument hints draft
        (index, pages) = Html.buildRenderIndexWithNavigationAndDocuments source
            ((source, [], blocks, Map.empty, document) :| [])
    context <- either (fail . show) pure (htmlRenderContext layout source)
    html <- either (fail . show) pure (Html.renderDocument context hints index (case pages of page :| _ -> page))
    pure (html, map (show . diagnosticMessage) diagnostics)
