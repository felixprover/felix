{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Felix.Test.Unit.Source (unitTests) where

import Base
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Semantic qualified as Semantic
import Felix.Cache.Codec qualified as Cache
import Felix.Module qualified as Module
import Felix.Parse qualified as Parse
import Felix.Parsed.Identity qualified as ParsedIdentity
import Felix.Parsed.Module qualified as ParsedModule
import Felix.Parsed.Payload qualified as Parsed
import Felix.Parsed.Workspace qualified as ParsedModule
import Felix.Prelude qualified as Prelude
import Felix.Source
import Felix.Source.Content qualified as Content
import Felix.Source.Graph
import Felix.Store qualified as Store
import Felix.Text.Hex (lowerHexText)
import Felix.Report.Location
    ( Location
    , Locatable(..)
    , anonymousSourceDescriptor
    , locColumn
    , locFile
    , locSourceDescriptor
    , locLine
    , sourceDescriptorIdentityPath
    , sourceDescriptorDisplayPath
    , sourceDescriptor
    )
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Adapt qualified as Adapt
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Interface qualified as Interface
import Felix.Syntax.Lexicon qualified as Lexicon
import Felix.Test.SourceScan.Adapter (scanTestSource)
import Felix.Test.Temp (withTemporaryDirectory)
import Felix.Verification qualified as Verification

import Control.Exception (evaluate)
import Data.ByteString qualified as ByteString
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Word (Word8)
import Database.SQLite.Simple qualified as SQLite
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix
import System.Posix.Files qualified as PosixFiles
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests = testGroup "Source resolution"
    [ testCase "validates mount-root-relative POSIX paths" validatesRelativePaths
    , testCase "rejects duplicate source mount ids" rejectsDuplicateMountIds
    , testCase "rejects duplicate canonical mount roots" rejectsDuplicateMountRoots
    , testCase "permits missing and rejects non-directory mounts"
        validatesMountRootTypes
    , testCase "rejects relative exact roots" rejectsRelativeExactRoots
    , testCase "retains exact root spelling as diagnostic trivia" retainsRootSpelling
    , testCase "searched and exact roots share canonical identity" rootFormsShareIdentity
    , testCase "attributes nested sources to the most specific mount" attributesNestedSources
    , testCase "configured order selects searched candidates" candidateOrderSelectsWinner
    , testCase "rejects a higher-priority special source"
        rejectsHigherPrioritySpecialSource
    , testCase "rejects exact roots outside configured mounts" rejectsOutsideExactRoot
    , testCase "loads source text as strict UTF-8" loadsStrictUtf8
    , testCase "reports malformed UTF-8 sequence starts"
        reportsInvalidUtf8Offsets
    , testCase "builds an imported-before-importer source graph" buildsSourceGraph
    , testCase "ignores heading command text during graph discovery"
        ignoresHeadingCommandTextInGraph
    , testCase "rejects late imports during complete parsing"
        rejectsLateImportDuringParsing
    , testCase "commits recognized formal environments during parsing"
        commitsRecognizedFormalEnvironmentDuringParsing
    , testCase "rejects reserved prelude sources as ordinary source"
        rejectsReservedPreludeSources
    , testCase "orders sibling imports by textual occurrence"
        ordersSiblingImports
    , testCase "orders shared dependencies before their importers"
        ordersSharedDependencies
    , testCase "retains repeated import-edge occurrences" retainsRepeatedImports
    , testCase "deduplicates canonical source nodes" deduplicatesCanonicalNodes
    , testCase "reports missing imports at their source location" reportsMissingImports
    , testCase "rejects unsafe imports at their source location" rejectsUnsafeImports
    , testCase "reports the located import cycle chain" reportsImportCycles
    , testCase "rejects malformed imported source before discovery" rejectsMalformedImportedSource
    , testCase "builds empty modules through the ordinary pipeline"
        buildsEmptyModules
    , testCase "identifies owner-independent parsed modules"
        identifiesOwnerIndependentParsedModules
    , testCase "detects representative parsed payload layout changes"
        detectsParsedPayloadLayoutChanges
    , testCase "bounded noun payloads retain scope fields and locations" retainsBoundedNounPayload
    , testCase "checks parsed verb surfaces at cache re-entry"
        checksParsedVerbSurfaceCache
    , testCase "checks parsed module source bindings"
        checksParsedModuleSourceBindings
    , testCase "admits parsed artifacts only in their source and syntax context"
        checksParsedArtefactContexts
    , testCase "checks ordered parsed import bindings"
        checksParsedImportBindings
    , testCase "keys effective direct syntax inputs"
        keysEffectiveDirectSyntaxInputs
    , testCase "reuses exact parsed syntax on a warm pass"
        reusesExactParsedSyntax
    , testCase "invalidates exact parsed inputs transitively"
        invalidatesExactParsedInputs
    , testCase "rebinds relocated parsed artefacts"
        rebindsRelocatedParsedArtefacts
    , testCase "rejects a corrupted cached declaration anchor"
        rejectsCorruptedCachedDeclarationAnchor
    , testCase "parses source-local blocks in graph order" parsesSourceGraph
    , testCase "does not leak syntax between sibling imports"
        rejectsSiblingSyntaxLeakage
    , testCase "parses source fixity levels and grouping"
        parsesSourceFixities
    , testCase "parses cdot and symdiff fixities"
        parsesLibraryFixities
    , testCase "validates source pragma associations"
        validatesSourcePragmaAssociations
    , testCase "rejects fixed-base category mismatches"
        rejectsFixedBaseCategoryMismatch
    , testCase "retains multi-item syntax occurrence order"
        retainsMultiItemSyntaxOccurrences
    , testCase "propagates and coalesces imported syntax"
        propagatesImportedSyntax
    , testCase "rejects unequal imported syntax"
        rejectsUnequalImportedSyntax
    , testCase "qualifies same-display cross-mount collisions"
        distinguishesPhysicalSourceLocations
    , testCase "retains each workspace location display path"
        retainsWorkspaceLocationDisplayPath
    , testCase "keeps source descriptors immutable"
        keepsSourceDescriptorImmutable
    , testCase
        "reports imported extraction errors before importer tokenizer errors"
        reportsImportedExtractionErrorFirst
    , testCase "returns malformed lexical declarations as typed errors"
        reportsMalformedLexicalDeclaration
    , testCase "validates inductive function patterns during extraction"
        rejectsMalformedInductivePattern
    , testCase "prepares article-bearing and explicit-base verbs"
        preparesCanonicalVerbMetadata
    , testCase "rejects invalid verb metadata deterministically"
        rejectsInvalidVerbMetadata
    , testCase "extracts and parses adjective signatures"
        acceptsAdjectiveSignature
    , testCase "extracts and parses typed constant signatures"
        acceptsTypedConstantSignature
    , testCase "rejects malformed math-led signature heads"
        rejectsMalformedSignatureHead
    , testCase "extracts canonical owned structure fields"
        extractsCanonicalOwnedStructureField
    , testCase "rejects a wrong owned structure-field receiver"
        rejectsWrongOwnedStructureFieldReceiver
    , testCase "locates conflicting declarations within one environment"
        reportsSameSourceLexiconCollision
    , testCase "accepts the first source declaration of a built-in pattern"
        acceptsBuiltinSourceDeclaration
    , testCase "keeps the built-in marker for a prefix predicate declaration"
        acceptsBuiltinPrefixPredicateDeclaration
    , testCase "does not rescan repeated canonical imports"
        avoidsAliasImportLexiconCollision
    , testCase "parses loaded sources without rereading files" parsesWithoutRereading
    , testCase "returns the first concrete failure after an earlier valid chunk"
        returnsSourceParseFailures
    , testCase "admits symbolic definition headers but rejects guarded abbreviations"
        checksGuardedSymbolicDeclarations
    , testCase "parses result annotations on set-valued definitions"
        parsesDefinitionResultAnnotations
    ]

keepsSourceDescriptorImmutable :: Assertion
keepsSourceDescriptorImmutable = do
    let first = sourceDescriptor
            "/virtual/felix-location-identity" "location-display.tex"
        second = sourceDescriptor
            "/virtual/felix-location-identity" "location-display.tex"
    assertEqual "repeated descriptor construction" first second
    assertEqual
        "physical identity"
        (Just "/virtual/felix-location-identity")
        (sourceDescriptorIdentityPath first)
    assertEqual
        "descriptor display path"
        "location-display.tex"
        (sourceDescriptorDisplayPath first)

validatesRelativePaths :: Assertion
validatesRelativePaths = do
    assertRight (safeRelativePath "theory/set.tex")
    assertRight (safeRelativePath "theory\\set.tex")
    assertLeft EmptyRelativePath (safeRelativePath "")
    assertLeft AbsoluteRelativePath (safeRelativePath "/theory.tex")
    assertLeft CurrentDirectoryComponent (safeRelativePath "./theory.tex")
    assertLeft ParentDirectoryComponent (safeRelativePath "a/../theory.tex")
    assertLeft EmptyPathComponent (safeRelativePath "a//theory.tex")
    assertLeft EmptyPathComponent (safeRelativePath "a/")
    assertLeft NullPathCharacter (safeRelativePath "a\0b")

rejectsDuplicateMountIds :: Assertion
rejectsDuplicateMountIds =
    withTemporaryDirectory "felix-source-duplicate-id" \temp -> do
        result <- prepareSourceMounts
            [ (sourceMountId "same", temp Posix.</> "one")
            , (sourceMountId "same", temp Posix.</> "two")
            ]
        assertEqual
            "duplicate id"
            (Left (DuplicateSourceMountId (sourceMountId "same")))
            result

rejectsDuplicateMountRoots :: Assertion
rejectsDuplicateMountRoots =
    withTemporaryDirectory "felix-source-duplicate-root" \temp -> do
        result <- prepareSourceMounts
            [ (sourceMountId "one", temp)
            , (sourceMountId "two", temp Posix.</> ".")
            ]
        canonical <- Directory.canonicalizePath temp
        case result of
            Left (DuplicateCanonicalMountRoot root firstId secondId) -> do
                assertEqual "canonical root" canonical (canonicalPathFilePath root)
                assertEqual "first mount id" (sourceMountId "one") firstId
                assertEqual "second mount id" (sourceMountId "two") secondId
            Left err ->
                assertFailure ("expected DuplicateCanonicalMountRoot, got " <> show err)
            Right mounts ->
                assertFailure ("expected duplicate-root rejection, got " <> show mounts)

validatesMountRootTypes :: Assertion
validatesMountRootTypes =
    withTemporaryDirectory "felix-source-mount-type" \temp -> do
        let ident = sourceMountId "project"
            missing = temp Posix.</> "missing"
            regularFile = temp Posix.</> "file"
        assertRight =<< prepareSourceMounts [(ident, missing)]

        writeFile regularFile ""
        result <- prepareSourceMounts [(ident, regularFile)]
        case result of
            Left SourceMountNotDirectory{} ->
                pure ()
            Left err ->
                assertFailure
                    ("expected SourceMountNotDirectory, got " <> show err)
            Right mounts ->
                assertFailure
                    ("expected non-directory rejection, got " <> show mounts)

rejectsRelativeExactRoots :: Assertion
rejectsRelativeExactRoots =
    assertEqual
        "relative exact roots are rejected"
        (Left (ExistingRootNotAbsolute "entry.tex"))
        =<< existingRoot "entry.tex"

retainsRootSpelling :: Assertion
retainsRootSpelling =
    withTemporaryDirectory "felix-source-root-spelling" \temp -> do
        let source = temp Posix.</> "entry.tex"
            alias = temp Posix.</> "entry-alias.tex"
        writeFile source ""
        Directory.createFileLink source alias
        direct <- expectRight =<< existingRoot source
        throughAlias <- expectRight =<< existingRoot alias
        assertEqual "canonical request identity" direct throughAlias
        assertEqual "diagnostic spelling" alias
            (rootRequestSpelling throughAlias)

rootFormsShareIdentity :: Assertion
rootFormsShareIdentity =
    withTemporaryDirectory "felix-source-root-identity" \temp -> do
        let source = temp Posix.</> "entry.tex"
        writeFile source "source"
        mounts <- oneMount "project" temp
        searched <- expectRight (searchedRoot "entry.tex")
        exact <- expectRight =<< existingRoot source
        searchedLoaded <- expectRight =<< resolveAndLoadRoot mounts searched
        exactLoaded <- expectRight =<< resolveAndLoadRoot mounts exact
        assertEqual "loaded source" searchedLoaded exactLoaded
        assertEqual "source mount"
            (resolvedSourceMount (loadedSource searchedLoaded))
            (resolvedSourceMount (loadedSource exactLoaded))
        assertEqual "mount-relative source path"
            (resolvedSourceRelativePath (loadedSource searchedLoaded))
            (resolvedSourceRelativePath (loadedSource exactLoaded))

rejectsReservedPreludeSources :: Assertion
rejectsReservedPreludeSources = do
    packaged <- expectRight =<< Prelude.loadReservedPreludeSourceInput
    canonical <- expectJust "packaged canonical path"
        (Prelude.reservedPreludeSourceCanonicalPath packaged)
    let path = canonicalPathFilePath canonical
    mounts <- oneMount "packaged" (Posix.takeDirectory path)
    request <- expectRight (searchedRoot (Posix.takeFileName path))
    let validate = Prelude.rejectOrdinaryPreludeSourceGraph packaged
        syntaxInputs = const []
    Parse.parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
        mounts request syntaxInputs validate >>= \case
            Left
                (Parse.SourceWorkspaceError
                    (ReservedPreludeSelectedAsOrdinarySource source)) ->
                        assertEqual "authority-free rejected path"
                            canonical
                            (resolvedSourceCanonicalPath source)
            other ->
                assertFailure
                    ("unexpected authority-free result: " <> show other)

    withTemporaryDirectory "felix-reserved-parse-store" \temp -> do
        foundation <- expectRight Foundation.checkedFoundation
        store <- openTestStore
            (temp Posix.</> "store.sqlite")
            (Identity.theoryId foundation)
        Parse.parseSourceWorkspaceWithStoreAndSyntaxInputsAndGraphValidation
            store mounts request syntaxInputs validate >>= \case
                Left
                    (Parse.ParseExecutionWorkspaceError
                        (Parse.SourceWorkspaceError
                            (ReservedPreludeSelectedAsOrdinarySource source))) ->
                                assertEqual "typed rejected path"
                                    canonical
                                    (resolvedSourceCanonicalPath source)
                other ->
                    assertFailure
                        ("unexpected typed result: " <> show other)
        Store.closeStore store

    assertLogicalPreludeRejected
        packaged "library" "prelude.tex"
    assertLogicalPreludeRejected
        packaged "project" Prelude.preludeDataFilePath
    assertUnrelatedPreludeAccepted packaged

assertLogicalPreludeRejected
    :: Prelude.ReservedPreludeSourceInput
    -> Text
    -> FilePath
    -> Assertion
assertLogicalPreludeRejected packaged mountName relative =
    withTemporaryDirectory "felix-logical-prelude" \temp -> do
        let sourcePath = temp Posix.</> relative
        Directory.createDirectoryIfMissing True
            (Posix.takeDirectory sourcePath)
        writeFile sourcePath "% logical prelude fixture\n"
        mounts <- oneMount mountName temp
        request <- expectRight (searchedRoot relative)
        Parse.parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
            mounts request (const [])
            (Prelude.rejectOrdinaryPreludeSourceGraph packaged) >>= \case
                Left
                    (Parse.SourceWorkspaceError
                        (ReservedPreludeSelectedAsOrdinarySource source)) -> do
                            assertEqual "reserved logical mount"
                                (sourceMountId mountName)
                                (resolvedSourceMount source)
                            assertEqual "reserved logical path"
                                relative
                                (safeRelativePathFilePath
                                    (resolvedSourceRelativePath source))
                other ->
                    assertFailure
                        ("unexpected logical prelude result: " <> show other)

assertUnrelatedPreludeAccepted
    :: Prelude.ReservedPreludeSourceInput
    -> Assertion
assertUnrelatedPreludeAccepted packaged =
    withTemporaryDirectory "felix-unrelated-prelude" \temp -> do
        let sourcePath = temp Posix.</> "prelude.tex"
        writeFile sourcePath "% unrelated prelude fixture\n"
        mounts <- oneMount "examples" temp
        request <- expectRight (searchedRoot "prelude.tex")
        Parse.parseSourceWorkspaceWithSyntaxInputsAndGraphValidation
            mounts request (const [])
            (Prelude.rejectOrdinaryPreludeSourceGraph packaged) >>= \case
                Right{} -> pure ()
                Left failure ->
                    assertFailure
                        ("unrelated prelude was rejected: " <> show failure)

attributesNestedSources :: Assertion
attributesNestedSources =
    withTemporaryDirectory "felix-source-nested-mount" \temp -> do
        let nested = temp Posix.</> "library"
            source = nested Posix.</> "entry.tex"
        Directory.createDirectory nested
        writeFile source "source"
        exact <- expectRight =<< existingRoot source
        outerFirst <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "project", temp)
            , (sourceMountId "library", nested)
            ]
        innerFirst <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "library", nested)
            , (sourceMountId "project", temp)
            ]
        searched <- expectRight (searchedRoot "library/entry.tex")
        outerFirstSource <- loadedSource <$> (expectRight =<< resolveAndLoadRoot outerFirst exact)
        innerFirstSource <- loadedSource <$> (expectRight =<< resolveAndLoadRoot innerFirst exact)
        searchedSource <- loadedSource <$> (expectRight =<< resolveAndLoadRoot outerFirst searched)
        assertEqual "order-independent attribution" outerFirstSource innerFirstSource
        assertEqual "root-form-independent attribution" outerFirstSource searchedSource
        assertEqual "most specific mount" (sourceMountId "library") (resolvedSourceMount outerFirstSource)
        assertEqual "mount-relative identity" "entry.tex"
            (safeRelativePathFilePath (resolvedSourceRelativePath outerFirstSource))

candidateOrderSelectsWinner :: Assertion
candidateOrderSelectsWinner =
    withTemporaryDirectory "felix-source-precedence" \temp -> do
        let firstRoot = temp Posix.</> "first"
            secondRoot = temp Posix.</> "second"
            firstSource = firstRoot Posix.</> "entry.tex"
            secondSource = secondRoot Posix.</> "entry.tex"
        Directory.createDirectory firstRoot
        Directory.createDirectory secondRoot
        writeFile firstSource "first"
        writeFile secondSource "second"
        request <- expectRight (searchedRoot "entry.tex")
        firstMounts <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "first", firstRoot)
            , (sourceMountId "second", secondRoot)
            ]
        secondMounts <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "second", secondRoot)
            , (sourceMountId "first", firstRoot)
            ]
        firstWinner <- expectRight =<< resolveAndLoadRoot firstMounts request
        secondWinner <- expectRight =<< resolveAndLoadRoot secondMounts request
        assertEqual "first configured source" "first" (loadedText firstWinner)
        assertEqual "reversed configured source" "second" (loadedText secondWinner)

rejectsHigherPrioritySpecialSource :: Assertion
rejectsHigherPrioritySpecialSource =
    withTemporaryDirectory "felix-source-special-precedence" \temp -> do
        let higherRoot = temp Posix.</> "higher"
            lowerRoot = temp Posix.</> "lower"
            higherSource = higherRoot Posix.</> "entry.tex"
            lowerSource = lowerRoot Posix.</> "entry.tex"
        Directory.createDirectory higherRoot
        Directory.createDirectory lowerRoot
        PosixFiles.createNamedPipe higherSource PosixFiles.ownerModes
        writeFile lowerSource "ordinary source"
        mounts <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "higher", higherRoot)
            , (sourceMountId "lower", lowerRoot)
            ]
        request <- expectRight (searchedRoot "entry.tex")
        result <- resolveRoot mounts request
        case result of
            Left
                (SelectedSourceNotRegular
                    (SearchedRootLookup relative)
                    selectedPath
                    canonical) -> do
                        assertEqual "searched path"
                            "entry.tex"
                            (safeRelativePathFilePath relative)
                        assertEqual "selected higher candidate"
                            higherSource
                            selectedPath
                        canonicalHigher <-
                            Directory.canonicalizePath higherSource
                        assertEqual "selected canonical target"
                            canonicalHigher
                            (canonicalPathFilePath canonical)
            Left err ->
                assertFailure
                    ("expected SelectedSourceNotRegular, got " <> show err)
            Right source ->
                assertFailure
                    ("expected special-source rejection, got " <> show source)

rejectsOutsideExactRoot :: Assertion
rejectsOutsideExactRoot =
    withTemporaryDirectory "felix-source-outside-root" \temp -> do
        let mountRoot = temp Posix.</> "mount"
            outsideRoot = temp Posix.</> "outside"
            source = outsideRoot Posix.</> "entry.tex"
        Directory.createDirectory mountRoot
        Directory.createDirectory outsideRoot
        writeFile source "source"
        mounts <- oneMount "project" mountRoot
        exact <- expectRight =<< existingRoot source
        result <- resolveAndLoadRoot mounts exact
        case result of
            Left (RootOutsideConfiguredMount spelling _canonical) ->
                assertEqual "exact-root diagnostic spelling" source spelling
            Left err ->
                assertFailure ("expected RootOutsideConfiguredMount, got " <> show err)
            Right loaded ->
                assertFailure ("expected outside-root rejection, got " <> show loaded)

loadsStrictUtf8 :: Assertion
loadsStrictUtf8 =
    withTemporaryDirectory "felix-source-utf8" \temp -> do
        let source = temp Posix.</> "unicode.tex"
            bytes =
                ByteString.pack
                    [ 0xCE, 0xB1, 0x20, 0xE2
                    , 0x88, 0x88, 0x20, 0x41
                    ]
        ByteString.writeFile source bytes
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "unicode.tex")
        loaded <- expectRight =<< resolveAndLoadRoot mounts request
        assertEqual "exact bytes" bytes (loadedBytes loaded)
        assertEqual "decoded text" ("α ∈ A" :: Text) (loadedText loaded)
        assertEqual
            "byte count"
            (fromIntegral (ByteString.length bytes))
            (loadedByteCount loaded)
        let identifier =
                Content.sourceContentId loaded
        identified <- Content.identifyLoadedSource loaded
        assertEqual
            "identified source retains loaded bytes"
            loaded
            (Content.identifiedSourceLoaded identified)
        assertEqual
            "identified source retains content identity"
            identifier
            (Content.identifiedSourceContentId identified)
        assertEqual
            "identified source uses its descriptor display path"
            (resolvedSourceLocationPath (loadedSource loaded))
            (sourceDescriptorDisplayPath (Content.identifiedSourceDescriptor identified))
        assertEqual
            "content identity cache round trip"
            (Right identifier)
            (Cache.decodeCache
                Content.getSourceContentIdCache
                (Cache.encodeCache
                    (Content.putSourceContentIdCache
                        identifier)))
        ByteString.writeFile source (bytes <> "\n")
        changed <- expectRight
            =<< loadResolvedSource (loadedSource loaded)
        assertBool
            "exact byte edits change source identity"
            (identifier /= Content.sourceContentId changed)

reportsInvalidUtf8Offsets :: Assertion
reportsInvalidUtf8Offsets =
    withTemporaryDirectory "felix-source-invalid-utf8" \temp -> do
        let source = temp Posix.</> "invalid.tex"
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "invalid.tex")
        let assertOffset label bytes expected = do
                ByteString.writeFile source (ByteString.pack bytes)
                result <- resolveAndLoadRoot mounts request
                case result of
                    Left (SourceDecodeError _source offset) ->
                        assertEqual label expected offset
                    Left err ->
                        assertFailure
                            ("expected SourceDecodeError, got " <> show err)
                    Right loaded ->
                        assertFailure
                            ("expected malformed UTF-8 rejection, got "
                                <> show loaded)
        assertOffset "malformed sequence start" [0x61, 0xC3, 0x28] 1
        assertOffset "incomplete sequence start" [0x61, 0xC3] 1

buildsSourceGraph :: Assertion
buildsSourceGraph =
    withTemporaryDirectory "felix-source-graph" \temp -> do
        writeTheory (temp Posix.</> "shared.tex") [] "shared"
        writeTheory (temp Posix.</> "entry.tex") ["shared.tex"] "entry"
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        preparation <- expectRight
            =<< buildResolvedSourceGraphMeasured mounts request
        let graph = sourceGraphPreparationGraph preparation
            measurements = sourceGraphPreparationMeasurements preparation
        assertEqual "two source nodes" 2 (length (sourceGraphNodes graph))
        assertEqual
            "one prefix observation per graph node"
            2
            (sourcePrefixScanCount measurements)
        case sourceGraphImportEdges graph of
            [edge] -> do
                assertEqual "root imports" (sourceGraphRoot graph) (sourceImportingNode edge)
                assertEqual
                    "imported-before-importer order"
                    [sourceImportedNode edge, sourceGraphRoot graph]
                    ( sourceNodeCanonicalPathForTest
                        <$> toList
                            (sourceGraphImportedBeforeImporter graph)
                    )
                assertEqual "import location line" 1
                    (locLine (importLocation (sourceImportReference edge)))
                assertEqual "selected location path" "entry.tex"
                    (locFile (importLocation (sourceImportReference edge)))
            edges ->
                assertFailure ("expected one import edge, got " <> show edges)

ignoresHeadingCommandTextInGraph :: Assertion
ignoresHeadingCommandTextInGraph =
    withTemporaryDirectory "felix-source-heading-import" \temp -> do
        writeTheory (temp Posix.</> "real.tex") [] "real"
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\section{Literal \\import{ghost.tex}}"
                , ""
                , "\\import{real.tex}"
                , theoryBlock "entry"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        order <- sourceGraphOrderPaths graph
        assertEqual
            "heading command text does not create a graph edge"
            ["real.tex", "entry.tex"]
            order

rejectsLateImportDuringParsing :: Assertion
rejectsLateImportDuringParsing =
    withTemporaryDirectory "felix-source-late-import" \temp -> do
        writeTheory (temp Posix.</> "first.tex") [] "first"
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\import{first.tex}"
                , ""
                , "\\section{Body}"
                , ""
                , "\\import{late.tex}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        assertEqual
            "graph remains prefix-only"
            ["first.tex", "entry.tex"]
            =<< sourceGraphOrderPaths graph
        result <- Parse.parseResolvedSourceGraph graph
        case result of
            Left (Parse.SourceParseError source failure) -> do
                assertEqual
                    "late-import source"
                    "entry.tex"
                    (safeRelativePathFilePath
                        (resolvedSourceRelativePath source))
                assertBool
                    "late-import diagnostic"
                    ( "imports must form one contiguous top-level block"
                        `List.isInfixOf` show failure
                    )
            Left failure ->
                assertFailure
                    ("expected late-import parse failure, got " <> show failure)
            Right workspace ->
                assertFailure
                    ("late import was accepted: " <> show workspace)

commitsRecognizedFormalEnvironmentDuringParsing :: Assertion
commitsRecognizedFormalEnvironmentDuringParsing =
    withTemporaryDirectory "felix-source-committed-formal" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            "\\begin{axiom}\\label{}"
        graph <- buildSearchedGraph temp "entry.tex"
        result <- Parse.parseResolvedSourceGraph graph
        case result of
            Left
                (Parse.SourceParseError
                    source
                    (Parse.TokenError failure)) -> do
                        assertEqual
                            "committed-formal source"
                            "entry.tex"
                            (safeRelativePathFilePath
                                (resolvedSourceRelativePath source))
                        assertBool
                            "committed-formal location"
                            ("1:21" `List.isInfixOf` failure)
                        assertBool
                            "committed-formal diagnostic"
                            ("unexpected input \"}\""
                                `List.isInfixOf` failure)
            Left failure ->
                assertFailure
                    ("expected committed formal token failure, got "
                        <> show failure)
            Right workspace ->
                assertFailure
                    ("malformed committed formal environment was accepted: "
                        <> show workspace)

ordersSiblingImports :: Assertion
ordersSiblingImports =
    withTemporaryDirectory "felix-source-sibling-order" \temp -> do
        writeTheory (temp Posix.</> "a.tex") [] "a"
        writeTheory (temp Posix.</> "b.tex") [] "b"
        writeTheory
            (temp Posix.</> "entry.tex")
            ["a.tex", "b.tex"]
            "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        order <- sourceGraphOrderPaths graph
        assertEqual "DFS completion order"
            ["a.tex", "b.tex", "entry.tex"]
            order

ordersSharedDependencies :: Assertion
ordersSharedDependencies =
    withTemporaryDirectory "felix-source-shared-order" \temp -> do
        writeTheory (temp Posix.</> "shared.tex") [] "shared"
        writeTheory (temp Posix.</> "a.tex") ["shared.tex"] "a"
        writeTheory (temp Posix.</> "b.tex") ["shared.tex"] "b"
        writeTheory
            (temp Posix.</> "entry.tex")
            ["a.tex", "b.tex"]
            "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        order <- sourceGraphOrderPaths graph
        assertEqual "shared dependency occurs once before both importers"
            ["shared.tex", "a.tex", "b.tex", "entry.tex"]
            order

retainsRepeatedImports :: Assertion
retainsRepeatedImports =
    withTemporaryDirectory "felix-source-repeated-import" \temp -> do
        writeTheory (temp Posix.</> "shared.tex") [] "shared"
        writeTheory
            (temp Posix.</> "entry.tex")
            ["shared.tex", "shared.tex"]
            "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        assertEqual "canonical node count" 2 (length (sourceGraphNodes graph))
        assertEqual "repeated edge count" 2 (length (sourceGraphImportEdges graph))

deduplicatesCanonicalNodes :: Assertion
deduplicatesCanonicalNodes =
    withTemporaryDirectory "felix-source-canonical-dedup" \temp -> do
        let shared = temp Posix.</> "shared.tex"
            alias = temp Posix.</> "alias.tex"
        writeTheory shared [] "shared"
        Directory.createFileLink shared alias
        writeTheory
            (temp Posix.</> "entry.tex")
            ["shared.tex", "alias.tex"]
            "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        assertEqual "one node for symlink aliases" 2 (length (sourceGraphNodes graph))
        case sourceGraphImportEdges graph of
            [firstEdge, secondEdge] ->
                assertEqual
                    "both occurrences reach one node"
                    (sourceImportedNode firstEdge)
                    (sourceImportedNode secondEdge)
            edges ->
                assertFailure ("expected two import edges, got " <> show edges)

reportsMissingImports :: Assertion
reportsMissingImports =
    withTemporaryDirectory "felix-source-missing-import" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "% heading"
                , "\\import{missing.tex}"
                , theoryBlock "entry"
                ])
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        result <- buildResolvedSourceGraph mounts request
        case result of
            Left (SourceNotFound (ImportedSourceLookup _ reference) _candidates) -> do
                assertEqual "missing import line" 2 (locLine (importLocation reference))
                assertEqual "missing import source" "entry.tex"
                    (locFile (importLocation reference))
            Left err ->
                assertFailure ("expected located SourceNotFound, got " <> show err)
            Right graph ->
                assertFailure ("expected missing-import rejection, got " <> show graph)

rejectsUnsafeImports :: Assertion
rejectsUnsafeImports =
    withTemporaryDirectory "felix-source-unsafe-import" \temp -> do
        writeTheory (temp Posix.</> "entry.tex") ["./shared.tex"] "entry"
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        result <- buildResolvedSourceGraph mounts request
        case result of
            Left (InvalidImportPath _source location raw CurrentDirectoryComponent) -> do
                assertEqual "raw import" "./shared.tex" raw
                assertEqual "unsafe import line" 1 (locLine location)
                assertEqual "unsafe import source" "entry.tex" (locFile location)
            Left err ->
                assertFailure ("expected InvalidImportPath, got " <> show err)
            Right graph ->
                assertFailure ("expected unsafe-import rejection, got " <> show graph)

reportsImportCycles :: Assertion
reportsImportCycles =
    withTemporaryDirectory "felix-source-cycle" \temp -> do
        writeTheory (temp Posix.</> "a.tex") ["b.tex"] "a"
        writeTheory (temp Posix.</> "b.tex") ["a.tex"] "b"
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "a.tex")
        result <- buildResolvedSourceGraph mounts request
        case result of
            Left (SourceImportCycle steps) -> do
                assertEqual "cycle length" 2 (length steps)
                assertEqual
                    "cycle importer sequence"
                    ["a.tex", "b.tex"]
                    [ safeRelativePathFilePath
                        (resolvedSourceRelativePath (cycleImporter step))
                    | step <- toList steps
                    ]
                assertEqual
                    "cycle import locations"
                    ["a.tex", "b.tex"]
                    [ locFile (importLocation (cycleImport step))
                    | step <- toList steps
                    ]
            Left err ->
                assertFailure ("expected SourceImportCycle, got " <> show err)
            Right graph ->
                assertFailure ("expected cycle rejection, got " <> show graph)

rejectsMalformedImportedSource :: Assertion
rejectsMalformedImportedSource =
    withTemporaryDirectory "felix-source-import-utf8" \temp -> do
        writeTheory (temp Posix.</> "entry.tex") ["bad.tex"] "entry"
        ByteString.writeFile
            (temp Posix.</> "bad.tex")
            (ByteString.pack [0x61, 0xFF])
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        result <- buildResolvedSourceGraph mounts request
        case result of
            Left (SourceDecodeError source offset) -> do
                assertEqual "bad source" "bad.tex"
                    (safeRelativePathFilePath (resolvedSourceRelativePath source))
                assertEqual "bad byte offset" 1 offset
            Left err ->
                assertFailure ("expected SourceDecodeError, got " <> show err)
            Right graph ->
                assertFailure ("expected malformed-source rejection, got " <> show graph)

buildsEmptyModules :: Assertion
buildsEmptyModules =
    withTemporaryDirectory "felix-source-empty" \temp ->
        forM_
            [ ("empty.tex", "")
            , ("comments.tex", "% heading\n% body")
            ]
            \(relative, contents) -> do
                writeFile (temp Posix.</> relative) contents
                graph <- buildSearchedGraph temp relative
                assertEqual
                    "one ordinary graph node"
                    1
                    (length (sourceGraphNodes graph))
                workspace <-
                    expectRight
                        =<< Parse.parseResolvedSourceGraph graph
                assertParsedProvenance (ParsedModule.parsedWorkspaceRootModule workspace)
                assertEqual
                    "empty parsed projection"
                    []
                    (ParsedModule.importedBeforeImporterBlocks workspace)
                assertBool
                    "empty syntax declarations"
                    (null
                        (Interface.canonicalSyntaxDeltaEntries
                            (Interface.moduleSyntaxLocalDelta
                                (ParsedModule.parsedModuleSyntaxInterface
                                    (ParsedModule.parsedWorkspaceRootModule
                                        workspace)))))

identifiesOwnerIndependentParsedModules :: Assertion
identifiesOwnerIndependentParsedModules =
    withTemporaryDirectory "felix-parsed-identity" \temp -> do
        let firstRoot = temp Posix.</> "first"
            secondRoot = temp Posix.</> "second"
            bytes = axiomBlock "same" "x = x"
        Directory.createDirectory firstRoot
        Directory.createDirectory secondRoot
        writeFile (firstRoot Posix.</> "entry.tex") bytes
        writeFile (secondRoot Posix.</> "entry.tex") bytes
        firstWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph firstRoot "entry.tex"
        secondWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph secondRoot "entry.tex"
        let first = ParsedModule.parsedWorkspaceRootModule firstWorkspace
            second = ParsedModule.parsedWorkspaceRootModule secondWorkspace
        assertBool
            "logical owners remain distinct"
            ( Module.moduleName (ParsedModule.parsedModuleAddress first)
                /= Module.moduleName (ParsedModule.parsedModuleAddress second)
            )
        assertEqual
            "equal bytes retain one content identity"
            (ParsedModule.parsedModuleSourceContentId first)
            (ParsedModule.parsedModuleSourceContentId second)
        assertEqual
            "physical source registration is outside parsed identity"
            (ParsedModule.parsedModuleId first)
            (ParsedModule.parsedModuleId second)
        assertEqual
            "canonical payload is owner-independent"
            (ParsedModule.parsedModulePayload first)
            (ParsedModule.parsedModulePayload second)
        let payload = ParsedModule.parsedModulePayload first
        assertEqual
            "canonical parsed payload cache round trip"
            (Right payload)
            (Cache.decodeCache
                Parsed.getCanonicalParsedPayloadCache
                (Cache.encodeCache
                    (Parsed.putCanonicalParsedPayloadCache payload)))
        rebound <- expectRight
            (Parsed.decodeParsedArtefact
                anonymousSourceDescriptor
                (ParsedModule.parsedModuleArtefact first))
        case Parsed.decodedParsedBlocks rebound of
            Raw.BlockAxiom location _title _marker _axiom : _ ->
                assertEqual
                    "decoded locations bind only to the current live file"
                    (Just anonymousSourceDescriptor)
                    (locSourceDescriptor location)
            blocks ->
                assertFailure
                    ("expected decoded axiom, got " <> show blocks)
        writeFile
            (secondRoot Posix.</> "entry.tex")
            (bytes <> "% content identity change\n")
        changedWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph secondRoot "entry.tex"
        assertBool
            "exact source changes parsed identity"
            ( ParsedModule.parsedModuleId first
                /= ParsedModule.parsedModuleId
                    (ParsedModule.parsedWorkspaceRootModule changedWorkspace)
            )

detectsParsedPayloadLayoutChanges :: Assertion
detectsParsedPayloadLayoutChanges = do
    workspace <- expectRight
        =<< Parse.parseResolvedSourceGraph
        =<< buildSearchedGraph "." "test/examples/proofdefinefunction.tex"
    let payload =
            ParsedModule.parsedModulePayload
                (ParsedModule.parsedWorkspaceRootModule workspace)
        digest =
            Cache.hashCacheFields
                "felix-representative-parsed-payload-v1"
                [Parsed.canonicalParsedPayloadBytes payload]
    assertEqual
        "representative parsed payload digest"
        "b0c63c4d826ff3f955361cadbea3b58b279dabeadfb79f7b248b5f8f16242e6a"
        (lowerHexText (Cache.cacheDigestBytes digest))

checksParsedVerbSurfaceCache :: Assertion
checksParsedVerbSurfaceCache = do
    let singular = Raw.patternFromHoley
            [Just (Raw.Word "covers"), Nothing]
        base = Raw.patternFromHoley
            [Just (Raw.Word "cover"), Nothing]
        mismatchedBase = Raw.patternFromHoley
            [Just (Raw.Word "cover"), Just (Raw.Word "everything")]
        encodePair second = Cache.encodeCache do
            Interface.putPatternCache singular
            Interface.putPatternCache second
    valid <- case Cache.decodeCache
            Parsed.getParsedVerbSurfacesCache
            (encodePair base) of
        Left failure ->
            assertFailure ("valid parsed verb surfaces failed: " <> show failure)
                >> fail "unreachable"
        Right surfaces -> pure surfaces
    assertEqual "parsed singular surface"
        (Raw.patternToHoley singular)
        (Raw.verbSurfaceSingular valid)
    assertEqual "parsed base surface"
        (Raw.patternToHoley base)
        (Raw.verbSurfaceBase valid)
    case Cache.decodeCache
            Parsed.getParsedVerbSurfacesCache
            (encodePair mismatchedBase) of
        Left{} -> pure ()
        Right surfaces ->
            assertFailure
                ("accepted malformed parsed verb surfaces: " <> show surfaces)

checksParsedModuleSourceBindings :: Assertion
checksParsedModuleSourceBindings =
    withTemporaryDirectory "felix-parsed-source-binding" \temp -> do
        let firstRoot = temp Posix.</> "first"
            secondRoot = temp Posix.</> "second"
        Directory.createDirectory firstRoot
        Directory.createDirectory secondRoot
        writeFile
            (firstRoot Posix.</> "entry.tex")
            (axiomBlock "first" "x = x")
        writeFile
            (secondRoot Posix.</> "entry.tex")
            (axiomBlock "second" "y = y")
        firstWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph firstRoot "entry.tex"
        secondWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph secondRoot "entry.tex"
        let first = ParsedModule.parsedWorkspaceRootModule firstWorkspace
            second = ParsedModule.parsedWorkspaceRootModule secondWorkspace
            firstSource =
                ParsedModule.parsedModuleIdentifiedSource first
        rebound <- expectRight
            (ParsedModule.bindParsedModule
                firstSource
                (ParsedModule.parsedModuleImports first)
                (ParsedModule.parsedModuleIdentified first))
        assertEqual
            "valid binding preserves parsed identity"
            (ParsedModule.parsedModuleId first)
            (ParsedModule.parsedModuleId rebound)
        failure <-
            case ParsedModule.bindParsedModule
                    firstSource
                    (ParsedModule.parsedModuleImports second)
                    (ParsedModule.parsedModuleIdentified second) of
                Left mismatch -> pure mismatch
                Right _bound ->
                    assertFailure
                        "expected distinct source content to reject binding"
        assertEqual
            "binding renderer is the Show representation"
            (Text.unpack
                (ParsedModule.renderParsedModuleSourceBindingError failure))
            (show failure)
        let source = ParsedModule.parsedModuleResolved first
            freshFailure =
                Verification.VerificationWorkspaceError
                    (Parse.SourceParsedModuleBindingInvariant source failure)
            cachedFailure =
                Verification.VerificationParsedArtefactIntegrityError
                    source
                    (Parse.ParsedArtefactSourceBindingMismatch failure)
            ordinarySourceFailure =
                Verification.VerificationWorkspaceError
                    (Parse.SourceParseError source Parse.EmptyParse)
            graphScannerFailure =
                Verification.VerificationWorkspaceError
                    (Parse.SourceWorkspaceError
                        (SourceGraphScanningInvariantViolation
                            source
                            "scanner invariant"))
        assertEqual
            "fresh binding mismatch is an infrastructure failure"
            Verification.VerificationInfrastructureFailure
            (Verification.verificationDriverErrorKind freshFailure)
        assertEqual
            "cached binding mismatch remains an integrity failure"
            Verification.VerificationInfrastructureFailure
            (Verification.verificationDriverErrorKind cachedFailure)
        assertEqual
            "ordinary parse rejection remains a source failure"
            Verification.VerificationSourceFailure
            (Verification.verificationDriverErrorKind ordinarySourceFailure)
        assertEqual
            "source graph scanner invariant is an infrastructure failure"
            Verification.VerificationInfrastructureFailure
            (Verification.verificationDriverErrorKind graphScannerFailure)

-- These assertions compare the live syntax, canonical projection, and key
-- independently of the module's stored identity fields.
assertParsedProvenance :: ParsedModule.ParsedModule -> Assertion
assertParsedProvenance parsed = do
    let syntax = ParsedModule.parsedModuleSyntaxInterface parsed
        payload = ParsedModule.parsedModulePayload parsed
        key = ParsedModule.parsedModuleKey parsed
    expectedKey <- expectRight
        (ParsedIdentity.parsedModuleKey
            (ParsedModule.parsedModuleSourceContentId parsed)
            (Interface.moduleSyntaxBase syntax)
            (Interface.moduleSyntaxDirectInputs syntax))
    assertEqual "key belongs to source and syntax context" expectedKey key
    assertEqual "payload encodes the live syntax" payload
        (Parsed.canonicalParsedPayload
            (ParsedModule.parsedImportReference <$> ParsedModule.parsedModuleImports parsed)
            (ParsedModule.parsedModuleBlocks parsed)
            (ParsedModule.parsedModuleSyntaxOccurrences parsed)
            (Interface.moduleSyntaxAssertedId syntax))
    assertEqual "identity belongs to the retained key and bytes"
        (ParsedIdentity.parsedModuleId key (Parsed.canonicalParsedPayloadBytes payload))
        (ParsedModule.parsedModuleId parsed)

checksParsedArtefactContexts :: Assertion
checksParsedArtefactContexts =
    withTemporaryDirectory "felix-parsed-context" $ \temp -> do
        let text = builtinZeroDefinition "source_zero"
        writeFile (temp Posix.</> "entry.tex") text
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph temp "entry.tex"
        let parsed = ParsedModule.parsedWorkspaceRootModule workspace
            source = ParsedModule.parsedModuleIdentifiedSource parsed
            content = ParsedModule.parsedModuleSourceContentId parsed
            syntax = ParsedModule.parsedModuleSyntaxInterface parsed
            artefact = ParsedModule.parsedModuleArtefact parsed
            descriptor = ParsedModule.parsedModuleSourceDescriptor parsed
        assertParsedProvenance parsed
        decoded <- expectRight (Parsed.decodeParsedArtefact descriptor artefact)
        admitted <- expectRight (ParsedModule.admitParsedModule content syntax decoded)
        bound <- expectRight (ParsedModule.bindParsedModule source [] admitted)
        assertEqual "reentry preserves exact artifact" artefact
            (ParsedModule.parsedModuleArtefact bound)
        assertEqual "reentry preserves blocks" (ParsedModule.parsedModuleBlocks parsed)
            (ParsedModule.parsedModuleBlocks bound)
        assertParsedProvenance bound
        emptyDelta <- expectRight (Interface.canonicalSyntaxDelta [])
        differentDelta <- expectRight
            (Interface.canonicalSyntaxDelta [Interface.CanonicalStructureOperation "other"])
        differentSyntax <- expectRight (Interface.moduleSyntaxInterface [] differentDelta)
        directSyntax <- expectRight
            (Interface.moduleSyntaxInterface [Interface.moduleSyntaxAssertedId syntax] emptyDelta)
        forM_
            [ (Content.sourceContentIdBytes "different source", syntax)
            , (content, directSyntax)
            ] $ \(otherContent, otherSyntax) ->
                case ParsedModule.admitParsedModule otherContent otherSyntax decoded of
                    Left ParsedModule.ParsedModuleContextKeyMismatch{} -> pure ()
                    other -> assertFailure ("expected context-key mismatch, got " <> show other)
        case ParsedModule.admitParsedModule content differentSyntax decoded of
            Left (ParsedModule.ParsedModuleSyntaxIdMismatch expected stored) -> do
                assertEqual "expected syntax is inspectable"
                    (Interface.moduleSyntaxAssertedId differentSyntax) expected
                assertEqual "stored syntax is inspectable"
                    (Interface.moduleSyntaxAssertedId syntax) stored
            other -> assertFailure ("expected syntax-ID mismatch, got " <> show other)
        let owner = Module.moduleName (ParsedModule.parsedModuleAddress parsed)
            reserved = Parse.reservedSourceFromText owner "entry.tex" (Text.pack text)
        (_input, reservedParsed) <- expectRight
            (Parse.parseReservedFreshModule reserved descriptor)
        assertEqual "reserved and physical producers retain one artifact" artefact
            (ParsedModule.identifiedParsedModuleArtefact reservedParsed)
        assertEqual "reserved and physical producers retain the same syntax"
            (ParsedModule.parsedModuleBlocks parsed)
            (ParsedModule.identifiedParsedModuleBlocks reservedParsed)

checksParsedImportBindings :: Assertion
checksParsedImportBindings =
    withTemporaryDirectory "felix-parsed-import-binding" $ \temp -> do
        writeTheory (temp Posix.</> "entry.tex") ["first.tex", "second.tex"] "entry"
        writeFile (temp Posix.</> "first.tex") ""
        writeFile (temp Posix.</> "second.tex") ""
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph temp "entry.tex"
        let parsed = ParsedModule.parsedWorkspaceRootModule workspace
            imports = ParsedModule.parsedModuleImports parsed
            references = ParsedModule.parsedImportReference <$> imports
        assertEqual "fixture contains ordered imports" 2 (length imports)
        assertParsedProvenance parsed
        forM_ [reverse imports, drop 1 imports] $ \otherImports ->
            case ParsedModule.bindParsedModule
                    (ParsedModule.parsedModuleIdentifiedSource parsed)
                    otherImports
                    (ParsedModule.parsedModuleIdentified parsed) of
                Left (ParsedModule.ParsedModuleImportMismatch expected stored) -> do
                    assertEqual "binding reports current graph references"
                        (ParsedModule.parsedImportReference <$> otherImports) expected
                    assertEqual "binding reports encoded references" references stored
                other -> assertFailure ("expected import mismatch, got " <> show other)

keysEffectiveDirectSyntaxInputs :: Assertion
keysEffectiveDirectSyntaxInputs =
    withTemporaryDirectory "felix-parsed-syntax-input" \temp -> do
        let firstRoot = temp Posix.</> "first"
            secondRoot = temp Posix.</> "second"
            rootBytes = "\\import{notation.tex}\n"
        Directory.createDirectory firstRoot
        Directory.createDirectory secondRoot
        writeFile (firstRoot Posix.</> "entry.tex") rootBytes
        writeFile (secondRoot Posix.</> "entry.tex") rootBytes
        writeFile
            (firstRoot Posix.</> "notation.tex")
            (syntaxFunctionDefinition
                "first_notation"
                "firstop"
                (Just "%! infixl 1"))
        writeFile
            (secondRoot Posix.</> "notation.tex")
            (syntaxFunctionDefinition
                "second_notation"
                "secondop"
                (Just "%! infixl 1"))
        firstWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph firstRoot "entry.tex"
        secondWorkspace <- expectRight
            =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph secondRoot "entry.tex"
        let first = ParsedModule.parsedWorkspaceRootModule firstWorkspace
            second = ParsedModule.parsedWorkspaceRootModule secondWorkspace
        assertEqual
            "root source bytes are unchanged"
            (ParsedModule.parsedModuleSourceContentId first)
            (ParsedModule.parsedModuleSourceContentId second)
        assertBool
            "effective syntax changes the parsed key"
            (ParsedModule.parsedModuleKey first /= ParsedModule.parsedModuleKey second)
        assertBool
            "effective syntax changes parsed identity"
            (ParsedModule.parsedModuleId first /= ParsedModule.parsedModuleId second)

reusesExactParsedSyntax :: Assertion
reusesExactParsedSyntax =
    withTemporaryDirectory "felix-parsed-warm" \temp -> do
        let datatype = unlines
                [ "\\begin{datatype}\\label{multi_item}"
                , "  Define $\\itemkind$ inductively as follows."
                , "  \\begin{enumerate}"
                , "    \\item $\\itemzero \\in \\itemkind$."
                , "    \\item $\\itemsucc{x} \\in \\itemkind$ for $x \\in \\itemkind$."
                , "  \\end{enumerate}"
                , "\\end{datatype}"
                ]
        writeFile
            (temp Posix.</> "entry.tex")
            (builtinZeroDefinition "source_zero" <> datatype)
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        foundation <- expectRight Foundation.checkedFoundation
        store <- openTestStore
            (temp Posix.</> "store.sqlite")
            (Identity.theoryId foundation)
        cold <- expectParseExecution
            =<< Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
                store mounts request (const [])
        warm <- expectParseExecution
            =<< Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
                store mounts request (const [])
        let coldRoot = ParsedModule.parsedWorkspaceRootModule cold
            warmRoot = ParsedModule.parsedWorkspaceRootModule warm
        assertParsedProvenance coldRoot
        assertParsedProvenance warmRoot
        let expectedChunkCount =
                length (ParsedModule.parsedModuleBlocks warmRoot)
        assertBool "fixture has source chunks" (expectedChunkCount > 0)
        assertEqual "warm blocks" (ParsedModule.parsedModuleBlocks coldRoot)
            (ParsedModule.parsedModuleBlocks warmRoot)
        assertEqual "warm occurrences"
            (ParsedModule.parsedModuleSyntaxOccurrences coldRoot)
            (ParsedModule.parsedModuleSyntaxOccurrences warmRoot)
        assertEqual "warm syntax interface"
            (ParsedModule.parsedModuleSyntaxInterface coldRoot)
            (ParsedModule.parsedModuleSyntaxInterface warmRoot)
        assertEqual "warm parsed identity"
            (ParsedModule.parsedModuleId coldRoot)
            (ParsedModule.parsedModuleId warmRoot)
        case ParsedModule.parsedModuleSyntaxOccurrences warmRoot of
            first : second : third : fourth : [] -> do
                assertEqual "fixed source marker" "source_zero"
                    (ParsedModule.parsedSyntaxOccurrenceMarker first)
                case ParsedModule.parsedSyntaxOccurrenceEntry first of
                    Interface.CanonicalExpressionFunction
                            _pattern marker _fixity ->
                        assertEqual "fixed authoritative marker" "zero" marker
                    entry ->
                        assertFailure
                            ("unexpected fixed cached entry: " <> show entry)
                assertEqual "multi-item block order" [1, 1, 1]
                    (ParsedModule.parsedSyntaxOccurrenceBlockIndex
                        <$> [second, third, fourth])
                assertEqual "multi-item extraction order"
                    ["multi_item", "itemzero", "itemsucc"]
                    (ParsedModule.parsedSyntaxOccurrenceMarker
                        <$> [second, third, fourth])
                case drop 1 (ParsedModule.parsedModuleBlocks warmRoot) of
                    block : _ ->
                        case block of
                            Raw.BlockData _location _title marker _datatype ->
                                assertEqual "cached declaration-head anchor"
                                    marker
                                    (ParsedModule.parsedSyntaxOccurrenceMarker second)
                            other ->
                                assertFailure
                                    ("expected cached datatype block, got "
                                        <> show other)
                    [] ->
                        assertFailure "cached datatype block is absent"
            occurrences ->
                assertFailure
                    ("unexpected cached syntax occurrences: "
                        <> show occurrences)
        Store.closeStore store

invalidatesExactParsedInputs :: Assertion
invalidatesExactParsedInputs =
    withTemporaryDirectory "felix-parsed-invalidation" \temp -> do
        let notationPath = temp Posix.</> "notation.tex"
            entryPath = temp Posix.</> "entry.tex"
            notation associativity level =
                syntaxFunctionDefinition
                    "join"
                    "join"
                    (Just
                        ("%! " <> associativity <> " " <> show level))
            entry suffix =
                "\\import{notation.tex}\n"
                    <> axiomBlock
                        "imported_syntax_use"
                        "a\\join b\\join c = a"
                    <> suffix
        writeFile notationPath (notation "infixl" (1 :: Int))
        writeFile entryPath (entry "")
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        foundation <- expectRight Foundation.checkedFoundation
        store <- openTestStore
            (temp Posix.</> "store.sqlite")
            (Identity.theoryId foundation)
        let parse =
                expectParseExecution
                    =<< Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
                        store mounts request (const [])
        coldWorkspace <- parse
        warmWorkspace <- parse
        coldNotation <- findParsedModule "notation.tex" coldWorkspace
        warmNotation <- findParsedModule "notation.tex" warmWorkspace
        let coldRoot = ParsedModule.parsedWorkspaceRootModule coldWorkspace
            warmRoot = ParsedModule.parsedWorkspaceRootModule warmWorkspace
        assertEqual "unchanged import identity"
            (ParsedModule.parsedModuleId coldNotation)
            (ParsedModule.parsedModuleId warmNotation)
        assertEqual "unchanged importer identity"
            (ParsedModule.parsedModuleId coldRoot)
            (ParsedModule.parsedModuleId warmRoot)

        writeFile entryPath (entry "% formatting-only edit\n")
        editedWorkspace <- parse
        editedNotation <- findParsedModule "notation.tex" editedWorkspace
        let editedRoot = ParsedModule.parsedWorkspaceRootModule editedWorkspace
        assertEqual "cached import retains identity"
            (ParsedModule.parsedModuleId warmNotation)
            (ParsedModule.parsedModuleId editedNotation)
        assertBool "exact source edit changes importer key"
            (ParsedModule.parsedModuleKey warmRoot
                /= ParsedModule.parsedModuleKey editedRoot)
        assertEqual "formatting retains parsed projection"
            (ParsedModule.parsedModulePayload warmRoot)
            (ParsedModule.parsedModulePayload editedRoot)

        writeFile notationPath (notation "infixr" (2 :: Int))
        syntaxWorkspace <- parse
        syntaxNotation <- findParsedModule "notation.tex" syntaxWorkspace
        let syntaxRoot = ParsedModule.parsedWorkspaceRootModule syntaxWorkspace
        assertBool "local syntax identity changes"
            ( Interface.moduleSyntaxAssertedId
                (ParsedModule.parsedModuleSyntaxInterface editedNotation)
                /= Interface.moduleSyntaxAssertedId
                    (ParsedModule.parsedModuleSyntaxInterface syntaxNotation)
            )
        assertEqual "importer source is unchanged"
            (ParsedModule.parsedModuleSourceContentId editedRoot)
            (ParsedModule.parsedModuleSourceContentId syntaxRoot)
        assertBool "direct syntax invalidates importer key"
            (ParsedModule.parsedModuleKey editedRoot
                /= ParsedModule.parsedModuleKey syntaxRoot)
        Store.closeStore store

rebindsRelocatedParsedArtefacts :: Assertion
rebindsRelocatedParsedArtefacts =
    withTemporaryDirectory "felix-parsed-relocation" \temp -> do
        let firstRoot = temp Posix.</> "first"
            secondRoot = temp Posix.</> "second"
            sourceBytes = axiomBlock "same" "x = x"
        Directory.createDirectory firstRoot
        Directory.createDirectory secondRoot
        writeFile (firstRoot Posix.</> "entry.tex") sourceBytes
        writeFile (secondRoot Posix.</> "entry.tex") sourceBytes
        firstMounts <- oneMount "first" firstRoot
        secondMounts <- oneMount "second" secondRoot
        request <- expectRight (searchedRoot "entry.tex")
        foundation <- expectRight Foundation.checkedFoundation
        let theory = Identity.theoryId foundation
        store <- openTestStore (temp Posix.</> "store.sqlite") theory
        firstWorkspace <- expectParseExecution
            =<< Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
                store firstMounts request (const [])
        secondWorkspace <- expectParseExecution
            =<< Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
                store secondMounts request (const [])
        let first = ParsedModule.parsedWorkspaceRootModule firstWorkspace
            second = ParsedModule.parsedWorkspaceRootModule secondWorkspace
            firstSource = ParsedModule.parsedModuleResolved first
            secondSource = ParsedModule.parsedModuleResolved second
        assertEqual "relocation retains parsed identity"
            (ParsedModule.parsedModuleId first)
            (ParsedModule.parsedModuleId second)
        assertEqual "relocation retains canonical payload"
            (ParsedModule.parsedModulePayload first)
            (ParsedModule.parsedModulePayload second)
        assertBool "relocation rebinds the physical source"
            (resolvedSourceCanonicalPath firstSource
                /= resolvedSourceCanonicalPath secondSource)
        assertBool "relocation rebinds the logical owner"
            (ParsedModule.parsedModuleAddress first
                /= ParsedModule.parsedModuleAddress second)
        firstSourceDescriptor <- expectJust "first location file id"
            (locSourceDescriptor (onlyAxiomLocation first))
        secondSourceDescriptor <- expectJust "second location file id"
            (locSourceDescriptor (onlyAxiomLocation second))
        assertBool "relocation rebinds locations"
            (firstSourceDescriptor /= secondSourceDescriptor)
        firstArtefactKey <- expectRight
            (Semantic.moduleArtefactKey
                (Module.moduleName (ParsedModule.parsedModuleAddress first))
                (ParsedModule.parsedModuleId first)
                []
                theory)
        secondArtefactKey <- expectRight
            (Semantic.moduleArtefactKey
                (Module.moduleName (ParsedModule.parsedModuleAddress second))
                (ParsedModule.parsedModuleId second)
                []
                theory)
        assertBool "module artefact remains owner-dependent"
            (Semantic.moduleArtefactId firstArtefactKey
                /= Semantic.moduleArtefactId secondArtefactKey)
        Store.closeStore store

rejectsCorruptedCachedDeclarationAnchor :: Assertion
rejectsCorruptedCachedDeclarationAnchor =
    withTemporaryDirectory "felix-parsed-corrupt-anchor" \temp -> do
        writeBuiltinZeroDefinition
            (temp Posix.</> "entry.tex")
            "source_zero"
        mounts <- oneMount "project" temp
        request <- expectRight (searchedRoot "entry.tex")
        foundation <- expectRight Foundation.checkedFoundation
        let storePath = temp Posix.</> "store.sqlite"
            theory = Identity.theoryId foundation
        store <- openTestStore storePath theory
        cold <- expectParseExecution
            =<< Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
                store mounts request (const [])
        let parsed = ParsedModule.parsedWorkspaceRootModule cold
            key = ParsedModule.parsedModuleKey parsed
        descriptor <- case ParsedModule.parsedModuleSyntaxOccurrences parsed of
            occurrence : _ ->
                expectJust
                    "parsed occurrence file id"
                    (locSourceDescriptor
                        (ParsedModule.parsedSyntaxOccurrenceLocation occurrence))
            [] ->
                assertFailure "parsed fixed occurrence is absent"
                    >> fail "unreachable"
        decoded <- expectRight
            (Parsed.decodeParsedArtefact
                descriptor
                (ParsedModule.parsedModuleArtefact parsed))
        Store.closeStore store
        let corruptedOccurrences = case Parsed.decodedParsedOccurrences decoded of
                occurrence : rest ->
                    Parsed.parsedSyntaxOccurrence
                        (Parsed.parsedSyntaxOccurrenceBlockIndex occurrence)
                        (Parsed.parsedSyntaxOccurrenceLocation occurrence)
                        "corrupted_anchor"
                        (Parsed.parsedSyntaxOccurrenceEntry occurrence) : rest
                [] ->
                    []
            corruptedPayload =
                Parsed.canonicalParsedPayload
                    (Parsed.decodedParsedImports decoded)
                    (Parsed.decodedParsedBlocks decoded)
                    corruptedOccurrences
                    (Parsed.decodedParsedSyntaxInterface decoded)
            corruptedId =
                ParsedIdentity.parsedModuleId
                    key
                    (Parsed.canonicalParsedPayloadBytes corruptedPayload)
        connection <- SQLite.open storePath
        SQLite.execute connection
            "UPDATE parsed_artefacts \
            \SET parsed_module_id = ?, payload = ? \
            \WHERE parsed_module_key = ?"
            ( Cache.cacheDigestBytes
                (ParsedIdentity.parsedModuleIdDigest corruptedId)
            , Parsed.canonicalParsedPayloadBytes corruptedPayload
            , Cache.cacheDigestBytes
                (ParsedIdentity.parsedModuleKeyDigest key)
            )
        SQLite.close connection
        current <- openTestStore storePath theory
        Parse.parseSourceWorkspaceWithStoreAndSyntaxInputs
            current mounts request (const []) >>= \case
                Left
                    (Parse.ParseExecutionArtefactIntegrityFailure
                        _source
                        (Parse.ParsedArtefactAssociationFailure
                            Parse.SyntaxOccurrenceMarkerMismatch{})) ->
                            pure ()
                other ->
                    assertFailure
                        ("unexpected corrupted parsed result: " <> show other)
        Store.closeStore current

openTestStore :: FilePath -> Identity.TheoryId -> IO Store.Store
openTestStore path theory =
    Store.openStore path theory >>= \case
        Left failure ->
            assertFailure (show failure) >> fail "unreachable"
        Right (_startup, store) ->
            pure store

expectParseExecution
    :: Either Parse.ParseExecutionError value
    -> IO value
expectParseExecution = \case
    Left failure ->
        assertFailure (show failure) >> fail "unreachable"
    Right value ->
        pure value

parsesSourceGraph :: Assertion
parsesSourceGraph =
    withTemporaryDirectory "felix-source-parse" \temp -> do
        writeTheory (temp Posix.</> "shared.tex") [] "shared"
        writeTheory (temp Posix.</> "entry.tex") ["shared.tex"] "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
        assertEqual "two parsed source nodes" 2
            (length (ParsedModule.parsedWorkspaceModules workspace))
        assertEqual "one source-local block per node" [1, 1]
            (toList
                (length . ParsedModule.parsedModuleBlocks
                    <$> ParsedModule.parsedWorkspaceImportedBeforeImporter workspace))
        assertEqual "imported-before-importer source order"
            ["shared.tex", "entry.tex"]
            (toList
                (safeRelativePathFilePath
                    . resolvedSourceRelativePath
                    . ParsedModule.parsedModuleResolved
                    <$> ParsedModule.parsedWorkspaceImportedBeforeImporter workspace))
        assertEqual "flattened block view" 2
            (length (ParsedModule.importedBeforeImporterBlocks workspace))

rejectsSiblingSyntaxLeakage :: Assertion
rejectsSiblingSyntaxLeakage =
    withTemporaryDirectory "felix-source-syntax-world" \temp -> do
        writeFile
            (temp Posix.</> "use.tex")
            (unlines
                [ "\\begin{axiom}\\label{use}"
                , "  $x$ is special."
                , "\\end{axiom}"
                ])
        writeAdjectiveDefinition
            (temp Posix.</> "declare.tex")
            "shared_special"
        writeTheory
            (temp Posix.</> "entry.tex")
            ["use.tex", "declare.tex"]
            "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        result <- Parse.parseResolvedSourceGraph graph
        case result of
            Left (Parse.SourceParseError source _parseError) ->
                assertEqual
                    "syntax consumer fails in its own module"
                    "use.tex"
                    (safeRelativePathFilePath
                        (resolvedSourceRelativePath source))
            Left err ->
                assertFailure
                    ("expected a source-local parse error, got "
                        <> show err)
            Right workspace ->
                assertFailure
                    ("sibling syntax leaked into use.tex: "
                        <> show workspace)

parsesSourceFixities :: Assertion
parsesSourceFixities =
    withTemporaryDirectory "felix-source-fixity" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            ( syntaxFunctionDefinition
                "loose"
                "loose"
                (Just "%! infixl 0")
              <> syntaxFunctionDefinition
                "tight"
                "tight"
                (Just "%! infixr 7")
              <> axiomBlock
                "loose_associativity"
                "a\\loose b\\loose c = a"
              <> axiomBlock
                "tight_associativity"
                "a\\tight b\\tight c = a"
              <> axiomBlock
                "mixed_precedence"
                "a\\loose b\\tight c = a"
              <> axiomBlock
                "parenthesized_precedence"
                "(a\\loose b)\\tight c = a"
            )
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        let root =
                ParsedModule.parsedWorkspaceRootModule workspace
            localEntries =
                Interface.canonicalSyntaxDeltaEntries
                    (Interface.moduleSyntaxLocalDelta
                        (ParsedModule.parsedModuleSyntaxInterface root))
        assertExpressionFixity
            "loose"
            Raw.LeftAssoc
            0
            localEntries
        assertExpressionFixity
            "tight"
            Raw.RightAssoc
            7
            localEntries
        assertEqual
            "source declaration occurrences"
            [0, 1]
            (ParsedModule.parsedSyntaxOccurrenceBlockIndex
                <$> ParsedModule.parsedModuleSyntaxOccurrences root)
        case drop 2 (ParsedModule.parsedModuleBlocks root) of
            [ looseAssociativity
              , tightAssociativity
              , mixedPrecedence
              , parenthesizedPrecedence
              ] -> do
                    assertAxiomLeftShape
                        "left associativity"
                        "loose(loose(a,b),c)"
                        looseAssociativity
                    assertAxiomLeftShape
                        "right associativity"
                        "tight(a,tight(b,c))"
                        tightAssociativity
                    assertAxiomLeftShape
                        "mixed precedence"
                        "loose(a,tight(b,c))"
                        mixedPrecedence
                    assertAxiomLeftShape
                        "parentheses override precedence"
                        "tight(loose(a,b),c)"
                        parenthesizedPrecedence
            blocks ->
                assertFailure
                    ("expected four fixity axioms, got "
                        <> show blocks)

parsesLibraryFixities :: Assertion
parsesLibraryFixities =
    withTemporaryDirectory "felix-source-library-fixity" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            ( syntaxFunctionDefinition
                "cdot"
                "cdot"
                (Just "%! infixl 4")
              <> syntaxFunctionDefinition
                "symdiff"
                "symdiff"
                (Just "%! infixl 1")
              <> axiomBlock
                "cdot_associativity"
                "a\\cdot b\\cdot c = a"
              <> axiomBlock
                "symdiff_associativity"
                "a\\symdiff b\\symdiff c = a"
              <> axiomBlock
                "library_mixed_precedence"
                "a\\symdiff b\\cdot c = a"
              <> axiomBlock
                "library_parentheses"
                "(a\\symdiff b)\\cdot c = a"
            )
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        case drop 2
                (ParsedModule.parsedModuleBlocks
                    (ParsedModule.parsedWorkspaceRootModule workspace)) of
            [ cdotAssociativity
              , symdiffAssociativity
              , mixedPrecedence
              , parenthesizedPrecedence
              ] -> do
                    assertAxiomLeftShape
                        "cdot left associativity"
                        "cdot(cdot(a,b),c)"
                        cdotAssociativity
                    assertAxiomLeftShape
                        "symdiff left associativity"
                        "symdiff(symdiff(a,b),c)"
                        symdiffAssociativity
                    assertAxiomLeftShape
                        "cdot binds tighter than symdiff"
                        "symdiff(a,cdot(b,c))"
                        mixedPrecedence
                    assertAxiomLeftShape
                        "library parentheses override precedence"
                        "cdot(symdiff(a,b),c)"
                        parenthesizedPrecedence
            blocks ->
                assertFailure
                    ("expected four library-fixity axioms, got "
                        <> show blocks)

validatesSourcePragmaAssociations :: Assertion
validatesSourcePragmaAssociations =
    forM_ cases \(description, contents, checkProblem) ->
        withTemporaryDirectory
            ("felix-source-pragma-" <> description)
            \temp -> do
                writeFile
                    (temp Posix.</> "entry.tex")
                    contents
                graph <- buildSearchedGraph temp "entry.tex"
                result <- Parse.parseResolvedSourceGraph graph
                case result of
                    Left
                        (Parse.SourceSyntaxDeclarationError
                            source
                            problem) -> do
                                assertEqual
                                    "pragma source"
                                    "entry.tex"
                                    (safeRelativePathFilePath
                                        (resolvedSourceRelativePath source))
                                checkProblem problem
                    Left err ->
                        assertFailure
                            ("expected source pragma error, got "
                                <> show err)
                    Right workspace ->
                        assertFailure
                            ("expected source pragma rejection, got "
                                <> show workspace)
  where
    cases
        :: [ ( String
             , String
             , Parse.SyntaxDeclarationError -> Assertion
             )
           ]
    cases =
        [ ( "outside"
          , "%! infixl 1\n" <> theoryBlock "outside"
          , \case
                Parse.SyntaxPragmaOutsideDeclaration{} ->
                    pure ()
                problem ->
                    unexpected "outside-declaration pragma" problem
          )
        , ( "inside-nonsyntax"
          , unlines
                [ "\\begin{axiom}\\label{inside_nonsyntax}"
                , "  %! infixl 1"
                , "  $x = x$."
                , "\\end{axiom}"
                ]
          , \case
                Parse.SyntaxPragmaOutsideDeclaration location ->
                    assertEqual
                        "pragma in non-syntax chunk"
                        2
                        (locLine location)
                problem ->
                    unexpected "non-syntax declaration pragma" problem
          )
        , ( "missing"
          , syntaxFunctionDefinition
                "missing"
                "missing"
                Nothing
          , \case
                Parse.MissingSyntaxPragma{} ->
                    pure ()
                problem ->
                    unexpected "missing pragma" problem
          )
        , ( "duplicate"
          , unlines
                [ "\\begin{abbreviation}\\label{duplicate}"
                , "  %! infixl 1"
                , "  %! infixl 1"
                , "  $x\\duplicate y = x$."
                , "\\end{abbreviation}"
                ]
          , \case
                Parse.DuplicateSyntaxPragma{} ->
                    pure ()
                problem ->
                    unexpected "duplicate pragma" problem
          )
        , ( "irrelevant"
          , unlines
                [ "\\begin{definition}\\label{irrelevant}"
                , "  %! infixl 1"
                , "  $x$ is irrelevant iff $x = x$."
                , "\\end{definition}"
                ]
          , \case
                Parse.IrrelevantSyntaxPragma{} ->
                    pure ()
                problem ->
                    unexpected "irrelevant pragma" problem
          )
        , ( "multiple-without-pragma"
          , unlines
                [ "\\begin{datatype}\\label{multiple_patterns}"
                , "  Define $\\patternkind$ inductively as follows."
                , "  \\begin{enumerate}"
                , "    \\item $(x \\firstpattern y) \\in \\patternkind$."
                , "    \\item $(x \\secondpattern y) \\in \\patternkind$."
                , "  \\end{enumerate}"
                , "\\end{datatype}"
                ]
          , \case
                problem@(Parse.MultipleNewSyntaxPatternsWithoutPragma
                        location
                        patterns) -> do
                            assertEqual
                                "first new pattern location"
                                4
                                (locLine location)
                            assertEqual
                                "new pattern count"
                                2
                                (NonEmpty.length patterns)
                            assertBool
                                "accurate multiple-pattern message"
                                ("several new eligible patterns that V1 cannot select between"
                                    `List.isInfixOf` show problem)
                            assertBool
                                "message requires an unambiguous declaration"
                                ("make the declaration unambiguous"
                                    `List.isInfixOf` show problem)
                problem ->
                    unexpected "multiple unannotated patterns" problem
          )
        , ( "fixed"
          , unlines
                [ "\\begin{abbreviation}\\label{local_addition}"
                , "  %! infixl 1"
                , "  $x + y = x$."
                , "\\end{abbreviation}"
                ]
          , \case
                Parse.SyntaxPragmaOnFixedReuse{} ->
                    pure ()
                problem ->
                    unexpected "fixed-base pragma" problem
          )
        ]

    unexpected expected problem =
        assertFailure
            ("expected " <> expected <> ", got " <> show problem)

rejectsFixedBaseCategoryMismatch :: Assertion
rejectsFixedBaseCategoryMismatch =
    withTemporaryDirectory "felix-source-fixed-category" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{definition}\\label{local_add_relation}"
                , "  $x + y$ iff $x = y$."
                , "\\end{definition}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        collision <- expectLexiconCollision
            =<< Parse.parseResolvedSourceGraph graph
        assertEqual
            "fixed collision pattern"
            (Raw.HoleCons
                (Raw.TokenCons
                    (Raw.Symbol "+")
                    (Raw.HoleCons Raw.End)))
            (Parse.lexiconCollisionPattern collision)
        case toList (Parse.lexiconCollisionOrigins collision) of
            [ Parse.FixedLexiconOrigin
                    Interface.CanonicalExpressionFunction{}
              , Parse.SourceLexiconOrigin
                    Interface.CanonicalRelation{}
                    source
                    location
              ] -> do
                    assertEqual
                        "local collision source"
                        "entry.tex"
                        (safeRelativePathFilePath
                            (resolvedSourceRelativePath source))
                    assertLocation
                        "local collision declaration"
                        "entry.tex"
                        1
                        location
            origins ->
                assertFailure
                    ("expected fixed/source category origins, got "
                        <> show origins)

retainsMultiItemSyntaxOccurrences :: Assertion
retainsMultiItemSyntaxOccurrences =
    withTemporaryDirectory "felix-source-multi-item-syntax" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{datatype}\\label{multi_item}"
                , "  Define $\\itemkind$ inductively as follows."
                , "  \\begin{enumerate}"
                , "    \\item $\\itemzero \\in \\itemkind$."
                , "    \\item $\\itemsucc{x} \\in \\itemkind$ for $x \\in \\itemkind$."
                , "  \\end{enumerate}"
                , "\\end{datatype}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        let root =
                ParsedModule.parsedWorkspaceRootModule workspace
            occurrences =
                ParsedModule.parsedModuleSyntaxOccurrences root
            summarize occurrence =
                case ParsedModule.parsedSyntaxOccurrenceEntry occurrence of
                    Interface.CanonicalExpressionFunction
                            _pattern
                            marker
                            _fixity ->
                        Right
                            ( ParsedModule.parsedSyntaxOccurrenceBlockIndex
                                occurrence
                            , locLine
                                (ParsedModule.parsedSyntaxOccurrenceLocation
                                    occurrence)
                            , ParsedModule.parsedSyntaxOccurrenceMarker occurrence
                            , marker
                            )
                    entry ->
                        Left entry
        case traverse summarize occurrences of
            Right summaries ->
                assertEqual
                    "block association and extraction order"
                    [ (0, 2, "multi_item", "multi_item")
                    , (0, 4, "itemzero", "itemzero")
                    , (0, 5, "itemsucc", "itemsucc")
                    ]
                    summaries
            Left entry ->
                assertFailure
                    ("expected an expression occurrence, got "
                        <> show entry)
        case (ParsedModule.parsedModuleBlocks root, occurrences) of
            ( Raw.BlockData _location _title blockMarker _datatype : _
              , firstOccurrence : _
              ) ->
                assertEqual
                    "first occurrence is the declaration-head anchor"
                    blockMarker
                    (ParsedModule.parsedSyntaxOccurrenceMarker firstOccurrence)
            _ ->
                assertFailure "expected a datatype block and its occurrences"

propagatesImportedSyntax :: Assertion
propagatesImportedSyntax =
    withTemporaryDirectory "felix-source-syntax-diamond" \temp -> do
        writeFile
            (temp Posix.</> "base.tex")
            (syntaxFunctionDefinition
                "star"
                "star"
                (Just "%! infixl 3"))
        writeFile
            (temp Posix.</> "left.tex")
            ("\\import{base.tex}\n"
                <> syntaxFunctionDefinition
                    "star"
                    "star"
                    Nothing)
        writeTheory
            (temp Posix.</> "right.tex")
            ["base.tex"]
            "right"
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\import{left.tex}"
                , "\\import{right.tex}"
                ]
                <> axiomBlock
                    "imported_use"
                    "a\\star b\\star c = a")
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        baseModule <- findParsedModule "base.tex" workspace
        leftModule <- findParsedModule "left.tex" workspace
        rightModule <- findParsedModule "right.tex" workspace
        let root =
                ParsedModule.parsedWorkspaceRootModule workspace
            interface =
                ParsedModule.parsedModuleSyntaxInterface
            localEntries parsed =
                Interface.canonicalSyntaxDeltaEntries
                    (Interface.moduleSyntaxLocalDelta
                        (interface parsed))
        assertEqual "base exports one syntax entry"
            1
            (length (localEntries baseModule))
        assertEqual "imported reuse emits no local entry"
            []
            (localEntries leftModule)
        assertEqual "imported reuse retains its occurrence"
            1
            (length
                (ParsedModule.parsedModuleSyntaxOccurrences leftModule))
        assertEqual "empty diamond branch has no occurrence"
            []
            (ParsedModule.parsedModuleSyntaxOccurrences rightModule)
        assertEqual "equal diamond interfaces"
            (Interface.moduleSyntaxAssertedId
                (interface leftModule))
            (Interface.moduleSyntaxAssertedId
                (interface rightModule))
        assertEqual "root coalesces equal direct interfaces"
            1
            (length
                (Interface.moduleSyntaxDirectInputs
                    (interface root)))
        case ParsedModule.parsedModuleBlocks root of
            [block] ->
                assertAxiomLeftShape
                    "imported left associativity"
                    "star(star(a,b),c)"
                    block
            blocks ->
                assertFailure
                    ("expected one imported-syntax axiom, got "
                        <> show blocks)
        writeFile
            (temp Posix.</> "left.tex")
            ("\\import{base.tex}\n"
                <> syntaxFunctionDefinition
                    "star"
                    "star"
                    (Just "%! infixl 3"))
        reuseGraph <- buildSearchedGraph temp "left.tex"
        reuseResult <-
            Parse.parseResolvedSourceGraph reuseGraph
        case reuseResult of
            Left
                (Parse.SourceSyntaxDeclarationError
                    _source
                    Parse.SyntaxPragmaOnImportedReuse{}) ->
                        pure ()
            Left err ->
                assertFailure
                    ("expected imported-reuse pragma rejection, got "
                        <> show err)
            Right reused ->
                assertFailure
                    ("expected imported-reuse pragma rejection, got "
                        <> show reused)

rejectsUnequalImportedSyntax :: Assertion
rejectsUnequalImportedSyntax =
    forM_ cases \(description, leftDefinition, rightDefinition) ->
        withTemporaryDirectory
            ("felix-source-imported-collision-" <> description)
            \temp -> do
                writeFile
                    (temp Posix.</> "a.tex")
                    leftDefinition
                writeFile
                    (temp Posix.</> "b.tex")
                    rightDefinition
                writeTheory
                    (temp Posix.</> "entry.tex")
                    ["a.tex", "b.tex"]
                    "entry"
                graph <- buildSearchedGraph temp "entry.tex"
                collision <- expectLexiconCollision
                    =<< Parse.parseResolvedSourceGraph graph
                (firstLocation, secondLocation) <-
                    expectTwoCollisionLocations collision
                assertLocation
                    "first imported declaration"
                    "a.tex"
                    1
                    firstLocation
                assertLocation
                    "second imported declaration"
                    "b.tex"
                    1
                    secondLocation
  where
    cases =
        [ ( "marker"
          , syntaxFunctionDefinition
                "clash_left"
                "clash"
                (Just "%! infixl 2")
          , syntaxFunctionDefinition
                "clash_right"
                "clash"
                (Just "%! infixl 2")
          )
        , ( "fixity"
          , syntaxFunctionDefinition
                "clash"
                "clash"
                (Just "%! infixl 2")
          , syntaxFunctionDefinition
                "clash"
                "clash"
                (Just "%! infixr 2")
          )
        ]

distinguishesPhysicalSourceLocations :: Assertion
distinguishesPhysicalSourceLocations =
    withTemporaryDirectory "felix-source-location-identity" \temp -> do
        let projectRoot = temp Posix.</> "project"
            libraryRoot = temp Posix.</> "library"
            projectEntry = projectRoot Posix.</> "entry.tex"
            libraryEntry = libraryRoot Posix.</> "entry.tex"
        Directory.createDirectory projectRoot
        Directory.createDirectory libraryRoot
        writeFile projectEntry
            ("\\import{entry.tex}\n"
                <> adjectiveDefinition "project_adjective")
        writeNounDefinition libraryEntry "library_noun"
        mounts <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "library", libraryRoot)
            , (sourceMountId "project", projectRoot)
            ]
        request <- expectRight =<< existingRoot projectEntry
        graph <- expectRight =<< buildResolvedSourceGraph mounts request
        collision <- expectLexiconCollision
            =<< Parse.parseResolvedSourceGraph graph
        assertEqual "normalized cross-category pattern"
            (Raw.TokenCons (Raw.Word "special") Raw.End)
            (Parse.lexiconCollisionPattern collision)
        (libraryLocation, projectLocation) <-
            expectTwoCollisionLocations collision
        assertEqual "accepted display path"
            "entry.tex"
            (locFile libraryLocation)
        assertEqual "accepted declaration line"
            1
            (locLine libraryLocation)
        assertEqual "colliding display path"
            "entry.tex"
            (locFile projectLocation)
        assertEqual "colliding declaration line"
            2
            (locLine projectLocation)
        canonicalProject <- Directory.canonicalizePath projectEntry
        canonicalLibrary <- Directory.canonicalizePath libraryEntry
        let rendered = show collision
            quotedLibrary = show canonicalLibrary
            quotedProject = show canonicalProject
        assertBool "rendered error includes accepted canonical path"
            (quotedLibrary `List.isInfixOf` rendered)
        assertBool "rendered error includes colliding canonical path"
            (quotedProject `List.isInfixOf` rendered)
        assertBool "canonical locations render in declaration order"
            (substringIndex quotedLibrary rendered
                < substringIndex quotedProject rendered)

retainsWorkspaceLocationDisplayPath :: Assertion
retainsWorkspaceLocationDisplayPath =
    withTemporaryDirectory "felix-source-location-display" \temp -> do
        let nested = temp Posix.</> "nested"
            entry = nested Posix.</> "entry.tex"
        Directory.createDirectory nested
        writeTheory entry [] "entry"
        outerMounts <- oneMount "project" temp
        outerRequest <- expectRight (searchedRoot "nested/entry.tex")
        outerGraph <- expectRight =<<
            buildResolvedSourceGraph outerMounts outerRequest
        outerWorkspace <- expectRight =<<
            Parse.parseResolvedSourceGraph outerGraph
        innerMounts <- oneMount "library" nested
        innerRequest <- expectRight (searchedRoot "entry.tex")
        innerGraph <- expectRight =<<
            buildResolvedSourceGraph innerMounts innerRequest
        innerWorkspace <- expectRight =<<
            Parse.parseResolvedSourceGraph innerGraph
        let outerLocation =
                onlyAxiomLocation
                    (ParsedModule.parsedWorkspaceRootModule outerWorkspace)
            innerLocation =
                onlyAxiomLocation
                    (ParsedModule.parsedWorkspaceRootModule innerWorkspace)
        assertEqual "outer-mount display path"
            "nested/entry.tex"
            (locFile outerLocation)
        assertEqual "more-specific-mount display path"
            "entry.tex"
            (locFile innerLocation)
        outerSourceDescriptor <- expectJust "outer workspace file id"
            (locSourceDescriptor outerLocation)
        innerSourceDescriptor <- expectJust "inner workspace file id"
            (locSourceDescriptor innerLocation)
        assertBool "distinct display registrations use distinct file ids"
            (outerSourceDescriptor /= innerSourceDescriptor)
        canonicalEntry <- Directory.canonicalizePath entry
        assertEqual "outer physical location key"
            (Just canonicalEntry)
            (sourceDescriptorIdentityPath outerSourceDescriptor)
        assertEqual "inner physical location key"
            (Just canonicalEntry)
            (sourceDescriptorIdentityPath innerSourceDescriptor)

reportsImportedExtractionErrorFirst :: Assertion
reportsImportedExtractionErrorFirst =
    withTemporaryDirectory "felix-source-lexer-error-order" \temp -> do
        let extractionFailure = unlines
                [ "\\begin{abbreviation}\\label{malformed_function}"
                , "  $x = \\emptyset$."
                , "\\end{abbreviation}"
                ]
            tokenizerFailure = unlines
                [ "\\begin{axiom}"
                , "#"
                , "\\end{axiom}"
                ]
        writeFile
            (temp Posix.</> "imported.tex")
            extractionFailure
        writeFile
            (temp Posix.</> "entry.tex")
            ("\\import{imported.tex}\n" <> tokenizerFailure)
        graph <- buildSearchedGraph temp "entry.tex"
        result <- Parse.parseResolvedSourceGraph graph
        case result of
            Left
                (Parse.SourceParseError
                    source
                    (Parse.LexiconExtractionFailure
                        Adapt.InvalidFunctionPattern{})) ->
                            assertEqual
                                "dependency extraction error"
                                "imported.tex"
                                (safeRelativePathFilePath
                                    (resolvedSourceRelativePath source))
            Left err ->
                assertFailure
                    ("expected imported extraction error, got " <> show err)
            Right workspace ->
                assertFailure
                    ("expected imported extraction error, got "
                        <> show workspace)

reportsMalformedLexicalDeclaration :: Assertion
reportsMalformedLexicalDeclaration =
    withTemporaryDirectory "felix-source-malformed-lexical" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{abbreviation}\\label{malformed_function}"
                , "  $x = \\emptyset$."
                , "\\end{abbreviation}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        result <- Parse.parseResolvedSourceGraph graph
        void (evaluate (length (show result)))
        case result of
            Left
                (Parse.SourceParseError
                    source
                    (Parse.LexiconExtractionFailure
                        (Adapt.InvalidFunctionPattern
                            location
                            Adapt.FunctionPatternBareVariable))) -> do
                                assertEqual "malformed source"
                                    "entry.tex"
                                    (safeRelativePathFilePath
                                        (resolvedSourceRelativePath source))
                                assertLocation
                                    "malformed declaration"
                                    "entry.tex"
                                    1
                                    location
            Left err ->
                assertFailure
                    ("expected typed lexicon extraction failure, got "
                        <> show err)
            Right workspace ->
                assertFailure
                    ("expected typed lexicon extraction failure, got "
                        <> show workspace)

rejectsMalformedInductivePattern :: Assertion
rejectsMalformedInductivePattern =
    case scanTestSource anonymousSourceDescriptor "inductive.tex" source of
        Left err ->
            assertFailure ("could not tokenize fixture: " <> show err)
        Right (_imports, [chunk]) ->
            case Adapt.preparedLexicalItems
                    <$> Adapt.prepareLexicalChunk chunk of
                Left
                    (Adapt.InvalidFunctionPattern
                        _location
                        Adapt.FunctionPatternBareVariable) ->
                            pure ()
                Left err ->
                    assertFailure
                        ("expected bare-variable extraction failure, got "
                            <> show err)
                Right extracted ->
                    assertFailure
                        ("expected bare-variable extraction failure, got "
                            <> show extracted)
        Right (_imports, chunks) ->
            assertFailure
                ("expected one lexical chunk, got " <> show (length chunks))
  where
    source =
        Text.pack
            (unlines
            [ "\\begin{inductive}\\label{malformed_inductive}"
            , "  Define $x\\subseteq\\pow{x}$ inductively."
            , "\\end{inductive}"
            ])

acceptsAdjectiveSignature :: Assertion
acceptsAdjectiveSignature =
    withTemporaryDirectory "felix-source-signature-adjective" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{signature}\\label{reflexive_signature}"
                , "  Suppose $A$ is a set."
                , "  Then $x$ can be reflexive."
                , "\\end{signature}"
                , "\\begin{axiom}\\label{reflexive_use}"
                , "  $x$ is reflexive."
                , "\\end{axiom}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        let blocks = ParsedModule.importedBeforeImporterBlocks workspace
        case blocks of
            [ Raw.BlockSig
                    _signatureLocation
                    _signatureTitle
                    _signatureMarker
                    [_signatureAssumption]
                    (Raw.SignatureAdj
                        _variable
                        (Raw.Adj _adjectiveLocation declaredAdjective []))
              , Raw.BlockAxiom{}
              ] -> do
                    assertEqual
                        "user adjective marker is removed after association"
                        Nothing
                        (Raw.adjectiveLexicalMarker declaredAdjective)
                    assertEqual
                        "predicative adjective retains its declared side"
                        Raw.LeftAdjectiveSide
                        (Raw.adjectiveLexicalSide declaredAdjective)
            _ ->
                assertFailure
                    ("unexpected adjective-signature blocks: " <> show blocks)

acceptsTypedConstantSignature :: Assertion
acceptsTypedConstantSignature =
    withTemporaryDirectory "felix-source-signature-typed" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{signature}\\label{typed_phi}"
                , "  $\\Phi : \\Set\\to\\Set\\to\\Prop$."
                , "\\end{signature}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        let blocks = ParsedModule.importedBeforeImporterBlocks workspace
        case blocks of
            [Raw.BlockSig
                _signatureLocation
                _signatureTitle
                _signatureMarker
                []
                (Raw.SignatureTypedConstant
                    _headLocation
                    (Raw.Variable "Phi")
                    coreType)] ->
                        assertEqual
                            "right-associated parsed type"
                            (Raw.ConcreteArrow
                                Raw.ConcreteSet
                                (Raw.ConcreteArrow
                                    Raw.ConcreteSet
                                    Raw.ConcreteProp))
                            coreType
            _ ->
                assertFailure
                    ("unexpected typed-signature blocks: " <> show blocks)

rejectsMalformedSignatureHead :: Assertion
rejectsMalformedSignatureHead = do
    case scanTestSource
        anonymousSourceDescriptor
        "malformed-signature.tex"
        (Text.unlines
            [ "\\begin{signature}\\label{bad_signature}"
            , "  $x$ can be."
            , "\\end{signature}"
            ]) of
        Left err ->
            assertFailure ("unexpected token error: " <> show err)
        Right (_imports, [chunk]) ->
            case Adapt.preparedLexicalItems
                    <$> Adapt.prepareLexicalChunk chunk of
                Left
                    (Adapt.InvalidFunctionPattern
                        location
                        Adapt.FunctionPatternBareVariable) -> do
                            assertEqual "error line" 1 (locLine location)
                            assertEqual "error column" 1 (locColumn location)
                Left err ->
                    assertFailure
                        ("expected malformed signature error, got " <> show err)
                Right extracted ->
                    assertFailure
                        ("expected malformed signature rejection, got "
                            <> show extracted)
        Right (_imports, chunks) ->
            assertFailure
                ("expected one malformed signature chunk, got "
                    <> show (length chunks))

extractsCanonicalOwnedStructureField :: Assertion
extractsCanonicalOwnedStructureField = do
    prepared <- prepareSingleChunk
        (Text.unlines
            [ "\\begin{struct}\\label{owned_field_widget}"
            , "  A widget $X$ is a onesorted structure equipped with"
            , "  \\begin{enumerate}"
            , "    \\item\\label{owned_field_value} a set $\\widgetValue[X]$;"
            , "  \\end{enumerate}."
            , "\\end{struct}"
            ])
    case Raw.unLocated <$> Adapt.preparedLexicalItems prepared of
        [ Adapt.ExtractedStructureNoun _phrase "owned_field_widget"
            , Adapt.ExtractedStructureOperation "widgetValue"
            ] -> pure ()
        items ->
            assertFailure
                ("unexpected extracted structure items: " <> show items)

rejectsWrongOwnedStructureFieldReceiver :: Assertion
rejectsWrongOwnedStructureFieldReceiver =
    withTemporaryDirectory "felix-owned-structure-field" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{struct}\\label{owned_field_widget}"
                , "  A widget $X$ is a onesorted structure equipped with"
                , "  \\begin{enumerate}"
                , "    \\item a set $\\widgetValue[Y]$;"
                , "  \\end{enumerate}."
                , "\\end{struct}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        Parse.parseResolvedSourceGraph graph >>= \case
            Left
                (Parse.SourceParseError _source
                    (Parse.ConcreteSyntaxFailure
                        (Concrete.OwnedStructureFieldReceiverMismatch
                            _location
                            (Raw.NamedVar "X")
                            (Raw.ExprVar (Raw.NamedVar "Y"))))) -> pure ()
            result ->
                assertFailure
                    ("unexpected wrong-receiver parse result: " <> show result)

reportsSameSourceLexiconCollision :: Assertion
reportsSameSourceLexiconCollision =
    withTemporaryDirectory "felix-source-local-lexicon-collision" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\begin{struct}\\label{duplicate_operations}"
                , "  A \\duplicateop $X$ is equipped with"
                , "  \\begin{enumerate}"
                , "    \\item $\\duplicateop$;"
                , "  \\end{enumerate}"
                , "\\end{struct}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        collision <- expectLexiconCollision
            =<< Parse.parseResolvedSourceGraph graph
        (firstLocation, secondLocation) <-
            expectTwoCollisionLocations collision
        assertEqual "first declaration file"
            "entry.tex"
            (locFile firstLocation)
        assertEqual "first declaration line" 1 (locLine firstLocation)
        assertEqual "colliding declaration file"
            "entry.tex"
            (locFile secondLocation)
        assertEqual "colliding declaration line" 4 (locLine secondLocation)
        assertBool "declarations have distinct locations"
            (firstLocation /= secondLocation)

acceptsBuiltinSourceDeclaration :: Assertion
acceptsBuiltinSourceDeclaration =
    withTemporaryDirectory "felix-source-builtin-declaration" \temp -> do
        writeBuiltinZeroDefinition
            (temp Posix.</> "entry.tex")
            "source_zero"
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        let root =
                ParsedModule.parsedWorkspaceRootModule workspace
        assertEqual
            "fixed reuse emits no local syntax"
            []
            (Interface.canonicalSyntaxDeltaEntries
                (Interface.moduleSyntaxLocalDelta
                    (ParsedModule.parsedModuleSyntaxInterface root)))
        case ParsedModule.parsedModuleBlocks root of
            [Raw.BlockAbbr
                    _location
                    _title
                    blockMarker
                    (Raw.AbbreviationEq
                        (Raw.SymbolPattern
                            (Raw.MixfixItem
                                _pattern
                                symbolMarker
                                _associativity)
                            [])
                        _expression)] -> do
                assertEqual
                    "declaration label remains independent"
                    "source_zero"
                    blockMarker
                assertEqual
                    "built-in marker remains authoritative"
                    "zero"
                    symbolMarker
                case ParsedModule.parsedModuleSyntaxOccurrences root of
                    [occurrence] ->
                        case ParsedModule.parsedSyntaxOccurrenceEntry occurrence of
                            Interface.CanonicalExpressionFunction
                                    _pattern
                                    occurrenceMarker
                                    _fixity -> do
                                        assertEqual
                                            "occurrence retains source marker"
                                            "source_zero"
                                            (ParsedModule.parsedSyntaxOccurrenceMarker
                                                occurrence)
                                        assertEqual
                                            "occurrence uses fixed marker"
                                            "zero"
                                            occurrenceMarker
                                        descriptor <- expectJust
                                            "fixed occurrence file id"
                                            (locSourceDescriptor
                                                (ParsedModule.parsedSyntaxOccurrenceLocation
                                                    occurrence))
                                        decoded <- expectRight
                                            (Parsed.decodeParsedArtefact
                                                descriptor
                                                (ParsedModule.parsedModuleArtefact root))
                                        assertEqual
                                            "decoded occurrence preserves both markers"
                                            [occurrence]
                                            (Parsed.decodedParsedOccurrences decoded)
                            entry ->
                                assertFailure
                                    ("unexpected fixed occurrence: "
                                        <> show entry)
                    occurrences ->
                        assertFailure
                            ("unexpected fixed occurrences: "
                                <> show occurrences)
            blocks ->
                assertFailure
                    ("unexpected built-in declaration parse: "
                        <> show blocks)

acceptsBuiltinPrefixPredicateDeclaration :: Assertion
acceptsBuiltinPrefixPredicateDeclaration =
    withTemporaryDirectory "felix-source-builtin-prefix" \temp -> do
        writeBuiltinCongDefinition
            (temp Posix.</> "entry.tex")
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        case ParsedModule.parsedModuleBlocks
            (ParsedModule.parsedWorkspaceRootModule workspace) of
                [Raw.BlockDefn
                    _location
                    _title
                    _blockMarker
                    (Raw.Defn
                        _assumptions
                        (Raw.DefnSymbolicPredicate
                            predicate
                            predicateMarker
                            _variables)
                        _statement)] -> do
                            assertEqual "built-in prefix predicate"
                                (Raw.PrefixPredicate "Cong" 4)
                                predicate
                            assertEqual
                                "built-in prefix marker remains authoritative"
                                "cong"
                                predicateMarker
                blocks ->
                    assertFailure
                        ("unexpected built-in prefix declaration parse: "
                            <> show blocks)

avoidsAliasImportLexiconCollision :: Assertion
avoidsAliasImportLexiconCollision =
    withTemporaryDirectory "felix-source-alias-lexicon" \temp -> do
        let shared = temp Posix.</> "shared.tex"
            alias = temp Posix.</> "alias.tex"
        writeAdjectiveDefinition shared "shared_special"
        Directory.createFileLink shared alias
        writeFile
            (temp Posix.</> "entry.tex")
            (unlines
                [ "\\import{shared.tex}"
                , "\\import{shared.tex}"
                , "\\import{alias.tex}"
                , "\\begin{axiom}\\label{root}"
                , "  $x$ is special."
                , "\\end{axiom}"
                ])
        graph <- buildSearchedGraph temp "entry.tex"
        workspace <- expectRight
            =<< Parse.parseResolvedSourceGraph graph
        assertEqual "canonical source is parsed once"
            ["shared.tex", "entry.tex"]
            (toList
                ( safeRelativePathFilePath
                    . resolvedSourceRelativePath
                    . ParsedModule.parsedModuleResolved
                    <$> ParsedModule.parsedWorkspaceImportedBeforeImporter workspace
                ))

parsesWithoutRereading :: Assertion
parsesWithoutRereading =
    withTemporaryDirectory "felix-source-no-reread" \temp -> do
        let shared = temp Posix.</> "shared.tex"
            entry = temp Posix.</> "entry.tex"
        writeTheory shared [] "shared"
        writeTheory entry ["shared.tex"] "entry"
        graph <- buildSearchedGraph temp "entry.tex"
        Directory.removeFile entry
        Directory.removeFile shared
        firstWorkspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
        secondWorkspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
        assertEqual "first flat projection" 2
            (length (ParsedModule.importedBeforeImporterBlocks firstWorkspace))
        assertEqual "repeated downstream projection" 2
            (length (ParsedModule.importedBeforeImporterBlocks secondWorkspace))

returnsSourceParseFailures :: Assertion
returnsSourceParseFailures =
    withTemporaryDirectory "felix-source-parse-error" \temp -> do
        writeFile
            (temp Posix.</> "entry.tex")
            (theoryBlock "accepted"
                <> unlines
                    [ "\\begin{axiom}\\label{first_failure}"
                    , "  $x \\unknown y$."
                    , "\\end{axiom}"
                    , "\\begin{axiom}\\label{later_failure}"
                    , "  $x \\anotherunknown y$."
                    , "\\end{axiom}"
                    ])
        graph <- buildSearchedGraph temp "entry.tex"
        result <- Parse.parseResolvedSourceGraph graph
        case result of
            Left (Parse.SourceParseError source (Parse.UnconsumedTokens _ tokens)) -> do
                assertEqual "failed source" "entry.tex"
                    (safeRelativePathFilePath
                        (resolvedSourceRelativePath source))
                assertEqual "first failing chunk, not the later one" 5
                    (locLine (Raw.startPos (NonEmpty.head tokens)))
            Left err ->
                assertFailure ("expected SourceParseError, got " <> show err)
            Right workspace ->
                assertFailure ("expected parse failure, got " <> show workspace)

checksGuardedSymbolicDeclarations :: Assertion
checksGuardedSymbolicDeclarations = do
    withTemporaryDirectory
        "felix-guarded-symbolic-definition"
        \temp -> do
            let relative = "entry.tex"
                source = unlines
                    [ "\\begin{definition}\\label{guarded_symbolic}"
                    , "  Suppose $\\top$."
                    , "  $\\guardedsymbolic{X} = X$."
                    , "\\end{definition}"
                    ]
            writeFile (temp Posix.</> relative) source
            graph <- buildSearchedGraph temp relative
            workspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
            blocks <- pure (ParsedModule.importedBeforeImporterBlocks workspace)
            case blocks of
                [Raw.BlockDefn _location _title _marker
                    (Raw.DefnOp
                        [Raw.AsmSuppose{}]
                        _pattern
                        _body
                        Nothing)] -> pure ()
                _ ->
                    assertFailure
                        ("guarded symbolic definition lost its header: "
                            <> show blocks)

    let kind = "abbreviation"
        failureLine = 2 :: Int
    withTemporaryDirectory
        "felix-guarded-symbolic-abbreviation"
        \temp -> do
            let relative = "entry.tex"
                source = unlines
                    [ "\\begin{abbreviation}\\label{guarded_symbolic}"
                    , "  Suppose $\\top$."
                    , "  $\\guardedsymbolic{X} = X$."
                    , "\\end{abbreviation}"
                    ]
            writeFile (temp Posix.</> relative) source
            graph <- buildSearchedGraph temp relative
            result <- Parse.parseResolvedSourceGraph graph
            case result of
                Left (Parse.SourceParseError failed parseFailure) -> do
                    assertEqual (kind <> " source") relative
                        (safeRelativePathFilePath
                            (resolvedSourceRelativePath failed))
                    assertBool
                        (kind <> " parse failure retains a located source position: "
                            <> show parseFailure)
                        (("entry.tex " <> show failureLine <> ":")
                            `List.isInfixOf` show parseFailure)
                Left failure ->
                    assertFailure
                        ("expected guarded-symbolic parse failure, got "
                            <> show failure)
                Right workspace ->
                    assertFailure
                        ("guarded symbolic " <> kind
                            <> " was silently accepted: " <> show workspace)

preparesCanonicalVerbMetadata :: Assertion
preparesCanonicalVerbMetadata = do
    inferred <- prepareSingleChunk
        (Text.unlines
            [ "\\begin{definition}\\label{has_clopen_basis}"
            , "  $X$ has a clopen basis iff $X=X$."
            , "\\end{definition}"
            ])
    inferredSurfaces <- soleExtractedVerb inferred
    assertEqual "literal article remains singular"
        (Raw.lexicalPhrase
            (Just "has" :| [Just "a", Just "clopen", Just "basis"]))
        (Raw.verbSurfaceSingular inferredSurfaces)
    assertEqual "literal article remains in the base form"
        (Raw.lexicalPhrase
            (Just "have" :| [Just "a", Just "clopen", Just "basis"]))
        (Raw.verbSurfaceBase inferredSurfaces)

    explicit <- prepareSingleChunk
        (Text.unlines
            [ "\\begin{definition}\\label{lies_over}"
            , "  \\verbbase{LIE}"
            , "  $X$ lies over $Y$ iff $X=X$."
            , "\\end{definition}"
            ])
    explicitSurfaces <- soleExtractedVerb explicit
    assertEqual "scanner-normalized explicit base"
        (Raw.lexicalPhrase
            (Just "lie" :| [Just "over", Nothing]))
        (Raw.verbSurfaceBase explicitSurfaces)
    assertBool "source metadata is absent from parser tokens"
        (all ((/= Raw.Command "verbbase") . Raw.unLocated)
            (Adapt.preparedLexicalTokens explicit))

rejectsInvalidVerbMetadata :: Assertion
rejectsInvalidVerbMetadata = do
    assertPreparationError
        "duplicate metadata wins before payload validation"
        (Text.unlines
            [ "\\begin{definition}\\label{duplicate}"
            , "  \\verbbase{}"
            , "  \\verbbase{have}"
            , "  $X$ has a property iff $X=X$."
            , "\\end{definition}"
            ])
        (\case
            Adapt.InvalidVerbMetadata location Adapt.DuplicateVerbBase ->
                assertEqual "second metadata line" 3 (locLine location)
            failure -> unexpectedPreparationError failure)
    assertPreparationError
        "misplaced metadata"
        (Text.unlines
            [ "\\begin{definition}\\label{misplaced}"
            , "  $X$ has \\verbbase{have} a property iff $X=X$."
            , "\\end{definition}"
            ])
        (\case
            Adapt.InvalidVerbMetadata _ Adapt.IllegalVerbBasePlacement ->
                pure ()
            failure -> unexpectedPreparationError failure)
    assertPreparationError
        "malformed metadata payload"
        (Text.unlines
            [ "\\begin{definition}\\label{malformed}"
            , "  \\verbbase{have two}"
            , "  $X$ has a property iff $X=X$."
            , "\\end{definition}"
            ])
        (\case
            Adapt.InvalidVerbMetadata _ Adapt.MalformedVerbBasePayload ->
                pure ()
            failure -> unexpectedPreparationError failure)
    assertPreparationError
        "metadata on a noun head"
        (Text.unlines
            [ "\\begin{definition}\\label{noun_metadata}"
            , "  \\verbbase{be}"
            , "  $X$ is a metadata object iff $X=X$."
            , "\\end{definition}"
            ])
        (\case
            Adapt.VerbBaseOnNonverbHead{} -> pure ()
            failure -> unexpectedPreparationError failure)
    assertPreparationError
        "invalid inferred base"
        (Text.unlines
            [ "\\begin{definition}\\label{empty_base}"
            , "  $X$ s iff $X=X$."
            , "\\end{definition}"
            ])
        (\case
            Adapt.InvalidVerbSurfaces
                    location
                    (Raw.EmptyLeadingVerbSurfaceWord Raw.BaseVerbSurface) ->
                assertEqual "leading verb line" 2 (locLine location)
            failure -> unexpectedPreparationError failure)
    assertPreparationError
        "metadata command in another formal environment"
        (Text.unlines
            [ "\\begin{proposition}\\label{reserved_metadata}"
            , "  \\verbbase{have}"
            , "  $X=X$."
            , "\\end{proposition}"
            ])
        (\case
            Adapt.InvalidVerbMetadata _ Adapt.IllegalVerbBasePlacement ->
                pure ()
            failure -> unexpectedPreparationError failure)

prepareSingleChunk :: Text -> IO Adapt.PreparedLexicalChunk
prepareSingleChunk source =
    case scanTestSource anonymousSourceDescriptor "verb-metadata.tex" source of
        Left failure ->
            assertFailure ("could not scan verb fixture: " <> show failure)
                >> fail "unreachable"
        Right (_imports, [chunk]) ->
            case Adapt.prepareLexicalChunk chunk of
                Left failure ->
                    assertFailure
                        ("could not prepare verb fixture: " <> show failure)
                        >> fail "unreachable"
                Right prepared -> pure prepared
        Right (_imports, chunks) ->
            assertFailure
                ("expected one verb fixture chunk, got "
                    <> show (length chunks))
                >> fail "unreachable"

soleExtractedVerb :: Adapt.PreparedLexicalChunk -> IO Raw.VerbSurfaces
soleExtractedVerb prepared =
    case Adapt.preparedLexicalItems prepared of
        [Raw.Located{Raw.unLocated = Adapt.ExtractedVerb surfaces _marker}] ->
            pure surfaces
        items ->
            assertFailure ("expected one extracted verb, got " <> show items)
                >> fail "unreachable"

assertPreparationError
    :: String
    -> Text
    -> (Adapt.LexiconExtractionError -> Assertion)
    -> Assertion
assertPreparationError label source check =
    case scanTestSource anonymousSourceDescriptor "verb-metadata.tex" source of
        Left failure ->
            assertFailure (label <> ": scanner failed: " <> show failure)
        Right (_imports, [chunk]) ->
            case Adapt.prepareLexicalChunk chunk of
                Left failure -> check failure
                Right _ -> assertFailure (label <> ": source was accepted")
        Right (_imports, chunks) ->
            assertFailure
                (label <> ": expected one chunk, got " <> show (length chunks))

unexpectedPreparationError :: Adapt.LexiconExtractionError -> Assertion
unexpectedPreparationError failure =
    assertFailure ("unexpected verb preparation failure: " <> show failure)

parsesDefinitionResultAnnotations :: Assertion
parsesDefinitionResultAnnotations =
    withTemporaryDirectory "felix-definition-result-annotation" \temp -> do
        let relative = "entry.tex"
            source = unlines
                [ "\\begin{definition}\\label{special}"
                , "  $x$ is special iff $\\top$."
                , "\\end{definition}"
                , "\\begin{definition}\\label{copy}"
                , "  Let $X$ be a set."
                , "  The copy of $X$, $X$, is $X$, which is a special set."
                , "\\end{definition}"
                , "\\begin{definition}\\label{clone}"
                , "  Let $X$ be a set."
                , "  $\\clone{X}=X$, which is a special set."
                , "\\end{definition}"
                ]
        writeFile (temp Posix.</> relative) source
        graph <- buildSearchedGraph temp relative
        workspace <- expectRight =<< Parse.parseResolvedSourceGraph graph
        case ParsedModule.importedBeforeImporterBlocks workspace of
            [ Raw.BlockDefn _ _ _ Raw.Defn{}
              , Raw.BlockDefn _ _ _
                    (Raw.DefnFun _ _ (Just _) _ (Just functionalResult))
              , Raw.BlockDefn _ _ _
                    (Raw.DefnOp _ _ _ (Just symbolicResult))
              ] -> do
                    assertResultPhrase "functional" functionalResult
                    assertResultPhrase "symbolic" symbolicResult
            blocks ->
                assertFailure
                    ("unexpected annotated definition parse: " <> show blocks)
  where
    assertResultPhrase label = \case
        Raw.NounPhrase
                [Raw.AdjL _ _ []]
                (Raw.Noun _ item [])
                (Raw.NounBinder Raw.Nameless Raw.Unbounded)
                []
                Nothing ->
            assertBool (label <> " result keeps the set core")
                (Lexicon.isBuiltinSetNoun item)
        phrase ->
            assertFailure
                (label <> " result phrase lost its atomic shape: "
                    <> show phrase)

buildSearchedGraph :: FilePath -> FilePath -> IO ResolvedSourceGraph
buildSearchedGraph root path = do
    mounts <- oneMount "project" root
    request <- expectRight (searchedRoot path)
    expectRight =<< buildResolvedSourceGraph mounts request

sourceGraphOrderPaths :: ResolvedSourceGraph -> IO [FilePath]
sourceGraphOrderPaths graph =
    pure
        [ safeRelativePathFilePath
            (resolvedSourceRelativePath (sourceNodeResolved node))
        | node <- toList (sourceGraphImportedBeforeImporter graph)
        ]

sourceNodeCanonicalPathForTest :: SourceNode -> CanonicalPath
sourceNodeCanonicalPathForTest =
    resolvedSourceCanonicalPath . sourceNodeResolved

onlyAxiomLocation :: ParsedModule.ParsedModule -> Location
onlyAxiomLocation node =
    case ParsedModule.parsedModuleBlocks node of
        [Raw.BlockAxiom location _title _marker _axiom] ->
            location
        blocks ->
            error ("expected one axiom block, got " <> show blocks)

syntaxFunctionDefinition
    :: String
    -> String
    -> Maybe String
    -> String
syntaxFunctionDefinition marker command pragma =
    unlines
        ( [ "\\begin{abbreviation}\\label{" <> marker <> "}"
          ]
          <> maybe [] (\line -> ["  " <> line]) pragma
          <> [ "  $x\\" <> command <> " y = x$."
             , "\\end{abbreviation}"
             ]
        )

axiomBlock :: String -> String -> String
axiomBlock marker statement =
    unlines
        [ "\\begin{axiom}\\label{" <> marker <> "}"
        , "  $" <> statement <> "$."
        , "\\end{axiom}"
        ]

assertExpressionFixity
    :: Text
    -> Raw.Associativity
    -> Word8
    -> [Interface.CanonicalLexicalEntry]
    -> Assertion
assertExpressionFixity marker associativity level entries =
    case
        [ fixity
        | Interface.CanonicalExpressionFunction
                _pattern
                (Raw.Marker candidate)
                fixity <-
            entries
        , candidate == marker
        ] of
        [Interface.Fixity actualAssociativity actualLevel] -> do
            assertEqual
                (Text.unpack marker <> " associativity")
                associativity
                actualAssociativity
            assertEqual
                (Text.unpack marker <> " level")
                level
                (Interface.mixfixLevelValue actualLevel)
        actual ->
            assertFailure
                ("expected one fixity for "
                    <> Text.unpack marker
                    <> ", got "
                    <> show actual)

assertAxiomLeftShape
    :: String
    -> String
    -> Raw.Block
    -> Assertion
assertAxiomLeftShape description expected block =
    case block of
        Raw.BlockAxiom
            _location
            _title
            _marker
            (Raw.Axiom
                _assumptions
                (Raw.StmtFormula
                    (Raw.FormulaChain
                        (Raw.ChainBase
                            (expression :| [])
                            _sign
                            _relation
                            _right)))) ->
                                assertEqual
                                    description
                                    expected
                                    (expressionShape expression)
        _ ->
            assertFailure
                ("expected an axiom with one left expression, got "
                    <> show block)

expressionShape :: Raw.Expr -> String
expressionShape = \case
    Raw.ExprVar (Raw.NamedVarAt _location name) ->
        Text.unpack name
    Raw.ExprOp
            _location
            symbol
            arguments ->
        let Raw.Marker marker =
                Raw.mixfixMarker symbol
        in
            Text.unpack marker
                <> "("
                <> List.intercalate ","
                    (expressionShape <$> arguments)
                <> ")"
    expression ->
        show expression

findParsedModule
    :: FilePath
    -> ParsedModule.ParsedSourceWorkspace
    -> IO ParsedModule.ParsedModule
findParsedModule relative workspace =
    case List.find hasPath
            (ParsedModule.parsedWorkspaceModules workspace) of
        Just parsed ->
            pure parsed
        Nothing ->
            assertFailure
                ("could not find parsed module " <> relative)
  where
    hasPath parsed =
        safeRelativePathFilePath
            (resolvedSourceRelativePath
                (ParsedModule.parsedModuleResolved parsed))
            == relative

writeAdjectiveDefinition :: FilePath -> String -> IO ()
writeAdjectiveDefinition path marker =
    writeFile path (adjectiveDefinition marker)

adjectiveDefinition :: String -> String
adjectiveDefinition marker =
    unlines
        [ "\\begin{definition}\\label{" <> marker <> "}"
        , "  $x$ is special iff $x = x$."
        , "\\end{definition}"
        ]

writeNounDefinition :: FilePath -> String -> IO ()
writeNounDefinition path marker =
    writeFile path
        (unlines
            [ "\\begin{definition}\\label{" <> marker <> "}"
            , "  $x$ is a special iff $x = x$."
            , "\\end{definition}"
            ])

writeBuiltinZeroDefinition :: FilePath -> String -> IO ()
writeBuiltinZeroDefinition path marker =
    writeFile path (builtinZeroDefinition marker)

builtinZeroDefinition :: String -> String
builtinZeroDefinition marker =
    unlines
        [ "\\begin{abbreviation}\\label{" <> marker <> "}"
        , "  $\\zero = \\emptyset$."
        , "\\end{abbreviation}"
        ]

writeBuiltinCongDefinition :: FilePath -> IO ()
writeBuiltinCongDefinition path =
    writeFile path
        (unlines
            [ "\\begin{definition}\\label{source_cong}"
            , "  $\\Cong{x}{y}{z}{w}$ iff $x = x$."
            , "\\end{definition}"
            ])

writeTheory :: FilePath -> [FilePath] -> String -> IO ()
writeTheory path imports label =
    writeFile path
        (unlines
            (["\\import{" <> imported <> "}" | imported <- imports]
                <> [theoryBlock label]))

theoryBlock :: String -> String
theoryBlock label =
    unlines
        [ "\\begin{axiom}\\label{" <> label <> "}"
        , "  $x = x$."
        , "\\end{axiom}"
        ]

oneMount :: Text -> FilePath -> IO SourceMounts
oneMount ident root =
    expectRight =<< prepareSourceMounts [(sourceMountId ident, root)]

assertRight :: (Show e, HasCallStack) => Either e a -> Assertion
assertRight = void . expectRight

expectRight :: (Show e, HasCallStack) => Either e a -> IO a
expectRight = \case
    Left err ->
        assertFailure ("expected Right, got Left " <> show err)
    Right value ->
        pure value

expectJust :: HasCallStack => String -> Maybe a -> IO a
expectJust description = \case
    Nothing ->
        assertFailure ("expected " <> description)
    Just value ->
        pure value

expectLexiconCollision
    :: Either Parse.ParseWorkspaceError a
    -> IO Parse.LexiconCollision
expectLexiconCollision = \case
    Left (Parse.SourceLexiconCollision collision) ->
        pure collision
    Left err ->
        assertFailure
            ("expected SourceLexiconCollision, got " <> show err)
    Right _value ->
        assertFailure "expected SourceLexiconCollision, got Right"

expectTwoCollisionLocations
    :: Parse.LexiconCollision
    -> IO (Location, Location)
expectTwoCollisionLocations collision =
    case Parse.lexiconCollisionDeclarations collision of
        firstLocation : secondLocation : _ ->
            pure (firstLocation, secondLocation)
        locations ->
            assertFailure
                ("expected two source collision locations, got "
                    <> show locations)

assertLocation :: String -> FilePath -> Int -> Location -> Assertion
assertLocation description expectedFile expectedLine location = do
    assertEqual (description <> " file")
        expectedFile
        (locFile location)
    assertEqual (description <> " line")
        expectedLine
        (locLine location)
    assertEqual (description <> " column")
        1
        (locColumn location)

substringIndex :: String -> String -> Int
substringIndex needle haystack =
    fromMaybe maxBound
        (List.findIndex
            (List.isPrefixOf needle)
            (List.tails haystack))

assertLeft :: (Eq e, Eq a, Show e, Show a, HasCallStack) => e -> Either e a -> Assertion
assertLeft expected actual =
    assertEqual "expected Left value" (Left expected) actual

retainsBoundedNounPayload :: Assertion
retainsBoundedNounPayload =
    withTemporaryDirectory "felix-bounded-noun-payload" \root -> do
        let source = Text.unlines
                [ "\\begin{proposition}\\label{bounded_payload}"
                , "For every element $x\\notin F$ of $A$ we have $x=x$."
                , "\\end{proposition}"
                ]
        writeFile (root Posix.</> "entry.tex") (Text.unpack source)
        workspace <- expectRight =<< Parse.parseResolvedSourceGraph
            =<< buildSearchedGraph root "entry.tex"
        let parsed = ParsedModule.parsedWorkspaceRootModule workspace
        decoded <- expectRight (Parsed.decodeParsedArtefact anonymousSourceDescriptor
            (ParsedModule.parsedModuleArtefact parsed))
        case Parsed.decodedParsedBlocks decoded of
            [Raw.BlockClaim _ _ _ _ (Raw.Claim []
                (Raw.StmtQuantPhrase _ (Raw.QuantPhrase Raw.Universally
                    (Raw.NounPhrase _ _ (Raw.NounBinder [variable]
                        (Raw.Bounded location sign (Raw.Relation _ symbol []) (Raw.ExprVar endpoint))) _ _)) _))] -> do
                    assertEqual "decoded name" "x" variable
                    assertEqual "decoded sign" Raw.Positive sign
                    assertEqual "decoded relation" Raw.NotElementSymbol symbol
                    assertEqual "decoded endpoint" "F" endpoint
                    for_ [locate variable, location, locate endpoint] \position -> do
                        assertEqual "location rebound to the live owner" (Just anonymousSourceDescriptor) (locSourceDescriptor position)
                        assertEqual "source line retained" 2 (locLine position)
                        assertBool "source column retained" (locColumn position > 1)
            blocks -> assertFailure ("bounded noun payload lost its fields: " <> show blocks)
