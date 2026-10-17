{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.SourceScanBenchmark
    ( unitTests
    ) where

import Base

import Control.Exception (evaluate)
import Data.ByteString qualified as ByteString
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Felix.Report.Location (anonymousSourceDescriptor)
import Felix.Source
    ( prepareSourceMounts
    , resolveAndLoadRoot
    , searchedRoot
    , sourceMountId
    )
import Felix.Source.Content (identifyLoadedSource)
import Felix.Source.Scan
    ( SourceScanFailure(..)
    , VerificationScanError(..)
    , forceSourceTokenChunksHandoff
    , scanCompleteSourceTokens
    , scanCompleteVerificationText
    )
import Felix.Syntax.Pragma
    ( SyntaxPragmaError(..)
    , SyntaxPragmaProblem(..)
    )
import Felix.Syntax.Token (Located(..), Token(..))
import Felix.Test.SourceScan.Candidate
import Felix.Test.SourceScan.Observation
import System.FilePath ((</>))
import System.IO.Temp qualified as Temp
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "source-scan benchmark schema"
        [ testCase "ignores physical read paths in corpus identity"
            ignoresPhysicalReadPaths
        , testCase "binds every logical corpus component"
            bindsLogicalCorpusComponents
        , testCase "normalizes a CRLF and tab boundary fixture"
            normalizesBoundaryFixture
        , testCase "keeps malformed pragmas mode-specific"
            keepsMalformedPragmasModeSpecific
        , testCase "normalized parse failures ignore source labels"
            normalizedFailuresIgnoreSourceLabels
        , testCase "candidate commits recognized formal environments"
            candidateCommitsRecognizedFormalEnvironments
        , testCase "complete verification preserves pragma precedence"
            completeVerificationPreservesPragmaPrecedence
        , testCase "late import failure retains its committed offset"
            lateImportFailureRetainsCommittedOffset
        , testCase "developer token scan ignores malformed pragmas"
            developerTokenScanIgnoresMalformedPragmas
        , testCase "binds every semantic observation component"
            bindsSemanticObservationComponents
        ]

ignoresPhysicalReadPaths :: Assertion
ignoresPhysicalReadPaths =
    corpusManifestDigest
        (manifestWithPaths "/tmp/first" "/tmp/first/library")
    @?= corpusManifestDigest
        (manifestWithPaths "/different/worktree" "/different/library")

bindsLogicalCorpusComponents :: Assertion
bindsLogicalCorpusComponents = do
    let baseline = corpusManifestDigest baseManifest
        differs description manifest =
            assertBool description
                (baseline /= corpusManifestDigest manifest)
    differs "root address"
        (makeCorpusManifest
            (LogicalSourceAddress "project" "other.tex")
            mountOrder
            sourceInputs)
    differs "mount search order"
        (makeCorpusManifest rootAddress (reverse mountOrder) sourceInputs)
    differs "source address"
        (makeCorpusManifest
            rootAddress
            mountOrder
            [ ManifestSourceInput
                (LogicalSourceAddress "library" "changed.tex")
                "/work/library/base.tex"
                "base"
            , secondInput
            ])
    differs "source bytes"
        (makeCorpusManifest
            rootAddress
            mountOrder
            [ firstInput{manifestInputBytes = "changed"}
            , secondInput
            ])
    differs "source order"
        (makeCorpusManifest rootAddress mountOrder (reverse sourceInputs))
    differs "length-delimited mount spelling"
        (makeCorpusManifest rootAddress ["pro", "jectlibrary"] sourceInputs)
  where
    baseManifest = makeCorpusManifest rootAddress mountOrder sourceInputs

normalizesBoundaryFixture :: Assertion
normalizesBoundaryFixture =
    withCandidateSource "boundary.tex" boundarySource \candidate -> do
        outcomes <- observeCandidate
            VerificationCompletionCase
            [candidate]
        assertEqual
            "normalized verification boundary"
            [ ( candidateSourceAddress candidate
              , NormalizedVerificationSuccess
                    [ NormalizedLocated
                        (NormalizedSourceLocation 0 1 1)
                        "base.tex"
                        NormalizedNoSpace
                    ]
                    ["base.tex"]
                    [ NormalizedPragma
                        (NormalizedSourceLocation 0 2 2)
                        NormalizedRightAssociative
                        7
                    ]
                    []
              )
            ]
            outcomes
  where
    boundarySource = "\\import{base.tex}\r\n\t%! infixr 7\r\n"

keepsMalformedPragmasModeSpecific :: Assertion
keepsMalformedPragmasModeSpecific =
    withCandidateSource "malformed-pragma.tex" "%! infixl 8\n" \source -> do
        prefix <- observeCandidate PrefixCase [source]
        verification <- observeCandidate VerificationCompletionCase [source]
        presentation <- observeCandidate PresentationDecodedCase [source]
        let address = candidateSourceAddress source
        assertEqual
            "prefix does not interpret pragma candidates"
            [(address, NormalizedPrefixSuccess [])]
            prefix
        assertEqual
            "verification rejects the pragma"
            [(address, snd expectedFailure)]
            verification
        assertEqual
            "presentation treats the malformed pragma as a comment"
            [(address, NormalizedPresentationSuccess [])]
            presentation
  where
    expectedFailure =
        ( fixtureAddress
        , NormalizedSourceFailure
            NormalizedFailure
                { normalizedFailurePhase = "pragma"
                , normalizedFailureKind = "level-out-of-range"
                , normalizedFailureLocation =
                    Just (NormalizedSourceLocation 0 1 1)
                , normalizedFailureDetails = []
                }
        )

normalizedFailuresIgnoreSourceLabels :: Assertion
normalizedFailuresIgnoreSourceLabels = do
    first <- observeSource "first.tex"
    second <- observeSource "second.tex"
    assertEqual "physical source labels are not semantic observations"
        (snd <$> first) (snd <$> second)
  where
    malformedImport = "\\import{}\n"
    observeSource label =
        withCandidateSource label malformedImport \candidate ->
            observeCandidate PrefixCase [candidate]

candidateCommitsRecognizedFormalEnvironments :: Assertion
candidateCommitsRecognizedFormalEnvironments =
    forM_ committedFailures \(label, source, column, unexpected) ->
        withCandidateSource label source \candidate -> do
            assertCandidateFailure
                VerificationCompletionCase
                "verification-tokenization"
                column
                unexpected
                candidate
            assertCandidateFailure
                PresentationDecodedCase
                "presentation-document"
                column
                unexpected
                candidate
  where
    committedFailures =
        [ ( "committed-empty-label.tex"
          , "\\begin{axiom}\\label{}"
          , 21
          , "}"
          )
        , ( "committed-tab.tex"
          , "\\begin{axiom}\t\\end{axiom}"
          , 14
          , "\t"
          )
        ]

assertCandidateFailure
    :: ObservationCase
    -> Text
    -> Int
    -> Text
    -> CandidateSourceInput
    -> Assertion
assertCandidateFailure selectedCase phase column unexpected candidate = do
    outcomes <- observeCandidate selectedCase [candidate]
    assertEqual
        "committed formal failure"
        [ ( candidateSourceAddress candidate
          , NormalizedSourceFailure
                NormalizedFailure
                    { normalizedFailurePhase = phase
                    , normalizedFailureKind = "unexpected-input"
                    , normalizedFailureLocation =
                        Just (NormalizedSourceLocation 0 1 column)
                    , normalizedFailureDetails = [unexpected]
                    }
          )
        ]
        outcomes

completeVerificationPreservesPragmaPrecedence :: Assertion
completeVerificationPreservesPragmaPrecedence = do
    case scanCompleteVerificationText anonymousSourceDescriptor label source of
        Left
            (SourceInputFailure
                (VerificationPragmaFailure
                    (InvalidSyntaxPragma _location problem))) ->
                        assertEqual
                            "malformed pragma wins over prefix rejection"
                            SyntaxPragmaLevelOutOfRange
                            problem
        Left failure ->
            assertFailure
                ("expected candidate pragma failure, got " <> show failure)
        Right verification ->
            assertFailure
                ("expected candidate rejection, got " <> show verification)
  where
    label = "complete-prefix-pragma.tex"
    source = "\\import{}\n%! infixl 8\n"

lateImportFailureRetainsCommittedOffset :: Assertion
lateImportFailureRetainsCommittedOffset =
    withCandidateSource label source \candidate -> do
        outcomes <- observeCandidate VerificationCompletionCase [candidate]
        case outcomes of
            [(_address, NormalizedSourceFailure failure)] -> do
                assertEqual
                    "late import fails after the reserved prefix"
                    (Just (NormalizedSourceLocation 0 3 9))
                    (normalizedFailureLocation failure)
                assertEqual
                    "late import remains an explicit lexer failure"
                    "explicit-failure"
                    (normalizedFailureKind failure)
            _ ->
                assertFailure
                    ("expected one normalized late-import failure, got "
                        <> show outcomes)
  where
    label = "late-import-offset.tex"
    source = Text.unlines
        [ "\\import{base.tex}"
        , "\\section{Body}"
        , "\\import{late.tex}"
        ]

developerTokenScanIgnoresMalformedPragmas :: Assertion
developerTokenScanIgnoresMalformedPragmas =
    withCandidateSource label source \candidate -> do
        let identified = candidateSourceIdentified candidate
        candidateChunks <- case scanCompleteSourceTokens identified of
            Left failure ->
                assertFailure
                    ("candidate token scan failed: " <> show failure)
            Right chunks -> do
                _ <- evaluate (forceSourceTokenChunksHandoff chunks)
                pure chunks
        assertEqual
            "malformed pragma line is uninterpreted token trivia"
            [[BeginEnv "axiom", EndEnv "axiom"]]
            (fmap unLocated <$> candidateChunks)
  where
    label = "token-pragma.tex"
    source = Text.unlines
        [ "%! infixl 8"
        , "\\begin{axiom}\\end{axiom}"
        ]

bindsSemanticObservationComponents :: Assertion
bindsSemanticObservationComponents = do
    let corpusDigest = corpusManifestDigest baseManifest
        secondAddress = LogicalSourceAddress "fixture" "second.tex"
        firstOutcome = NormalizedPrefixSuccess []
        secondOutcome =
            NormalizedPrefixSuccess
                [ NormalizedLocated
                    (NormalizedSourceLocation 1 2 3)
                    "dependency.tex"
                    NormalizedSpace
                ]
        outcomes =
            [ (fixtureAddress, firstOutcome)
            , (secondAddress, secondOutcome)
            ]
        baseline = compactCaseRecord PrefixCase corpusDigest outcomes
        differs description record =
            assertBool description
                ( compactAggregateDigest baseline
                    /= compactAggregateDigest record
                )
    assertEqual "retains corpus identity"
        corpusDigest
        (compactCorpusDigest baseline)
    differs "case tag"
        (compactCaseRecord PresentationDecodedCase corpusDigest outcomes)
    differs "logical source address"
        (compactCaseRecord
            PrefixCase
            corpusDigest
            [ (LogicalSourceAddress "other" "source.tex", firstOutcome)
            , (secondAddress, secondOutcome)
            ])
    differs "source outcome"
        (compactCaseRecord
            PrefixCase
            corpusDigest
            [ (fixtureAddress, NormalizedPrefixSuccess
                    [ NormalizedLocated
                        (NormalizedSourceLocation 0 1 1)
                        "changed.tex"
                        NormalizedNoSpace
                    ])
            , (secondAddress, secondOutcome)
            ])
    differs "source order"
        (compactCaseRecord PrefixCase corpusDigest (reverse outcomes))
  where
    baseManifest = makeCorpusManifest rootAddress mountOrder sourceInputs

observeCandidate
    :: ObservationCase
    -> [CandidateSourceInput]
    -> IO [(LogicalSourceAddress, NormalizedSourceOutcome)]
observeCandidate selectedCase sources = do
    raw <- either (assertFailure . Text.unpack) pure
        (runCandidateCase selectedCase sources)
    _ <- evaluate (forceCandidateCaseResult raw)
    either (assertFailure . Text.unpack) pure
        (normalizeCandidateCaseResult sources raw)

withCandidateSource
    :: FilePath
    -> Text
    -> (CandidateSourceInput -> IO value)
    -> IO value
withCandidateSource relative source action =
    Temp.withSystemTempDirectory "felix-source-scan-candidate" \root -> do
        ByteString.writeFile (root </> relative) (Text.encodeUtf8 source)
        mounts <- expectRight
            =<< prepareSourceMounts [(sourceMountId "fixture", root)]
        request <- expectRight (searchedRoot relative)
        loaded <- expectRight =<< resolveAndLoadRoot mounts request
        identified <- identifyLoadedSource loaded
        let address = LogicalSourceAddress "fixture" (Text.pack relative)
        action (CandidateSourceInput address identified)

expectRight :: (Show error, HasCallStack) => Either error value -> IO value
expectRight = \case
    Left failure ->
        assertFailure ("expected Right, got Left " <> show failure)
    Right value -> pure value

fixtureAddress :: LogicalSourceAddress
fixtureAddress = LogicalSourceAddress "fixture" "source.tex"

manifestWithPaths :: FilePath -> FilePath -> CorpusManifest
manifestWithPaths projectPath libraryPath =
    makeCorpusManifest
        rootAddress
        mountOrder
        [ firstInput{manifestInputReadPath = projectPath}
        , secondInput{manifestInputReadPath = libraryPath}
        ]

rootAddress :: LogicalSourceAddress
rootAddress = LogicalSourceAddress "project" "root.tex"

mountOrder :: [Text]
mountOrder = ["project", "library"]

sourceInputs :: [ManifestSourceInput]
sourceInputs = [firstInput, secondInput]

firstInput :: ManifestSourceInput
firstInput =
    ManifestSourceInput
        (LogicalSourceAddress "library" "base.tex")
        "/work/library/base.tex"
        "base"

secondInput :: ManifestSourceInput
secondInput =
    ManifestSourceInput
        rootAddress
        "/work/root.tex"
        "root"
