{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Module.Notion (fastTests, acceptanceTests) where

import Base
import Felix.Cache.Codec
import Felix.Parsed.Payload qualified as Payload
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.FinalPrelude qualified as FinalPrelude
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Module
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Notion.WholePattern qualified as WholePattern
import Felix.Checking.Notion.Registration qualified as Registration
import Felix.Checking.Notion.Rule qualified as FormationRule
import Felix.Checking.Notion.Diagnostics qualified as FormationDiagnostics
import Felix.Checking.Notion.Catalog qualified as FormationCatalog
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Semantic qualified as Semantic
import Felix.Module (moduleName, moduleNameFromParts, moduleNameNamespace)
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Source
import Felix.Store qualified as Store
import Felix.Syntax.Abstract qualified as Raw
import Felix.Verification qualified as Verification
import Felix.Test.Support.FormationReference qualified as Reference
import Felix.Test.Support.FormationProduction qualified as Production
import Felix.Test.Support.FormationReferenceImports qualified as ReferenceImports
import Felix.Test.Support.FormationReferenceReplay (checkImportedReferenceReplay, checkScopedReferenceReplay)
import Felix.Test.Support.FormationReferenceScope qualified as ReferenceScope
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Test.Support.Imports (admitTestModule)
import Felix.Test.Unit.Module.Support

import Control.Exception (bracket)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Control.Monad (foldM, when)
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Planning qualified as Planning
import Data.ByteString qualified as ByteString
import Data.Either (isLeft)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as StrictText
import Data.Text.Encoding qualified as Text
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import System.Directory (getCurrentDirectory)
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import Test.Tasty
import Test.Tasty.HUnit


fastTests :: [TestTree]
fastTests =
    [ testCase "replays real registrations through the finite formation reference" replaysImportedFormationReference
    , testCase "preserves written structure parameters through elaboration" preservesStructureParameters
    , testCase "bounds duplicating declarations and rich abbreviation uses" boundsRichAbbreviationExpansion
    , testCase "rotates recursive scoped alternatives beside an easy proof" checksScopedFairness
    , testCase "shares exact declaration descriptions while retaining their checked sources" deduplicatesDeclarationDescriptions
    , testCase "groups repeated contract leaves without supplying their siblings" checksGroupedFormationContracts
    , testCase "retains preparation after an early group answer" checksMixedGroupPreparation
    , testCase "checks set-valued term formation contracts"
        checksSetTermFormationContracts
    , testCase "instantiates earlier quantified headers with scoped membership evidence"
        checksQuantifiedHeaderFormation
    , testCase "scoped universals preserve bounds and discharge weaker guards" checksSuppliedUniversalRejections
    , testCase "compiles hosted definition conjunctions left to right"
        checksHostedDefinitionConjunctionGuards
    , testCase "uses expanded predicates as whole rule premises"
        usesExpandedWholePremises
    , testCase "projects quantified results while preserving whole authority boundaries"
        preservesWholeAuthorityBoundaries
    , testCase "uses conclusion-determined conjunctive finite-evidence rules"
        usesCompositeProductRule
    , testCase "joins direct finite-evidence rows"
        joinsDirectFiniteEvidenceRows
    , testCase "joins provider and exact-alias finite-evidence rows"
        joinsProviderAndAliasFiniteEvidenceRows
    , testCase "uses the exact graph-domain bridge"
        usesGraphDomainBridge
    , testCase "expands identity abbreviations without a provider"
        preservesTransparentIdentityProviders
    , testCase "uses exact named relations throughout notion reasoning"
        usesExactNamedRelationNotions
    , testCase "uses exact named verbs throughout notion reasoning"
        usesExactNamedVerbNotions
    , testCase "expands verb abbreviations through their body evidence"
        expandsVerbAbbreviations
    , testCase "registers the algebra vocabulary contract"
        registersAlgebraVocabularyContract
    , testCase "preserves hosted contract and base-projection order"
        preservesHostedContractAndBaseProjectionOrder
    , testCase "publishes prefix-definition notion projections"
        publishesPrefixDefinitionProjections
    , testCase "composes positive definitions across predicate surfaces"
        composesPositiveDefinitions
    , testCase "registers provider-result theorems"
        registersProviderResultTheorems
    , testCase "uses unconditional provider-result theorems"
        usesUnconditionalProviderResultTheorems
    , testCase "classifies closed named providers"
        classifiesClosedNamedProviders
    , testCase "registers checked definition results"
        registersCheckedDefinitionResults
    , testCase "registers multi-atomic definition results"
        registersMultiAtomicDefinitionResults
    , testCase "registers verbal definition results"
        registersVerbalDefinitionResults
    , testCase "groups ordinary phrase residuals once"
        groupsOrdinaryPhraseResiduals
    , testCase "uses completed heads only for the explicit residual"
        checksCompletedPhraseHeads
    , testCase "bounded nouns stage evidence before independent modifiers"
        checksBoundedNounEvidence
    , testCase "accounts provider depth and bucket width"
        accountsProviderDepthAndBucketWidth
    , testGroup "elaborates distinct notion heads across active sources"
        (distinctNotionHeadElaborationCase <$> [4, 16, 64])
    ]

acceptanceTests :: [TestTree]
acceptanceTests =
    [ hostedPredicateFormationTests
    , testCase "checks maintained library provider contracts"
        checksLibraryProviderFormationContracts
    , testCase "checks readability vocabulary expansions"
        checksReadabilityVocabulary
    , testCase "checks bounded noun statement equivalences"
        checksBoundedNounEquivalences
    , testCase "uses the generic typed-image rule"
        usesTypedImageFiniteEvidence
    , testCase "uses direct function endpoint consumers"
        usesDirectEndpointConsumers
    , testCase "invalidates formation snapshots when registrations change"
        invalidatesFormationSnapshots
    , testCase "checks neighbourhood guards in their ordinary imported environment"
        usesNeighbourhoodFormation
    , testCase "checks psi-space headers in their ordinary imported environment" usesPsiSpaceFormation
    , testCase "checks f-adic guards in their ordinary imported environment"
        usesFAdicFormation
    , testCase "rejects inexact, negated, and dynamic relation evidence"
        rejectsInexactRelationEvidence
    , testCase "uses only positive exact verb evidence"
        usesOnlyPositiveExactVerbEvidence
    , testCase "uses exact source-terminal prefix predicates"
        usesExactSourceTerminalPrefixPredicates
    , testCase "expands atomic and compound verb abbreviation evidence"
        expandsVerbAbbreviationEvidence
    , testCase "uses explicit-field endpoint consumers"
        usesFieldEndpointConsumers
    , testCase "transports exact compiler-owned local aliases"
        checksExactLocalAliases
    , testCase "transports logical notions across checked equality"
        transportsNotionsAcrossEquality
    , testCase "uses finite-set provider-result theorems"
        usesFiniteSetProviderResultTheorems
    , testCase "caches unconditional provider-result theorems"
        cachesUnconditionalProviderResultTheorems
    , testCase "replays whole contracts and supplied universal goals" checksSuppliedConstructionContract
    , testCase "caches complete supplied universal premises"
        (cachesProviderClassification "notion-supplied-universal")
    , testCase "caches ordered exact classification bundles"
        (cachesProviderClassification "notion-classification-bundle")
    , testCase "elaborates rich open-structure phrases"
        elaboratesRichOpenStructurePhrases
    , testCase "caches checked definition results"
        cachesCheckedDefinitionResults
    , testCase "caches prefix-definition notion projections"
        cachesPrefixDefinitionProjections
    , testCase "uses verbal definition results"
        usesVerbalDefinitionResults
    , testCase "diagnoses invalid definition results"
        diagnosesInvalidDefinitionResults
    , testCase "keeps definition results on their exact provider"
        keepsDefinitionResultsOnExactProvider
    , testCase "uses fixed intrinsic provider classifications"
        usesIntrinsicProviderClassifications
    , testCase "distinguishes nullary classification failures"
        distinguishesNullaryClassificationFailures
    , testCase "handles repeated same-head notion queries"
        handlesRepeatedSameHeadNotionQueries
    , testCase "replays whole library chains through formation consumers"
        replaysWholeLibraryChains
    , testCase "composes indexed library contracts and widens codomains" checksScopedLibraryGoals
    , testCase "transports whole definition result annotations" checksWholeResultAnnotations
    , testCase "joins explicit signed evidence through real consumers" checksSignedGoals
    , testCase "introduces scoped whole goals for proofs contracts and premises" checksScopedGoals
    , testCase "replays disjunction and guarded biconditional reasoning" checksConnectiveGoals
    , testCase "finds finite witnesses in the ordinary choice environment" checksFiniteWitnesses
    , testCase "freezes independent whole-source inputs before clause evaluation" checksWholeSourceSupport
    , testCase "eliminates imported quantified definitions for ordinary consumers"
        replaysQuantifiedDefinitions
    , testCase "replays closed and anchored whole classifications"
        replaysWholeClassifications
    , testCase "proves source-preserved atomic and whole goals by notion"
        provesAtomicGoalsByNotion
    , testCase "diagnoses unavailable atomic and whole notion proofs"
        diagnosesNotionProofFailures
    ]

replaysWholeLibraryChains :: Assertion
replaysWholeLibraryChains =
    withAcceptedFixtureVampire "notion-whole-library-chains" \prover ->
        withFreshVerificationSession \session ->
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover "test/phase9/notion-whole-library-chains.tex" >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("whole library consumer/replay failed: " <> show result)

checksScopedLibraryGoals :: Assertion
checksScopedLibraryGoals =
    withAcceptedFixtureVampire "notion-horn-scoped-library" \prover ->
        checkFileFresh prover "test/phase9/notion-horn-scoped-library.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _) -> pure ()
            result -> assertFailure ("scoped library consumer/replay failed: " <> show result)

checksWholeResultAnnotations :: Assertion
checksWholeResultAnnotations =
    withAcceptedFixtureVampire "notion-horn-results" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        prelude <- Temp.withSystemTempDirectory "contextual-result-prelude" \directory ->
            bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store ->
                    expectRightIO (acquireFinalPreludeSession store foundation resolver)
        workspace <- parseFinalWorkspace prelude mounts "test/phase9/notion-definition-result-contextual.tex"
        modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
        root <- case reverse modules of
            current:_ -> pure current
            [] -> fail "contextual result compiled no module"
        let results = [rule
                | batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix root)
                , Semantic.Registration _ _ (Semantic.RegisterWholeConclusion rule) <-
                    Semantic.declarationDeltaRegistrations (Commit.committedBatchDelta batch)]
        assertEqual "the contextual annotation publishes its whole result, independently of reflexive consumers"
            [2] (Semantic.wholeConclusionArity <$> results)
        withFreshVerificationSession \session -> do
            for_ ["test/phase9/notion-horn-results.tex", "test/phase9/notion-definition-result-contextual-import.tex"] \relative ->
                for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                    checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests prover relative >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure (relative <> ": whole result annotation/replay failed: " <> show result)
            for_ ["partial"] \name ->
                checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-definition-result-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("supported result phrase failed: " <> show result)
            -- The modified phrase parses, but its named adjective has no
            -- classification from the header. Definition views remain forward.
            checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                prover "test/phase9/notion-definition-result-modified.tex" >>= \case
                    Right (Verification.VerificationCheckingFailure _
                        (Verification.VerificationTypedModuleError _ failure _), _) ->
                            assertBool ("unexpected annotation rejection: " <> show failure)
                                ("ElaborationDefinitionResultUnavailable" `StrictText.isInfixOf` StrictText.pack (show failure))
                    result -> assertFailure ("an unsupported adjective acquired its converse definition: " <> show result)

checksSignedGoals :: Assertion
checksSignedGoals =
    withAcceptedFixtureVampire "notion-horn-signed" \prover ->
        withFreshVerificationSession \session -> do
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover "test/phase9/notion-horn-signed.tex" >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("signed Horn consumer/replay failed: " <> show result)
            for_ ["missing", "direction", "contradiction"] \name ->
                checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-horn-signed-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCheckingFailure _
                            (Verification.VerificationTypedModuleError _ failure _), _) ->
                            assertBool ("unexpected signed rejection: " <> show failure)
                                ("ProofNotionUnavailable" `StrictText.isInfixOf` StrictText.pack (show failure))
                        result -> assertFailure ("signed inference accepted " <> name <> ": " <> show result)

checksScopedGoals :: Assertion
checksScopedGoals =
    withAcceptedFixtureVampire "notion-horn-scoped" \prover ->
        withFreshVerificationSession \session -> do
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover "test/phase9/notion-horn-scoped-recursive.tex" >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("scoped Horn consumer/replay failed: " <> show result)
            for_ ["different-index", "fresh-binder", "assumption-sibling", "equality-sibling"] \name ->
                checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-horn-scoped-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCheckingFailure _
                            (Verification.VerificationTypedModuleError _ failure _), _) ->
                            assertBool ("unexpected scoped rejection: " <> show failure)
                                ("ProofNotionUnavailable" `StrictText.isInfixOf` StrictText.pack (show failure))
                        result -> assertFailure ("a scoped proof leaked into " <> name <> ": " <> show result)

checksConnectiveGoals :: Assertion
checksConnectiveGoals =
    withAcceptedFixtureVampire "notion-horn-connectives" \prover ->
        withFreshVerificationSession \session -> do
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover "test/phase9/notion-horn-connectives.tex" >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("connective inference or replay failed: " <> show result)
            for_ ["unseeded", "sibling"] \name ->
                checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-horn-connectives-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCheckingFailure _
                            (Verification.VerificationTypedModuleError _ failure _), _) ->
                            assertBool ("unexpected connective rejection: " <> show failure)
                                ("ProofNotionUnavailable" `StrictText.isInfixOf` StrictText.pack (show failure))
                        result -> assertFailure ("connective inference accepted " <> name <> ": " <> show result)

checksFiniteWitnesses :: Assertion
checksFiniteWitnesses =
    withAcceptedFixtureVampire "notion-horn-choice" \prover ->
        withFreshVerificationSession \session -> do
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                for_ ["notion-horn-existential", "notion-horn-choice", "notion-horn-positive-premises"] \name ->
                    checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                        prover ("test/phase9/" <> name <> ".tex") >>= \case
                            Right (Verification.VerificationCompleted{}, _) -> pure ()
                            result -> assertFailure ("finite witness inference or replay failed: " <> show result)
            for_ ["notion-horn-choice-missing", "notion-horn-positive-premises-missing"] \name ->
              checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                prover ("test/phase9/" <> name <> ".tex") >>= \case
                    Right (Verification.VerificationCheckingFailure _
                        (Verification.VerificationTypedModuleError _ failure _), _) ->
                        assertBool ("unexpected missing-witness rejection: " <> show failure)
                            ("ProofNotionUnavailable" `StrictText.isInfixOf` StrictText.pack (show failure))
                    result -> assertFailure ("choice acquired an unfounded witness: " <> show result)

-- A small shared query allowance must cover both the unfinished recursive
-- child and the successful sibling. Query again after admission to isolate
-- scheduling from declaration preparation, then replay the selected proof.
checksScopedFairness :: Assertion
checksScopedFairness = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    limits <- maybe (assertFailure "invalid fairness allowance" >> fail "unreachable") pure
        (Notion.formationSearchLimits 65536 65536 65536 65536 10000 256)
    let run alternatives = Temp.withSystemTempDirectory "felix-scoped-fair" \directory -> do
            writeFile (directory Posix.</> "root.tex") (source alternatives)
            mounts <- exactFixtureMounts directory
            workspace <- parseWorkspace bootstrap mounts "root.tex"
            modules <- compileParsedWorkspace foundation bootstrap workspace
            let parsed = Parsed.parsedWorkspaceRootModule workspace
            Raw.Claim assumptions conclusion <- sole "fairness consumer"
                [claim | Raw.BlockClaim _ _ _ marker claim <- Parsed.parsedModuleBlocks parsed,
                    marker == "fair_consumer"]
            driven <- expectRight =<< runModuleDriver foundation
                (moduleName (Parsed.parsedModuleAddress parsed))
                (completedModuleEvidence <$> modules) unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    prepared <- Elaboration.elaborateClaimEnvelope assumptions conclusion
                    case prepared of
                        Left failure -> pure (Left failure)
                        Right envelope -> case Elaboration.elaboratedClaimConclusionAssertions envelope of
                            [assertion] -> do
                                let context = Elaboration.elaboratedClaimContext envelope
                                    sources = [Elaboration.formationEvidenceSource
                                        (Elaboration.elaborationContextSupport context)
                                        (Elaboration.compiledHeaderCore header)
                                        (Elaboration.compiledHeaderEvidence header) ordinal
                                        Elaboration.FormationProofAssumption
                                        | (ordinal, header) <- zip [0..] (Elaboration.elaboratedClaimAntecedents envelope)]
                                active <- either (error . show) pure
                                    (foldM (flip Elaboration.addFormationPremiseSource) context sources)
                                result <- Elaboration.elaborateProofNotionEvidenceWithBudget
                                    (Notion.initialFormationSearchBudget limits) active Nowhere assertion
                                case result of
                                    Right (Elaboration.NotionQueryFound evidence, budget) -> do
                                        closure <- Declaration.checkedObjectClosureLowering
                                        replayed <- Declaration.replayTransientFormationLowering closure evidence
                                            (Notion.sourceAssertionFormula assertion)
                                        pure (Right (budget, replayed))
                                    Left failure -> pure (Left failure)
                                    Right (Elaboration.NotionQueryUnavailable failure, _) ->
                                        error ("scoped fairness query failed: " <> show failure)
                            _ -> error "fairness consumer lost its atomic goal")
            case driven of
                Declaration.DriverSucceeded (Right (budget, replayed)) _ _ -> do
                    void (expectRight replayed)
                    pure (Map.findWithDefault 0 FormationDiagnostics.LeafSearch
                        (FormationDiagnostics.operationCounts (Notion.formationSearchBudgetDiagnostics budget)))
                _ -> assertFailure "scoped fairness consumer failed" >> fail "unreachable"
    baseline <- run [easy]
    for_ [[recursive, easy], [easy, recursive]] \alternatives -> do
        searches <- run alternatives
        assertBool ("recursive child must actually start: " <> show (baseline, searches))
            (searches > baseline)
  where
    source alternatives = unlines
        ([ "\\begin{definition}\\label{fair_primary}"
         , "    $X$ is a fair primary iff $X=\\emptyset$."
         , "\\end{definition}"
         , "\\begin{definition}\\label{fair_complete}"
         , "    $X$ is a fair complete iff $X=X$."
         , "\\end{definition}"
         ] <> concat alternatives <>
         [ "\\begin{proposition}\\label{fair_consumer}"
         , "    Let $A$ be a fair primary."
         , "    Then $A$ is a fair complete."
         , "\\end{proposition}"
         , "\\begin{proof}"
         , "    Follows by notion."
         , "\\end{proof}"
         ])
    classification label premise =
        [ "\\begin{classification}\\label{" <> label <> "}"
        , "    Suppose for every $x$ we have " <> premise <> "."
        , "    Then $A$ is a fair complete."
        , "\\end{classification}"
        , "\\begin{proof}"
        , "    Follows by \\obv{fair_complete}."
        , "\\end{proof}"
        ]
    recursive = classification "fair_recursive" "$(A,x)$ is a fair complete"
    easy = classification "fair_easy" "$A$ is a fair primary"

checksWholeSourceSupport :: Assertion
checksWholeSourceSupport =
    withAcceptedFixtureVampire "notion-horn-whole-source-support" \prover ->
        withFreshVerificationSession \session ->
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
              for_ ["whole-source-support","whole-template-support","partial-equality"] \name ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-horn-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("whole-source support/replay failed: " <> show result)

replaysQuantifiedDefinitions :: Assertion
replaysQuantifiedDefinitions =
    withAcceptedFixtureVampire "notion-horn-quantified" \prover ->
        withFreshVerificationSession \session ->
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
              for_ ["quantified","monoid-unit"] \name ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-horn-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("quantified source consumer/replay failed: " <> show result)

replaysWholeClassifications :: Assertion
replaysWholeClassifications =
    withAcceptedFixtureVampire "notion-whole-classification" \prover ->
        withFreshVerificationSession \session ->
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover "test/phase9/notion-whole-classification.tex" >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("whole classification/replay failed: " <> show result)

provesAtomicGoalsByNotion :: Assertion
provesAtomicGoalsByNotion =
    withAcceptedFixtureVampire "notion-by-notion" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        Temp.withSystemTempDirectory "felix-notion-proof" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                (\store -> do
                    fresh <- verify store Verification.FreshStoreValidation prover
                    expectCompletedWithGap "fresh" fresh
                    warm <- verify store Verification.WarmStoreValidation prover
                    expectCompletedWithGap "warm" warm)
  where
    verify store mode prover =
        checkFileWithStore
            store
            mode
            ignoredVerificationRequests
            prover
            "test/phase9/notion-by-notion.tex"

    expectCompletedWithGap pass = \case
        Right
            (Verification.CompletedWithExplicitGaps report _presentation,
                _slowReport) ->
            assertEqual
                (pass <> " notion proof fixture has one deliberate gap")
                1
                (length (Verification.verificationDirectEscapes report))
        Right result ->
            assertFailure
                (pass <> " notion proof fixture failed: " <> show result)
        Left failure ->
            assertFailure
                (pass <> " notion proof fixture did not run: " <> show failure)

diagnosesNotionProofFailures :: Assertion
diagnosesNotionProofFailures =
    withAcceptedFixtureVampire "notion-by-notion-failures" \prover -> do
        -- Implication introduction now reuses its scoped whole hypothesis.
        checkFileFresh prover "test/phase9/notion-by-notion-unsupported.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _) -> pure ()
            result -> assertFailure ("introduced whole implication failed: " <> show result)
        checkFailure
            prover
            "test/phase9/notion-by-notion-unavailable.tex"
            \case
                Proof.ProofNotionUnavailable location failure -> do
                    assertEqual "unavailable notion proof line"
                        11 (locLine location)
                    let rendered =
                            Elaboration.renderNotionQueryFailure failure
                    assertBool "unavailable diagnostic names the goal"
                        ("X is a notion unavailable alias"
                            `StrictText.isInfixOf` rendered)
                    assertBool "unavailable diagnostic suggests an explicit fact"
                        ("Prove the missing notion explicitly"
                            `StrictText.isInfixOf` rendered)
                failure ->
                    assertFailure
                        ("unavailable notion goal failed differently: "
                            <> show failure)
  where
    checkFailure prover relative check =
        checkFileFresh prover relative >>= \case
            Right
                ( Verification.VerificationCheckingFailure _report
                    (Verification.VerificationTypedModuleError
                        _source
                        (Module.TypedActionFailed
                            (Module.TypedProofFailed failure))
                        _prefix)
                , _slowReport
                ) -> check failure
            Right result ->
                assertFailure
                    (relative <> ": notion proof failure was not retained: "
                        <> show result)
            Left failure ->
                assertFailure
                    (relative <> ": notion proof fixture did not run: "
                        <> show failure)

usesExpandedWholePremises :: Assertion
usesExpandedWholePremises = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-transparent-head.tex"
    compiled <- compileParsedWorkspace foundation bootstrap workspace
    assertBool "transparent notion fixture compiled" (not (null compiled))

preservesWholeAuthorityBoundaries :: Assertion
preservesWholeAuthorityBoundaries = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace bootstrap mounts "test/phase9/notion-whole-boundaries.tex"
    dependencies <- compileParsedWorkspace foundation bootstrap workspace
    quantified <- parseWorkspace bootstrap mounts "test/phase9/notion-whole-derived-universal.tex"
    void (compileParsedWorkspace foundation bootstrap quantified)
    for_ ["derived-equality", "transport-abbreviation", "transport-expansion"] \name -> do
        rejected <- parseWorkspace bootstrap mounts ("test/phase9/notion-whole-" <> name <> ".tex")
        input <- expectRightIO (typedModuleInput foundation
            (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule rejected) dependencies)
        runTypedModule input >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed
                (Module.TypedProofFailed Proof.ProofNotionUnavailable{})) _ -> pure ()
            Module.TypedModuleFailed failure _ -> assertFailure (name <> ": " <> show failure)
            Module.TypedModuleOpenFailed failure -> assertFailure (name <> ": " <> show failure)
            Module.TypedModuleSucceeded{} -> assertFailure (name <> ": a whole result acquired an atomic capability")

usesCompositeProductRule :: Assertion
usesCompositeProductRule = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-composite-product.tex"
    modules <- withAcceptedFixtureVampire "notion-composite-product" \prover ->
        compileParsedWorkspaceWithResolver
            foundation
            bootstrap
            (Declaration.vampireResolver
                (Provers.runPreparedTypedProver prover))
            workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "composite notion fixture compiled no module"
            >> fail "unreachable"
    let rules =
            [ rule
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterFiniteEvidence rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
    assertEqual "the product theorems register two generic rules"
        2 (length rules)
    assertBool "the theorem premise grouping is retained"
        (all (not . null . Semantic.checkedNotionRulePremises . Semantic.finiteEvidenceSkeleton) rules)

joinsDirectFiniteEvidenceRows :: Assertion
joinsDirectFiniteEvidenceRows = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-finite-evidence-direct.tex"
    modules <- withAcceptedFixtureVampire "notion-finite-evidence-direct" \prover ->
        compileParsedWorkspaceWithResolver
            foundation
            bootstrap
            (Declaration.vampireResolver
                (Provers.runPreparedTypedProver prover))
            workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "finite-evidence fixture compiled no module"
            >> fail "unreachable"
    let rules =
            [ rule
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterFiniteEvidence rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
    assertBool "the direct and row-safe classifications retain their clauses" (length rules >= 2)
    let views =
            [ view
            | batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix root)
            , view <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry]) (Commit.committedBatchDelta batch)
            ]
    assertBool "an erased-parameter unary result may reconstruct a powerset"
        (any (\view -> case Semantic.notionViewConclusion view of
            Semantic.AtomicLeaf (Semantic.GlobalAtomTemplate _ arguments) -> any (\case
                Semantic.TemplateProvider
                    (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) _ -> True
                _ -> False) arguments
            _ -> False) views)

joinsProviderAndAliasFiniteEvidenceRows :: Assertion
joinsProviderAndAliasFiniteEvidenceRows = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts
        "test/phase9/notion-finite-evidence-provider-alias.tex"
    modules <- withAcceptedFixtureVampire
        "notion-finite-evidence-provider-alias" \prover ->
            compileParsedWorkspaceWithResolver
                foundation
                bootstrap
                (Declaration.vampireResolver
                    (Provers.runPreparedTypedProver prover))
                workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure
            "finite provider/alias fixture compiled no module"
            >> fail "unreachable"
    let clauses =
            [ rule
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterFiniteEvidence rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
    assertBool "provider and alias consumers register generic clauses"
        (length clauses >= 2)

usesTypedImageFiniteEvidence :: Assertion
usesTypedImageFiniteEvidence =
    withAcceptedFixtureVampire "notion-typed-image" \prover -> do
        withFreshVerificationSession \session -> do
            -- A checked definition view supplies the deferred function row;
            -- the finite evaluator may use that row in the typed-image rule.
            for_ [ (Verification.FreshStoreValidation, "test/phase9/notion-typed-image.tex")
                 , (Verification.WarmStoreValidation, "test/phase9/notion-typed-image-base-demand.tex")
                 ] \(mode, relative) ->
              check session mode prover relative >>= \case
                    Right (Verification.VerificationCompleted{}, _slowReport) ->
                        pure ()
                    Right result ->
                        assertFailure
                            (relative <> ": typed-image fixture failed: " <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": typed-image fixture did not run: "
                                <> show failure)
            let relative = "test/phase9/notion-typed-image-missing-subset.tex"
            check session Verification.WarmStoreValidation prover relative >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source actionFailure _prefix)
                    , _slowReport
                    )
                        | missingFormationRequirement actionFailure -> pure ()
                Right result ->
                    assertFailure
                        (relative <> ": typed-image boundary failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        (relative <> ": typed-image boundary did not run: "
                            <> show failure)
  where
    check session mode prover =
        checkFileWithSession
            session mode testSequentialJobs ignoredVerificationRequests
            prover

    missingFormationRequirement = \case
        Module.TypedActionFailed
                (Module.TypedElaborationFailed
                    Elaboration.ElaborationFormationRequirementMissing{}) ->
            True
        Module.TypedActionFailed
                (Module.TypedProofFailed
                    (Proof.ProofElaborationFailed
                        Elaboration.ElaborationFormationRequirementMissing{})) ->
            True
        _ -> False

usesGraphDomainBridge :: Assertion
usesGraphDomainBridge = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-graph-domain.tex"
    modules <- withAcceptedFixtureVampire "notion-graph-domain" \prover ->
        compileParsedWorkspaceWithResolver
            foundation
            bootstrap
            (Declaration.vampireResolver
                (Provers.runPreparedTypedProver prover))
            workspace
    let rules =
            [ rule
            | current <- modules
            , batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix current)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterGraphDomain rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
    assertEqual "the fixture registers one graph-domain rule"
        1 (length rules)

invalidatesFormationSnapshots :: Assertion
invalidatesFormationSnapshots =
    withAcceptedFixtureVampire "notion-snapshot-invalidation" \prover ->
        checkFileFresh prover "test/phase9/notion-snapshot-invalidation.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _) -> pure ()
            result -> assertFailure ("formation snapshot invalidation failed: " <> show result)

usesNeighbourhoodFormation :: Assertion
usesNeighbourhoodFormation =
    withAcceptedFixtureVampire "notion-neighbourhood-formation-cost" \prover ->
        checkFileFresh prover "test/phase9/notion-neighbourhood-formation-cost.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _) -> pure ()
            result -> assertFailure ("neighbourhood formation fixture failed: " <> show result)

usesPsiSpaceFormation :: Assertion
usesPsiSpaceFormation =
    withAcceptedFixtureVampire "notion-psi-space-formation-cost" \prover ->
        checkFileFresh prover "library/topology/psi-space.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _) -> pure ()
            result -> assertFailure ("psi-space formation route failed: " <> show result)

usesFAdicFormation :: Assertion
usesFAdicFormation =
    withAcceptedFixtureVampire "notion-f-adic-formation-cost" \prover ->
        checkFileFresh prover "library/topology/topological-ring-f-adic.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _) -> pure ()
            result -> assertFailure ("f-adic formation route failed: " <> show result)

usesDirectEndpointConsumers :: Assertion
usesDirectEndpointConsumers =
    withAcceptedFixtureVampire "notion-endpoint-direct" \prover ->
        checkFileFresh prover "test/phase9/notion-endpoint-direct.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _slowReport) ->
                pure ()
            Right result ->
                assertFailure
                    ("the direct endpoint fixture failed: " <> show result)
            Left failure ->
                assertFailure
                    ("the direct endpoint fixture did not run: " <> show failure)

preservesStructureParameters :: Assertion
preservesStructureParameters = do
    foundation <- expectRight Foundation.checkedFoundation
    mounts <- exactFixtureMounts =<< getCurrentDirectory
    (prelude, workspace, modules) <- withAcceptedFixtureVampire "structure-parameters" \prover -> do
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        prelude <- Temp.withSystemTempDirectory "structure-parameters-prelude" \directory ->
            bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store ->
                    expectRightIO (acquireFinalPreludeSession store foundation resolver)
        workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/structure-parameter-sources.tex"
        modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
        pure (Module.finalPreludeModule prelude, workspace, modules)
    let parsed = Parsed.parsedWorkspaceRootModule workspace
        claims = [(marker, assumptions, conclusion)
            | Raw.BlockClaim _ _ _ marker (Raw.Claim assumptions conclusion) <- Parsed.parsedModuleBlocks parsed
            , marker `elem` (Raw.Marker <$> ["parameter_nested_source", "parameter_field_source", "parameter_function_source"])]
        parameter assertion = case Notion.sourceAssertionAtom assertion of
            Semantic.StructureAtomTemplate _head arguments -> sole "structure parameter" (drop 1 (toList arguments))
            _ -> fail "expected a structure assertion"
        sourceCore = Core.scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore
        pair occurrence = maybe (fail "written pair was erased") pure
            (SourceTerm.sourceTermOccurrenceOrderedPair occurrence)
    let namedDelta name = sole (StrictText.unpack name)
            [ delta
            | sealed <- modules
            , batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)
            , let delta = Commit.committedBatchDelta batch
            , any ((== Semantic.semanticName name) . Semantic.semanticAliasName) (Semantic.declarationDeltaAliases delta)]
    providerDelta <- namedDelta "parameter_provider_result"
    rule <- sole "source-aware provider result" [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations providerDelta]
    case Semantic.providerResultConclusion rule of
        Semantic.StructureAtomTemplate _ arguments -> case toList arguments of
            [Semantic.ResultRuleProviderValue, Semantic.ResultRuleTerm parameterTemplate] ->
                parameterTemplate @?= Semantic.TemplateVariable (Semantic.ViewVariableIx 2)
            _ -> fail "registered conclusion lost the expanded parameter"
        _ -> fail "registered result lost its structure predicate"
    finiteDelta <- namedDelta "parameter_finite_rule"
    assertBool "an expanded tautology remains a theorem without executable rules"
        (null (Semantic.declarationDeltaRegistrations finiteDelta))
    assertBool "the tautological theorem is still published"
        (not (null (Semantic.declarationDeltaAliases finiteDelta)))
    for_ claims \(marker, assumptions, conclusion) -> do
        driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
            (Module.sealedTypedModuleEvidence prelude : (completedModuleEvidence <$> modules))
            unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver (Elaboration.elaborateClaimEnvelope assumptions conclusion))
        envelope <- case driven of
            Declaration.DriverSucceeded result _ _ -> expectRight result
            _ -> fail "structure parameter claim did not elaborate"
        result <- sole "structure conclusion" (Elaboration.elaboratedClaimConclusionAssertions envelope)
        resultParameter <- parameter result
        header <- sole "matching last structure header"
            (take 1 (reverse (concatMap Elaboration.compiledHeaderAssertions
                (Elaboration.elaboratedClaimAntecedents envelope))))
        headerParameter <- parameter header
        let arity = fromIntegral (length (Elaboration.elaboratedClaimVariables envelope))
        headerTemplate <- expectRight (Notion.compileSourceRuleTermTemplate arity headerParameter)
        resultTemplate <- expectRight (Notion.compileSourceRuleTermTemplate arity resultParameter)
        headerTemplate @?= resultTemplate
        assertBool "parameters keep their own location, not the receiver location"
            (case SourceTerm.sourceTermOccurrencePresentation resultParameter of
                Elaboration.PresentedSourceTerm location _ -> location /= Notion.sourceAssertionLocation result
                Elaboration.LocatedSourceTerm location -> location /= Notion.sourceAssertionLocation result)
        case marker of
            Raw.Marker "parameter_nested_source" -> do
                (x, nested) <- pair resultParameter
                (keep, y) <- pair nested
                sourceCore x @?= Core.CBound 2
                sourceCore y @?= Core.CBound 1
                sourceCore keep @?= Core.CBound 2
                assertBool "the expanded identity retains no abbreviation provider"
                    (isNothing (SourceTerm.sourceTermOccurrenceProvider keep))
                Notion.compileSourceRuleTermTemplate arity x @?=
                    Right (Semantic.TemplateVariable (Semantic.ViewVariableIx 2))
                Notion.compileSourceRuleTermTemplate arity keep @?=
                    Right (Semantic.TemplateVariable (Semantic.ViewVariableIx 2))
                let opaque = SourceTerm.sourceTermOccurrence
                        (SourceTerm.sourceTermOccurrenceCore resultParameter) Core.TySet ()
                assertBool "equal Core does not recover a pair"
                    (isLeft (Notion.compileSourceRuleTermTemplate arity opaque))
            Raw.Marker "parameter_field_source" ->
                case SourceTerm.sourceTermProviderHead <$> SourceTerm.sourceTermOccurrenceProvider resultParameter of
                    Just Semantic.StructureFieldSourceProvider{} -> pure ()
                    _ -> fail "explicit field provider was erased"
            Raw.Marker "parameter_function_source" ->
                case SourceTerm.sourceTermProviderHead <$> SourceTerm.sourceTermOccurrenceProvider resultParameter of
                    Just Semantic.GlobalSourceProvider{} -> pure ()
                    _ -> fail "functional noun provider was erased"
            _ -> fail "unexpected structure parameter test claim"

preservesTransparentIdentityProviders :: Assertion
preservesTransparentIdentityProviders = do
    (_foundation, _bootstrap, _workspace, modules) <- compileFixture
        "test/phase9/notion-normalization-identity-provider.tex"
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure
            "identity-provider fixture compiled no module"
            >> fail "unreachable"
    let bindings =
            [ binding
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta batch))
            ]
        bindingLabel =
            Semantic.semanticBindingLabelText
                . Semantic.semanticGlobalBindingLabel
        bindingWithLabel :: Text -> IO Semantic.SemanticGlobalBinding
        bindingWithLabel label =
            sole (StrictText.unpack label)
                [ binding
                | binding <- bindings
                , bindingLabel binding == label
                ]
    provider <- bindingWithLabel "notion_normalization_identity_provider"
    assertEqual "an identity abbreviation retains its formal"
        (Just (Semantic.TermExpansion (Semantic.ExpansionFormal 0)))
        (Semantic.semanticGlobalBindingExpansion provider)
    member <- bindingWithLabel "notion_normalization_identity_member"
    redirected <- bindingWithLabel "notion_normalization_identity_redirected"
    normalization <- maybe
        (assertFailure "identity-member normalization was not retained"
            >> fail "unreachable")
        pure
        (Semantic.semanticGlobalBindingExpansion member)
    assertEqual "an identity abbreviation preserves the written argument"
        (Just (Semantic.MembershipAtomTemplate (Semantic.ExpansionFormal 0) (Semantic.ExpansionFormal 1)))
        (expansionAtom normalization)
    assertBool "the redirected subject also has a terminal expansion"
        (isJust (Semantic.semanticGlobalBindingExpansion redirected >>= expansionAtom))

usesExactNamedRelationNotions :: Assertion
usesExactNamedRelationNotions = do
    (_foundation, _bootstrap, _workspace, modules) <- compileFixture
        "test/phase9/notion-relation.tex"
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "relation-notion fixture compiled no module"
            >> fail "unreachable"
    let deltas =
            [ Commit.committedBatchDelta batch
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            ]
        bindings =
            [ binding
            | delta <- deltas
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment delta)
            ]
        bindingLabel =
            Semantic.semanticBindingLabelText
                . Semantic.semanticGlobalBindingLabel
        normalization label = do
            binding <- sole (StrictText.unpack label)
                [ candidate
                | candidate <- bindings
                , bindingLabel candidate == label
                ]
            maybe
                (assertFailure
                    (StrictText.unpack label <> " has no atomic normalization")
                    >> fail "unreachable")
                pure
                (Semantic.semanticGlobalBindingExpansion binding >>= expansionAtom)
        views =
            [ view
            | delta <- deltas
            , view <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry]) delta
            ]
        finiteRules =
            [ rule
            | delta <- deltas
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterFiniteEvidence rule) <- Semantic.declarationDeltaRegistrations entry]) delta
            ]

    nounAlias <- normalization "notion_relation_noun_alias"
    case nounAlias of
        Semantic.GlobalAtomTemplate
                Semantic.RelationNotionHead{}
                arguments ->
            assertEqual "noun-to-relation normalization keeps notion order"
                [0, 1, 2]
                (normalizationVariable <$> toList arguments)
        template -> assertFailure
            ("noun alias did not normalize to its relation: " <> show template)

    symbolicAlias <- normalization "notion_relation_symbolic_alias"
    assertNounTarget "relation-to-noun normalization" symbolicAlias
    symbolicChain <- normalization "notion_relation_symbolic_chain"
    assertNounTarget "terminal relation alias chain" symbolicChain

    memberAlias <- normalization "notion_relation_member_alias"
    case memberAlias of
        Semantic.MembershipAtomTemplate element set ->
            assertEqual "relation-to-membership normalization"
                [0, 1]
                (normalizationVariable <$> [element, set])
        template -> assertFailure
            ("relation alias did not normalize to membership: "
                <> show template)

    assertBool "a relation premise registers as a unary notion view"
        (any isRelationView views)
    assertBool
        ("the grouped relation classification retains two premise atoms: "
            <> show finiteRules)
        (any ((== 2) . countRelationPremises
            . Semantic.checkedNotionRulePremises
            . Semantic.finiteEvidenceSkeleton) finiteRules)
  where
    normalizationVariable = \case
        Semantic.ExpansionFormal index -> index
        term -> error ("unexpected rich normalization term: " <> show term)

    assertNounTarget label = \case
        Semantic.GlobalAtomTemplate Semantic.NounNotionHead{} arguments ->
            assertEqual label
                [1, 0, 2]
                (normalizationVariable <$> toList arguments)
        template -> assertFailure
            (label <> " has the wrong terminal template: " <> show template)

    isRelationView view = case Semantic.notionViewPremise view of
        Semantic.GlobalNotionViewPremise Semantic.RelationNotionHead{} _ -> True
        _ -> False

    countRelationPremises
        :: [Semantic.RulePremiseTree term]
        -> Int
    countRelationPremises bundles = sum (countTree <$> bundles)
    countTree :: Semantic.RulePremiseTree term -> Int
    countTree = \case
        Semantic.RulePremiseAtom
                (Semantic.GlobalAtomTemplate
                    Semantic.RelationNotionHead{} _arguments) -> 1
        Semantic.RulePremiseAtom{} -> 0
        Semantic.RulePremiseUniversal{} -> 0
        Semantic.RulePremiseResidual{} -> 0
        Semantic.RulePremiseAnd left right ->
            countTree left + countTree right

usesExactNamedVerbNotions :: Assertion
usesExactNamedVerbNotions = do
    (foundation, bootstrap, _workspace, modules) <-
        compileFixture "test/phase9/notion-verb.tex"
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "verb-notion fixture compiled no module"
            >> fail "unreachable"
    let deltas =
            [ Commit.committedBatchDelta batch
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            ]
        bindings =
            [ binding
            | delta <- deltas
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment delta)
            ]
        bindingLabel =
            Semantic.semanticBindingLabelText
                . Semantic.semanticGlobalBindingLabel
        bindingByLabel label =
            sole (StrictText.unpack label)
                [ binding
                | binding <- bindings
                , bindingLabel binding == label
                ]
        labelByKey = Map.fromList
            [ (Semantic.semanticGlobalBindingKey binding, bindingLabel binding)
            | binding <- bindings
            ]
        labelForReference reference =
            Map.lookup (Semantic.globalBindingRefKey reference) labelByKey
        views =
            [ view
            | delta <- deltas
            , view <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry]) delta
            ]
    verbBinding <- bindingByLabel "notion_verb_seal"
    case Semantic.semanticGlobalBindingKey verbBinding of
        Semantic.SemanticVerb surfaces -> do
            assertEqual "verb definition retains its singular surface"
                [ Just (Raw.Word "has")
                , Just (Raw.Word "a")
                , Just (Raw.Word "notion")
                , Just (Raw.Word "verb")
                , Just (Raw.Word "seal")
                , Just (Raw.Word "over")
                , Nothing
                ]
                (Raw.verbSurfaceSingular surfaces)
            assertEqual "verb definition retains its inferred base surface"
                [ Just (Raw.Word "have")
                , Just (Raw.Word "a")
                , Just (Raw.Word "notion")
                , Just (Raw.Word "verb")
                , Just (Raw.Word "seal")
                , Just (Raw.Word "over")
                , Nothing
                ]
                (Raw.verbSurfaceBase surfaces)
        key -> assertFailure
            ("verb definition has the wrong semantic family: " <> show key)

    guardedBinding <- bindingByLabel "notion_verb_guarded_seal"
    case Semantic.semanticGlobalBindingContract guardedBinding of
        Just contract ->
            case toList (Semantic.formationContractRequirements contract) of
                [Semantic.AtomicLeaf (Semantic.GlobalAtomTemplate
                        (Semantic.NounNotionHead reference) arguments)] -> do
                    assertEqual "hosted verb contract names its noun domain"
                        (Just "notion_verb_base")
                        (labelForReference reference)
                    assertEqual "hosted verb contract keeps its subject"
                        [0]
                        (templateVariable <$> toList arguments)
                requirements ->
                    assertFailure
                        ("unexpected hosted-verb formation contract: "
                            <> show requirements)
        Nothing -> assertFailure "hosted verb has no formation contract"

    if any (isVerbToAcceptedView labelForReference) views
        then pure ()
        else assertFailure
            ("a verb premise did not register as a unary notion view: "
                <> show views)

    repository <- getCurrentDirectory
    mounts <- exactFixtureMounts repository
    rejectedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-verb-formation-missing.tex"
    input <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule rejectedWorkspace)
            [root])
    runTypedModule input >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed actionFailure)
                prefix -> do
            (location, failure) <- case actionFailure of
                Module.TypedElaborationFailed
                        value@(
                            Elaboration.ElaborationFormationRequirementMissing
                                location _requirement) ->
                    pure (location, value)
                Module.TypedProofFailed
                        (Proof.ProofElaborationFailed
                            value@(
                                Elaboration.ElaborationFormationRequirementMissing
                                    location _requirement)) ->
                    pure (location, value)
                _ ->
                    assertFailure
                        ("hosted verb formation failed differently: "
                            <> show actionFailure)
                        >> fail "unreachable"
            assertEqual "hosted verb formation failure line" 4
                (locLine location)
            let rendered = Elaboration.renderElaborationError failure
            assertBool "formation diagnostic names the selected verb"
                ("cannot use the verb \"carries a notion verb guarded seal over _\""
                    `StrictText.isInfixOf` rendered)
            assertBool "formation diagnostic renders the noun requirement"
                ("requires that X is a notion verb base"
                    `StrictText.isInfixOf` rendered)
            assertBool "formation diagnostic names the verb declaration"
                ("selected declaration \"notion_verb_guarded_seal\""
                    `StrictText.isInfixOf` rendered)
            assertBool "failed hosted verb publishes no partial declaration"
                (null (Commit.pendingModulePrefixBatches prefix))
        Module.TypedModuleSucceeded{} ->
            assertFailure "hosted verb ignored its formation contract"
        Module.TypedModuleOpenFailed{} ->
            assertFailure "the hosted-verb failure fixture did not open"
        Module.TypedModuleFailed failure _prefix ->
            assertFailure
                ("hosted verb formation failed differently: "
                    <> StrictText.unpack
                        (Module.renderTypedModuleFailure failure))
  where
    templateVariable = \case
        Semantic.TemplateVariable (Semantic.OccurrenceArgumentIx index) -> index
        template -> error
            ("unexpected rich verb-contract term: " <> show template)

    isVerbToAcceptedView labelForReference view =
        case
            ( Semantic.notionViewPremise view
            , Semantic.notionViewConclusion view
            ) of
            ( Semantic.GlobalNotionViewPremise
                (Semantic.VerbNotionHead premise) premiseArguments
              , Semantic.AtomicLeaf (Semantic.GlobalAtomTemplate
                (Semantic.AdjectiveNotionHead conclusion) conclusionArguments)
              ) ->
                labelForReference premise == Just "notion_verb_seal"
                    && labelForReference conclusion
                        == Just "notion_verb_accepted"
                    && length premiseArguments == 2
                    && length conclusionArguments == 2
            _ -> False

registersAlgebraVocabularyContract :: Assertion
registersAlgebraVocabularyContract = do
    (_foundation, _bootstrap, _workspace, modules) <-
        compileFixture "test/phase9/algebra-vocabulary.tex"
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "algebra vocabulary fixture compiled no module"
            >> fail "unreachable"
    let bindings =
            [ binding
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta batch))
            ]
        bindingLabel =
            Semantic.semanticBindingLabelText
                . Semantic.semanticGlobalBindingLabel
        bindingByLabel label =
            sole (StrictText.unpack label)
                [ binding
                | binding <- bindings
                , bindingLabel binding == label
                ]
        expectedNouns =
            [ ("spike_phrase_magma_hom", 3)
            , ("spike_phrase_magma_embedding", 3)
            , ("spike_phrase_magma_surjection", 3)
            , ("spike_phrase_magma_isomorphism", 3)
            , ("spike_phrase_monoid_hom", 3)
            , ("spike_phrase_monoid_embedding", 3)
            , ("spike_phrase_monoid_surjection", 3)
            , ("spike_phrase_monoid_isomorphism", 3)
            , ("spike_phrase_monoid_unit", 2)
            , ("spike_phrase_closure_system", 2)
            , ("spike_phrase_prime_natural", 1)
            , ("spike_phrase_ring_hom", 3)
            , ("spike_phrase_ring_embedding", 3)
            , ("spike_phrase_ring_surjection", 3)
            , ("spike_phrase_ring_isomorphism", 3)
            , ("spike_phrase_subring", 2)
            , ("spike_phrase_module_embedding", 4)
            , ("spike_phrase_module_surjection", 4)
            , ("spike_phrase_module_isomorphism", 4)
            , ("spike_phrase_right_module", 2)
            , ("spike_phrase_left_ideal", 2)
            , ("spike_phrase_right_ideal", 2)
            , ("spike_phrase_two_sided_ideal", 2)
            , ("spike_phrase_ideal", 2)
            ]
        expectedAdjectives =
            [ ("spike_phrase_coprime_naturals", 2)
            , ("spike_phrase_indexed_module_linear_independence", 4)
            ]
        expectedVerbs =
            [ ("spike_phrase_natural_divisibility", 2)
            , ("spike_phrase_indexed_module_spanning", 4)
            , ("spike_phrase_indexed_module_basis", 4)
            ]

    for_ expectedNouns \(label, expectedArity) -> do
        binding <- bindingByLabel label
        assertNotionFocus label binding
        case Semantic.semanticGlobalBindingKey binding of
            Semantic.SemanticNoun singular plural -> do
                assertEqual (StrictText.unpack label <> " singular arity")
                    expectedArity (1 + patternArity singular)
                assertEqual (StrictText.unpack label <> " plural arity")
                    expectedArity (1 + patternArity plural)
            key -> assertFailure
                (StrictText.unpack label <> " has the wrong notion owner: "
                    <> show key)

    for_ expectedAdjectives \(label, expectedArity) -> do
        binding <- bindingByLabel label
        assertNotionFocus label binding
        case Semantic.semanticGlobalBindingKey binding of
            Semantic.SemanticRightAdjective
                    Semantic.OrdinaryAdjectiveReading patternValue ->
                assertEqual (StrictText.unpack label <> " argument arity")
                    expectedArity (1 + patternArity patternValue)
            key -> assertFailure
                (StrictText.unpack label <> " has the wrong notion owner: "
                    <> show key)

    for_ expectedVerbs \(label, expectedArity) -> do
        binding <- bindingByLabel label
        assertNotionFocus label binding
        case Semantic.semanticGlobalBindingKey binding of
            Semantic.SemanticVerb surfaces -> do
                assertEqual (StrictText.unpack label <> " singular arity")
                    expectedArity
                    (1 + patternArity
                        (Raw.patternFromHoley
                            (Raw.verbSurfaceSingular surfaces)))
                assertEqual (StrictText.unpack label <> " base arity")
                    expectedArity
                    (1 + patternArity
                        (Raw.patternFromHoley
                            (Raw.verbSurfaceBase surfaces)))
            key -> assertFailure
                (StrictText.unpack label <> " has the wrong notion owner: "
                    <> show key)
  where
    assertNotionFocus label binding =
        assertEqual (StrictText.unpack label <> " distinguished subject")
            (Just (Semantic.OccurrenceArgumentIx 0))
            (Semantic.globalNotionHostFocus
                (Semantic.semanticGlobalBindingKey binding))

    patternArity :: Raw.Pattern -> Int
    patternArity = \case
        Raw.End -> 0
        Raw.HoleCons rest -> 1 + patternArity rest
        Raw.TokenCons _token rest -> patternArity rest

expandsVerbAbbreviations :: Assertion
expandsVerbAbbreviations = do
    (_foundation, _bootstrap, _workspace, modules) <-
        compileFixture "test/phase9/notion-verb-abbreviation.tex"
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "verb-abbreviation fixture compiled no module"
            >> fail "unreachable"
    let bindingRowsFor moduleValue =
            [ ( binding
              , Semantic.globalBindingRef
                    (Semantic.declarationDeltaSlot delta)
                    (Semantic.semanticGlobalBindingKey binding)
              )
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix moduleValue)
            , let delta = Commit.committedBatchDelta batch
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment delta)
            ]
        rootBindings = fst <$> bindingRowsFor root
        allBindingRows = concatMap bindingRowsFor modules
        bindingLabel =
            Semantic.semanticBindingLabelText
                . Semantic.semanticGlobalBindingLabel
        bindingByLabel label =
            sole (StrictText.unpack label)
                [ binding
                | binding <- rootBindings
                , bindingLabel binding == label
                ]
        labelByReference = Map.fromList
            [ (reference, bindingLabel binding)
            | (binding, reference) <- allBindingRows
            ]
        normalization label = do
            binding <- bindingByLabel label
            pure
                (Semantic.semanticGlobalBindingExpansion binding >>= expansionAtom)
        labelForReference reference = Map.lookup reference labelByReference

    for_
        [ "notion_verb_alias"
        , "notion_verb_adjective_alias"
        , "notion_verb_chain"
        ] \label -> do
            template <- normalization label
            case template of
                Just
                    (Semantic.GlobalAtomTemplate
                        (Semantic.VerbNotionHead reference) arguments) -> do
                            assertEqual
                                (StrictText.unpack label
                                    <> " terminal verb owner")
                                (Just "notion_verb_seal")
                                (labelForReference reference)
                            assertEqual
                                (StrictText.unpack label
                                    <> " terminal argument order")
                                [0, 1]
                                (normalizationVariable <$> toList arguments)
                other ->
                    assertFailure
                        (StrictText.unpack label
                            <> " has the wrong normalization: " <> show other)

    memberTemplate <- normalization "notion_verb_member_alias"
    case memberTemplate of
        Just (Semantic.MembershipAtomTemplate element set) ->
            assertEqual "verb-to-membership normalization argument order"
                [0, 1]
                (normalizationVariable <$> [element, set])
        other -> assertFailure
            ("verb-to-membership normalization failed: " <> show other)

    normalization "notion_verb_compound_alias" >>= assertEqual
        "a compound verb expansion is not one atom" Nothing
    normalization "notion_verb_negative_alias" >>= \case
        Just (Semantic.NegativeGlobalAtomTemplate (Semantic.VerbNotionHead reference) arguments) -> do
            labelForReference reference @?= Just "notion_verb_seal"
            (normalizationVariable <$> toList arguments) @?= [0,1]
        other -> assertFailure ("a negative verb lost its signed argument view: " <> show other)
  where
    normalizationVariable = \case
        Semantic.ExpansionFormal index -> index
        term -> error
            ("unexpected rich verb-normalization term: " <> show term)

rejectsInexactRelationEvidence :: Assertion
rejectsInexactRelationEvidence =
    withAcceptedFixtureVampire "notion-relation-negative" \prover -> do
        for_
            [ "test/phase9/notion-relation-exact-negative.tex"
            , "test/phase9/notion-relation-negated-negative.tex"
            , "test/phase9/notion-relation-dynamic-negative.tex"
            ] \relative ->
                checkFileFresh prover relative >>= \case
                    Right
                        ( Verification.VerificationCheckingFailure _report
                            (Verification.VerificationTypedModuleError
                                _source
                                actionFailure
                                _prefix)
                        , _slowReport
                        ) -> do
                            failure <- case actionFailure of
                                Module.TypedActionFailed
                                        (Module.TypedElaborationFailed
                                            value@Elaboration.ElaborationFormationRequirementMissing{}) ->
                                    pure value
                                Module.TypedActionFailed
                                        (Module.TypedProofFailed
                                            (Proof.ProofElaborationFailed
                                                value@Elaboration.ElaborationFormationRequirementMissing{})) ->
                                    pure value
                                _ -> assertFailure
                                    (relative
                                        <> ": relation evidence failed differently: "
                                        <> show actionFailure)
                                    >> fail "unreachable"
                            let rendered =
                                    Elaboration.renderElaborationError failure
                            assertBool
                                (relative
                                    <> ": the diagnostic lost the written symbolic relation")
                                ("notionRelation"
                                    `StrictText.isInfixOf` rendered)
                    Right result ->
                        assertFailure
                            (relative <> ": inexact relation evidence escaped: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": relation fixture did not run: "
                                <> show failure)
        checkFileFresh prover
            "test/phase9/notion-relation-fixed-header-negative.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                actionFailure)
                            _prefix)
                    , _slowReport
                    )
                        | isUnsupportedHeader actionFailure -> pure ()
                Right result ->
                    assertFailure
                        ("fixed relation Let header failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("fixed relation Let fixture did not run: "
                            <> show failure)
  where
    isUnsupportedHeader = \case
        Module.TypedElaborationFailed
                Elaboration.ElaborationUnsupportedHeaderAssumption{} -> True
        Module.TypedProofFailed
                (Proof.ProofElaborationFailed
                    Elaboration.ElaborationUnsupportedHeaderAssumption{}) -> True
        _ -> False

usesOnlyPositiveExactVerbEvidence :: Assertion
usesOnlyPositiveExactVerbEvidence =
    withAcceptedFixtureVampire "notion-verb-evidence" \prover -> do
        checkFileFresh prover "test/phase9/notion-verb.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _slowReport) ->
                pure ()
            Right result ->
                assertFailure
                    ("positive verb notion fixture failed: " <> show result)
            Left failure ->
                assertFailure
                    ("positive verb notion fixture did not run: "
                        <> show failure)

        checkFileFresh prover "test/phase9/notion-verb-import.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _slowReport) ->
                pure ()
            Right result ->
                assertFailure
                    ("imported verb notion fixture failed: " <> show result)
            Left failure ->
                assertFailure
                    ("imported verb notion fixture did not run: "
                        <> show failure)

        checkFileFresh prover "test/phase9/notion-verb-negative.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    (Proof.ProofNotionUnavailable
                                        location failure)))
                            _prefix)
                    , _slowReport
                    ) -> do
                        assertEqual "negative verb notion proof line"
                            8 (locLine location)
                        let rendered =
                                Elaboration.renderNotionQueryFailure failure
                        assertBool "verb notion diagnostic names the exact goal"
                            ("X has a notion verb seal over Y"
                                `StrictText.isInfixOf` rendered)
                        assertBool
                            "verb notion diagnostic hides internal constructors"
                            (not ("VerbNotionHead"
                                `StrictText.isInfixOf` rendered))
                Right result ->
                    assertFailure
                        ("negated verb evidence escaped: " <> show result)
                Left failure ->
                    assertFailure
                        ("negative verb notion fixture did not run: "
                            <> show failure)

usesExactSourceTerminalPrefixPredicates :: Assertion
usesExactSourceTerminalPrefixPredicates =
    withAcceptedFixtureVampire "notion-prefix-predicate" \prover -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        let theory = Identity.theoryId foundation
            resolver = Declaration.vampireResolver
                (Provers.runPreparedTypedProver prover)
        Temp.withSystemTempDirectory "felix-prefix-predicate" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
                open = do
                    (_startup, store) <- expectRight
                        =<< Store.openStore storePath theory
                    pure store
            bracket open Store.closeStore \store -> do
                prelude <- expectRight
                    =<< acquireFinalPreludeSession store foundation resolver
                mounts <- exactFixtureMounts repository
                registrationWorkspace <- parseFinalWorkspace
                    prelude mounts
                    "test/phase9/notion-prefix-predicate-registration.tex"
                registrationModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver registrationWorkspace
                registration <- case reverse registrationModules of
                    current : _imports -> pure current
                    [] -> assertFailure
                        "prefix-predicate registration compiled no module"
                        >> fail "unreachable"

                let deltas =
                        [ Commit.committedBatchDelta batch
                        | batch <- Commit.pendingModulePrefixBatches
                            (Module.completedTypedModulePrefix registration)
                        ]
                    rules = concatMap
                        (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) deltas
                    views = concatMap
                        (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry,
                            Semantic.AtomicLeaf{} <- [Semantic.notionViewConclusion rule]]) deltas
                    bindings =
                        [ binding
                        | delta <- deltas
                        , binding <- Semantic.semanticEnvironmentBindings
                            (Semantic.declarationDeltaEnvironment delta)
                        ]
                    bindingLabel =
                        Semantic.semanticBindingLabelText
                            . Semantic.semanticGlobalBindingLabel
                    aliasRows =
                        [ binding
                        | binding <- bindings
                        , bindingLabel binding
                            == "notion_boolean_subalgebra_alias"
                        ]
                    prefixPremiseAtom = \case
                        Semantic.RulePremiseAtom
                                (Semantic.GlobalAtomTemplate
                                    Semantic.PrefixPredicateNotionHead{}
                                    _arguments) -> True
                        Semantic.RulePremiseAnd left right ->
                            prefixPremiseAtom left && prefixPremiseAtom right
                        _ -> False
                alias <- sole
                    "prefix-predicate hosted abbreviation" aliasRows
                assertEqual
                    "the Boolean-subalgebra classification registers one provider rule"
                    1 (length rules)
                for_ rules \rule ->
                    case Semantic.providerResultPremises rule of
                        Semantic.ProviderResultGuarded
                                (Semantic.RulePremiseBundles premises) ->
                            assertBool
                                "the provider rule retains the exact prefix premise"
                                (all prefixPremiseAtom premises)
                        Semantic.ProviderResultUnconditional ->
                            assertFailure
                                "the guarded prefix rule became unconditional"
                assertEqual
                    "the prefix premise also registers one ordinary view"
                    1 (length views)
                for_ views \view ->
                    case Semantic.notionViewPremise view of
                        Semantic.GlobalNotionViewPremise
                                Semantic.PrefixPredicateNotionHead{}
                                _arguments -> pure ()
                        premise -> assertFailure
                            ("the ordinary view lost its prefix premise: "
                                <> show premise)
                assertBool "a hosted abbreviation retains its terminal prefix expansion"
                    (isJust (Semantic.semanticGlobalBindingExpansion alias >>= expansionAtom))

                runConsumer registration foundation prelude mounts
                    "test/phase9/notion-prefix-predicate.tex" >>= \case
                        Module.TypedModuleSucceeded{} -> pure ()
                        result -> unexpectedResult
                            "exact prefix-predicate evidence did not replay"
                            result

                for_
                    [ "test/phase9/notion-prefix-predicate-missing.tex"
                    , "test/phase9/notion-prefix-predicate-unfolded.tex"
                    , "test/phase9/notion-prefix-predicate-components.tex"
                    ] \relative ->
                        runConsumer
                            registration foundation prelude mounts relative
                            >>= \case
                                Module.TypedModuleFailed
                                        (Module.TypedActionFailed
                                            (Module.TypedProofFailed
                                                (Proof.ProofNotionUnavailable
                                                    _location _failure)))
                                        _prefix -> pure ()
                                result -> unexpectedResult
                                    (relative
                                        <> ": non-exact evidence failed by the wrong boundary")
                                    result

                runConsumer registration foundation prelude mounts
                    "test/phase9/notion-prefix-predicate-conclusion.tex"
                    >>= \case
                        Module.TypedModuleSucceeded{} -> pure ()
                        result -> unexpectedResult
                            "a checked prefix-predicate Horn conclusion did not replay"
                            result
  where
    runConsumer registration foundation prelude mounts relative = do
        workspace <- parseFinalWorkspace prelude mounts relative
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.finalPreludeReadiness prelude)
                unusedResolver
                AlwaysMissValidation
                (Parsed.parsedWorkspaceRootModule workspace)
                [registration])
        runTypedModule input

    unexpectedResult label = \case
        Module.TypedModuleOpenFailed failure ->
            assertFailure (label <> ": " <> show failure)
        Module.TypedModuleFailed failure _prefix ->
            assertFailure
                (label <> ": "
                    <> StrictText.unpack
                        (Module.renderTypedModuleFailure failure))
        Module.TypedModuleSucceeded{} ->
            assertFailure (label <> ": module unexpectedly succeeded")

expandsVerbAbbreviationEvidence :: Assertion
expandsVerbAbbreviationEvidence =
    withAcceptedFixtureVampire "notion-verb-abbreviation" \prover -> do
        for_ [ "test/phase9/notion-verb-abbreviation.tex"
             , "test/phase9/notion-verb-abbreviation-compound.tex"
             ] \relative -> checkFileFresh prover relative >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("verb abbreviation fixture failed: " <> show result)
                Left failure ->
                    assertFailure
                        ("verb abbreviation fixture did not run: "
                            <> show failure)

        for_
            [ "test/phase9/notion-verb-abbreviation-negative-body.tex" ] \relative ->
                checkFileFresh prover relative >>= \case
                    Right
                        ( Verification.VerificationCheckingFailure _report
                            (Verification.VerificationTypedModuleError
                                _source
                                (Module.TypedActionFailed
                                    (Module.TypedProofFailed
                                        (Proof.ProofNotionUnavailable
                                            location _failure)))
                                _prefix)
                        , _slowReport
                        ) ->
                            assertEqual
                                (relative <> ": unavailable proof line")
                                8 (locLine location)
                    Right result ->
                        assertFailure
                            (relative
                                <> ": negation supplied positive evidence: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": fixture did not run: "
                                <> show failure)

usesFieldEndpointConsumers :: Assertion
usesFieldEndpointConsumers =
    withAcceptedFixtureVampire "notion-endpoint-field" \prover ->
        checkFileFresh prover "test/phase9/notion-endpoint-field.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _slowReport) ->
                pure ()
            Right result ->
                assertFailure
                    ("the field endpoint fixture failed: " <> show result)
            Left failure ->
                assertFailure
                    ("the field endpoint fixture did not run: " <> show failure)

checksExactLocalAliases :: Assertion
checksExactLocalAliases =
    withAcceptedFixtureVampire "notion-alias" \prover -> do
        for_ ["test/phase9/notion-alias.tex", "test/phase9/notion-alias-repeated.tex", "test/phase9/notion-alias-domain.tex"] \relative ->
          checkFileFresh prover relative >>= \case
            Right (Verification.VerificationCompleted{}, _slowReport) ->
                pure ()
            Right result ->
                assertFailure
                    ("the exact local-alias fixture failed: " <> show result)
            Left failure ->
                assertFailure
                    ("the exact local-alias fixture did not run: "
                        <> show failure)

        for_
            [ "test/phase9/notion-alias-repeated-negative.tex"
            , "test/phase9/notion-alias-domain-negative.tex"
            ] \relative ->
                checkFileFresh prover relative >>= \case
                    Right
                        ( Verification.VerificationCheckingFailure _report
                            (Verification.VerificationTypedModuleError
                                _source actionFailure _prefix)
                        , _slowReport
                        )
                            | isMissingFormationRequirement actionFailure ->
                                pure ()
                    Right result ->
                        assertFailure
                            (relative <> ": alias boundary failed differently: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": alias boundary did not run: "
                                <> show failure)
  where
    isMissingFormationRequirement = \case
        Module.TypedActionFailed
                (Module.TypedElaborationFailed
                    Elaboration.ElaborationFormationRequirementMissing{}) ->
            True
        Module.TypedActionFailed
                (Module.TypedProofFailed
                    (Proof.ProofElaborationFailed
                        Elaboration.ElaborationFormationRequirementMissing{})) ->
            True
        _ -> False

transportsNotionsAcrossEquality :: Assertion
transportsNotionsAcrossEquality =
    withAcceptedFixtureVampire "notion-equality-transport" \prover ->
        withFreshVerificationSession \session -> do
            for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
                checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                    prover "test/phase9/notion-equality-transport.tex" >>= \case
                        Right (Verification.VerificationCompleted{}, _) -> pure ()
                        result -> assertFailure ("argument equality or replay failed: " <> show result)
            for_ ["missing", "proper-subterm"] \name ->
                checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                    prover ("test/phase9/notion-equality-" <> name <> ".tex") >>= \case
                        Right (Verification.VerificationCheckingFailure _
                            (Verification.VerificationTypedModuleError _ failure _), _) ->
                            assertBool ("unexpected equality rejection: " <> show failure)
                                ("ProofNotionUnavailable" `StrictText.isInfixOf` StrictText.pack (show failure))
                        result -> assertFailure ("equality crossed the argument boundary: " <> show result)

usesFiniteSetProviderResultTheorems :: Assertion
usesFiniteSetProviderResultTheorems =
    withAcceptedFixtureVampire "notion-finite-set-provider" \prover -> do
        withFreshVerificationSession \session -> do
            check session Verification.FreshStoreValidation prover
                "test/phase9/notion-finite-set-provider-import.tex"
                >>= expectCompleted "fresh imported use"
            check session Verification.WarmStoreValidation prover
                "test/phase9/notion-finite-set-provider-missing.tex" >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedElaborationFailed
                                    failure@(
                                        Elaboration.ElaborationFormationRequirementMissing
                                            location _requirement)))
                            _prefix)
                    , _slowReport
                    ) -> do
                        assertEqual "missing pair member line"
                            7 (locLine location)
                        let rendered = Elaboration.renderElaborationError failure
                        assertBool "diagnostic identifies the finite literal"
                            ("written finite-set literal"
                                `StrictText.isInfixOf` rendered)
                        assertBool "diagnostic reports the exact missing member"
                            ("could not establish that b is an element of"
                                `StrictText.isInfixOf` rendered)
                        assertBool "diagnostic suggests the exact repair"
                            ("establish \"b is an element of"
                                `StrictText.isInfixOf` rendered)
                Right result ->
                    assertFailure
                        ("missing finite-set premise failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("missing finite-set fixture did not run: "
                            <> show failure)
  where
    check session mode prover =
        checkFileWithSession
            session mode testSequentialJobs ignoredVerificationRequests
            prover

    expectCompleted pass = \case
        Right (Verification.VerificationCompleted{}, _slowReport) -> pure ()
        Right result ->
            assertFailure (pass <> " failed: " <> show result)
        Left failure ->
            assertFailure (pass <> " did not run: " <> show failure)

registersProviderResultTheorems :: Assertion
registersProviderResultTheorems = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-provider-rule-registration.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "provider-result fixture compiled no module"
            >> fail "unreachable"
    let rules =
            [ rule
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
    assertEqual "the classifications register their provider-result rules"
        7 (length rules)
    assertEqual "provider-result arities retain declaration arguments"
        [1, 1, 1, 1, 2, 2, 2]
        (List.sort
            [ Vector.length
            (Semantic.resultProviderTemplateArguments
                (Semantic.providerResultProvider rule))
            | rule <- rules
            ])
    assertEqual "provider-result rules retain exact curried premise bundles"
        [1, 1, 1, 1, 2, 2, 2]
        (List.sort
            [ length premises
            | rule <- rules
            , Semantic.ProviderResultGuarded
                (Semantic.RulePremiseBundles premises) <-
                    [Semantic.providerResultPremises rule]
            ])
    for_ rules \rule -> do
        let provider = Semantic.providerResultProvider rule
        assertBool "provider rules retain at least one provider argument"
            (not (Vector.null
                (Semantic.resultProviderTemplateArguments provider)))
        case Semantic.providerResultPremises rule of
            Semantic.ProviderResultUnconditional ->
                assertFailure
                    "a guarded provider-rule fixture became unconditional"
            Semantic.ProviderResultGuarded
                    (Semantic.RulePremiseBundles premises) ->
                assertBool "provider rules retain at least one premise bundle"
                    (not (null premises))
    importedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-provider-rule-import.tex"
    importedModules <-
        compileParsedWorkspace foundation bootstrap importedWorkspace
    assertBool "an imported provider-result rule materializes"
        (not (null importedModules))

    registration <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "provider registration fixture has no root"
            >> fail "unreachable"
    let checkRejected relative expectedDetails checkStatistics = do
            rejectedWorkspace <- parseWorkspace bootstrap mounts relative
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule rejectedWorkspace)
                    [registration])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedElaborationFailed
                                failure@(
                                    Elaboration.ElaborationFormationRequirementMissing
                                        _location requirement)))
                        _prefix -> do
                    checkDiagnostic relative expectedDetails failure
                    checkStatistics
                        (Elaboration.formationRequirementFailureSearchStatistics
                            requirement)
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedProofFailed
                                (Proof.ProofElaborationFailed
                                    failure@(
                                        Elaboration.ElaborationFormationRequirementMissing
                                            _location requirement))))
                        _prefix -> do
                    checkDiagnostic relative expectedDetails failure
                    checkStatistics
                        (Elaboration.formationRequirementFailureSearchStatistics
                            requirement)
                Module.TypedModuleSucceeded{} ->
                    assertFailure
                        (relative <> ": equal-Core provider evidence leaked")
                Module.TypedModuleOpenFailed{} ->
                    assertFailure (relative <> ": fixture did not open")
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        (relative <> ": failed differently: "
                            <> StrictText.unpack
                                (Module.renderTypedModuleFailure failure))
    -- Different written provider heads can denote the same complete value.
    -- Finite discovery finds the registered view; its guards still need proof.
    sibling <- parseWorkspace bootstrap mounts "test/phase9/notion-provider-rule-sibling-missing.tex"
    void (compileParsedWorkspace foundation bootstrap sibling)
    -- The first written provider supplies an admitted view in this sealed
    -- group. Its proved exact conclusion can discharge the equal-Core sibling;
    -- this does not recover the sibling's provider arguments.
    equalCore <- parseWorkspace bootstrap mounts "test/phase9/notion-provider-repeated-core-missing.tex"
    void (compileParsedWorkspace foundation bootstrap equalCore)
    checkRejected
        "test/phase9/notion-provider-premise-missing.tex"
        [ "written provider \"\\notionProviderValue"
        , "selected from declaration \"notion_provider_value\""
        , "is blocked because Felix could not establish"
        , "Suggested repair: establish \"X is a notion "
        ]
        (assertLiveFailure "blocked")
    checkRejected
        "test/phase9/notion-provider-closure-missing.tex"
        [ "written provider \"\\notionIndexedProviderValue"
        , "selected from declaration \"notion_indexed_provider_value\""
        , "no applicable classification established the requested notion"
        , "Suggested repair: add an applicable classification reaching"
        ]
        (assertLiveFailure "unavailable result")
  where
    checkDiagnostic relative expectedDetails failure = do
        let rendered = Elaboration.renderElaborationError failure
        for_ expectedDetails \expectedDetail ->
            assertBool
                (relative <> ": expected diagnostic fragment "
                    <> StrictText.unpack expectedDetail <> "\nActual: " <> StrictText.unpack rendered)
                (expectedDetail `StrictText.isInfixOf` rendered)
        when (relative == "test/phase9/notion-provider-premise-missing.tex") do
            assertBool "repair names a missing prerequisite, not a circular intermediate goal"
                (any (`StrictText.isInfixOf` rendered)
                    ["Suggested repair: establish \"X is a notion base\"",
                     "Suggested repair: establish \"X is a notion unavailable\""])
        assertEqual (relative <> ": exactly one suggested repair")
            2
            (length (StrictText.splitOn "Suggested repair:" rendered))

    assertLiveFailure label statistics = do
        assertEqual (label <> " does not run the Composite controller") 0
            (Notion.formationSearchCompositePremiseRequests statistics)
        assertBool (label <> " retains the live evaluator's structural work")
            (Notion.formationSearchViewInspections statistics > 0)

classifiesClosedNamedProviders :: Assertion
classifiesClosedNamedProviders = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-closed-provider.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "closed provider fixture compiled no module"
            >> fail "unreachable"
    let deltas =
            [ Commit.committedBatchDelta batch
            | current <- modules
            , batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix current)
            ]
        rules = concatMap (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) deltas
    for_ deltas \delta ->
        assertEqual "closed registrations survive the bounded canonical codec"
            (Right delta)
            (decodeCache Semantic.getDeclarationInterfaceDeltaCache
                (encodeCache (Semantic.putDeclarationInterfaceDeltaCache delta)))
    case rules of
        [rule] -> do
            let provider = Semantic.providerResultProvider rule
            assertEqual "the closed provider has no artificial argument"
                Vector.empty (Semantic.resultProviderTemplateArguments provider)
            assertEqual "the theorem has no artificial premise"
                Semantic.ProviderResultUnconditional
                (Semantic.providerResultPremises rule)
            case Semantic.resultProviderTemplateHead provider of
                Semantic.GlobalSourceProvider{} -> pure ()
                other -> assertFailure
                    ("expected the named provider's identity, found " <> show other)
        _ -> assertFailure ("expected one closed provider rule, found " <> show rules)
    importedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-closed-provider-import.tex"
    void (compileParsedWorkspace foundation bootstrap importedWorkspace)
    equalWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-closed-provider-equal.tex"
    void (compileParsedWorkspace foundation bootstrap equalWorkspace)
    missingWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-closed-provider-missing.tex"
    missingInput <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule missingWorkspace)
            [root])
    runTypedModule missingInput >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed
                            Elaboration.ElaborationFormationRequirementMissing{})))
                _prefix -> pure ()
        Module.TypedModuleFailed failure _prefix ->
            assertFailure ("expected a missing formation guard: " <> show failure)
        Module.TypedModuleSucceeded{} ->
            assertFailure "an unclassified closed provider passed formation"
        Module.TypedModuleOpenFailed failure ->
            assertFailure ("the missing-guard fixture did not open: " <> show failure)

usesUnconditionalProviderResultTheorems :: Assertion
usesUnconditionalProviderResultTheorems = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-unconditional-provider.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "unconditional provider fixture compiled no module"
            >> fail "unreachable"
    let rules =
            [ rule
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
        unconditionalRules =
            [ rule
            | rule <- rules
            , Semantic.ProviderResultUnconditional <-
                [Semantic.providerResultPremises rule]
            ]
        guardedRules =
            [ rule
            | rule <- rules
            , Semantic.ProviderResultGuarded{} <-
                [Semantic.providerResultPremises rule]
            ]
    assertEqual "two source spellings publish premise-free registrations"
        2 (length unconditionalRules)
    assertEqual "the later recursive alternative remains guarded"
        1 (length guardedRules)
    for_ unconditionalRules \rule ->
        assertEqual "an unconditional provider retains its unary spine"
            1
            (Vector.length
                (Semantic.resultProviderTemplateArguments
                    (Semantic.providerResultProvider rule)))

    importedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-unconditional-provider-import.tex"
    importedModules <-
        compileParsedWorkspace foundation bootstrap importedWorkspace
    assertBool "an imported premise-free provider theorem materializes"
        (not (null importedModules))

    secondary <- parseWorkspace bootstrap mounts "test/phase9/notion-unconditional-secondary-focus.tex"
    void (compileParsedWorkspace foundation bootstrap secondary)
    for_
        [ ( "test/phase9/notion-unconditional-undetermined.tex"
          , "a notion rule must use exactly its dense nearest-first theorem context"
          )
        , ( "test/phase9/notion-classification-bundle-undetermined.tex"
          , "a notion rule must use exactly its dense nearest-first theorem context"
          )
        ] \(relative, expected) -> do
            rejectedWorkspace <- parseWorkspace bootstrap mounts relative
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule rejectedWorkspace)
                    [root])
            runTypedModule input >>= \case
                Module.TypedModuleFailed failure _prefix ->
                    assertBool
                        (relative <> ": unexpected rejection: "
                            <> StrictText.unpack
                                (Module.renderTypedModuleFailure failure))
                        (StrictText.pack expected `StrictText.isInfixOf`
                            Module.renderTypedModuleFailure failure)
                Module.TypedModuleSucceeded{} ->
                    assertFailure
                        (relative <> ": invalid classification was accepted")
                Module.TypedModuleOpenFailed failure ->
                    assertFailure
                        (relative <> ": rejection fixture did not open: "
                            <> show failure)

    equalityWorkspace <- parseWorkspace bootstrap mounts
        "test/phase9/notion-unconditional-equality-header.tex"
    equalityModules <- compileParsedWorkspace foundation bootstrap equalityWorkspace
    equalityRoot <- sole "equality-premise importer" (take 1 (reverse equalityModules))
    equalityRule <- sole "equality-premise provider rule"
        [ rule
        | batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix equalityRoot)
        , Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <-
            Semantic.declarationDeltaRegistrations (Commit.committedBatchDelta batch)
        ]
    case Semantic.providerResultPremises equalityRule of
        Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles
            (Semantic.RulePremiseResidual premise :| [])) ->
                assertEqual "an equality header remains a required whole premise"
                    (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0))
                    (Semantic.residualTemplateFormula premise)
        actual -> assertFailure ("the equality header lost its whole premise: " <> show actual)

    closureWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-unconditional-closure-missing.tex"
    closureInput <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule closureWorkspace)
            [root])
    runTypedModule closureInput >>= \case
        Module.TypedModuleFailed failure _prefix -> do
            let rendered = Module.renderTypedModuleFailure failure
            assertBool "premise-free failure names the registered result without claiming an unused proof"
                ("registered result classification for notion head \"notion unconditional output\""
                    `StrictText.isInfixOf` rendered)
            assertBool "premise-free closure failure does not invent a premise"
                (not ("blocked because" `StrictText.isInfixOf` rendered))
        Module.TypedModuleSucceeded{} ->
            assertFailure "the premise-free closure-missing fixture succeeded"
        Module.TypedModuleOpenFailed failure ->
            assertFailure
                ("the premise-free closure fixture did not open: "
                    <> show failure)

    Raw.Claim assumptions conclusion <-
        sole "unconditional provider budget query"
            [ claim
            | Raw.BlockClaim _kind _location _title marker claim <-
                Parsed.parsedModuleBlocks
                    (Parsed.parsedWorkspaceRootModule workspace)
            , marker == "notion_unconditional_provider_by_notion"
            ]
    variable <- case assumptions of
        [Raw.AsmLetNoun variables _noun] ->
            pure (NonEmpty.head variables)
        _ ->
            assertFailure
                "the unconditional query fixture lost its neutral set binder"
                >> fail "unreachable"
    context <- expectRight
        (Elaboration.extendElaborationContext
            ((Elaboration.localId 0, variable) :| [])
            Elaboration.emptyElaborationContext)
    let preludeModule = Module.bootstrapPreludeCompleted bootstrap
        directModules = [preludeModule, root]
        directInputs = completedModuleEvidence <$> directModules
        targetModule =
            Parsed.parsedWorkspaceRootModule importedWorkspace
        action
            :: Declaration.ModuleDriver Text
                ( Either Elaboration.ElaborationError
                    (Elaboration.NotionQueryOutcome, Notion.FormationSearchBudget)
                , Either Elaboration.ElaborationError
                    (Elaboration.NotionQueryOutcome, Notion.FormationSearchBudget)
                )
        action = do
            Declaration.runProspectiveLoweringDriver do
                elaborated <- Elaboration.elaborateProposition context conclusion
                case elaborated of
                    Left failure -> pure (Left failure, Left failure)
                    Right proposition -> case
                            Elaboration.elaboratedPropositionAssertions proposition of
                        [assertion] -> do
                            first <- Elaboration.elaborateProofNotionEvidenceWithBudget
                                (Notion.initialFormationSearchBudget
                                    Notion.defaultFormationSearchLimits)
                                context Nowhere assertion
                            case first of
                                Left failure -> pure (Left failure, Left failure)
                                Right (_outcome, finalBudget) -> do
                                    let statistics =
                                            Notion.formationSearchBudgetStatistics
                                                finalBudget
                                        inferenceLimit =
                                            inferenceInspections statistics
                                        positive value = max 1 value
                                        tightLimits = fromMaybe
                                            (impossible
                                                "positive formation limits were rejected")
                                            (Notion.formationSearchLimits
                                                (positive
                                                    (Notion.formationSearchRelevantHeadEdges
                                                        statistics))
                                                (positive
                                                    (Notion.formationSearchRelevantViews
                                                        statistics))
                                                (positive
                                                    ( Notion.formationSearchDirectGroundAtoms
                                                        statistics
                                                      + Notion.formationSearchDerivedGroundAtoms
                                                        statistics
                                                      + Notion.formationSearchIndexedRows
                                                        statistics
                                                    ))
                                                (positive inferenceLimit)
                                                64
                                                16)
                                    second <-
                                        Elaboration.elaborateProofNotionEvidenceWithBudget
                                            (Notion.initialFormationSearchBudget
                                                tightLimits)
                                            context Nowhere assertion
                                    pure (first, second)
                        _ ->
                            impossible
                                "the unconditional query did not retain one atomic assertion"
    driven <- expectRight
        =<< runModuleDriver
            foundation
            (moduleName (Parsed.parsedModuleAddress targetModule))
            directInputs
            unusedResolver
            AlwaysMissValidation
            action
    case driven of
        Declaration.DriverSucceeded
                (first, tight) _interface _prefix -> do
            firstStatistics <- assertSuccessfulQuery "default" first
            tightStatistics <- assertSuccessfulQuery "tight" tight
            assertEqual "both fresh queries reuse admitted preparation, not query witnesses"
                (inferenceInspections firstStatistics) (inferenceInspections tightStatistics)
            assertEqual "the unconditional provider query bypasses the legacy controller"
                0
                (Notion.formationSearchCompositePremiseRequests firstStatistics)
            assertEqual "premise-free application makes no premise request"
                0
                (Notion.formationSearchProviderPremiseRequests firstStatistics)
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("unconditional budget query failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("unconditional budget query did not seal: " <> show failure)
  where
    assertSuccessfulQuery label = \case
        Right (Elaboration.NotionQueryUnsupported, _) ->
            assertFailure (label <> " unconditional atom was unsupported") >> fail "unreachable"
        Left failure ->
            assertFailure
                (label <> " unconditional query failed: "
                    <> StrictText.unpack
                        (Elaboration.renderElaborationError failure))
                >> fail "unreachable"
        Right (Elaboration.NotionQueryUnavailable failure, _budget) ->
            assertFailure
                (label <> " unconditional query was unavailable: "
                    <> StrictText.unpack
                        (Elaboration.renderNotionQueryFailure failure))
                >> fail "unreachable"
        Right (Elaboration.NotionQueryFound materialized, budget) -> do
            assertEqual (label <> " query has no invented hypotheses")
                0
                (Vector.length
                    (Notion.materializedFormationHypotheses materialized))
            assertEqual (label <> " query imports provider and unary theorems")
                2
                (Vector.length
                    (Notion.materializedFormationImports materialized))
            pure (Notion.formationSearchBudgetStatistics budget)

    inferenceInspections statistics =
        Notion.formationSearchViewInspections statistics
            + Notion.formationSearchProviderRuleInspections statistics
            + Notion.formationSearchCompositeRuleInspections statistics
            + Notion.formationSearchCompositePremiseRequests statistics
            + Notion.formationSearchEqualitySourceInspections statistics
            + Notion.formationSearchEqualityEdgeInspections statistics
            + Notion.formationSearchEqualityTransportSteps statistics
            + Notion.formationSearchSourceIndexInspections statistics

cachesUnconditionalProviderResultTheorems :: Assertion
cachesUnconditionalProviderResultTheorems =
    cachesProviderClassification "notion-unconditional-provider"

cachesProviderClassification :: String -> Assertion
cachesProviderClassification fixture =
    withAcceptedFixtureVampire (fixture <> "-cache") \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        Temp.withSystemTempDirectory "felix-unconditional-provider" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
                producer = "test/phase9/" <> fixture <> ".tex"
                importer = "test/phase9/" <> fixture <> "-import.tex"
                forbiddenObserver =
                    Verification.verificationRequestObserver
                        (\position _request ->
                            assertFailure
                                ("unchanged warm import scheduled proof work at "
                                    <> show position))
                check store mode observer relative label =
                    checkFileWithStore store mode observer prover relative
                        >>= \case
                            Right
                                (Verification.VerificationCompleted{},
                                    _slowReport) ->
                                pure ()
                            Right result ->
                                assertFailure
                                    (label <> " failed: " <> show result)
                            Left failure ->
                                assertFailure
                                    (label <> " did not run: " <> show failure)
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                (\store -> do
                    check store Verification.FreshStoreValidation
                        ignoredVerificationRequests producer "fresh producer"
                    check store Verification.WarmStoreValidation
                        ignoredVerificationRequests importer
                        "fresh importer over cached producer"
                    check store Verification.WarmStoreValidation
                        forbiddenObserver importer "unchanged warm importer")

registersCheckedDefinitionResults :: Assertion
registersCheckedDefinitionResults = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-definition-result.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "definition-result fixture compiled no module"
            >> fail "unreachable"
    let rules =
            [ rule
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
                (Commit.committedBatchDelta batch)
            ]
    assertEqual "the annotated definitions publish their result rules"
        4 (length rules)
    let providerKeys =
            [ Semantic.globalBindingRefKey reference
            | rule <- rules
            , Semantic.GlobalSourceProvider reference <-
                [ Semantic.resultProviderTemplateHead
                    (Semantic.providerResultProvider rule)
                ]
            ]
        functionProviderCount = length
            [ ()
            | Semantic.SemanticFunctionPhrase{} <- providerKeys
            ]
        symbolicProviderCount = length
            [ ()
            | Semantic.SemanticExpressionFunction{} <- providerKeys
            ]
    assertEqual "one result rule belongs to a functional definition"
        1 functionProviderCount
    assertEqual "three result rules belong to symbolic definitions"
        3 symbolicProviderCount
    case rules of
        [firstRule, secondRule, thirdRule, fourthRule] ->
          for_ [firstRule, secondRule, thirdRule, fourthRule] \rule -> do
            let provider =
                    Semantic.providerResultProvider rule
            assertEqual "the annotated provider retains its argument"
                1
                (Vector.length
                    (Semantic.resultProviderTemplateArguments provider))
            case Semantic.providerResultPremises rule of
                Semantic.ProviderResultUnconditional ->
                    assertFailure
                        "a definition-result annotation became unconditional"
                Semantic.ProviderResultGuarded
                        (Semantic.RulePremiseBundles premises) ->
                    assertEqual "the annotation retains its guarded header"
                        1 (length premises)
        _ -> pure ()

registersMultiAtomicDefinitionResults :: Assertion
registersMultiAtomicDefinitionResults = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    let compileRoot relative = do
            workspace <- parseWorkspace bootstrap mounts relative
            modules <- compileParsedWorkspace foundation bootstrap workspace
            case reverse modules of
                current : _imports -> pure current
                [] -> assertFailure (relative <> " compiled no module")
                    >> fail "unreachable"
    root <- compileRoot
        "test/phase9/notion-definition-result-multiple.tex"
    let resultDeltas =
            [ delta
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , let delta = Commit.committedBatchDelta batch
            , not
                (null
                    [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations delta])
            ]
        ruleCounts = List.sort
            (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
                <$> resultDeltas)
        factCounts = List.sort
            (length . Semantic.declarationDeltaFacts <$> resultDeltas)
    assertEqual
        "five annotated definitions publish eight canonical result rules"
        [1, 1, 1, 1, 4]
        ruleCounts
    assertEqual
        "each canonical result receives one independent hidden fact"
        [2, 2, 2, 2, 5]
        factCounts

    wide <- compileRoot "test/phase9/notion-definition-result-wide.tex"
    let wideResultDeltas =
            [ delta
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix wide)
            , let delta = Commit.committedBatchDelta batch
            , not
                (null
                    [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations delta])
            ]
    case wideResultDeltas of
        [delta] -> do
            assertEqual "sixteen atoms produce sixteen result rules"
                16
                (length
                    [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations delta])
            assertEqual
                "sixteen atoms produce sixteen independent hidden facts"
                17
                (length (Semantic.declarationDeltaFacts delta))
        deltas ->
            assertFailure
                ("wide result fixture published unexpected result batches: "
                    <> show (length deltas))

registersVerbalDefinitionResults :: Assertion
registersVerbalDefinitionResults = do
    (_foundation, _bootstrap, _workspace, modules) <-
        compileFixture "test/phase9/notion-definition-result-verbal.tex"
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "verbal result fixture compiled no module"
            >> fail "unreachable"
    let resultDeltas =
            [ delta
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix root)
            , let delta = Commit.committedBatchDelta batch
            , not
                (null
                    [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations delta])
            ]
        rules = concatMap
            (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
            resultDeltas
        verbConclusionCount = length
            [ ()
            | rule <- rules
            , Semantic.GlobalAtomTemplate Semantic.VerbNotionHead{} _ <-
                [Semantic.providerResultConclusion rule]
            ]
        nounConclusionCount = length
            [ ()
            | rule <- rules
            , Semantic.GlobalAtomTemplate Semantic.NounNotionHead{} _ <-
                [Semantic.providerResultConclusion rule]
            ]
    assertEqual "single and complete verbal results publish one and two rules"
        [1, 2]
        (List.sort
            (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
                <$> resultDeltas))
    assertEqual "both annotated values retain their verb result"
        2 verbConclusionCount
    assertEqual "the complete phrase retains its noun result independently"
        1 nounConclusionCount
    for_ rules \rule -> do
        assertEqual "verbal result provider retains its argument"
            1
            (Vector.length
                (Semantic.resultProviderTemplateArguments
                    (Semantic.providerResultProvider rule)))
        case Semantic.providerResultPremises rule of
            Semantic.ProviderResultUnconditional ->
                assertFailure
                    "a verbal definition result became unconditional"
            Semantic.ProviderResultGuarded
                    (Semantic.RulePremiseBundles premises) ->
                assertEqual "verbal result retains its guarded base premise"
                    1 (length premises)

groupsOrdinaryPhraseResiduals :: Assertion
groupsOrdinaryPhraseResiduals = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-grouped-ordinary.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "grouped ordinary fixture compiled no module"
            >> fail "unreachable"
    grouped <- checkedNotionPropositionTermByAlias
        root "notion_grouped_ordinary"
    repeated <- checkedNotionPropositionTermByAlias
        root "notion_repeated_ordinary"
    assertEqual
        "one grouped noun header and an explicit repeated spelling agree"
        repeated grouped
    universal <- checkedNotionPropositionTermByAlias
        root "notion_grouped_universal"
    case Core.frozenCoreTerm universal of
        Core.CForall Core.TySet
                (Core.CForall Core.TySet (Core.CImp _restriction _body)) ->
            pure ()
        target ->
            assertFailure
                ("grouped universal did not retain one shared restriction: "
                    <> show target)

checksCompletedPhraseHeads :: Assertion
checksCompletedPhraseHeads = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-completed-head.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    (root, control, vocabulary) <- case reverse modules of
        current : repeated : declarations : _ ->
            pure (current, repeated, declarations)
        _ -> assertFailure "completed-head fixture lost its imports"
            >> fail "unreachable"
    repeated <- checkedNotionPropositionTermByAlias
        control "notion_completed_repeated"
    for_ ["notion_completed_grouped", "notion_completed_right"] \label -> do
        grouped <- checkedNotionPropositionTermByAlias root label
        assertEqual "completed-head evidence preserves emitted assumptions"
            repeated grouped
    for_ ["sibling", "negative", "circular", "disjunction"] \suffix -> do
        let relative = "test/phase9/notion-completed-head-" <> suffix <> ".tex"
        rejected <- parseWorkspace bootstrap mounts relative
        input <- expectRightIO
            (typedModuleInput foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver AlwaysMissValidation
                (Parsed.parsedWorkspaceRootModule rejected) [vocabulary])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed failure) prefix -> do
                case failure of
                    Module.TypedElaborationFailed
                            Elaboration.ElaborationFormationRequirementMissing{} ->
                        pure ()
                    Module.TypedProofFailed (Proof.ProofElaborationFailed
                            Elaboration.ElaborationFormationRequirementMissing{}) ->
                        pure ()
                    _ -> assertFailure (suffix <> ": " <> show failure)
                assertBool (suffix <> " publishes no failed declaration")
                    (null (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleFailed failure _ ->
                assertFailure (suffix <> ": " <> show failure)
            _ -> assertFailure (suffix <> ": expected missing formation evidence")

elaboratesRichOpenStructurePhrases :: Assertion
elaboratesRichOpenStructurePhrases =
    withAcceptedFixtureVampire "notion-grouped-structure" \prover -> do
        for_ [ "test/phase9/notion-grouped-structure.tex"
             , "test/phase9/notion-completed-structure.tex"
             ] \relative ->
            checkFileFresh prover relative >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("rich structure phrase fixture failed: " <> show result)
                Left failure ->
                    assertFailure
                        ("rich structure phrase fixture did not run: "
                            <> show failure)

        expectFailure prover
            "test/phase9/notion-grouped-structure-ambiguous.tex"
            \case
                Elaboration.ElaborationStructureReceiverAmbiguous
                        _location
                        (Raw.StructSymbol "phasefivecombine")
                        receivers ->
                    assertEqual "both grouped receivers remain visible"
                        ["B", "A"] (toList receivers)
                failure -> unexpected "grouped receiver ambiguity" failure

        expectFailure prover
            "test/phase9/notion-structure-term-receiver-missing.tex"
            \case
                Elaboration.ElaborationStructureFieldNotAvailable
                        _location
                        (Raw.StructSymbol "phasefivecombine") ->
                    pure ()
                failure -> unexpected "term receiver requirement" failure

        expectFailure prover
            "test/phase9/notion-structure-shadow-restored.tex"
            \case
                Elaboration.ElaborationStructureFieldNotAvailable
                        _location
                        (Raw.StructSymbol "phasefivecombine") ->
                    pure ()
                failure -> unexpected "temporary receiver restoration" failure
  where
    expectFailure prover relative check =
        checkFileFresh prover relative >>= \case
            Right
                ( Verification.VerificationCheckingFailure _report
                    (Verification.VerificationTypedModuleError
                        _source actionFailure _prefix)
                , _slowReport
                ) -> case actionFailure of
                    Module.TypedActionFailed
                            (Module.TypedElaborationFailed failure) ->
                        check failure
                    Module.TypedActionFailed
                            (Module.TypedProofFailed
                                (Proof.ProofElaborationFailed failure)) ->
                        check failure
                    failure ->
                        assertFailure
                            (relative <> ": failed outside elaboration: "
                                <> show failure)
            Right result ->
                assertFailure
                    (relative <> ": unexpectedly did not fail: " <> show result)
            Left failure ->
                assertFailure
                    (relative <> ": fixture did not run: " <> show failure)

    unexpected label failure =
        assertFailure
            (label <> " failed differently: "
                <> StrictText.unpack
                    (Elaboration.renderElaborationError failure))

checkedNotionPropositionTermByAlias
    :: Module.CompletedTypedModule
    -> Text
    -> IO (Core.FrozenCheckedCore Identity.ObjectId)
checkedNotionPropositionTermByAlias sealed name = do
    batch <- sole
        ("declaration batch for " <> StrictText.unpack name)
        [ candidate
        | candidate <- Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed)
        , alias <- Semantic.declarationDeltaAliases
            (Commit.committedBatchDelta candidate)
        , Semantic.semanticAliasName alias == Semantic.semanticName name
        ]
    alias <- sole
        ("semantic alias for " <> StrictText.unpack name)
        [ candidate
        | candidate <- Semantic.declarationDeltaAliases
            (Commit.committedBatchDelta batch)
        , Semantic.semanticAliasName candidate == Semantic.semanticName name
        ]
    occurrence <- sole
        ("semantic fact for " <> StrictText.unpack name)
        [ candidate
        | candidate <- Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch)
        , Semantic.semanticFactFingerprint candidate
            == Semantic.semanticAliasTarget alias
        ]
    proposition <- sole
        ("checked proposition for " <> StrictText.unpack name)
        [ candidate
        | candidate <- Commit.committedBatchPropositions batch
        , Identity.checkedPropositionId candidate
            == Semantic.semanticFactProposition occurrence
        ]
    pure (Identity.checkedPropositionTerm proposition)

cachesCheckedDefinitionResults :: Assertion
cachesCheckedDefinitionResults =
    withAcceptedFixtureVampire "notion-definition-result-cache" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        Temp.withSystemTempDirectory "felix-notion-definition-result" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                (\store -> do
                    check "fresh" store Verification.FreshStoreValidation prover
                    check "warm" store Verification.WarmStoreValidation prover)
  where
    check label store mode prover =
        checkFileWithStore
            store
            mode
            ignoredVerificationRequests
            prover
            "test/phase9/notion-definition-result-multiple.tex"
            >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        (label <> " definition-result fixture failed: "
                            <> show result)
                Left failure ->
                    assertFailure
                        (label <> " definition-result fixture did not run: "
                            <> show failure)

cachesPrefixDefinitionProjections :: Assertion
cachesPrefixDefinitionProjections =
    withAcceptedFixtureVampire "notion-prefix-definition-cache" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        Temp.withSystemTempDirectory "felix-prefix-definition" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
                source = "test/phase9/notion-definition-projection.tex"
                forbiddenObserver =
                    Verification.verificationRequestObserver
                        (\position _request ->
                            assertFailure
                                ("unchanged warm prefix projection scheduled proof work at "
                                    <> show position))
                check store mode observer label =
                    checkFileWithStore store mode observer prover source
                        >>= \case
                            Right
                                (Verification.VerificationCompleted{},
                                    _slowReport) -> pure ()
                            Right result -> assertFailure
                                (label <> " prefix-projection fixture failed: "
                                    <> show result)
                            Left failure -> assertFailure
                                (label
                                    <> " prefix-projection fixture did not run: "
                                    <> show failure)
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                (\store -> do
                    check store Verification.FreshStoreValidation
                        ignoredVerificationRequests "fresh"
                    check store Verification.WarmStoreValidation
                        forbiddenObserver "warm")

usesVerbalDefinitionResults :: Assertion
usesVerbalDefinitionResults =
    withAcceptedFixtureVampire "notion-definition-result-verbal" \prover ->
        for_
            [ "test/phase9/notion-definition-result-verbal.tex"
            , "test/phase9/notion-definition-result-verbal-import.tex"
            ] \relative ->
                checkFileFresh prover relative >>= \case
                    Right (Verification.VerificationCompleted{}, _slowReport) ->
                        pure ()
                    Right result ->
                        assertFailure
                            (relative <> ": verbal result fixture failed: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": verbal result fixture did not run: "
                                <> show failure)

diagnosesInvalidDefinitionResults :: Assertion
diagnosesInvalidDefinitionResults =
    withAcceptedFixtureVampire "notion-definition-result-errors" \prover -> do
        checkFailure prover
            "test/phase9/notion-definition-result-missing.tex"
            \case
                Elaboration.ElaborationDefinitionResultUnavailable{} -> pure ()
                failure -> unexpected "missing evidence" failure
        checkFailure prover
            "test/phase9/notion-definition-result-verbal-missing.tex"
            \case
                Elaboration.ElaborationDefinitionResultUnavailable{} -> pure ()
                failure -> unexpected "missing verbal evidence" failure
        checkFailureWithPrefix prover
            "test/phase9/notion-definition-result-multiple-missing.tex"
            \failure prefix -> case failure of
                Elaboration.ElaborationDefinitionResultUnavailable{} ->
                    assertBool
                        "a failed multi-result definition publishes no result rule"
                        (null
                            [ rule
                            | batch <- Commit.pendingModulePrefixBatches prefix
                            , rule <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry])
                                (Commit.committedBatchDelta batch)
                            ])
                _ -> unexpected "partial multi-result evidence" failure
        checkFailure prover
            "test/phase9/notion-definition-result-synonym-missing.tex"
            \failure -> case failure of
                Elaboration.ElaborationDefinitionResultUnavailable{} ->
                    assertBool
                        "a canonical duplicate retains its first written name"
                        ("phase nine written missing result"
                            `StrictText.isInfixOf`
                                Elaboration.renderElaborationError failure)
                _ -> unexpected "synonym result origin" failure
        checkFailure prover
            "test/phase9/notion-definition-result-unconditional.tex"
            \case
                Elaboration.ElaborationDefinitionResultRequiresGuardedProvider{} ->
                    pure ()
                failure -> unexpected "unconditional annotation" failure
        for_
            [ "test/phase9/notion-definition-result-set-only.tex"
            , "test/phase9/notion-definition-result-residual.tex"
            ] \relative ->
                checkFailure prover relative \case
                    Elaboration.ElaborationDefinitionResultShapeUnsupported{} ->
                        pure ()
                    failure -> unexpected "unsupported result phrase" failure
        for_ ["negative", "verbal-negative", "contextual-missing", "horn-missing-domain"] \name ->
            checkFailure prover ("test/phase9/notion-definition-result-" <> name <> ".tex") \case
                Elaboration.ElaborationDefinitionResultUnavailable{} -> pure ()
                failure -> unexpected "unproved whole result" failure
  where
    checkFailure prover relative check =
        checkFailureWithPrefix prover relative \failure _prefix ->
            check failure

    checkFailureWithPrefix prover relative check =
        checkFileFresh prover relative >>= \case
            Right
                ( Verification.VerificationCheckingFailure _report
                    (Verification.VerificationTypedModuleError
                        _source
                        (Module.TypedActionFailed
                            (Module.TypedElaborationFailed failure))
                        prefix)
                , _slowReport
                ) -> check failure prefix
            Right result ->
                assertFailure
                    (relative <> ": definition-result failure was not retained: "
                        <> show result)
            Left failure ->
                assertFailure
                    (relative <> ": fixture did not run: " <> show failure)

    unexpected label failure =
        assertFailure
            (label <> " failed differently: "
                <> StrictText.unpack
                    (Elaboration.renderElaborationError failure))

keepsDefinitionResultsOnExactProvider :: Assertion
keepsDefinitionResultsOnExactProvider =
    withAcceptedFixtureVampire "notion-definition-result-provider" \prover ->
        checkFileFresh prover
            "test/phase9/notion-definition-result-wrapper-missing.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    Proof.ProofNotionUnavailable{}))
                            _prefix)
                    , _slowReport
                    ) -> pure ()
                Right result ->
                    assertFailure
                        ("transparent result wrapper failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("transparent result wrapper did not run: "
                            <> show failure)

usesIntrinsicProviderClassifications :: Assertion
usesIntrinsicProviderClassifications =
    withAcceptedFixtureVampire "notion-intrinsic-provider" \prover -> do
        withFreshVerificationSession \session -> do
            check session Verification.FreshStoreValidation prover
                "test/phase9/notion-intrinsic-provider.tex" >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("intrinsic provider fixture failed: " <> show result)
                Left failure ->
                    assertFailure
                        ("intrinsic provider fixture did not run: " <> show failure)

            for_ ["test/phase9/notion-product-projection-alternative.tex",
                  "test/phase9/notion-product-secondary-wrapper.tex"] \relative ->
                check session Verification.WarmStoreValidation prover relative >>= \case
                    Right (Verification.VerificationCompleted{}, _) -> pure ()
                    result -> assertFailure (relative <> ": product-provider fixture failed: " <> show result)

            for_
                [ "test/phase9/notion-intrinsic-powerset-missing.tex"
                , "test/phase9/notion-intrinsic-choice-missing.tex"
                , "test/phase9/notion-intrinsic-wrapper-missing.tex"
                , "test/phase9/notion-first-projection-missing.tex"
                , "test/phase9/notion-first-projection-wrapper.tex"
                , "test/phase9/notion-second-projection-missing.tex"
                , "test/phase9/notion-product-provider-wrapper.tex"
                ] \relative ->
                    check session Verification.WarmStoreValidation prover relative
                        >>= \case
                    Right
                        ( Verification.VerificationCheckingFailure _report
                            (Verification.VerificationTypedModuleError
                                _source actionFailure _prefix)
                        , _slowReport
                        )
                            | isMissingFormationRequirement actionFailure ->
                                pure ()
                    Right result ->
                        assertFailure
                            (relative <> ": intrinsic boundary failed differently: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": intrinsic boundary did not run: "
                                <> show failure)

            for_
                [ "test/phase9/notion-first-projection-wrong-endpoint.tex"
                , "test/phase9/notion-second-projection-wrong-endpoint.tex"
                ] \relative ->
                    check session Verification.WarmStoreValidation prover relative
                        >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source actionFailure _prefix)
                    , _slowReport
                    )
                        | isUnprovedProjectionEndpoint actionFailure -> pure ()
                Right result ->
                    assertFailure
                        (relative <> ": wrong projection endpoint failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        (relative <> ": wrong projection endpoint did not run: "
                            <> show failure)

            check session Verification.WarmStoreValidation prover
                "test/phase9/notion-first-projection-repeated-variable.tex"
                >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("repeated projection variable was not accepted: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("repeated projection variable did not run: "
                            <> show failure)
  where
    check session mode prover =
        checkFileWithSession
            session mode testSequentialJobs ignoredVerificationRequests
            prover

    isMissingFormationRequirement = \case
        Module.TypedActionFailed
                (Module.TypedElaborationFailed
                    Elaboration.ElaborationFormationRequirementMissing{}) ->
            True
        Module.TypedActionFailed
                (Module.TypedProofFailed
                    (Proof.ProofElaborationFailed
                        Elaboration.ElaborationFormationRequirementMissing{})) ->
            True
        _ -> False

    isUnprovedProjectionEndpoint = \case
        Module.TypedActionFailed
                (Module.TypedProofFailed
                    Proof.ProofObviousInferenceFailed{}) -> True
        Module.TypedActionFailed
                (Module.TypedProofFailed
                    Proof.ProofObviousInferenceReported{}) -> True
        _ -> False

distinguishesNullaryClassificationFailures :: Assertion
distinguishesNullaryClassificationFailures =
    withAcceptedFixtureVampire "notion-nullary-classification" \prover -> do
        checkFileFresh prover "test/phase9/notion-nullary-whole-missing.tex" >>= \case
            Right (Verification.VerificationCheckingFailure _
                (Verification.VerificationTypedModuleError _ actionFailure _), _) ->
                    case requirementFailure actionFailure of
                        Just (_,requirement@Elaboration.WholeFormationRequirementFailure{}) ->
                            assertBool "an existential requirement has no atomic nullary diagnostic"
                                (isNothing (extractDetail requirement))
                        _ -> assertFailure ("expected the whole existential requirement: " <> show actionFailure)
            result -> assertFailure ("whole nullary requirement failed differently: " <> show result)
        expectNullaryFailure prover
            "test/phase9/notion-nullary-classification-missing.tex"
            \failure classificationFailure -> do
                case classificationFailure of
                    Elaboration.NullaryClassificationMissing
                            Semantic.EmptySetProvider -> pure ()
                    other ->
                        assertFailure
                            ("missing nullary classification was diagnosed as "
                                <> show other)
                let rendered = Elaboration.renderElaborationError failure
                assertBool "missing diagnostic reports actual absence"
                    ("has no registered closed classification."
                        `StrictText.isInfixOf` rendered)

        expectNullaryFailure prover
            "test/phase9/notion-nullary-classification-unreachable.tex"
            \failure classificationFailure -> do
                case classificationFailure of
                    Elaboration.NullaryClassificationClosureMissing
                            Semantic.EmptySetProvider fingerprint _resultHead ->
                        assertBool "closure failure retains a fact fingerprint"
                            (not (null (show fingerprint)))
                    other ->
                        assertFailure
                            ("unreachable nullary classification was diagnosed as "
                                <> show other)
                let rendered = Elaboration.renderElaborationError failure
                assertBool "closure diagnostic names the registered result notion"
                    ("registered result notion \"finite\""
                        `StrictText.isInfixOf` rendered)
                assertBool "closure diagnostic does not report absence"
                    (not
                        ("has no registered closed classification."
                            `StrictText.isInfixOf` rendered))

        checkFileFresh prover
            "test/phase9/notion-nullary-classification-continuation.tex" >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("nullary unary-continuation fixture failed: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("nullary unary-continuation fixture did not run: "
                            <> show failure)
  where
    expectNullaryFailure prover relative check =
        checkFileFresh prover relative >>= \case
            Right
                ( Verification.VerificationCheckingFailure _report
                    (Verification.VerificationTypedModuleError
                        _source actionFailure _prefix)
                , _slowReport
                ) -> case nullaryFailure actionFailure of
                    Just result -> uncurry check result
                    Nothing ->
                        assertFailure
                            (relative
                                <> ": failed without a nullary-classification diagnostic: "
                                <> show actionFailure)
            Right result ->
                assertFailure
                    (relative <> ": unexpectedly did not fail: " <> show result)
            Left failure ->
                assertFailure
                    (relative <> ": did not run: " <> show failure)

    nullaryFailure actionFailure = do
        (failure,requirement) <- requirementFailure actionFailure
        pair failure <$> extractDetail requirement

    requirementFailure = \case
        Module.TypedActionFailed
                (Module.TypedElaborationFailed
                    failure@(Elaboration.ElaborationFormationRequirementMissing
                        _location requirement)) ->
            Just (failure,requirement)
        Module.TypedActionFailed
                (Module.TypedProofFailed
                    (Proof.ProofElaborationFailed
                        failure@(Elaboration.ElaborationFormationRequirementMissing
                            _location requirement))) ->
            Just (failure,requirement)
        _ -> Nothing

    extractDetail = \case
        Elaboration.FormationRequirementFailure
            { Elaboration.formationRequirementFailureDetail = Just (Elaboration.RichNullaryClassificationFailure value) } -> Just value
        Elaboration.FormationRequirementFailure{} -> Nothing
        Elaboration.WholeFormationRequirementFailure{} -> Nothing

    pair left right = (left, right)

accountsProviderDepthAndBucketWidth :: Assertion
accountsProviderDepthAndBucketWidth = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    fixtureMounts <- exactFixtureMounts repository
    registrationWorkspace <- parseWorkspace
        bootstrap fixtureMounts
        "test/phase9/notion-provider-rule-registration.tex"
    registrationModules <- compileParsedWorkspace
        foundation bootstrap registrationWorkspace
    registration <- case reverse registrationModules of
        root : _imports -> pure root
        [] -> assertFailure "provider registration workspace compiled no module"
            >> fail "unreachable"
    depthWork <- for [1 :: Int, 4, 16] \depth ->
        Temp.withSystemTempDirectory "felix-notion-provider-depth" \directory -> do
            let root = directory Posix.</> "root.tex"
            writeFile root (providerDepthSource depth)
            mounts <- generatedFixtureMounts repository directory
            statistics <- rejectedFormationStatistics
                foundation bootstrap mounts [registration]
            assertEqual "nested providers do not restart the Composite controller" 0
                (Notion.formationSearchCompositePremiseRequests statistics)
            pure (Notion.formationSearchViewInspections statistics)
    widthWork <- for [4 :: Int, 16, 64] \width ->
        Temp.withSystemTempDirectory "felix-notion-provider-width" \directory -> do
            let root = directory Posix.</> "root.tex"
            writeFile root (providerWidthSource width)
            mounts <- exactFixtureMounts directory
            statistics <- rejectedFormationStatistics
                foundation bootstrap mounts []
            assertEqual "wide rule buckets do not restart the Composite controller" 0
                (Notion.formationSearchCompositePremiseRequests statistics)
            pure (Notion.formationSearchViewInspections statistics)
    assertBool "nested provider work is charged as depth grows"
        (and (zipWith (<) depthWork (drop 1 depthWork)))
    assertBool "duplicate admitted rules do not increase query inspection work"
        (and (zipWith (==) widthWork (drop 1 widthWork)))
  where
    generatedFixtureMounts repository directory =
        expectRight
            =<< prepareSourceMounts
                [ (sourceMountId "generated", directory)
                , (sourceMountId "fixtures", repository)
                , (sourceMountId "library", repository Posix.</> "library")
                , (sourceMountId "debug", repository Posix.</> "debug")
                ]

    rejectedFormationStatistics foundation bootstrap mounts direct = do
        workspace <- parseWorkspace bootstrap mounts "root.tex"
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                (Parsed.parsedWorkspaceRootModule workspace)
                direct)
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed
                            (Elaboration.ElaborationFormationRequirementMissing
                                _location requirement)))
                    _prefix ->
                pure
                    (Elaboration.formationRequirementFailureSearchStatistics
                        requirement)
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofElaborationFailed
                                (Elaboration.ElaborationFormationRequirementMissing
                                    _location requirement))))
                    _prefix ->
                pure
                    (Elaboration.formationRequirementFailureSearchStatistics
                        requirement)
            Module.TypedModuleSucceeded{} ->
                assertFailure "generated provider resource fixture succeeded"
                    >> fail "unreachable"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("generated provider resource fixture did not open: "
                        <> show failure)
                    >> fail "unreachable"
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("generated provider resource fixture failed differently: "
                        <> StrictText.unpack
                            (Module.renderTypedModuleFailure failure))
                    >> fail "unreachable"

    providerDepthSource depth = unlines
        [ "\\import{test/phase9/notion-provider-rule-registration.tex}"
        , ""
        , "\\begin{proposition}\\label{notion_generated_provider_depth}"
        , "    $" <> nestedProvider depth "X" <> "$ is notion selected."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows."
        , "\\end{proof}"
        ]

    nestedProvider 0 argument = argument
    nestedProvider depth argument =
        "\\notionProviderValue{"
            <> nestedProvider (depth - 1) argument
            <> "}"

    providerWidthSource width = unlines
        ( [ "\\begin{definition}\\label{notion_width_input}"
          , "    $X$ is a notion width input iff $X=X$."
          , "\\end{definition}"
          , ""
          , "\\begin{definition}\\label{notion_width_output}"
          , "    $X$ is a notion width output iff $X=X$."
          , "\\end{definition}"
          , ""
          , "\\begin{definition}\\label{notion_width_final}"
          , "    $X$ is a notion width final iff $X=X$."
          , "\\end{definition}"
          , ""
          , "\\begin{definition}\\label{notion_width_provider}"
          , "    $\\notionWidthProvider{X}=X$."
          , "\\end{definition}"
          , ""
          ]
          <> concatMap widthRule [1 .. width]
          <> [ "\\begin{classification}\\label{notion_width_output_is_final}"
             , "    Let $X$ be a notion width output."
             , "    Then $X$ is a notion width final."
             , "\\end{classification}"
             , "\\begin{proof}"
             , "    Follows."
             , "\\end{proof}"
             , ""
             , "\\begin{definition}\\label{notion_width_selected}"
             , "    Let $X$ be a notion width final."
             , "    $X$ is notion width selected iff $X=X$."
             , "\\end{definition}"
             , ""
             , "\\begin{proposition}\\label{notion_generated_provider_width}"
             , "    $\\notionWidthProvider{X}$ is notion width selected."
             , "\\end{proposition}"
             , "\\begin{proof}"
             , "    Follows."
             , "\\end{proof}"
             ])

    widthRule ordinal =
        [ "\\begin{classification}\\label{notion_width_rule_"
            <> show ordinal <> "}"
        , "    Let $X$ be a notion width input."
        , "    Then $\\notionWidthProvider{X}$ is a notion width output."
        , "\\end{classification}"
        , "\\begin{proof}"
        , "    Follows."
        , "\\end{proof}"
        , ""
        ]


checksQuantifiedHeaderFormation :: Assertion
checksQuantifiedHeaderFormation = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    domainWorkspace <- parseWorkspace bootstrap mounts
        "test/phase9/notion-quantified-domain.tex"
    domains <- compileParsedWorkspace foundation bootstrap domainWorkspace
    for_ ["notion-quantified-phrase.tex", "notion-quantified-headers.tex", "notion-quantified-proof.tex", "notion-supplied-universal.tex", "notion-supplied-universal-import.tex", "notion-universal-alias.tex", "notion-quantified-unanchored.tex"] \name -> do
        workspace <- parseWorkspace bootstrap mounts ("test/phase9/" <> name)
        _ <- compileParsedWorkspace foundation bootstrap workspace
        pure ()
    for_ [ ("notion-quantified-missing.tex", 4)
         , ("notion-quantified-missing-guard.tex", 5)
         , ("notion-quantified-wrong-bound.tex", 6)
         , ("notion-quantified-cycle.tex", 6)
         ]
        \(name, line) -> do
            workspace <- parseWorkspace bootstrap mounts ("test/phase9/" <> name)
            input <- expectRightIO (typedModuleInput foundation
                (Module.bootstrapPreludeReadiness bootstrap) unusedResolver
                AlwaysMissValidation (Parsed.parsedWorkspaceRootModule workspace) domains)
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                    (Module.TypedActionFailed (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed
                            failure@(Elaboration.ElaborationFormationRequirementMissing location _)))) _ -> do
                    assertEqual "the later quantified adjective requires its own domain" line (locLine location)
                    assertBool "the missing requirement names the current bound subject"
                        ("requires that j is a quantified base"
                            `StrictText.isInfixOf` Elaboration.renderElaborationError failure)
                Module.TypedModuleFailed failure _ ->
                    assertFailure ("unexpected quantified-header failure: " <> show failure)
                Module.TypedModuleOpenFailed failure ->
                    assertFailure ("could not open quantified-header module: " <> show failure)
                Module.TypedModuleSucceeded{} ->
                    assertFailure "a quantified source discharged a missing or mismatched guard"


checksSuppliedUniversalRejections :: Assertion
checksSuppliedUniversalRejections = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    producer <- parseWorkspace bootstrap mounts "test/phase9/notion-supplied-universal.tex"
    dependencies <- compileParsedWorkspace foundation bootstrap producer
    producerModule <- case reverse dependencies of
        present : _ -> pure present
        [] -> fail "supplied-universal producer was not compiled"
    for_ ["wrong-bound", "finite-samples", "extra-guard", "missing-guard", "wrong-capture", "equality-only"] \name -> do
        -- Equality discharges the introduced membership guard at its complete
        -- set argument; the universal itself is still proved in a child scope.
        let supported = name `elem` ["missing-guard", "equality-only"]
        workspace <- parseWorkspace bootstrap mounts ("test/phase9/notion-supplied-" <> name <> ".tex")
        input <- expectRightIO (typedModuleInput foundation
            (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule workspace) [producerModule])
        runTypedModule input >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed
                (Module.TypedProofFailed Proof.ProofNotionUnavailable{})) _ ->
                    assertBool "a supplied or transported guard should discharge the introduced requirement" (not supported)
            Module.TypedModuleFailed failure _ -> assertFailure ("unexpected supplied-premise failure: " <> show failure)
            Module.TypedModuleOpenFailed failure -> assertFailure ("supplied-premise module did not open: " <> show failure)
            Module.TypedModuleSucceeded{} -> assertBool
                ("an incomplete supplied premise was accepted: " <> name) supported

    for_ [("definition-header", "ElaborationGuardedTransparentDefinition"),
          ("unanchored-rule", "must determine every parameter")] \(name, reason) -> do
        workspace <- parseWorkspace bootstrap mounts ("test/phase9/notion-supplied-" <> name <> ".tex")
        input <- expectRightIO (typedModuleInput foundation
            (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule workspace) [producerModule])
        runTypedModule input >>= \case
            Module.TypedModuleFailed failure _ -> assertBool
                ("wrong rejection for " <> name <> ": " <> show failure)
                (reason `StrictText.isInfixOf` StrictText.pack (show failure))
            Module.TypedModuleOpenFailed failure -> assertFailure (show failure)
            Module.TypedModuleSucceeded{} -> assertFailure ("an unsupported contract was accepted: " <> name)


checksSuppliedConstructionContract :: Assertion
checksSuppliedConstructionContract = withAcceptedFixtureVampire "supplied-construction" \prover ->
    withFreshVerificationSession \session -> do
        for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
            checkFileWithSession session mode testSequentialJobs ignoredVerificationRequests
                prover "test/phase9/notion-supplied-construction-header.tex" >>= \case
                    Right (Verification.VerificationCompleted{}, _) -> pure ()
                    result -> assertFailure ("whole contract/replay failed: " <> show result)
        for_ ["swapped", "guard"] \name ->
            checkFileWithSession session Verification.WarmStoreValidation testSequentialJobs ignoredVerificationRequests
                prover ("test/phase9/notion-whole-contract-" <> name <> ".tex") >>= \case
                    Right (Verification.VerificationCheckingFailure _
                        (Verification.VerificationTypedModuleError _ failure _), _) ->
                        assertBool ("unexpected whole contract rejection: " <> show failure)
                            ("WholeFormationRequirementFailure" `StrictText.isInfixOf` StrictText.pack (show failure))
                    result -> assertFailure (name <> ": a missing whole contract was accepted: " <> show result)


boundsRichAbbreviationExpansion :: Assertion
boundsRichAbbreviationExpansion = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    let name index = "\\expand" <> [toEnum (fromEnum 'a' + index)]
        declaration index body = unlines
            ["\\begin{abbreviation}\\label{expansion_" <> show index <> "}",
             "$" <> name index <> "{x} = " <> body <> "$.", "\\end{abbreviation}"]
        chain depth = concat [declaration index (if index == 0 then "(x,x)" else
            "(" <> name (index-1) <> "{x}," <> name (index-1) <> "{x})") | index <- [0..depth]]
        argument 0 = "x"
        argument depth = let prior = argument (depth-1) in "(" <> prior <> "," <> prior <> ")"
        largeUse = chain 0 <> unlines ["\\begin{proposition}\\label{large_expansion}",
            "Let $x$ be a set.", "Then $" <> name 0 <> "{" <> argument (13 :: Int) <> "} = x$.", "\\end{proposition}"]
        run source = Temp.withSystemTempDirectory "felix-bounded-expansion" \directory -> do
            writeFile (directory Posix.</> "root.tex") source
            mounts <- exactFixtureMounts directory
            workspace <- parseWorkspace bootstrap mounts "root.tex"
            input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule workspace) [])
            runTypedModule input
    run (chain 3) >>= \case
        Module.TypedModuleSucceeded{} -> pure ()
        Module.TypedModuleFailed failure _ -> assertFailure (StrictText.unpack (Module.renderTypedModuleFailure failure))
        _ -> assertFailure "ordinary nested expansion did not open"
    for_ [chain 14, largeUse] \source -> run source >>= \case
        Module.TypedModuleFailed (Module.TypedActionFailed failure) _ -> do
            elaboration <- case failure of
                Module.TypedElaborationFailed problem -> pure problem
                Module.TypedProofFailed (Proof.ProofElaborationFailed problem) -> pure problem
                _ -> assertFailure ("unexpected expansion failure: " <> show failure) >> fail "unreachable"
            case elaboration of
                Elaboration.ElaborationExpansionFailed _ _ problem
                    | Just _ <- Semantic.expansionRejectedDebit problem ->
                        assertBool "the diagnostic retains its body path"
                            ("body" `StrictText.isInfixOf` Semantic.renderExpansionFailure problem)
                _ -> assertFailure ("expansion escaped its own error boundary: " <> show elaboration)
        _ -> assertFailure "expansion escaped its own allowance"

-- Declaration descriptions may share execution, but remain independently
-- checked and addressable. Equal local sources are covered by capture tests.
deduplicatesDeclarationDescriptions :: Assertion
deduplicatesDeclarationDescriptions = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    let run copies complete = Temp.withSystemTempDirectory "felix-notion-description" \directory -> do
            writeFile (directory Posix.</> "root.tex") (source copies complete)
            mounts <- exactFixtureMounts directory
            workspace <- parseWorkspace bootstrap mounts "root.tex"
            input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule workspace) [])
            runTypedModule input
        missing copies = run copies False >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedElaborationFailed
                (Elaboration.ElaborationFormationRequirementMissing _ failure))) _ ->
                    pure (Notion.formationSearchRelevantViews
                        (Elaboration.formationRequirementFailureSearchStatistics failure))
            Module.TypedModuleFailed failure _ -> assertFailure (StrictText.unpack (Module.renderTypedModuleFailure failure)) >> fail "unreachable"
            _ -> assertFailure "duplicate control did not reach a missing requirement" >> fail "unreachable"
    one <- missing 1
    two <- missing 2
    assertBool "the live control enters registered search" (one > 0)
    assertEqual "live admission does not execute the duplicate description" one two
    root <- run 2 True >>= \case
        Module.TypedModuleSucceeded completed -> pure completed
        Module.TypedModuleFailed failure _ -> assertFailure (StrictText.unpack (Module.renderTypedModuleFailure failure)) >> fail "unreachable"
        _ -> assertFailure "duplicate classifications did not open" >> fail "unreachable"
    let semantic = completedModuleSemantic root
        batches = Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix root)
        sources = [registration | delta <- Semantic.semanticInterfaceDeclarations semantic,
            alias <- Semantic.declarationDeltaAliases delta,
            Semantic.semanticAliasName alias `elem` (Semantic.semanticName <$> ["dedup_0", "dedup_1"]),
            registration <- Semantic.declarationDeltaRegistrations delta,
            Semantic.registrationSource registration == Semantic.semanticAliasTarget alias]
        parents = [completedModuleEvidence (Module.bootstrapPreludeCompleted bootstrap)]
    assertEqual "both independently checked theorem sources are retained" 2 (length sources)
    readmitted <- expectRight =<< admitTestModule (Identity.theoryId foundation) parents semantic
        (concatMap Commit.committedBatchObjects batches)
        (concatMap Commit.committedBatchPropositions batches)
        (concatMap Commit.committedBatchValidationCertificates batches)
    for_ [completedModuleEvidence root, readmitted] \imported -> do
        driven <- expectRight =<< runModuleDriver foundation (Semantic.semanticInterfaceOwner semantic)
            (parents <> [imported]) unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver do
                registered <- fmap fst <$> Declaration.visibleFormationRegistrationsLowering
                addressed <- traverse (Declaration.resolveVisibleFormationSourceLowering . Semantic.registrationSource) sources
                catalog <- Declaration.formationCatalogLowering
                let selected = [branch | ordinal <- [0 .. FormationCatalog.catalogSize catalog - 1],
                        Just (Left (Notion.FormationViewRule view)) <- [FormationCatalog.lookupSource (fromIntegral ordinal) catalog],
                        let branch = Notion.visibleNotionViewSource view,
                        Semantic.semanticFactBranchFact branch `elem` (Semantic.registrationSource <$> sources)]
                pure (registered, isJust <$> addressed, selected))
        case driven of
            Declaration.DriverSucceeded (registered, addressed, selected) _ _ -> do
                assertBool "explicit registration lookup retains the later declaration"
                    (all (`elem` registered) sources)
                addressed @?= [True, True]
                assertEqual "import execution uses the earliest checked representative"
                    (take 1 (Semantic.registrationBranch <$> sources)) selected
            _ -> assertFailure "duplicate import did not prepare"
  where
    source copies complete = unlines
        ([ "\\begin{definition}\\label{dedup_root}"
         , "    $X$ is a dedup root iff $X=X$."
         , "\\end{definition}"
         , "\\begin{definition}\\label{dedup_base}"
         , "    $X$ is a dedup base iff $X=X$."
         , "\\end{definition}"
         ] <> concat
         [ [ "\\begin{classification}\\label{dedup_" <> show index <> "}"
           , "    Let $X$ be a dedup root."
           , "    Then $X$ is a dedup base."
           , "\\end{classification}"
           , "\\begin{proof}"
           , "    Follows."
           , "\\end{proof}"
           ] | index <- [0 .. copies - 1 :: Int]] <>
         [ "\\begin{definition}\\label{dedup_gate}"
         , "    Let $Y$ be a dedup base."
         , "    $\\dedupGate{Y}=Y$."
         , "\\end{definition}"
         , "\\begin{definition}\\label{dedup_consumer}"
         , "    Let $X$ be a dedup root."
         ] <> ["    Let $Y$ be a dedup root." | complete] <>
         [ "    $\\dedupConsumer{X}{Y}=\\dedupGate{Y}$."
         , "\\end{definition}"
         ])

checksGroupedFormationContracts :: Assertion
checksGroupedFormationContracts = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    let run width complete = Temp.withSystemTempDirectory "felix-notion-contract-group" \directory -> do
            writeFile (directory Posix.</> "root.tex") (source width complete)
            mounts <- exactFixtureMounts directory
            workspace <- parseWorkspace bootstrap mounts "root.tex"
            input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule workspace) [])
            runTypedModule input
        failed width = run width False >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedElaborationFailed
                (Elaboration.ElaborationFormationRequirementMissing _ requirement))) _ -> do
                    assertBool "the unproved distinct leaf remains the reported requirement"
                        ("Y" `StrictText.isInfixOf` StrictText.pack (show (formationRequirementPresentations requirement)))
                    pure (Elaboration.formationRequirementFailureSearchStatistics requirement)
            Module.TypedModuleFailed failure _ -> assertFailure (StrictText.unpack (Module.renderTypedModuleFailure failure)) >> fail "unreachable"
            _ -> assertFailure "a proved repeated leaf supplied its missing sibling" >> fail "unreachable"
    small <- failed 4
    large <- failed 64
    assertBool "the control performs source lookup" (Notion.formationSearchSourceIndexInspections small > 0)
    assertEqual "identical leaves reuse their completed search"
        (Notion.formationSearchSourceIndexInspections small) (Notion.formationSearchSourceIndexInspections large)
    assertBool "memo key and target work grows with the written leaf count"
        (Notion.formationSearchViewInspections large > Notion.formationSearchViewInspections small
            && Notion.formationSearchViewInspections large < 24 * Notion.formationSearchViewInspections small)
    run 64 True >>= \case
        Module.TypedModuleSucceeded{} -> pure ()
        Module.TypedModuleFailed failure _ -> assertFailure (StrictText.unpack (Module.renderTypedModuleFailure failure))
        _ -> assertFailure "the shared contract proof did not open"
  where
    variable index = "X_{" <> show (index :: Int) <> "}"
    argument value = "{" <> value <> "}"
    source width complete = unlines
        ([ "\\begin{definition}\\label{group_root}"
         , "    $X$ is a group root iff $X=X$."
         , "\\end{definition}"
         , "\\begin{definition}\\label{group_base}"
         , "    $X$ is a group base iff $X=X$."
         , "\\end{definition}"
         , "\\begin{classification}\\label{group_root_base}"
         , "    Let $X$ be a group root."
         , "    Then $X$ is a group base."
         , "\\end{classification}"
         , "\\begin{proof}"
         , "    Follows."
         , "\\end{proof}"
         , "\\begin{definition}\\label{group_gate}"
         ] <> ["    Let $" <> variable index <> "$ be a group base." | index <- [0..width-1]] <>
         [ "    Let $Y$ be a group base."
         , "    $\\groupGate" <> concatMap (argument . variable) [0..width-1] <> "{Y}=" <> variable 0 <> "$."
         , "\\end{definition}"
         , "\\begin{definition}\\label{group_consumer}"
         , "    Let $X$ be a group root."
         ] <> ["    Let $Y$ be a group root." | complete] <>
         [ "    $\\groupConsumer{X}{Y}=\\groupGate" <> concat (replicate width "{X}") <> "{Y}$."
         , "\\end{definition}"
         ])

checksMixedGroupPreparation :: Assertion
checksMixedGroupPreparation = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    Temp.withSystemTempDirectory "felix-notion-mixed-group" \directory -> do
        writeFile (directory Posix.</> "root.tex") source
        mounts <- exactFixtureMounts directory
        workspace <- parseWorkspace bootstrap mounts "root.tex"
        modules <- compileParsedWorkspace foundation bootstrap workspace
        let parsed = Parsed.parsedWorkspaceRootModule workspace
        Raw.Claim assumptions conclusion <- sole "mixed group consumer"
            [claim | Raw.BlockClaim _ _ _ marker claim <- Parsed.parsedModuleBlocks parsed, marker == "mixed_consumer"]
        for_ [False,True] \reversed -> do
            driven <- expectRight =<< runModuleDriver foundation
                (moduleName (Parsed.parsedModuleAddress parsed))
                (completedModuleEvidence <$> modules) unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    envelope <- Elaboration.elaborateClaimEnvelope assumptions conclusion >>= either (error . show) pure
                    let context = Elaboration.elaboratedClaimContext envelope
                        sources = [Elaboration.formationEvidenceSource
                            (Elaboration.elaborationContextSupport context)
                            (Elaboration.compiledHeaderCore header)
                            (Elaboration.compiledHeaderEvidence header) ordinal Elaboration.FormationProofAssumption
                            | (ordinal,header) <- zip [0..] (Elaboration.elaboratedClaimAntecedents envelope)]
                        assertions = Elaboration.elaboratedClaimConclusionAssertions envelope
                    active <- either (error . show) pure (foldM (flip Elaboration.addFormationPremiseSource) context sources)
                    (first,second) <- case if reversed then reverse assertions else assertions of
                        [a,b] -> pure (a,b)
                        _ -> error "mixed group lost its two distinct targets"
                    let goal = fromMaybe (error "mixed group contexts disagree")
                            (Core.conjoinExactScopedCore (Notion.sourceAssertionFormula first) (Notion.sourceAssertionFormula second))
                        evidence = SourceEvidence.SourceAnd (SourceEvidence.SourceAtom first) (SourceEvidence.SourceAtom second)
                    result <- Elaboration.prepareProofNotionGoalWithBudget
                        (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits) active Nowhere goal evidence
                    case result of
                        Right (Elaboration.NotionQueryFound proof,budget,_) -> do
                            closure <- Declaration.checkedObjectClosureLowering
                            replayed <- Declaration.replayTransientFormationLowering closure proof goal
                            pure (Notion.formationSearchBudgetDiagnostics budget,replayed)
                        Left failure -> error ("mixed group failed: " <> show failure)
                        Right (Elaboration.NotionQueryUnavailable failure,_,_) ->
                            error ("mixed group unavailable: " <> show failure)
                        Right (Elaboration.NotionQueryUnsupported,_,_) -> error "mixed group unsupported")
            case driven of
                Declaration.DriverSucceeded (diagnostics,replayed) _ _ -> do
                    void (expectRight replayed)
                    let count operation = Map.findWithDefault 0 operation (FormationDiagnostics.operationCounts diagnostics)
                    count FormationDiagnostics.SelectionPreparation @?= 1
                    count FormationDiagnostics.SourceInputMaterialization @?= 1
                    when (not reversed) (count FormationDiagnostics.SelectionReuse @?= 1)
                _ -> assertFailure "mixed group driver failed"
  where
    source = unlines
        [ "\\begin{definition}\\label{mixed_base}"
        , "    $X$ is a mixed base iff $X=X$."
        , "\\end{definition}"
        , "\\begin{definition}\\label{mixed_root}"
        , "    $X$ is a mixed root iff $X$ is a mixed base."
        , "\\end{definition}"
        , "\\begin{definition}\\label{mixed_final}"
        , "    $X$ is a mixed final iff $X=X$."
        , "\\end{definition}"
        , "\\begin{classification}\\label{mixed_rule}"
        , "    Let $X$ be a mixed base. Then $X$ is a mixed final."
        , "\\end{classification}"
        , "\\begin{proof} Follows. \\end{proof}"
        , "\\begin{proposition}\\label{mixed_consumer}"
        , "    Let $A,B$ be mixed roots."
        , "    Then $A$ is a mixed base and $B$ is a mixed final."
        , "\\end{proposition}"
        , "\\begin{proof} Follows by notion. \\end{proof}"
        ]

checksSetTermFormationContracts :: Assertion
checksSetTermFormationContracts = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    acceptedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-term-contract.tex"
    acceptedModules <-
        compileParsedWorkspace foundation bootstrap acceptedWorkspace
    accepted <- case reverse acceptedModules of
        root : _imports -> pure root
        [] -> assertFailure "set-term contract workspace compiled no module"
            >> fail "unreachable"
    let bindings =
            [ binding
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix accepted)
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta batch))
            ]
        contractedLabels =
            [ Semantic.semanticBindingLabelText
                (Semantic.semanticGlobalBindingLabel binding)
            | binding <- bindings
            , isJust (Semantic.semanticGlobalBindingContract binding)
            ]
    assertEqual "every hosted set term carries its checked contract"
        [ "notion_term_value"
        , "notion_term_wrapper"
        , "notion_membership_value"
        , "notion_membership_wrapper"
        , "notion_binary_term"
        ]
        contractedLabels

    compositeWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-composite-contract.tex"
    compositeModules <-
        compileParsedWorkspace foundation bootstrap compositeWorkspace
    assertBool "a provider-valued header contract extracts and discharges"
        (not (null compositeModules))

    let checkRejected relative expectedLine selected requirementText = do
            rejectedWorkspace <- parseWorkspace bootstrap mounts relative
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule rejectedWorkspace)
                    [accepted])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedElaborationFailed
                                (Elaboration.ElaborationFormationRequirementMissing
                                    location requirement)))
                        prefix -> do
                    let rendered = Elaboration.renderElaborationError
                            (Elaboration.ElaborationFormationRequirementMissing
                                location requirement)
                    assertEqual (relative <> " requirement line")
                        expectedLine (locLine location)
                    assertBool (relative <> " selected declaration")
                        (("selected declaration \"" <> selected <> "\"")
                            `StrictText.isInfixOf` rendered)
                    assertBool (relative <> " source requirement")
                        (requirementText `StrictText.isInfixOf` rendered)
                    assertBool (relative <> " hides internal ground keys")
                        (not ("GroundNotionKey"
                            `StrictText.isInfixOf` rendered))
                    assertBool (relative <> " publishes no failed prefix")
                        (null (Commit.pendingModulePrefixBatches prefix))
                Module.TypedModuleSucceeded{} ->
                    assertFailure
                        (relative <> ": missing requirement was admitted")
                Module.TypedModuleOpenFailed{} ->
                    assertFailure (relative <> ": fixture did not open")
                Module.TypedModuleFailed{} ->
                    assertFailure (relative <> ": failed differently")

    checkRejected
        "test/phase9/notion-term-contract-missing.tex"
        4
        "notion_term_value"
        "requires that X is a notion base"
    checkRejected
        "test/phase9/notion-term-contract-sibling-missing.tex"
        5
        "notion_binary_term"
        "requires that Y is a notion base"

    checkRejected
        "test/phase9/notion-term-contract-discarded-missing.tex"
        4
        "notion_term_value"
        "requires that Y is a notion base"


checksHostedDefinitionConjunctionGuards :: Assertion
checksHostedDefinitionConjunctionGuards = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    contractWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-term-contract.tex"
    contractModules <-
        compileParsedWorkspace foundation bootstrap contractWorkspace
    contract <- case reverse contractModules of
        root : _imports -> pure root
        [] -> assertFailure "term-contract workspace compiled no module"
            >> fail "unreachable"

    let runRoot relative = do
            workspace <- parseWorkspace bootstrap mounts relative
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule workspace)
                    [contract])
            runTypedModule input

    runRoot "test/phase9/notion-definition-conjunction-guard.tex"
        >>= \case
            Module.TypedModuleSucceeded{} -> pure ()
            result -> unexpected
                "left-to-right definition conjunction failed" result

    runRoot "test/phase9/notion-definition-disjunction-guard.tex"
        >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed
                            (Elaboration.ElaborationFormationRequirementMissing
                                location _requirement)))
                    prefix -> do
                assertEqual "disjunction does not carry formation evidence"
                    6 (locLine location)
                assertBool "failed definition publishes no partial declaration"
                    (null (Commit.pendingModulePrefixBatches prefix))
            result -> unexpected
                "excluded connective crossed the definition guard" result
  where
    unexpected label = \case
        Module.TypedModuleOpenFailed failure ->
            assertFailure (label <> ": " <> show failure)
        Module.TypedModuleFailed failure _prefix ->
            assertFailure
                (label <> ": "
                    <> StrictText.unpack
                        (Module.renderTypedModuleFailure failure))
        Module.TypedModuleSucceeded{} ->
            assertFailure (label <> ": module unexpectedly succeeded")


checksReadabilityVocabulary :: Assertion
checksReadabilityVocabulary =
    withAcceptedFixtureVampire "readability-vocabulary" \prover ->
        checkFileFresh prover "test/phase9/readability-vocabulary.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _report) -> pure ()
            result -> assertFailure ("readability vocabulary failed: " <> show result)

checksBoundedNounEquivalences :: Assertion
checksBoundedNounEquivalences =
    withAcceptedFixtureVampire "readability-bounded-equivalence" \prover ->
        checkFileFresh prover "test/phase9/readability-bounded-equivalence.tex" >>= \case
            Right (Verification.VerificationCompleted{}, _report) -> pure ()
            result -> assertFailure ("bounded noun equivalence failed: " <> show result)

checksLibraryProviderFormationContracts :: Assertion
checksLibraryProviderFormationContracts =
    withAcceptedFixtureVampire "notion-library-provider-contracts" \prover -> do
        withFreshVerificationSession \session -> do
            check session Verification.FreshStoreValidation prover
                "test/phase9/notion-library-provider-contracts.tex" >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("library provider contract fixture failed: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("library provider contract fixture did not run: "
                            <> show failure)

            for_
                [ "test/phase9/notion-library-closure-total.tex"
                , "test/phase9/notion-library-generated-total-group.tex"
                , "test/phase9/notion-library-generated-total-subset.tex"
                ] \relative ->
                    check session Verification.WarmStoreValidation prover relative
                        >>= \case
                    Right (Verification.VerificationCompleted{}, _slowReport) ->
                        pure ()
                    Right result ->
                        assertFailure
                            (relative <> ": total construction failed: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": total construction did not run: "
                                <> show failure)

            for_
                [ ( "test/phase9/notion-library-normal-closure-missing-subset.tex"
                  , "normal_closure"
                  , "requires that A \\subseteq"
                  )
                , ( "test/phase9/notion-library-cyclic-missing-member.tex"
                  , "cyclic_subgroup"
                  , "requires that a is an element of"
                  )
                ] \(relative, selected, requirementText) ->
                    check session Verification.WarmStoreValidation prover relative
                        >>= \case
                    Right
                        ( Verification.VerificationCheckingFailure _report
                            (Verification.VerificationTypedModuleError
                                _source
                                (Module.TypedActionFailed
                                    (Module.TypedElaborationFailed
                                        failure@(
                                            Elaboration.ElaborationFormationRequirementMissing{})))
                                _prefix)
                        , _slowReport
                        ) -> do
                            let rendered =
                                    Elaboration.renderElaborationError failure
                            assertBool (relative <> ": selected declaration")
                                (("selected declaration \"" <> selected <> "\"")
                                    `StrictText.isInfixOf` rendered)
                            assertBool (relative <> ": source requirement")
                                (requirementText
                                    `StrictText.isInfixOf` rendered)
                    Right result ->
                        assertFailure
                            (relative <> ": contract failed differently: "
                                <> show result)
                    Left failure ->
                        assertFailure
                            (relative <> ": contract fixture did not run: "
                                <> show failure)
  where
    check session mode prover =
        checkFileWithSession
            session mode testSequentialJobs ignoredVerificationRequests
            prover


preservesHostedContractAndBaseProjectionOrder :: Assertion
preservesHostedContractAndBaseProjectionOrder = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <-
        parseWorkspace
            bootstrap mounts "test/phase9/notion-contract-order.tex"
    moduleValue <- sole "ordered hosted notion module"
        =<< compileParsedWorkspace foundation bootstrap workspace
    let deltas =
            [ Commit.committedBatchDelta batch
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix moduleValue)
            ]
        bindings =
            [ binding
            | delta <- deltas
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment delta)
            ]
        bindingsByKey = Map.fromList
            [ (Semantic.semanticGlobalBindingKey binding, binding)
            | binding <- bindings
            ]
        bindingLabel binding =
            Semantic.semanticBindingLabelText
                (Semantic.semanticGlobalBindingLabel binding)
        labelForReference reference =
            bindingLabel
                <$> Map.lookup
                    (Semantic.globalBindingRefKey reference)
                    bindingsByKey
        renderOccurrenceTemplate = \case
            Semantic.AtomicLeaf (Semantic.GlobalAtomTemplate
                    (Semantic.NounNotionHead reference) arguments) ->
                fmap
                    (\label -> (label, toList arguments))
                    (labelForReference reference)
            template ->
                error
                    ("unexpected hosted-order notion template: "
                        <> show template)
        orderedBinding =
            fromMaybe
                (error "missing ordered hosted notion binding")
                (find
                    ((== "notion_ordered_object") . bindingLabel)
                    bindings)
        orderedKey = Semantic.semanticGlobalBindingKey orderedBinding
        contractRequirements =
            maybe []
                (toList . Semantic.formationContractRequirements)
                (Semantic.semanticGlobalBindingContract orderedBinding)
        orderedViews =
            [ view
            | delta <- deltas
            , view <- (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry]) delta
            , Semantic.GlobalNotionViewPremise
                (Semantic.NounNotionHead reference) _arguments <-
                    [Semantic.notionViewPremise view]
            , Semantic.globalBindingRefKey reference == orderedKey
            ]
        renderViewConclusion view =
            case Semantic.notionViewConclusion view of
                Semantic.AtomicLeaf (Semantic.GlobalAtomTemplate
                        (Semantic.NounNotionHead reference) arguments) ->
                    Right $ fmap
                        (\label -> (label, toList arguments))
                        (labelForReference reference)
                Semantic.WholeLeaf (Semantic.ResidualTemplate formula) -> Left formula
                template ->
                    error
                        ("unexpected hosted-order view conclusion: "
                            <> show template)
        expectedContract =
            [ ( "notion_order_base_b"
              , [ Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 1)
                ]
              )
            , ( "notion_order_base_a"
              , [ Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 1)
                ]
              )
            ]
        expectedBases =
            [ ( "notion_order_base_b"
              , [Semantic.TemplateVariable (Semantic.ViewVariableIx 1)]
              )
            , ( "notion_order_base_a"
              , [Semantic.TemplateVariable (Semantic.ViewVariableIx 1)]
              )
            , ( "notion_order_base_b"
              , [Semantic.TemplateVariable (Semantic.ViewVariableIx 0)]
              )
            , ( "notion_order_base_a"
              , [Semantic.TemplateVariable (Semantic.ViewVariableIx 0)]
              )
            ]
    assertEqual "contract keeps first exact requirement in source order"
        (Just <$> expectedContract)
        (renderOccurrenceTemplate <$> contractRequirements)
    assertEqual "projections retain both subjects and the whole body in source order"
        ((Right . Just <$> expectedBases) <>
            [Left (Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 1))])
        (renderViewConclusion <$> orderedViews)


composesPositiveDefinitions :: Assertion
composesPositiveDefinitions = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-definition-chain.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "definition-chain fixture compiled no module"
            >> fail "unreachable"
    importedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-definition-chain-import.tex"
    void (compileParsedWorkspace foundation bootstrap importedWorkspace)
    for_
        [ ("reverse", True)
        , ("disjunction", False)
        , ("wrong-argument", False)
        ] \(suffix, proofFailure) -> do
            let relative = "test/phase9/notion-definition-chain-" <> suffix <> ".tex"
            negativeWorkspace <- parseWorkspace bootstrap mounts relative
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule negativeWorkspace)
                    [root])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedProofFailed failure)) _prefix ->
                    case failure of
                        Proof.ProofNotionUnavailable{} | proofFailure -> pure ()
                        Proof.ProofElaborationFailed
                                Elaboration.ElaborationFormationRequirementMissing{}
                            | not proofFailure -> pure ()
                        _ -> assertFailure (relative <> ": " <> show failure)
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure (relative <> ": " <> show failure)
                Module.TypedModuleSucceeded{} ->
                    assertFailure (relative <> ": an invalid view was accepted")
                Module.TypedModuleOpenFailed failure ->
                    assertFailure (relative <> ": " <> show failure)

publishesPrefixDefinitionProjections :: Assertion
publishesPrefixDefinitionProjections = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-definition-projection.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    root <- case reverse modules of
        current : _imports -> pure current
        [] -> assertFailure "prefix-projection workspace compiled no module"
            >> fail "unreachable"
    let moduleBatches sealed =
            Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed)
        rootBatches = moduleBatches root
        rootDeltas =
            Commit.committedBatchDelta <$> rootBatches
        bindings =
            [ binding
            | sealed <- modules
            , batch <- moduleBatches sealed
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta batch))
            ]
        bindingLabel =
            Semantic.semanticBindingLabelText
                . Semantic.semanticGlobalBindingLabel
        bindingByLabel label =
            fromMaybe
                (error ("missing binding " <> StrictText.unpack label))
                (find ((== label) . bindingLabel) bindings)
        bindingKey label =
            Semantic.semanticGlobalBindingKey (bindingByLabel label)
        referenceLabel reference =
            bindingLabel
                <$> find
                    ((== Semantic.globalBindingRefKey reference)
                        . Semantic.semanticGlobalBindingKey)
                    bindings
        guardKey = bindingKey "notion_projection_guard"
        descriptiveKey = bindingKey "notion_projection_descriptive"
        views = concatMap (\entry -> [(registration, rule) | registration@(Semantic.Registration _ _ (Semantic.RegisterNotionView rule)) <- Semantic.declarationDeltaRegistrations entry]) rootDeltas
        guardViews =
            [ (registration, view)
            | (registration, view) <- views
            , Semantic.GlobalNotionViewPremise
                (Semantic.PrefixPredicateNotionHead reference)
                _arguments <- [Semantic.notionViewPremise view]
            , Semantic.globalBindingRefKey reference == guardKey
            ]
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        pair = Semantic.TemplateOrderedPair variable variable
        renderConclusion (_, view) =
            case Semantic.notionViewConclusion view of
                Semantic.AtomicLeaf (Semantic.GlobalAtomTemplate head' arguments) ->
                    Right $ (\label -> (label, toList arguments))
                        <$> referenceLabel (Semantic.globalNotionHeadReference head')
                Semantic.WholeLeaf (Semantic.ResidualTemplate formula) -> Left formula
                conclusion -> error
                    ("unexpected prefix-definition projection: "
                        <> show conclusion)
        facts =
            [ fact
            | delta <- rootDeltas
            , fact <- Semantic.declarationDeltaFacts delta
            ]
        propositions =
            [ proposition
            | batch <- rootBatches
            , proposition <- Commit.committedBatchPropositions batch
            ]
        factByFingerprint = Map.fromList
            [ (Semantic.semanticFactFingerprint fact, fact)
            | fact <- facts
            ]
        propositionById = Map.fromList
            [ (Identity.checkedPropositionId proposition, proposition)
            | proposition <- propositions
            ]
        viewProposition (registration, _) = do
            fact <- Map.lookup
                (Semantic.registrationSource registration)
                factByFingerprint
            proposition <- Map.lookup
                (Semantic.semanticFactProposition fact)
                propositionById
            pure
                (Core.frozenCoreTerm
                    (Identity.checkedPropositionTerm proposition))
        object label =
            Semantic.semanticGlobalTargetObject
                (Semantic.semanticGlobalBindingTarget
                    (bindingByLabel label))
        bound = Core.CBound 0
        guardPredicate = Core.CApp
            (Core.CGlobal (object "notion_projection_guard")) bound
        base term = Core.CApp
            (Core.CGlobal (object "notion_base")) term
        orderedPair = Core.CApp
            (Core.CApp (Core.CIntrinsic Core.OrderedPair) bound) bound
        disjunction = Core.COr
            (Core.CApp (Core.CGlobal (object "notion_excluded_projection")) bound)
            (Core.CEq Core.TySet bound bound)
        expectedPropositions =
            [ Core.CForall Core.TySet (Core.CImp guardPredicate (base bound))
            , Core.CForall Core.TySet
                (Core.CImp guardPredicate (base orderedPair))
            , Core.CForall Core.TySet
                (Core.CImp guardPredicate
                    (Core.CApp
                        (Core.CGlobal (object "notion_projection_terminal")) bound))
            , Core.CForall Core.TySet (Core.CImp guardPredicate disjunction)
            ]
        viewFingerprints =
            Semantic.registrationSource . fst <$> guardViews
    guardAlias <- sole "prefix-definition equation alias"
        [ alias
        | delta <- rootDeltas
        , alias <- Semantic.declarationDeltaAliases delta
        , Semantic.semanticAliasName alias
            == Semantic.semanticName "notion_projection_guard"
        ]
    assertEqual "the prefix definition retains atomic leaves and the exact disjunction"
        [ Right (Just ("notion_base", [variable]))
        , Right (Just ("notion_base", [pair]))
        , Right (Just ("notion_projection_terminal", [variable]))
        , Left disjunction
        ]
        (renderConclusion <$> guardViews)
    assertEqual "each generated view has its exact checked theorem"
        (Just <$> expectedPropositions)
        (viewProposition <$> guardViews)
    let authorizations = Map.fromList
            [ (Semantic.semanticFactFingerprint fact, Authority.validationDirectAuthorization certificate)
            | batch <- rootBatches
            , (fact, certificate) <- zip
                (Semantic.declarationDeltaFacts (Commit.committedBatchDelta batch))
                (Commit.committedBatchValidationCertificates batch)
            ]
    for_ guardViews \(registration, _) ->
        case Map.lookup (Semantic.registrationSource registration) authorizations of
            Just (Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionProjection identity _path)) ->
                assertEqual "projection authorization names its own definition"
                    (object "notion_projection_guard") identity
            other -> assertFailure ("missing exact definition projection: " <> show other)
    let semantic = completedModuleSemantic root
        parents =
            [ completedModuleEvidence sealed
            | sealed <- Module.bootstrapPreludeCompleted bootstrap : modules
            , Semantic.semanticInterfaceAssertedId (completedModuleSemantic sealed)
                `elem` Semantic.semanticInterfaceDirectInputs semantic
            ]
        originalCertificates = concatMap Commit.committedBatchValidationCertificates rootBatches
        admit certificates = admitTestModule (Identity.theoryId foundation) parents semantic
            (concatMap Commit.committedBatchObjects rootBatches) propositions certificates
    portable <- for originalCertificates \certificate ->
        expectRight (decodeCache Authority.getValidationCertificateCache
            (encodeCache (Authority.putValidationCertificateCache certificate)))
    void (expectRight =<< admit portable)
    let retag change certificate =
            case Authority.validationDirectAuthorization certificate of
                Authority.CheckedKernelConstruction (Authority.CheckedDefinitionProjection identity path) ->
                    expectRight (Authority.validationCertificate (Authority.validationTarget certificate)
                        (Authority.CheckedKernelConstruction (change identity path)))
                _ -> pure certificate
    for_
        [ ("wrong imported selector", \identity path ->
            Authority.CheckedDefinitionProjection identity (Notion.ConjunctionLeft path))
        , ("wrong imported definition", \_ path ->
            Authority.CheckedDefinitionProjection (object "notion_projection_terminal") path)
        ] \(label, change) -> do
            tampered <- traverse (retag change) portable
            admit tampered >>= \case
                Left Declaration.NotionViewMaterializationInvalid{} -> pure ()
                Left failure -> assertFailure (label <> ": " <> show failure)
                Right _ -> assertFailure (label <> " was admitted")
    assertEqual "each generated theorem has a distinct view fingerprint"
        4 (Set.size (Set.fromList viewFingerprints))
    assertBool "view fingerprints remain distinct from the definition equation"
        (all
            (/= Semantic.semanticAliasTarget guardAlias)
            viewFingerprints)
    assertEqual "the adjective exposes its positive body through the same view path"
        [Right (Just ("notion_base", [variable]))]
        [ renderConclusion entry
        | entry@(_, view) <- views
        , Semantic.GlobalNotionViewPremise head' _arguments <-
            [Semantic.notionViewPremise view]
        , Semantic.globalBindingRefKey (Semantic.globalNotionHeadReference head')
            == descriptiveKey
        ]

    let runNegative relative = do
            negativeWorkspace <- parseWorkspace bootstrap mounts relative
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule negativeWorkspace)
                    [root])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedProofFailed
                                Proof.ProofNotionUnavailable{}))
                        _prefix -> pure ()
                Module.TypedModuleOpenFailed failure ->
                    assertFailure (relative <> ": " <> show failure)
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        (relative <> ": "
                            <> StrictText.unpack
                                (Module.renderTypedModuleFailure failure))
                Module.TypedModuleSucceeded{} ->
                    assertFailure
                        (relative <> ": excluded projection was synthesized")
    terminalWorkspace <- parseWorkspace bootstrap mounts
        "test/phase9/notion-definition-projection-prefix-result.tex"
    void (compileParsedWorkspace foundation bootstrap terminalWorkspace)
    runNegative
        "test/phase9/notion-definition-projection-excluded-negative.tex"

nestedApplicationPresentation :: Int -> Text
nestedApplicationPresentation depth =
    StrictText.concat (replicate depth "f(")
        <> "x"
        <> StrictText.concat (replicate depth ")")

handlesRepeatedSameHeadNotionQueries :: Assertion
handlesRepeatedSameHeadNotionQueries =
    checkFileFresh
        (Provers.vampire
            "vampire"
            Provers.defaultTimeLimit
            Provers.defaultMemoryLimit)
        "test/phase9/notion-repeated-query.tex"
        >>= \case
            Right (Verification.VerificationCompleted{}, _slowReport) -> pure ()
            Right _result ->
                assertFailure "the repeated notion-query fixture failed"
            Left failure ->
                assertFailure
                    ("the repeated notion-query fixture did not run: "
                        <> show failure)

distinctNotionHeadElaborationCase :: Natural -> TestTree
distinctNotionHeadElaborationCase size =
    testGroup (show size)
        [ testCase "many sources, one requested head"
            (checksDistinctNotionHeadElaboration size 1 1)
        , testCase "one source, many requested heads"
            (checksDistinctNotionHeadElaboration 1 size 1)
        , testCase "many sources and requested heads"
            (checksDistinctNotionHeadElaboration size size 1)
        , testCase "repeated requests for one extracted head"
            (checksDistinctNotionHeadElaboration size 1 size)
        ]

checksDistinctNotionHeadElaboration
    :: Natural
    -> Natural
    -> Natural
    -> Assertion
checksDistinctNotionHeadElaboration sourceCount headCount repetitions =
    Temp.withSystemTempDirectory "felix-notion-head-matrix" \root -> do
        let relative = "notion-head-matrix.tex"
            sourcePath = root Posix.</> relative
            source = notionHeadMatrixSource
                sourceCount headCount repetitions
        ByteString.writeFile sourcePath (Text.encodeUtf8 source)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <- expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        sealed <- compileParsedWorkspace foundation bootstrap workspace
        void (sole "notion head matrix module" sealed)

notionHeadMatrixSource :: Natural -> Natural -> Natural -> Text
notionHeadMatrixSource sourceCount headCount repetitions =
    StrictText.unlines
        ( [ definition "matrix_root" "matrixroot"
          ]
        <> [ definition
                ("matrix_noise_" <> suffix index)
                ("matrixnoise" <> suffix index)
           | index <- indices (sourceCount - 1)
           ]
        <> concat
            [ [ definition
                    ("matrix_base_" <> suffix index)
                    ("matrixbase" <> suffix index)
              , hostedDefinition index
              , notionView index
              ]
            | index <- indices headCount
            ]
        <> [ consumer ]
        )
  where
    suffix = StrictText.concat . reverse . letters . (+ 1)
      where
        letters 0 = []
        letters value =
            let (quotient, remainder) = (value - 1) `divMod` 25
            in letter remainder : letters quotient
        letter offset =
            let skipPluralSuffix = if offset >= 18 then 1 else 0
            in StrictText.singleton
                (toEnum
                    (fromEnum 'a' + fromIntegral offset + skipPluralSuffix)
                    :: Char)
    number :: Natural -> StrictText.Text
    number value =
        "\\opaqueInteger{" <> StrictText.pack (show value) <> "}"
    indices indexCount =
        take (fromIntegral indexCount) ([0 ..] :: [Natural])

    definition label noun = StrictText.unlines
        [ "\\begin{definition}\\label{" <> label <> "}"
        , "    $X$ is a " <> noun <> " iff $X=X$."
        , "\\end{definition}"
        ]

    hostedDefinition index = StrictText.unlines
        [ "\\begin{definition}\\label{matrix_guard_" <> suffix index <> "}"
        , "    Let $X$ be a matrixbase" <> suffix index <> "."
        , "    $X$ is matrixguard" <> suffix index <> " iff $X=X$."
        , "\\end{definition}"
        ]

    notionView index = StrictText.unlines
        [ "\\begin{classification}\\label{matrix_view_" <> suffix index <> "}"
        , "    Let $X$ be a matrixroot."
        , "    Then $X$ is a matrixbase" <> suffix index <> "."
        , "\\end{classification}"
        , "\\begin{proof}"
        , "    Follows."
        , "\\end{proof}"
        ]

    activeSources =
        [ "    Suppose $" <> number 0 <> "$ is a matrixroot." ]
        <> [ "    Suppose $" <> number (index + 1)
                <> "$ is a matrixnoise" <> suffix index <> "."
           | index <- indices (sourceCount - 1)
           ]

    distinctGoals =
        [ "$" <> number 0 <> "$ is matrixguard" <> suffix index
        | index <- indices headCount
        ]
    repeatedGoals = concat (replicate (fromIntegral repetitions) distinctGoals)
    consumer = StrictText.unlines
        ( [ "\\begin{proposition}\\label{matrix_consumer}"
          ]
        <> activeSources
        <> [ "    Then " <> StrictText.intercalate " and " repeatedGoals <> "."
           , "\\end{proposition}"
           , "\\begin{proof}"
           , "    Follows."
           , "\\end{proof}"
           ]
        )

formationRequirementPresentations
    :: Elaboration.FormationRequirementFailure
    -> [Elaboration.SourceTermPresentation]
formationRequirementPresentations failure =
    toList (Elaboration.formationRequirementFailureRequirement failure)

hostedPredicateFormationTests :: TestTree
hostedPredicateFormationTests =
    withResource hostedPredicateFormationFixture (const (pure ())) \fixture ->
        testGroup "hosted predicate formation"
            [ testCase "declarations and domain closure"
                (fixture >>= checksHostedPredicateDeclarations)
            , testCase "deep presentation store admission"
                (fixture >>= checksHostedPredicateStoreDepth)
            , testCase "direct and view-derived evidence"
                (fixture >>= checksHostedPredicateEvidence)
            , testCase "guarded scopes and negative evidence"
                (fixture >>= checksHostedPredicateGuardScopes)
            , testCase "source-oriented diagnostics"
                (fixture >>= checksHostedPredicateDiagnostics)
            , testCase "membership and structure integration"
                (fixture >>= checksHostedPredicateMembershipAndStructures)
            ]

data HostedPredicateFormationFixture = HostedPredicateFormationFixture
    !Foundation.CheckedFoundation
    !Module.BootstrapPreludeFixture
    !SourceMounts
    !Module.CompletedTypedModule

hostedPredicateFormationFixture :: IO HostedPredicateFormationFixture
hostedPredicateFormationFixture = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight
        =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    acceptedWorkspace <- parseWorkspace
        bootstrap mounts "test/phase9/notion-direct.tex"
    accepted <- sole "hosted notion module"
        =<< compileParsedWorkspace foundation bootstrap acceptedWorkspace
    pure (HostedPredicateFormationFixture
        foundation bootstrap mounts accepted)

withHostedPredicateStore
    :: HostedPredicateFormationFixture
    -> (Store.Store -> Provers.Vampire -> Assertion)
    -> Assertion
withHostedPredicateStore
        (HostedPredicateFormationFixture foundation _bootstrap _mounts _accepted)
        action =
    Temp.withSystemTempDirectory "felix-notion-integration" \directory -> do
        let storePath = directory Posix.</> "store.sqlite"
            prover = Provers.vampire
                "vampire"
                Provers.defaultTimeLimit
                Provers.defaultMemoryLimit
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            (\store -> action store prover)

checksHostedPredicateDeclarations
    :: HostedPredicateFormationFixture
    -> Assertion
checksHostedPredicateDeclarations
        (HostedPredicateFormationFixture _foundation _bootstrap _mounts accepted) = do
    let bindings =
            [ binding
            | batch <- Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix accepted)
            , binding <- Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta batch))
            ]
    assertEqual "hosted notion binding count" 3 (length bindings)
    assertEqual "only hosted predicates carry contracts" 2
        (length
            [ ()
            | binding <- bindings
            , isJust (Semantic.semanticGlobalBindingContract binding)
            ])

checksHostedPredicateDiagnostics
    :: HostedPredicateFormationFixture
    -> Assertion
checksHostedPredicateDiagnostics
        (HostedPredicateFormationFixture foundation bootstrap mounts accepted) = do
    rejectedWorkspace <-
        parseWorkspace
            bootstrap mounts "test/phase9/notion-direct-missing.tex"
    input <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule rejectedWorkspace)
            [accepted])
    runTypedModule input >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedElaborationFailed
                        (Elaboration.ElaborationFormationRequirementMissing
                            location requirement)))
                prefix -> do
            let rendered = Elaboration.renderElaborationError
                    (Elaboration.ElaborationFormationRequirementMissing
                        location requirement)
            assertEqual "missing notion requirement line" 4 (locLine location)
            case formationRequirementPresentations requirement of
                [Elaboration.PresentedSourceTerm argumentLocation "X"] ->
                    assertEqual "source argument location"
                        4 (locLine argumentLocation)
                arguments ->
                    assertFailure
                        ("unexpected structured source argument: "
                            <> show arguments)
            assertBool "diagnostic names the selected declaration"
                ("selected declaration \"notion_guarded\""
                    `StrictText.isInfixOf` rendered)
            assertBool "diagnostic renders the source-level requirement"
                ("requires that X is a notion base"
                    `StrictText.isInfixOf` rendered)
            assertBool "diagnostic does not expose a ground-key constructor"
                (not ("GroundNotionKey"
                    `StrictText.isInfixOf` rendered))
            assertBool "failed definition publishes no partial declaration"
                (null (Commit.pendingModulePrefixBatches prefix))
        Module.TypedModuleSucceeded{} ->
            assertFailure "the missing notion requirement was admitted"
        Module.TypedModuleOpenFailed{} ->
            assertFailure "the negative notion fixture did not open"
        Module.TypedModuleFailed{} ->
            assertFailure
                "checking rejected the negative notion fixture differently"

    presentationBaseWorkspace <-
        parseWorkspace
            bootstrap mounts "test/phase9/notion-presentation-base.tex"
    presentationBaseInput <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule presentationBaseWorkspace)
            [accepted])
    presentationBase <- runTypedModule presentationBaseInput >>= \case
        Module.TypedModuleSucceeded moduleValue -> pure moduleValue
        Module.TypedModuleOpenFailed failure ->
            assertFailure
                ("notion presentation base did not open: " <> show failure)
                >> fail "unreachable"
        Module.TypedModuleFailed failure _prefix ->
            assertFailure
                ("notion presentation base failed: " <> show failure)
                >> fail "unreachable"

    for_
        [ ( "test/phase9/notion-presentation-application.tex"
          , "f(x)"
          , 4
          )
        , ( "test/phase9/notion-presentation-apply.tex"
          , "f(x)"
          , 4
          )
        , ( "test/phase9/notion-presentation-nested.tex"
          , "f({x})"
          , 4
          )
        , ( "test/phase9/notion-presentation-symbolic-bound.tex"
          , "f(x)"
          , 4
          )
        , ( "test/phase9/notion-presentation-deep-failure.tex"
          , nestedApplicationPresentation 128
          , 4
          )
        ]
        \(relative, expectedPresentation, expectedLine) -> do
            workspace <- parseWorkspace bootstrap mounts relative
            presentationInput <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule workspace)
                    [presentationBase])
            let checkPresentation = \case
                    Elaboration.ElaborationFormationRequirementMissing
                            _location presentationFailure ->
                        case formationRequirementPresentations
                                presentationFailure of
                            [Elaboration.PresentedSourceTerm
                                    argumentLocation actualPresentation] -> do
                                assertEqual (relative <> " presentation")
                                    expectedPresentation actualPresentation
                                assertEqual (relative <> " argument line")
                                    expectedLine (locLine argumentLocation)
                            arguments ->
                                assertFailure
                                    (relative <> ": unexpected source arguments "
                                        <> show arguments)
                    failure ->
                        assertFailure
                            (relative <> ": unexpected elaboration failure: "
                                <> show failure)
            runTypedModule presentationInput >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedElaborationFailed failure))
                        _prefix ->
                    checkPresentation failure
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedProofFailed
                                (Proof.ProofElaborationFailed failure)))
                        _prefix ->
                    checkPresentation failure
                Module.TypedModuleSucceeded{} ->
                    assertFailure
                        (relative <> ": missing formation requirement succeeded")
                Module.TypedModuleOpenFailed{} ->
                    assertFailure (relative <> ": fixture did not open")
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        (relative <> ": fixture failed by another route: "
                            <> show failure)

    let projectionLocation = mkLocation anonymousSourceDescriptor 17 9
        projectionVariable = Raw.NamedVarAt projectionLocation "X"
        projection = Raw.TermExpr
            (Raw.ExprStructOp
                projectionLocation
                Raw.CarrierSymbol
                (Just (Raw.ExprVar projectionVariable)))
    assertEqual "structure projection source presentation"
        (Elaboration.PresentedSourceTerm
            projectionLocation "\\carrier[X]")
        (Elaboration.sourceTermPresentation projection)

-- Application syntax retains an expression and its argument list per level.
-- The 120-application source reaches decoder depth 256; 128 reaches 272.
-- Formation can still check the latter in memory, but persistence must reject
-- it before publication under the unchanged standard admission policy.
checksHostedPredicateStoreDepth :: HostedPredicateFormationFixture -> Assertion
checksHostedPredicateStoreDepth fixture@(HostedPredicateFormationFixture foundation bootstrap mounts _) =
    withHostedPredicateStore fixture $ \store _prover ->
        for_ [(False, "test/phase9/notion-presentation-deep-accepted.tex"),
              (True, "test/phase9/notion-presentation-deep-over-limit.tex")] $ \(outside, relative) -> do
            workspace <- parseWorkspace bootstrap mounts relative
            root <- maybe (fail "missing parsed root") pure
                (listToMaybe (reverse (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))))
            let artefact = Parsed.parsedModuleArtefact root
                bytes = Payload.canonicalParsedPayloadBytes (Parsed.parsedModulePayload root)
                key = Parsed.parsedModuleKey root
                decode = Payload.decodedParsedArtefactFromBytesWithLimits standardDecoderLimits
                    (Parsed.parsedModuleSourceDescriptor root) key bytes
            if outside then do
                -- This is a store-policy rejection, not a broken notion proof.
                _ <- compileParsedWorkspace foundation bootstrap workspace
                case decode of
                    Left (CacheResourceLimitExceeded failure) -> do
                        decoderLimitedResource failure @?= DecoderDepth
                        decoderRequestedAmount failure @?= 257
                        decoderResourceLimit failure @?= 256
                    other -> assertFailure ("expected depth rejection: " <> show other)
                Store.writeParsedArtefact store artefact >>= \case
                    Left (Store.StoreRowResourceLimitExceeded Store.ParsedArtefacts failure) ->
                        decoderLimitedResource failure @?= DecoderDepth
                    other -> assertFailure ("expected publication rejection: " <> show other)
                found <- Store.loadParsedArtefact store (Parsed.parsedModuleSourceDescriptor root) key
                    >>= expectRight
                assertBool "rejected deep syntax leaves no stored row" (isNothing found)
            else do
                (_, usage) <- expectRight decode
                decoderPeakDepth usage @?= maximumDecoderDepth standardDecoderLimits
                _ <- Store.writeParsedArtefact store artefact >>= expectRight
                found <- Store.loadParsedArtefact store (Parsed.parsedModuleSourceDescriptor root) key
                    >>= expectRight
                (Payload.decodedParsedArtefact <$> found) @?= Just artefact

checksHostedPredicateEvidence
    :: HostedPredicateFormationFixture
    -> Assertion
checksHostedPredicateEvidence fixture = do
    withHostedPredicateStore fixture \store prover -> do
        for_
            [ ( Verification.FreshStoreValidation
              , "test/phase9/notion-presentation-deep-accepted.tex"
              )
            , ( Verification.WarmStoreValidation
              , "test/phase9/notion-presentation-deep-accepted.tex"
              )
            , ( Verification.WarmStoreValidation
              , "test/phase9/notion-structure.tex"
              )
            , ( Verification.WarmStoreValidation
              , "test/phase9/notion-erased-global.tex"
              )
            ] \(mode, relative) ->
            checkFileWithStore
                store
                mode
                ignoredVerificationRequests
                prover
                relative
                >>= \case
                    Right (Verification.VerificationCompleted{}, _slowReport) ->
                        pure ()
                    Right _result ->
                        assertFailure
                            (relative <> ": the notion fixture failed")
                    Left failure ->
                        assertFailure
                            (relative <> ": the notion fixture did not run: "
                                <> show failure)

        checkFileWithStore
            store
            Verification.WarmStoreValidation
            ignoredVerificationRequests
            prover
            "test/phase9/notion-finite.tex"
            >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right _result ->
                    assertFailure "the finite notion pilot failed"
                Left failure ->
                    assertFailure
                        ("the finite notion pilot did not run: "
                            <> show failure)

        checkFileWithStore
            store
            Verification.WarmStoreValidation
            ignoredVerificationRequests
            prover
            "test/phase9/notion-finite-ambiguous.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    (Proof.ProofElaborationFailed
                                        (Elaboration.ElaborationAdjectiveReadingAmbiguous
                                            location readings))))
                            prefix)
                    , _slowReport
                    ) -> do
                        let rendered =
                                Elaboration.renderElaborationError
                                    (Elaboration.ElaborationAdjectiveReadingAmbiguous
                                        location readings)
                        assertEqual "ambiguous finite line"
                            4 (locLine location)
                        assertEqual "bare finite has two readings"
                            2 (length (toList readings))
                        assertBool
                            "ambiguous finite publishes no local declaration"
                            (null (Commit.pendingModulePrefixBatches prefix))
                        for_
                            [ "bare adjective \"finite\""
                            , "ordinary adjective"
                            , "structure adjective"
                            , "complete noun or structure phrase"
                            ]
                            \detail ->
                                assertBool
                                    ("ambiguous finite explains "
                                        <> StrictText.unpack detail)
                                    (detail `StrictText.isInfixOf` rendered)
                        for_
                            [ "SemanticLeftAdjective"
                            , "OrdinaryAdjectiveReading"
                            , "StructureAdjectiveReading"
                            , "TokenCons"
                            ]
                            \constructor ->
                                assertBool
                                    ("ambiguous finite hides "
                                        <> StrictText.unpack constructor)
                                    (not
                                        (constructor
                                            `StrictText.isInfixOf` rendered))
                Right result ->
                    assertFailure
                        ("bare finite failed differently: " <> show result)
                Left failure ->
                    assertFailure
                        ("the bare-finite fixture did not run: "
                            <> show failure)

        traverse_
            (\(label, source) ->
                checkFileWithStore
                    store
                    Verification.WarmStoreValidation
                    ignoredVerificationRequests
                    prover
                    source
                    >>= \case
                        Right
                            (Verification.VerificationCompleted{},
                                _slowReport) ->
                            pure ()
                        Right result ->
                            assertFailure
                                (label <> " failed: " <> show result)
                        Left failure ->
                            assertFailure
                                (label <> " did not run: " <> show failure))
            [ ( "the theorem-site notion-view fixture"
              , "test/phase9/notion-view.tex"
              )
            , ( "the generated noun-view fixture"
              , "test/phase9/notion-noun-view.tex"
              )
            ]

checksHostedPredicateGuardScopes
    :: HostedPredicateFormationFixture
    -> Assertion
checksHostedPredicateGuardScopes fixture = do
    withHostedPredicateStore fixture \store prover -> do
        checkFileWithStore
            store
            Verification.FreshStoreValidation
            ignoredVerificationRequests
            prover
            "test/phase9/notion-guard.tex"
            >>= \case
                Right (Verification.VerificationCompleted{}, _slowReport) ->
                    pure ()
                Right result ->
                    assertFailure
                        ("the checked implication guard failed: " <> show result)
                Left failure ->
                    assertFailure
                        ("the checked implication guard did not run: "
                            <> show failure)

        let checkReachableFrontier expectedHead expectedLine location requirement = do
                let explanation =
                        Elaboration.formationRequirementFailureExplanation
                            requirement
                    rendered = Elaboration.renderElaborationError
                        (Elaboration.ElaborationFormationRequirementMissing
                            location requirement)
                case Notion.formationFailureFrontier explanation of
                    Just
                            (Notion.FormationFailureFrontier
                                (Notion.GlobalNotionHeadKey _head)
                                (Elaboration.FormationFromCheckedGuard _ origin)) ->
                        assertEqual "retained answer order fixes the source on equal-cost ties"
                            expectedLine (locLine origin)
                    frontier ->
                        assertFailure
                            ("unexpected reachable frontier: " <> show frontier)
                assertBool "diagnostic renders reachable notion head"
                    (("A retained source-backed notion head \"" <> expectedHead <> "\"")
                        `StrictText.isInfixOf` rendered)
                assertBool "the requested goal is not reported as retained evidence"
                    (not ("A retained source-backed notion head \"notion frontier ready\""
                        `StrictText.isInfixOf` rendered))
                assertBool "diagnostic identifies the checked guard"
                    ("from a checked guard at" `StrictText.isInfixOf` rendered)

        for_ [ ("missing", "notion view base", 4)
             , ("tied", "notion view base", 5)
             , ("ranked", "notion view target", 26)
             ] \(suffix, expectedHead, expectedLine) ->
          for_ [Verification.FreshStoreValidation, Verification.WarmStoreValidation] \mode ->
          checkFileWithStore
            store
            mode
            ignoredVerificationRequests
            prover
            ("test/phase9/notion-view-frontier-" <> suffix <> ".tex")
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedElaborationFailed
                                    (Elaboration.ElaborationFormationRequirementMissing
                                        location requirement)))
                            _prefix)
                    , _slowReport
                    ) -> checkReachableFrontier expectedHead expectedLine location requirement
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    (Proof.ProofElaborationFailed
                                        (Elaboration.ElaborationFormationRequirementMissing
                                            location requirement))))
                            _prefix)
                    , _slowReport
                    ) -> checkReachableFrontier expectedHead expectedLine location requirement
                Right result ->
                    assertFailure
                        ("reachable-frontier fixture failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("the reachable-frontier fixture did not run: "
                            <> show failure)

        checkFileWithStore
            store
            Verification.WarmStoreValidation
            ignoredVerificationRequests
            prover
            "test/phase9/notion-guard-no-escape.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    (Proof.ProofElaborationFailed
                                        (Elaboration.ElaborationFormationRequirementMissing
                                            location _requirement))))
                            _prefix)
                    , _slowReport
                    ) -> assertEqual "implication assertion escape line"
                        5 (locLine location)
                Right result ->
                    assertFailure
                        ("implication assertions escaped their guard: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("the implication-guard negative fixture did not run: "
                            <> show failure)

checksHostedPredicateMembershipAndStructures
    :: HostedPredicateFormationFixture
    -> Assertion
checksHostedPredicateMembershipAndStructures fixture = do
    withHostedPredicateStore fixture \store prover -> do
        checkFileWithStore
            store
            Verification.FreshStoreValidation
            ignoredVerificationRequests
            prover
            "test/phase9/notion-membership-negative.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    (Proof.ProofElaborationFailed
                                        (Elaboration.ElaborationFormationRequirementMissing
                                            location _requirement))))
                            _prefix)
                    , _slowReport
                    ) -> assertEqual "negative membership evidence line"
                        5 (locLine location)
                Right result ->
                    assertFailure
                        ("negative membership became notion evidence: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("the negative membership fixture did not run: "
                            <> show failure)

        checkFileWithStore
            store
            Verification.WarmStoreValidation
            ignoredVerificationRequests
            prover
            "test/phase9/notion-structure-view-missing.tex"
            >>= \case
                Right
                    ( Verification.VerificationCheckingFailure _report
                        (Verification.VerificationTypedModuleError
                            _source
                            (Module.TypedActionFailed
                                (Module.TypedProofFailed
                                    (Proof.ProofElaborationFailed
                                        (Elaboration.ElaborationFormationRequirementMissing
                                            location requirement))))
                            _prefix)
                    , _slowReport
                    ) -> do
                        let rendered = Elaboration.renderElaborationError
                                (Elaboration.ElaborationFormationRequirementMissing
                                    location requirement)
                        assertEqual "constructed-parent rejection line"
                            10 (locLine location)
                        assertBool
                            "constructed-parent diagnostic renders the set term"
                            ("over {A}" `StrictText.isInfixOf` rendered)
                        assertBool
                            "constructed-parent diagnostic hides Core syntax"
                            (not ("CIntrinsic" `StrictText.isInfixOf` rendered)
                                && not ("CApp" `StrictText.isInfixOf` rendered))
                Right result ->
                    assertFailure
                        ("constructed-parent fixture failed differently: "
                            <> show result)
                Left failure ->
                    assertFailure
                        ("the constructed-parent fixture did not run: "
                            <> show failure)

checksBoundedNounEvidence :: Assertion
checksBoundedNounEvidence = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace bootstrap mounts "test/phase9/notion-bounded-nouns.tex"
    modules <- compileParsedWorkspace foundation bootstrap workspace
    vocabulary <- case reverse modules of
        _root : declarations : _ -> pure declarations
        _ -> assertFailure "bounded noun fixture lost its vocabulary" >> fail "unreachable"
    for_ ["negative", "sibling", "endpoint", "scope"] \suffix -> do
        rejected <- parseWorkspace bootstrap mounts
            ("test/phase9/notion-bounded-noun-" <> suffix <> ".tex")
        input <- expectRightIO (typedModuleInput foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule rejected) [vocabulary])
        runTypedModule input >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed actionFailure) prefix -> do
                failure <- case actionFailure of
                    Module.TypedElaborationFailed elaborationFailure -> pure elaborationFailure
                    Module.TypedProofFailed (Proof.ProofElaborationFailed elaborationFailure) ->
                        pure elaborationFailure
                    other -> assertFailure (suffix <> ": " <> show other) >> fail "unreachable"
                case (suffix, failure) of
                    ("scope", Elaboration.ElaborationNounBoundScope{}) -> pure ()
                    (_, Elaboration.ElaborationFormationRequirementMissing{})
                        | suffix /= "scope" -> pure ()
                    _ -> assertFailure (suffix <> ": " <> show failure)
                assertBool "rejected noun publishes no declaration"
                    (null (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleFailed failure _ -> assertFailure (suffix <> ": " <> show failure)
            _ -> assertFailure (suffix <> ": expected rejection")

-- Exercise every registration in several small, genuinely compiled module
-- graphs. Supply exact ground premises, then ask the independent calculus for
-- the result and replay every witness against the real checked source theorem.
replaysImportedFormationReference :: Assertion
replaysImportedFormationReference = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    mounts <- exactFixtureMounts repository
    withAcceptedFixtureVampire "formation-reference-imports" \prover -> do
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        built <- FinalPrelude.buildFinalPreludeCandidate foundation resolver
        candidate <- case built of
            FinalPrelude.FinalPreludeBuilt value -> pure value
            _ -> fail "reference prelude did not complete"
        let completedPrelude = Module.completeFinalPreludeCandidate candidate
            prelude = Module.completedTypedModuleSealed completedPrelude
        readiness <- expectRight (Module.fixtureFinalPreludeReadinessFromSealed foundation
            (Declaration.naturalNumeralBasisObject (FinalPrelude.finalPreludeNaturalNumeralBasis candidate)) prelude)
        inventories <- for
            [ "notion-definition-chain.tex", "notion-finite-evidence-direct.tex"
            , "notion-composite-product.tex", "notion-graph-domain.tex"
            , "notion-unconditional-provider.tex", "notion-reference-closed.tex", "notion-structure.tex"
            , "notion-reference-identity.tex", "notion-reference-definition.tex"
            , "notion-classification-bundle-import.tex"
            , "notion-classification-bundle-premises.tex", "notion-registration-order.tex"
            ] \file -> do
                workspace <- parseWorkspaceWithPrelude prelude mounts ("test/phase9/" <> file)
                modules <- compileParsedWorkspaceWithReadiness foundation readiness resolver AlwaysMissValidation workspace
                root <- sole "reference fixture root" (take 1 (reverse modules))
                let allModules = completedPrelude : modules
                    closure = Declaration.evidenceClosure (completedModuleEvidence root)
                    deltas = concatMap (Semantic.semanticInterfaceDeclarations . completedModuleSemantic) allModules
                imported <- expectRight (ReferenceImports.importedReferenceRules allModules)
                let describeImports = fmap (\rule ->
                        (ReferenceImports.importedReferenceOccurrence rule,
                            ReferenceImports.importedReferencePath rule,
                            ReferenceImports.importedReferenceRegistration rule,
                            Identity.checkedPropositionId (ReferenceImports.importedReferenceProposition rule),
                            Identity.checkedPropositionTerm (ReferenceImports.importedReferenceProposition rule)))
                    prepareRules allowance = Reference.runReference allowance
                        (describeImports <$> ReferenceImports.prepareImportedReferenceRules allModules)
                    (preparedRules, ruleWork) = prepareRules 1000000
                    oldTableRows = fromIntegral (sum
                        [length (Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)) | delta <- deltas]
                        + sum [Map.size (Schema.resolvedSchemaFields schema) | sealed <- allModules,
                            schema <- Declaration.evidenceLocalStructureSchemas (completedModuleEvidence sealed)])
                    prepareTerms allowance = Reference.runReference allowance do
                        _ <- ReferenceImports.prepareImportedReferenceTerm closure allModules (const (Core.CIntrinsic Core.Empty))
                        pure ()
                assertEqual "metered inventory preserves every registration and checked source"
                    (Right (describeImports imported)) preparedRules
                assertEqual "registration adaptation shares its exact allowance"
                    (preparedRules, ruleWork) (prepareRules ruleWork)
                assertEqual "one-short inventory adaptation exhausts"
                    (Left Reference.ReferenceWorkExhausted) (fst (prepareRules (ruleWork - 1)))
                let compileProduction allowance = Reference.runReference allowance
                        (ReferenceImports.prepareProductionRuleDescriptions allModules)
                    (production, productionWork) = compileProduction 1000000
                    expectedProduction = (\rule -> (ReferenceImports.importedReferenceOccurrence rule,
                        ReferenceImports.importedReferenceRegistration rule)) <$> imported
                assertEqual "all six production registration families preserve the independent source contract"
                    (Right expectedProduction) production
                checkVisibleRegistrations foundation root allModules imported expectedProduction
                when (file == "notion-classification-bundle-import.tex") do
                    checkClosedBundle foundation closure allModules imported
                        (Parsed.parsedWorkspaceRootModule workspace)
                    wholeBundle <- parseWorkspaceWithPrelude prelude mounts "test/phase9/notion-classification-bundle-whole.tex"
                    producer <- sole "bundle producer"
                        [sealed | sealed <- modules,
                            any ((== "notion_bundle_exact") . Semantic.semanticNameText . Semantic.semanticAliasName)
                                (concatMap Semantic.declarationDeltaAliases
                                    (Semantic.semanticInterfaceDeclarations (completedModuleSemantic sealed)))]
                    input <- expectRightIO (typedModuleInput foundation
                        readiness unusedResolver AlwaysMissValidation
                        (Parsed.parsedWorkspaceRootModule wholeBundle) [producer])
                    runTypedModule input >>= \case
                        Module.TypedModuleSucceeded completed -> do
                            let registrations = concatMap Semantic.declarationDeltaRegistrations
                                    (Semantic.semanticInterfaceDeclarations (completedModuleSemantic completed))
                            assertEqual "both atomic and whole branches remain registered" 2 (length registrations)
                            assertEqual "the residual sibling uses the whole family" 1
                                (length [() | Semantic.Registration _ _ Semantic.RegisterWholeConclusion{} <- registrations])
                        Module.TypedModuleFailed failure _ -> assertFailure (StrictText.unpack (Module.renderTypedModuleFailure failure))
                        Module.TypedModuleOpenFailed failure -> assertFailure (show failure)
                assertEqual "production registration compilation shares its exact allowance"
                    (production,productionWork) (compileProduction productionWork)
                assertEqual "one-short production compilation exhausts"
                    (Left Reference.ReferenceWorkExhausted) (fst (compileProduction (productionWork - 1)))
                assertEqual "provider preparation charges inventory visits beyond emitted table rows"
                    (Left Reference.ReferenceWorkExhausted) (fst (prepareTerms oldTableRows))
                assertBool (file <> " has registered rules") (not (Map.null imported))
                when (file == "notion-reference-definition.tex")
                    (checkDefinitionScope foundation allModules (Parsed.parsedWorkspaceRootModule workspace))
                -- The row reference handles relational premises. Complete
                -- portable contracts are compared above; whole-truth closure
                -- is exercised by the independent finite Horn oracle.
                for_ (Map.toAscList imported) \entry@(_,rule) ->
                    when (all relationalTree (Reference.referenceRulePremises
                        (Reference.registrationRule (ReferenceImports.importedReferenceRegistration rule))))
                        (checkRule closure allModules entry)
                when (file == "notion-finite-evidence-direct.tex") (checkFiniteChain closure allModules imported)
                legacyBackward <- if file == "notion-definition-chain.tex" then do
                    checkChain closure allModules imported
                    checkScopedClaim "notion_package_chain_replay" foundation closure allModules imported (Parsed.parsedWorkspaceRootModule workspace)
                    checkLegacyBackward foundation (Semantic.semanticInterfaceOwner (completedModuleSemantic root))
                    else pure 0
                when (file == "notion-finite-evidence-direct.tex")
                    (checkScopedClaim "notion_finite_evidence_from_membership" foundation closure allModules imported
                        (Parsed.parsedWorkspaceRootModule workspace))
                when (file == "notion-graph-domain.tex")
                    (checkScopedClaim "notion_graph_domain_intro" foundation closure allModules imported
                        (Parsed.parsedWorkspaceRootModule workspace))
                when (file == "notion-reference-identity.tex")
                    (for_ ["notion_reference_identity_direct", "notion_reference_erased_argument"] \label ->
                        checkScopedClaim label foundation closure allModules imported
                            (Parsed.parsedWorkspaceRootModule workspace))
                pure
                    [ sum (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry]) <$> deltas)
                    , sum (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNullaryProvider rule) <- Semantic.declarationDeltaRegistrations entry]) <$> deltas)
                    , sum (length . Semantic.declarationDeltaRegistrations <$> deltas)
                    , legacyBackward + sum (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterBackwardNotion rule) <- Semantic.declarationDeltaRegistrations entry]) <$> deltas)
                    , sum (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterFiniteEvidence rule) <- Semantic.declarationDeltaRegistrations entry]) <$> deltas)
                    , sum (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterGraphDomain rule) <- Semantic.declarationDeltaRegistrations entry]) <$> deltas)
                    ]
        let totals = foldl' (zipWith (+)) (replicate 6 0) inventories
        assertBool ("all six admitted registration families reach the oracle: " <> show totals)
            (all (> 0) totals)
  where
    checkClosedBundle foundation closure modules imported parsed = do
        Raw.Claim assumptions conclusion <- sole "exact bundle consumer"
            [claim | Raw.BlockClaim _ _ _ marker claim <- Parsed.parsedModuleBlocks parsed
                , marker == "notion_bundle_import_exact"]
        let deltas = concatMap (Semantic.semanticInterfaceDeclarations . completedModuleSemantic) modules
            bundleDeltas = [delta | delta <- deltas,
                any ((`elem` ["notion_bundle_exact", "notion_bundle_nested"])
                    . Semantic.semanticNameText . Semantic.semanticAliasName) (Semantic.declarationDeltaAliases delta)]
            roundTrip delta = decodeCache Semantic.getDeclarationInterfaceDeltaCache
                (encodeCache (Semantic.putDeclarationInterfaceDeltaCache delta))
        assertEqual "closed and nested bundles both retain all branches" [2,3]
            (length . Semantic.declarationDeltaRegistrations <$> bundleDeltas)
        for_ bundleDeltas \delta -> do
            assertEqual "one original theorem supports the complete bundle" 1 (length (Semantic.declarationDeltaFacts delta))
            assertEqual "branch identity, order, and multiplicity survive decoding" (Right delta) (roundTrip delta)
            assertEqual "the bundle refers only to its original theorem"
                (Set.fromList (Semantic.semanticFactFingerprint <$> Semantic.declarationDeltaFacts delta))
                (Set.fromList (Semantic.registrationSource <$> Semantic.declarationDeltaRegistrations delta))
            assertEqual "identical formulas at different paths remain distinct"
                (length (Semantic.declarationDeltaRegistrations delta))
                (Set.size (Set.fromList (Semantic.declarationDeltaRegistrations delta)))
        let here = Notion.ConjunctionHere
            left = Notion.ConjunctionLeft
            right = Notion.ConjunctionRight
        assertEqual "branches retain left-to-right source order and indivisible exact atoms"
            [[left here, right here], [left (left here), left (right here), right here]]
            [Semantic.registrationPath <$> Semantic.declarationDeltaRegistrations delta
                | delta <- bundleDeltas]
        mixed <- sole "mixed-family bundle" [delta | delta <- deltas,
            any ((== "notion_bundle_mixed") . Semantic.semanticNameText . Semantic.semanticAliasName)
                (Semantic.declarationDeltaAliases delta)]
        case Semantic.declarationDeltaRegistrations mixed of
            [Semantic.Registration _ nullaryPath Semantic.RegisterNullaryProvider{},
             Semantic.Registration _ providerPath Semantic.RegisterProviderResult{}] -> do
                assertEqual "family order precedes cross-family source order" (right here)
                    nullaryPath
                assertEqual "provider branch keeps its original left selector" (left here)
                    providerPath
            _ -> assertFailure "mixed bundle did not retain canonical family order"
        let shapeFor marker = sole "named checked shape"
                [Semantic.semanticRecordShapeKey schema | sealed <- modules,
                    schema <- Declaration.evidenceLocalStructureSchemas (completedModuleEvidence sealed),
                    Schema.structurePhraseMarker (Schema.resolvedSchemaPhrase schema) == marker]
        carrierShape <- shapeFor "notion_bundle_carrier"
        reflexiveShape <- shapeFor "notion_bundle_reflexive_carrier"
        assertEqual "law-only schema differences share exact-shape identity" carrierShape reflexiveShape
        driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
            (completedModuleEvidence <$> modules) unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver do
                envelope <- Elaboration.elaborateClaimEnvelope assumptions conclusion
                case envelope of
                    Left failure -> pure (Left failure)
                    Right prepared -> do
                        let assertions = Elaboration.elaboratedClaimConclusionAssertions prepared
                            context = Elaboration.elaboratedClaimContext prepared
                            initial = Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits
                        (_, results) <- foldM (\(budget, retained) assertion -> do
                            query <- Elaboration.elaborateProofNotionEvidenceWithBudget budget context Nowhere assertion
                            case query of
                                Right (Elaboration.NotionQueryFound evidence, next) -> do
                                    replayed <- Declaration.replayTransientFormationLowering closure evidence
                                        (Notion.sourceAssertionFormula assertion)
                                    pure (next, retained <> [(evidence, replayed)])
                                _ -> error "a closed classification branch did not answer its own atom")
                            (initial, []) assertions
                        pure (Right results))
        case driven of
            Declaration.DriverSucceeded (Right results) _ _ -> do
                assertEqual "open and exact assertions are independently queried" 2 (length results)
                for_ results \(evidence, replayed) -> do
                    void (expectRight replayed)
                    assertEqual "branch replay imports one complete source theorem" 1
                        (Vector.length (Notion.materializedFormationImports evidence))
                    assertBool "closed branch replay borrows no proof locals"
                        (Vector.null (Notion.materializedFormationHypotheses evidence))
            _ -> assertFailure "closed classification boundary replay failed"
        let exactRules = [Reference.registrationRule (ReferenceImports.importedReferenceRegistration rule)
                | rule <- Map.elems imported,
                Semantic.ExactStructureAtomTemplate{} <- [Reference.referenceRuleConclusion
                    (Reference.registrationRule (ReferenceImports.importedReferenceRegistration rule))]]
        for_ exactRules \rule -> do
            let goal = fmap (fmap (\(Semantic.ViewVariableIx ix) -> Reference.OpaqueSeed ix))
                    (Reference.referenceRuleConclusion rule)
                openRows = [fmap (fmap (\(Semantic.ViewVariableIx ix) -> Reference.OpaqueSeed ix)) row
                    | entry <- Map.elems imported,
                    let candidate = Reference.registrationRule (ReferenceImports.importedReferenceRegistration entry),
                    Reference.referenceRuleArity candidate == 0,
                    let row = Reference.referenceRuleConclusion candidate,
                    Semantic.StructureAtomTemplate{} <- [row]]
                observations = [Reference.ReferenceFact row
                    (Reference.WitnessSummary (Set.singleton ordinal) Set.empty Set.empty)
                    | (ordinal, row) <- zip [0 :: Natural ..] openRows]
            (_, absent) <- expectRight (fst (Reference.evaluateFormation 1000000 Map.empty observations Set.empty goal))
            assertBool "open evidence cannot establish exact shape"
                (all ((/= goal) . fst) (Map.keys (Reference.referenceAnswers absent)))

    -- The source lowerer now emits finite-evidence rules for these shapes;
    -- exercise the retained backward family through its real checked admission
    -- API, using an ordinary kernel proof of membership identity.
    checkVisibleRegistrations foundation root modules imported expected = do
        relative <- expectRight (safeRelativePath "formation-registry-client.tex")
        let owner = moduleNameFromParts
                (moduleNameNamespace (Semantic.semanticInterfaceOwner (completedModuleSemantic root))) relative
            atomTerms = toList
            treeTerms = \case
                Semantic.RulePremiseAtom value -> atomTerms value
                Semantic.RulePremiseUniversal{} -> []
                Semantic.RulePremiseResidual{} -> []
                Semantic.RulePremiseAnd left right -> treeTerms left <> treeTerms right
            templates = Set.toAscList (Set.fromList (concat
                [atomTerms (Reference.referenceRuleConclusion rule)
                    <> concatMap treeTerms (Reference.referenceRulePremises rule)
                | (_, registration) <- Map.elems expected, let rule = Reference.registrationRule registration]))
            owned = Set.toAscList (Set.fromList
                [(Semantic.declarationDeltaSlot delta, registration)
                | sealed <- modules
                , delta <- Semantic.semanticInterfaceDeclarations (completedModuleSemantic sealed)
                , registration <- Semantic.declarationDeltaRegistrations delta
                , ReferenceImports.atomicConclusion registration])
            family = \case
                Semantic.RegisterNotionView{} -> 0 :: Int
                Semantic.RegisterNullaryProvider{} -> 1
                Semantic.RegisterProviderResult{} -> 2
                Semantic.RegisterBackwardNotion{} -> 3
                Semantic.RegisterFiniteEvidence{} -> 4
                Semantic.RegisterGraphDomain{} -> 5
                Semantic.RegisterWholeConclusion{} -> 6
            expectedOrder = snd <$> List.sortOn
                (\(slot, registration) -> (family (Semantic.registrationBody registration), slot, registration)) owned
            nullary = Map.fromListWith min
                [(Semantic.nullaryProvider rule, (slot, Semantic.registrationBranch registration, rule))
                | (slot, registration) <- owned
                , Semantic.RegisterNullaryProvider rule <- [Semantic.registrationBody registration]]
            leafCore (Semantic.ViewVariableIx index) = Core.COpaqueInteger (toInteger index + 1)
        driven <- expectRight =<< runModuleDriver foundation owner
            (completedModuleEvidence <$> modules) unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver do
                registrations <- List.filter ReferenceImports.atomicConclusion . fmap fst <$> Declaration.visibleFormationRegistrationsLowering
                sources <- for registrations \registration -> do
                    let occurrence = Semantic.registrationSource registration
                    source <- Declaration.resolveVisibleFormationSourceLowering occurrence
                    pure (occurrence, source)
                catalog <- Declaration.formationCatalogLowering
                closure <- Declaration.checkedObjectClosureLowering
                initial <- Elaboration.initialElaborationStateLowering closure Elaboration.emptyElaborationContext
                reconstructed <- Except.runExceptT (State.evalStateT
                    (for templates \template -> do
                        let run allowance = Elaboration.interpretFormationTemplate allowance Nowhere
                                (\work value -> pure (Right (leafCore value), work)) template
                        ample@(_, remaining) <- run 1000000
                        exact <- run (1000000 - remaining)
                        short <- run (1000000 - remaining - 1)
                        pure (ample, exact, short)) initial)
                diagnostics <- for (Map.keys nullary) \provider -> do
                    selected <- Declaration.firstVisibleNullaryProviderClassificationLowering provider
                    pure ((\runtime -> (Notion.visibleNullaryProviderClassificationSource runtime,
                        Notion.visibleNullaryProviderClassificationPayload runtime)) <$> selected)
                pure (registrations, sources, closure, reconstructed, catalog, diagnostics))
        (registrations, sources, closure, reconstructed, catalog, diagnostics) <- case driven of
            Declaration.DriverSucceeded value _ _ -> pure value
            _ -> fail "visible formation registry could not be prepared"
        assertEqual "registry order is family, owner, then complete source branch and payload" expectedOrder registrations
        assertEqual "competing nullary diagnostics select the first owner and complete registration"
            [Just (branch, rule) | (_, branch, rule) <- Map.elems nullary] diagnostics
        terms <- expectRight reconstructed
        for_ (zip templates terms) \(template, ((result, _), exact, short)) -> do
            term <- expectRight result
            assertEqual "template interpretation shares its exact allowance across Core work"
                (Right term, 0) exact
            assertEqual "one-short interpretation exhausts without returning a partial term"
                (Left Core.CountedCoreStructuralWorkExhausted, 0) short
            expectedCore <- expectRight (ReferenceImports.importedReferenceTerm closure modules
                (\(Reference.OpaqueSeed index) -> Core.COpaqueInteger (toInteger index + 1))
                (fmap (\(Semantic.ViewVariableIx index) -> Reference.OpaqueSeed index) template))
            assertEqual "normal interpretation agrees with independent provider denotation" expectedCore term
            checked <- expectRight (Core.checkScopedCanonicalCore
                (Identity.globalTypingFromClosure closure) [] term)
            assertEqual "interpreted mathematical templates are sets in the owner scope" Core.TySet (Core.scopedCoreType checked)
        resolved <- for sources \(occurrence, source) -> do
            value@(proposition, _) <- maybe (fail "visible registration has no checked source contract") pure source
            assertBool "visible registry retains the exact checked source proposition"
                (any (\rule -> ReferenceImports.importedReferenceOccurrence rule == occurrence
                    && ReferenceImports.importedReferenceProposition rule == proposition) (Map.elems imported))
            pure (occurrence, value)
        let compile allowance = Reference.runReference allowance $
                Registration.compileRegistrationRules (Reference.chargeReferenceWork . fromIntegral)
                    (\occurrence -> maybe (Reference.invalidReferenceInput "missing visible source") pure
                        (Map.lookup occurrence (Map.fromList resolved))) registrations
                    >>= either (Reference.invalidReferenceInput . fromString . show) (pure . fmap describe)
            describe (occurrence, entry) =
                let (arity, premises, conclusion) = FormationRule.ruleDescription (FormationRule.registeredRule entry)
                    atom = case conclusion of
                        Semantic.AtomicLeaf value -> value
                        Semantic.WholeLeaf{} -> error "atomic reference registry received a whole conclusion"
                    rule = Reference.ReferenceRule arity premises atom Set.empty
                in (occurrence, case entry of
                    FormationRule.RegisteredClassification{} -> Reference.ClassificationRule rule
                    FormationRule.RegisteredDefinition{} -> Reference.DefinitionRule rule)
            (result, work) = compile 1000000
        actual <- expectRight result
        cached <- expectRight (fst (Reference.runReference 1000000 do
            rules <- FormationCatalog.registeredRules (Reference.chargeReferenceWork . fromIntegral) catalog
            for [(ordinal,entry) | (ordinal,entry) <- Map.toAscList rules,
                let (_,_,conclusion) = FormationRule.ruleDescription (FormationRule.registeredRule entry),
                Semantic.AtomicLeaf{} <- [conclusion],
                case FormationCatalog.lookupSource ordinal catalog of
                    Just (Left Notion.FormationProjectionRule{}) -> False
                    Just (Left Notion.FormationEliminationRule{}) -> False
                    _ -> True] \(ordinal,entry) -> do
                Reference.chargeReferenceWork 1
                taggedSource <- maybe (Reference.invalidReferenceInput "compiled registration lost its exact source") pure
                    (FormationCatalog.lookupSource ordinal catalog)
                source <- either pure (const (Reference.invalidReferenceInput
                    "a declaration catalogue contains a scoped producer")) taggedSource
                let (Semantic.SemanticFactBranch occurrence path, body) = case source of
                        Notion.FormationViewRule value -> (Notion.visibleNotionViewSource value,
                            Semantic.RegisterNotionView (Notion.visibleNotionViewPayload value))
                        Notion.FormationNullaryRule value -> (Notion.visibleNullaryProviderClassificationSource value,
                            Semantic.RegisterNullaryProvider (Notion.visibleNullaryProviderClassificationPayload value))
                        Notion.FormationProviderRule value -> (Notion.visibleProviderResultRuleSource value,
                            Semantic.RegisterProviderResult (Notion.visibleProviderResultRulePayload value))
                        Notion.FormationBackwardRule value -> (Notion.visibleBackwardNotionRuleSource value,
                            Semantic.RegisterBackwardNotion (Notion.visibleBackwardNotionRulePayload value))
                        Notion.FormationFiniteRule value -> (Notion.visibleFiniteEvidenceRuleSource value,
                            Semantic.RegisterFiniteEvidence (Notion.visibleFiniteEvidenceRulePayload value))
                        Notion.FormationGraphRule value -> (Notion.visibleGraphDomainRuleSource value,
                            Semantic.RegisterGraphDomain (Notion.visibleGraphDomainRulePayload value))
                        Notion.FormationWholeRule value -> (Notion.visibleWholeConclusionRuleSource value,
                            Semantic.RegisterWholeConclusion (Notion.visibleWholeConclusionRulePayload value))
                        Notion.FormationProjectionRule{} -> error "a projected consequence entered the original-registration audit"
                        Notion.FormationEliminationRule{} -> error "a whole elimination entered the original-registration audit"
                        Notion.FormationIntroductionRule{} -> error "a query introduction entered the original-registration audit"
                    registration = Semantic.Registration occurrence path body
                recompiled <- Registration.compileRegistrationRules (Reference.chargeReferenceWork . fromIntegral)
                    (\fingerprint -> maybe (Reference.invalidReferenceInput "runtime lost its source theorem") pure
                        (Map.lookup fingerprint (Map.fromList resolved))) [registration]
                    >>= either (Reference.invalidReferenceInput . fromString . show) pure
                when (fmap describe recompiled /= [describe (occurrence, entry)])
                    (Reference.invalidReferenceInput "compiled rule is paired with a different runtime registration")
                pure (describe (occurrence,entry))))
        let description registration (_, entry) =
                (Semantic.registrationBody registration, case entry of
                    Reference.DefinitionRule rule -> (True, Reference.referenceRuleArity rule)
                    Reference.ClassificationRule rule -> (False, Reference.referenceRuleArity rule))
            descriptions = Set.fromList (zipWith description registrations actual)
        assertEqual "the executable catalogue retains each exact description once"
            (Set.size descriptions) (length cached)
        assertEqual "every retained representative has its actual checked source association"
            [] (foldl' (flip List.delete) cached actual)
        assertEqual "visible owner preserves registration multiplicity" (Map.size expected) (length actual)
        assertEqual "visible owner compiles every independent registration contract"
            [] (foldl' (flip List.delete) actual (Map.elems expected))
        assertEqual "visible compilation accepts its exact allowance" (result, work) (compile work)
        assertEqual "visible compilation rejects one-short allowance"
            (Left Reference.ReferenceWorkExhausted) (fst (compile (work - 1)))

    checkLegacyBackward foundation owner = do
        closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
        let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
            set = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
            row = Semantic.MembershipAtomTemplate x set
            forest = Semantic.RulePremiseBundles (Semantic.RulePremiseAtom row :| [])
            formula = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) (Core.CBound 1)) (Core.CBound 0)
        premise <- expectRight (Core.checkScopedCanonicalCore (Identity.globalTypingFromClosure closure)
            [Core.TySet,Core.TySet] formula)
        proposition <- expectRight (Identity.validatePropositionContent closure
            (Core.CForall Core.TySet (Core.CForall Core.TySet (Core.CImp formula formula))))
        let pending = Semantic.Registration (Planning.plannedEarlierCandidate 0 0) Notion.ConjunctionHere (Semantic.RegisterBackwardNotion (Semantic.BackwardNotionRule forest row))
            candidate = Declaration.checkedCandidate
                (Declaration.candidateSpec proposition Semantic.SearchIneligible [])
                (Declaration.checkedNoExternalSourceProofPlanning [])
            declaration = Declaration.checkedCompiledDeclarationWithRegistrations
                (Semantic.declarationSyntaxId "reference-backward")
                []
                [proposition]
                []
                Nothing
                [pending]
                [candidate :| []]
                ()
            authorize _ stages = case stages of
                [result :| []] -> Declaration.authorizeKernelProofCandidate result (pure
                    (Kernel.forallIntroductionDerivation Core.TySet
                        (Kernel.forallIntroductionDerivation Core.TySet
                            (Kernel.implicationIntroductionDerivation premise
                                (Kernel.localHypothesisDerivation (Kernel.hypothesisIx 0))))))
                _ -> error "unexpected reference candidate stages"
        check <- Declaration.newImportCheck foundation
        prepared <- expectRight =<< Declaration.prepareImports check []
        outcome <- expectRight =<< Declaration.runModuleDriverFreshIO foundation owner prepared unusedResolver
            (snd <$> Declaration.admitCheckedDeclaration declaration authorize)
        batch <- case outcome of
            Declaration.DriverSucceeded batch _ _ -> pure batch
            _ -> fail "legacy backward reference declaration did not seal"
        imported <- expectRight (ReferenceImports.referenceRulesFromBatches [batch])
        for_ (Map.toAscList imported) (checkRule closure [])
        pure (length [rule | Semantic.Registration _ _ (Semantic.RegisterBackwardNotion rule) <- Semantic.declarationDeltaRegistrations (Commit.committedBatchDelta batch)])

    namedBinding modules label = sole (StrictText.unpack label)
        [(Semantic.globalBindingRef (Semantic.declarationDeltaSlot delta)
            (Semantic.semanticGlobalBindingKey binding), binding)
        | sealed <- modules
        , delta <- Semantic.semanticInterfaceDeclarations (completedModuleSemantic sealed)
        , binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)
        , Semantic.semanticBindingLabelText (Semantic.semanticGlobalBindingLabel binding) == label]

    checkFiniteChain closure modules imported = do
        let registrations = ReferenceImports.importedReferenceRegistration <$> imported
            ambient = replicate 3 Core.TySet
            checked = expectRight . Core.checkScopedCanonicalCore (Identity.globalTypingFromClosure closure) ambient
            atom label indices = do
                (reference, binding) <- namedBinding modules label
                let row = Semantic.GlobalAtomTemplate (Semantic.NounNotionHead reference)
                        (Vector.fromList [Semantic.TemplateVariable (Reference.OpaqueSeed index) | index <- indices])
                    formula = foldl' Core.CApp
                        (Core.CGlobal (Semantic.semanticGlobalTargetObject (Semantic.semanticGlobalBindingTarget binding)))
                        (Core.CBound <$> indices)
                pure (row, formula)
        (base, baseFormula) <- atom "notion_base" [1]
        (row, rowFormula) <- atom "notion_finite_evidence_row" [0,1]
        (alias, _) <- atom "notion_finite_evidence_row_alias" [0,1]
        (selectedReference, selectedBinding) <- namedBinding modules "notion_finite_evidence_selected"
        let target = Semantic.GlobalAtomTemplate (Semantic.AdjectiveNotionHead selectedReference)
                (Vector.singleton (Semantic.TemplateVariable (Reference.OpaqueSeed 0)))
            observed ordinal value = Reference.ReferenceFact value
                (Reference.WitnessSummary (Set.singleton ordinal) Set.empty Set.empty)
            facts = [observed 0 base, observed 1 row]
            run input = expectRight (fst (Reference.evaluateFormation 1000000 registrations input Set.empty target))
        premises <- traverse checked [baseFormula, rowFormula]
        (snapshot, result) <- run facts
        assertBool "an ordinary classification does not expand initial definition evidence"
            (all ((/= alias) . fst) (Map.keys (Reference.referenceAnswers (Reference.referenceSnapshotInitial snapshot))))
        meanings <- checkImportedReferenceReplay closure imported ambient
            (ReferenceImports.importedReferenceTerm closure modules (\(Reference.OpaqueSeed index) -> Core.CBound index))
            (ReferenceImports.importedReferenceAtom modules (ReferenceImports.importedReferenceTerm closure modules (\(Reference.OpaqueSeed index) -> Core.CBound index)))
            (zip facts premises) result
        expected <- checked (Core.CApp (Core.CGlobal (Semantic.semanticGlobalTargetObject
            (Semantic.semanticGlobalBindingTarget selectedBinding))) (Core.CBound 0))
        assertEqual "derived row supplies the correlated output for the actual theorem"
            (Just expected) (Map.lookup target meanings)
        (wrongBase, _) <- atom "notion_base" [2]
        for_ [[observed 1 row], [observed 0 wrongBase, observed 1 row]] \input -> do
            (_, negative) <- run input
            assertBool "a missing or differently correlated guard cannot complete the join"
                (all ((/= target) . fst) (Map.keys (Reference.referenceAnswers negative)))

    checkChain closure modules imported = do
        let named = namedBinding modules
        (relation, _) <- named "notion_package_relation"
        (base, baseBinding) <- named "notion_base"
        initial <- sole "relation definition source"
            [ entry | entry <- Map.elems imported
            , Reference.DefinitionRule rule <- [ReferenceImports.importedReferenceRegistration entry]
            , [Semantic.RulePremiseAtom (Semantic.GlobalAtomTemplate head' _)] <- [Reference.referenceRulePremises rule]
            , Semantic.globalNotionHeadReference head' == relation]
        let initialRule = Reference.registrationRule (ReferenceImports.importedReferenceRegistration initial)
            arity = Reference.referenceRuleArity initialRule
            ambient = replicate (fromIntegral arity) Core.TySet
            registrations = ReferenceImports.importedReferenceRegistration <$> imported
            checked = expectRight . Core.checkScopedCanonicalCore (Identity.globalTypingFromClosure closure) ambient
            open 0 term = term
            open n (Core.CForall Core.TySet body) = open (n-1) body
            open _ _ = error "malformed sealed reference telescope"
        (row, subject, premise) <- case (Reference.referenceRulePremises initialRule,
                open arity (Core.frozenCoreTerm (Identity.checkedPropositionTerm
                    (ReferenceImports.importedReferenceProposition initial)))) of
            ([Semantic.RulePremiseAtom atom@(Semantic.GlobalAtomTemplate _ terms)], Core.CImp premise _)
                | Just (Semantic.TemplateVariable (Semantic.ViewVariableIx subject), _) <- Vector.uncons terms ->
                    pure (fmap (fmap (\(Semantic.ViewVariableIx index) -> Reference.OpaqueSeed index)) atom, subject, premise)
            _ -> fail "relation fixture lost its source atom"
        let seed index = Semantic.TemplateVariable (Reference.OpaqueSeed index)
            goal index = Semantic.GlobalAtomTemplate (Semantic.NounNotionHead base) (Vector.singleton (seed index))
            observation = Reference.ReferenceFact row (Reference.WitnessSummary (Set.singleton 0) Set.empty Set.empty)
            run facts target = expectRight (fst (Reference.evaluateFormation 1000000 registrations facts Set.empty target))
        hypothesis <- checked premise
        (snapshot, result) <- run [observation] (goal subject)
        assertBool "real definition origins expand initial evidence across predicate surfaces"
            (any ((== goal subject) . fst) (Map.keys (Reference.referenceAnswers (Reference.referenceSnapshotInitial snapshot))))
        meanings <- checkImportedReferenceReplay closure imported ambient
            (ReferenceImports.importedReferenceTerm closure modules (\(Reference.OpaqueSeed index) -> Core.CBound index))
            (ReferenceImports.importedReferenceAtom modules (ReferenceImports.importedReferenceTerm closure modules (\(Reference.OpaqueSeed index) -> Core.CBound index)))
            [(observation, hypothesis)] result
        expected <- checked (Core.CApp (Core.CGlobal (Semantic.semanticGlobalTargetObject
            (Semantic.semanticGlobalBindingTarget baseBinding))) (Core.CBound subject))
        assertEqual "composed imported witness proves the actual base predicate"
            (Just expected) (Map.lookup (goal subject) meanings)
        for_ [([], goal subject), ([observation], goal (if subject == 0 then 1 else 0))] \(facts, target) -> do
            (_, negative) <- run facts target
            assertBool "definition composition needs the exact source and subject"
                (all ((/= target) . fst) (Map.keys (Reference.referenceAnswers negative)))

    checkDefinitionScope foundation modules parsed = do
        let dependencies = take (length modules - 1) modules
        (location, assumptions, variable, expression, resultPhrase) <- sole "reference definition source"
            [(location, assumptions, variable, expression, resultPhrase)
            | Raw.BlockDefn location _ marker (Raw.DefnOp assumptions (Raw.SymbolPattern _ [variable]) expression resultPhrase)
                <- Parsed.parsedModuleBlocks parsed, marker == "notion_reference_definition_identity"]
        (provider, _) <- namedBinding modules "notion_reference_definition_identity"
        driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
            (completedModuleEvidence <$> dependencies) unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver do
                closure <- Declaration.checkedObjectClosureLowering
                initial <- Elaboration.initialElaborationStateLowering closure Elaboration.emptyElaborationContext
                Except.runExceptT (State.runStateT (do
                    Elaboration.setElaborationDefinitionProvider provider
                    Elaboration.initializeDefinitionElaboration (Map.singleton variable (0, Core.TySet)) 1 False
                    (_, live) <- Elaboration.compileHostedSetTermDefinitionWithFormationObservation id
                        location assumptions resultPhrase (Elaboration.compileNamedSetExpressionWithSource expression)
                    pure (closure, live)) initial))
        (closure, live, finished) <- case driven of
            Declaration.DriverSucceeded outcome _ _ -> do
                ((closure, live), finished) <- expectRight outcome
                pure (closure, live, finished)
            _ -> fail "reference definition did not elaborate"
        prepared <- sole "prepared reference definition result"
            (maybe [] (toList . Elaboration.preparedDefinitionResultItems) (Elaboration.elaborationDefinitionResults live))
        target <- case Elaboration.preparedDefinitionResultConclusion prepared of
            Semantic.AtomicLeaf description -> do
                arguments <- traverse (\case
                    Semantic.ResultRuleProviderValue -> pure (Elaboration.preparedDefinitionResultBody prepared)
                    _ -> fail "the reference identity result gained a non-result operand") description
                pure (Notion.sourceNotionAssertionFromTemplate arguments
                    (Elaboration.preparedDefinitionResultProposition prepared) Notion.ConjunctionHere location)
            _ -> fail "the reference identity result ceased to be atomic"
        let ambient = Core.scopedCoreContext (Notion.sourceAssertionFormula target)
            snapshot allowance consumer state = Elaboration.countedElaborationFormationObservations allowance
                Notion.defaultFormationSearchLimits consumer state
            emptyAliases = Elaboration.alignFormationAliases Elaboration.emptyElaborationContext
            snapshotAction consumer state = Reference.countedReferenceOperation (\allowance ->
                case snapshot allowance consumer state of
                    (Right value, remaining) -> (Right value, remaining)
                    (Left Core.CountedCoreStructuralWorkExhausted, remaining) -> (Left Reference.ReferenceWorkExhausted, remaining)
                    (Left (Core.CountedCoreOperationFailed failure), remaining) ->
                        (Left (Reference.ReferenceInvalidInput (StrictText.pack (show failure))), remaining))
            run allowance consumer state = Reference.runReference allowance do
                rules <- ReferenceImports.prepareImportedReferenceRules dependencies
                (observations, _) <- snapshotAction consumer state
                inputs <- ReferenceScope.prepareObservedReferenceInputs ambient emptyAliases observations target
                denote <- ReferenceImports.prepareImportedReferenceTerm closure dependencies
                    (\seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
                (_, result) <- Reference.evaluateFormationReferenceBy denote ReferenceImports.equalReferenceCore
                    (ReferenceImports.importedReferenceRegistration <$> rules) (ReferenceScope.scopedReferenceFacts inputs)
                    (ReferenceScope.scopedReferenceAliases inputs) (ReferenceScope.scopedReferenceGoal inputs)
                pure (inputs, result)
            (answer, used) = run 1000000 Elaboration.DefinitionResultNotionQuery live
        (inputs, result) <- expectRight answer
        let goal = ReferenceScope.scopedReferenceGoal inputs
            terms = ReferenceImports.importedReferenceTerm closure dependencies
                (\seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
        assertBool "actual definition headers supply the reference result"
            (any ((== goal) . fst) (Map.keys (Reference.referenceAnswers result)))
        assertEqual "definition observation and reference evaluation share exact work"
            (fmap snd answer, used) (case run used Elaboration.DefinitionResultNotionQuery live of
                (value, work) -> (fmap snd value, work))
        assertEqual "one-short definition reference work exhausts" (Left Reference.ReferenceWorkExhausted)
            (fmap snd (fst (run (used - 1) Elaboration.DefinitionResultNotionQuery live)))
        (observations, _) <- expectRight (fst (snapshot 1000000 Elaboration.DefinitionResultNotionQuery live))
        assertBool "observations retain compiler-owned definition-header origins"
            (not (null observations) && all (\observation -> case Elaboration.formationObservationOrigin observation of
                Elaboration.FormationFromDefinitionHeader{} -> True
                _ -> False) observations)
        for_ [(Elaboration.ProofNotionQuery, live), (Elaboration.DefinitionResultNotionQuery, finished)] \(consumer, state) -> do
            (excluded, _) <- expectRight (fst (snapshot 1000000 consumer state))
            assertBool "headers neither become proof locals nor outlive their definition" (null excluded)
            (negativeInputs, negative) <- expectRight (fst (run 1000000 consumer state))
            assertBool "excluded headers cannot prove the result through the reference"
                (all ((/= ReferenceScope.scopedReferenceGoal negativeInputs) . fst) (Map.keys (Reference.referenceAnswers negative)))
        imported <- expectRight (ReferenceImports.importedReferenceRules dependencies)
        checkScopedReferenceReplay closure imported ambient terms (ReferenceImports.importedReferenceAtom dependencies terms)
            [] inputs result >>= \case
                Left{} -> pure ()
                Right{} -> assertFailure "provisional definition headers became ordinary proof hypotheses"
        -- Check the conditional law using its real checked headers as explicit
        -- assumptions. This does not make them local facts of a caller's proof.
        let facts = [Reference.ReferenceFact row (Reference.WitnessSummary (Set.singleton ordinal) Set.empty Set.empty)
                | (ordinal, Reference.ReferenceFact row _) <- zip [0..] (ReferenceScope.scopedReferenceFacts inputs)]
            parents = Elaboration.formationObservationSource <$> observations
        assertEqual "the reference assumptions are exactly the prepared checked headers"
            (Elaboration.compiledHeaderCore <$> Elaboration.preparedDefinitionResultHeaders prepared) parents
        (_, conditional) <- expectRight (fst (Reference.evaluateFormation 1000000
            (ReferenceImports.importedReferenceRegistration <$> imported) facts Set.empty goal))
        meanings <- checkImportedReferenceReplay closure imported ambient terms
            (ReferenceImports.importedReferenceAtom dependencies terms) (zip facts parents) conditional
        assertEqual "the conditional definition result independently replays"
            (Just (Notion.sourceAssertionFormula target)) (Map.lookup goal meanings)

    checkScopedClaim label foundation closure modules imported parsed = do
        Raw.Claim assumptions conclusion <- sole "scoped reference source claim"
            [claim | Raw.BlockClaim _ _ _ marker claim <- Parsed.parsedModuleBlocks parsed
            , marker == label]
        driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
            (completedModuleEvidence <$> modules) unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver (Elaboration.elaborateClaimEnvelopeWithFormationObservation id assumptions conclusion))
        (envelope, liveHeaders) <- case driven of
            Declaration.DriverSucceeded result _ _ -> expectRight result
            _ -> fail "scoped reference claim did not elaborate"
        target <- sole "scoped reference conclusion" (Elaboration.elaboratedClaimConclusionAssertions envelope)
        let initial = Elaboration.elaboratedClaimContext envelope
            ambient = snd <$> toList (Elaboration.elaborationContextSupport initial)
            checked = expectRight . Core.checkScopedCanonicalCore (Identity.globalTypingFromClosure closure) ambient
            kind = Elaboration.FormationProofAssumption
            origin ordinal = Elaboration.FormationFromProofLocal ordinal kind
        -- Exercise the live declaration context before constructing any proof
        -- locals. Header evidence is eligible for formation, not proof search.
        headerNested <- expectRight (Elaboration.extendElaborationContext
            ((Elaboration.localId 999, Raw.NamedVar "headerFresh") :| []) liveHeaders)
        for_ [liveHeaders, headerNested] \headerContext -> do
            let headerTypes = snd <$> toList (Elaboration.elaborationContextSupport headerContext)
                added = take (length headerTypes - length ambient) headerTypes
                align :: Elaboration.ScopedSourceTerm -> Either Text Elaboration.ScopedSourceTerm
                align = maybe (Left "header source term failed to weaken") Right
                    . SourceTerm.alignScopedSourceTermOccurrence headerTypes
            headerTarget <- expectRight (Notion.traverseSourceNotionAssertionParts align
                (Right . (\core -> foldr Core.weakenCheckedScopedCore core added)) target)
            (headerInputs, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
                Elaboration.FormationNotionQuery headerContext headerTarget)
            let headerFacts = ReferenceScope.scopedReferenceFacts headerInputs
                headerGoal = ReferenceScope.scopedReferenceGoal headerInputs
                headerTerms = ReferenceImports.importedReferenceTerm closure modules
                    (\seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves headerInputs Map.! seed))
                registrations = ReferenceImports.importedReferenceRegistration <$> imported
                provisional = \case
                    Elaboration.FormationFromCheckedGuard{} -> True
                    _ -> False
            assertBool "live formation sees the actual provisional declaration headers"
                (any (\(Reference.ReferenceFact _ summary) -> any provisional (Set.toList (Reference.witnessOrigins summary))) headerFacts)
            (_, headerResult) <- expectRight (fst (Reference.evaluateFormationWithDenotation headerTerms 1000000
                registrations headerFacts (ReferenceScope.scopedReferenceAliases headerInputs) headerGoal))
            assertBool "live declaration assumptions answer the reference formation request"
                (any ((== headerGoal) . fst) (Map.keys (Reference.referenceAnswers headerResult)))
            (proofInputs, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
                Elaboration.ProofNotionQuery headerContext headerTarget)
            assertBool "proof queries cannot borrow provisional declaration assumptions"
                (null (ReferenceScope.scopedReferenceFacts proofInputs))
            checkScopedReferenceReplay closure imported headerTypes headerTerms
                (ReferenceImports.importedReferenceAtom modules headerTerms) [] headerInputs headerResult >>= \case
                    Left{} -> pure ()
                    Right{} -> assertFailure "provisional formation evidence became proof-local authority"
        (afterHeaders, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
            Elaboration.FormationNotionQuery initial target)
        assertBool "leaving claim headers removes their provisional evidence"
            (null (ReferenceScope.scopedReferenceFacts afterHeaders))
        -- Retain the parsed atom inside a larger local conjunction. The oracle
        -- must use that original local slot and its projection, including after
        -- weakening under another binder; the atom is never a fresh hypothesis.
        sources <- for (zip [42..] (Elaboration.elaboratedClaimAntecedents envelope)) \(ordinal, header) -> do
            let core = Elaboration.compiledHeaderCore header
                reflexive = Core.CEq Core.TySet (Core.CIntrinsic Core.Empty) (Core.CIntrinsic Core.Empty)
            parent <- checked (Core.CAnd reflexive (Core.CAnd (Core.scopedCoreTerm core) reflexive))
            let evidence = SourceEvidence.SourceAnd (SourceEvidence.SourceResidual Nothing)
                    (SourceEvidence.SourceAnd (Elaboration.compiledHeaderEvidence header) (SourceEvidence.SourceResidual Nothing))
            pure (Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport initial)
                    parent evidence ordinal kind, Notion.materializedNotionHypothesis parent (origin ordinal))
        active <- expectRight (foldM (flip Elaboration.addFormationPremiseSource) initial (fst <$> sources))
        nested <- expectRight (Elaboration.extendElaborationContext
            ((Elaboration.localId 1000, Raw.NamedVar "fresh") :| []) active)
        for_ [active, nested] \context -> do
            let currentTypes = snd <$> toList (Elaboration.elaborationContextSupport context)
                added = take (length currentTypes - length ambient) currentTypes
                weaken core = foldr Core.weakenCheckedScopedCore core added
                alignTerm :: Elaboration.ScopedSourceTerm -> Either Text Elaboration.ScopedSourceTerm
                alignTerm = maybe (Left "source term failed to weaken") Right
                    . SourceTerm.alignScopedSourceTermOccurrence currentTypes
            alignedTarget <- expectRight (Notion.traverseSourceNotionAssertionParts alignTerm (Right . weaken) target)
            (inputs, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
                Elaboration.ProofNotionQuery context alignedTarget)
            let registrations = ReferenceImports.importedReferenceRegistration <$> imported
                goal = ReferenceScope.scopedReferenceGoal inputs
                facts = ReferenceScope.scopedReferenceFacts inputs
                terms = ReferenceImports.importedReferenceTerm closure modules
                    (\seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
                locals = [Notion.materializedNotionHypothesis
                    (weaken (Notion.materializedNotionHypothesisProposition local))
                    (Notion.materializedNotionHypothesisOrigin local) | (_,local) <- sources]
            (_, result) <- expectRight (fst (Reference.evaluateFormationWithDenotation terms 1000000 registrations facts (ReferenceScope.scopedReferenceAliases inputs) goal))
            let metered allowance = Reference.runReference allowance do
                    preparedRules <- ReferenceImports.prepareImportedReferenceRules modules
                    (prepared, _) <- ReferenceScope.prepareScopedReferenceInputs Notion.defaultFormationSearchLimits
                        Elaboration.ProofNotionQuery context alignedTarget
                    denote <- ReferenceImports.prepareImportedReferenceTerm closure modules
                        (\seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves prepared Map.! seed))
                    Reference.evaluateFormationReferenceBy denote ReferenceImports.equalReferenceCore
                        (ReferenceImports.importedReferenceRegistration <$> preparedRules)
                        (ReferenceScope.scopedReferenceFacts prepared)
                        (ReferenceScope.scopedReferenceAliases prepared) (ReferenceScope.scopedReferenceGoal prepared)
                (meteredResult, usedWork) = metered 1000000
            (_, interpreted) <- expectRight meteredResult
            assertEqual "metered scoped preparation and Core interpretation preserve all reference answers" result interpreted
            assertEqual "scoped preparation, provider tables, and Core substitution share the exact allowance"
                (meteredResult, usedWork) (metered usedWork)
            assertEqual "one-short Core interpretation work is exhaustion"
                (Left Reference.ReferenceWorkExhausted) (fst (metered (usedWork - 1)))
            let production allowance = Reference.runReference allowance do
                    denote <- ReferenceImports.prepareImportedReferenceTerm closure modules
                        (\seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
                    let firstHole = fromIntegral (length currentTypes)
                    partial <- ReferenceImports.prepareImportedReferenceTerm closure modules
                        (\case Nothing -> Core.CBound firstHole
                               Just seed -> Core.scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
                    let compatible a b = do
                            left <- partial a
                            right <- partial b
                            WholePattern.mayEqualOperands (Reference.chargeReferenceWork . fromIntegral) firstHole left right
                    (productionGoal,rows) <- ReferenceScope.productionScopedRows inputs
                    let productionFacts = zipWith (\row (Reference.ReferenceFact _ summary) -> Reference.ReferenceFact row summary) rows facts
                    Production.evaluateProduction compatible denote ReferenceImports.equalReferenceCore registrations productionFacts
                        (ReferenceScope.scopedReferenceAliases inputs) productionGoal
                (produced,productionWork) = production 1000000
            productionResult <- expectRight produced
            let rootSummaries evaluation = Set.fromList
                    [summary | ((row,summary),_) <- Map.toList (Reference.referenceAnswers evaluation), row == goal]
            assertEqual "scoped production agrees on every eligible root answer"
                (rootSummaries result) (rootSummaries productionResult)
            assertEqual "scoped production shares exact accounting" (produced,productionWork) (production productionWork)
            assertEqual "one-short scoped production exhausts" (Left Reference.ReferenceWorkExhausted)
                (fst (production (productionWork - 1)))
            productionMeanings <- expectRight =<< checkScopedReferenceReplay closure imported currentTypes terms
                (ReferenceImports.importedReferenceAtom modules terms) locals inputs productionResult
            assertEqual "production witnesses replay to the actual scoped goal"
                (Just (Notion.sourceAssertionFormula alignedTarget)) (Map.lookup goal productionMeanings)
            when (label == "notion_reference_identity_direct") do
                assertBool "the imported identity already has the argument's exact source meaning"
                    (not (any (\witness -> case Reference.referenceWitnessRecipe witness of
                        Reference.SameDenotation{} -> True
                        _ -> False) (Map.elems (Reference.referenceWitnesses result))))
            meanings <- expectRight =<< checkScopedReferenceReplay closure imported currentTypes terms (ReferenceImports.importedReferenceAtom modules terms) locals inputs result
            assertEqual "parsed scoped reference proves its original goal"
                (Just (Notion.sourceAssertionFormula alignedTarget)) (Map.lookup goal meanings)
            let changedKind = [Notion.materializedNotionHypothesis (Notion.materializedNotionHypothesisProposition local)
                    (Elaboration.FormationFromProofLocal ordinal Elaboration.FormationProofDerivedClaim)
                    | local <- locals, Elaboration.FormationFromProofLocal ordinal _ <- [Notion.materializedNotionHypothesisOrigin local]]
                changedFormula = [Notion.materializedNotionHypothesis
                    (fromMaybe (error "negating a checked proposition failed")
                        (Core.negateScopedCore (Notion.materializedNotionHypothesisProposition local)))
                    (Notion.materializedNotionHypothesisOrigin local) | local <- locals]
                provisional = [Notion.materializedNotionHypothesis
                    (Notion.materializedNotionHypothesisProposition local)
                    (Elaboration.FormationFromDefinitionHeader ordinal Nothing Nowhere)
                    | (ordinal, local) <- zip [0..] locals]
            for_ [[], changedKind, changedFormula, provisional, locals <> locals] \invalid ->
                for_ [result,productionResult] \evaluated ->
                    checkScopedReferenceReplay closure imported currentTypes terms (ReferenceImports.importedReferenceAtom modules terms) invalid inputs evaluated >>= \case
                        Left{} -> pure ()
                        Right{} -> assertFailure "scoped replay accepted the wrong actual local source"
            case goal of
                Semantic.GlobalAtomTemplate _ arguments | Just argument <- Vector.headM arguments -> do
                    let mislabeled = Semantic.MembershipAtomTemplate argument argument
                        wrongGoal = inputs {ReferenceScope.scopedReferenceGoal = mislabeled}
                    checkScopedReferenceReplay closure imported currentTypes terms
                        (ReferenceImports.importedReferenceAtom modules terms) locals wrongGoal result >>= \case
                            Left message -> assertEqual "atom labels must independently denote the source goal"
                                "reference atom disagrees with its checked source formula" message
                            Right{} -> assertFailure "a different atom label was accepted for the same source formula"
                _ -> pure ()
            for_ (take 1
                [(index, Semantic.MembershipAtomTemplate argument argument)
                | (index, Reference.ReferenceFact (Semantic.GlobalAtomTemplate _ arguments) _) <- zip [0 :: Int ..] facts
                , Just argument <- [Vector.headM arguments]]) \(changed, mislabeled) -> do
                    let wrongFacts = inputs {ReferenceScope.scopedReferenceFacts =
                            [Reference.ReferenceFact (if index == changed then mislabeled else row) summary
                            | (index, Reference.ReferenceFact row summary) <- zip [0..] facts]}
                    checkScopedReferenceReplay closure imported currentTypes terms
                        (ReferenceImports.importedReferenceAtom modules terms) locals wrongFacts result >>= \case
                            Left message -> assertEqual "observed atom labels must denote their actual local formula"
                                "reference atom disagrees with its checked source formula" message
                            Right{} -> assertFailure "a mislabeled observation was accepted"
            when (label == "notion_reference_erased_argument") do
                let assertion = ReferenceScope.scopedViewAssertion (ReferenceScope.scopedReferenceTarget inputs)
                assertBool "discarded abbreviation arguments leave no provider in the target"
                    (all (isNothing . SourceTerm.sourceTermOccurrenceProvider) (Notion.sourceAssertionAtom assertion))
            let lostOrigins = inputs {ReferenceScope.scopedReferenceFacts =
                    [Reference.ReferenceFact row summary {Reference.witnessOrigins = Set.empty}
                    | Reference.ReferenceFact row summary <- facts]}
            checkScopedReferenceReplay closure imported currentTypes terms (ReferenceImports.importedReferenceAtom modules terms) locals lostOrigins result >>= \case
                Left{} -> pure ()
                Right{} -> assertFailure "scoped reference replay accepted a row with erased origins"
            ordinary <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                (completedModuleEvidence <$> modules) unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    query <- Elaboration.elaborateProofNotionEvidenceWithBudget
                        (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits)
                        context Nowhere alignedTarget
                    replayed <- case query of
                        Right (Elaboration.NotionQueryFound evidence, _) ->
                            Just <$> Declaration.replayTransientFormationLowering closure evidence
                                (Notion.sourceAssertionFormula alignedTarget)
                        _ -> pure Nothing
                    pure (query, replayed))
            case ordinary of
                Declaration.DriverSucceeded
                        (Right (Elaboration.NotionQueryFound evidence, budget), Just (Right _)) _ _ ->
                    when (label `elem`
                            [ "notion_package_chain_replay"
                            , "notion_finite_evidence_from_membership"
                            , "notion_graph_domain_intro"
                            , "notion_reference_identity_direct"
                            , "notion_reference_erased_argument"
                            ]) do
                        when (label `notElem` ["notion_reference_identity_direct", "notion_reference_erased_argument"])
                            (assertBool "the live rule query uses declaration-owned witnesses"
                                (not (Vector.null (Notion.materializedFormationImports evidence))))
                        assertEqual "the live rule query bypasses the legacy controller"
                            0 (Notion.formationSearchCompositePremiseRequests
                                (Notion.formationSearchBudgetStatistics budget))
                _ -> assertFailure "the ordinary scoped query or its replay disagrees with the reference"

    relationalTree = \case
        Semantic.RulePremiseAtom{} -> True
        Semantic.RulePremiseAnd left right -> relationalTree left && relationalTree right
        _ -> False

    checkRule closure modules (ordinal, imported) = do
        let registration = ReferenceImports.importedReferenceRegistration imported
            rule = Reference.registrationRule registration
            arity = Reference.referenceRuleArity rule
            ambient = replicate (fromIntegral arity) Core.TySet
            instantiate = fmap (fmap (\(Semantic.ViewVariableIx index) -> Reference.OpaqueSeed index))
            target = instantiate (Reference.referenceRuleConclusion rule)
            source = Core.frozenCoreTerm (Identity.checkedPropositionTerm
                (ReferenceImports.importedReferenceProposition imported))
            open 0 formula = pure formula
            open n (Core.CForall Core.TySet body) = open (n-1) body
            open _ _ = fail "reference theorem has the wrong binder telescope"
            split [] formula = pure ([], formula)
            split (tree : rest) (Core.CImp premise remaining) = do
                rows <- leaves tree premise
                (later, result) <- split rest remaining
                pure (rows <> later, result)
            split _ _ = fail "reference theorem has the wrong premise grouping"
            leaves (Semantic.RulePremiseAtom row) formula = pure [(instantiate row, formula)]
            leaves (Semantic.RulePremiseAnd left right) (Core.CAnd a b) = (<>) <$> leaves left a <*> leaves right b
            leaves _ _ = fail "reference conjunction tree disagrees with its actual theorem"
            checked = expectRight . Core.checkScopedCanonicalCore (Identity.globalTypingFromClosure closure) ambient
        body <- open arity source
        (rows, resultBody) <- split (Reference.referenceRulePremises rule) body
        let select Notion.ConjunctionHere formula = pure formula
            select (Notion.ConjunctionLeft rest) (Core.CAnd left _) = select rest left
            select (Notion.ConjunctionRight rest) (Core.CAnd _ right) = select rest right
            select _ _ = fail "reference registration has an invalid source selector"
        conclusion <- select (ReferenceImports.importedReferencePath imported) resultBody
        facts <- for (zip [0..] rows) \(index, (row, formula)) -> do
            proposition <- checked formula
            pure (Reference.ReferenceFact row (Reference.WitnessSummary (Set.singleton index) Set.empty Set.empty), proposition)
        let registrations = Map.singleton ordinal registration
            (answer, _) = Reference.evaluateFormation 1000000 registrations (fst <$> facts) Set.empty target
        (_snapshot, result) <- expectRight answer
        assertBool ("real registration did not produce its result: " <> show ordinal)
            (any ((== target) . fst) (Map.keys (Reference.referenceAnswers result)))
        meanings <- checkImportedReferenceReplay closure (Map.singleton ordinal imported) ambient
            (ReferenceImports.importedReferenceTerm closure modules (\(Reference.OpaqueSeed index) -> Core.CBound index))
            (ReferenceImports.importedReferenceAtom modules (ReferenceImports.importedReferenceTerm closure modules (\(Reference.OpaqueSeed index) -> Core.CBound index))) facts result
        expected <- checked conclusion
        assertEqual "reference result denotes its actual checked conclusion" (Just expected) (Map.lookup target meanings)

expansionAtom :: Semantic.AbbreviationExpansion -> Maybe (Semantic.AtomTemplate Semantic.ExpansionTerm)
expansionAtom (Semantic.PropositionExpansion (SourceEvidence.SourceAtom atom) []) = Just atom
expansionAtom _ = Nothing
