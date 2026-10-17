{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Declaration (unitTests) where

import Base
import Felix.Cache.Codec (decodeCache, encodeCache)
import Felix.Checking.Binding qualified as Binding
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Backend.Problem qualified as Backend
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.FinalPrelude qualified as FinalPrelude
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Kernel.SetLfp qualified as KernelSetLfp
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Planning qualified as Planning
import Felix.Checking.SetConstruction qualified as SetConstruction
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.ValidationCache qualified as ValidationCache
import Felix.Math.Codec
import Felix.Module
import Felix.Source
import Felix.Source.Scan qualified as SourceScan
import Felix.Store qualified as Store
import Felix.Test.Support.Declarations qualified as DeclTest
import Felix.Test.Support.Imports
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Interface qualified as Syntax
import Felix.Syntax.Lexicon qualified as Lexicon

import Data.List.NonEmpty qualified as NonEmpty
import Data.List qualified as List
import Data.ByteString qualified as ByteString
import Data.IORef qualified as IORef
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import Data.Vector qualified as Vector
import Effectful (Eff, IOE, (:>), runEff)
import Numeric.Natural (Natural)
import UnliftIO.Async qualified as Async
import System.Timeout qualified as Timeout
import Control.Exception (bracket)
import Control.Exception qualified as Exception
import Control.Monad (foldM)
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix
import Test.Tasty
import Test.Tasty.HUnit
import Text.Earley (fullParses, parser)


unitTests :: TestTree
unitTests =
    testGroup "Typed declaration seam"
        [ testCase "enforces staged candidate order"
            enforcesStagedCandidateOrder
        , testCase "retains only appended declaration prefixes"
            retainsOnlyAppendedPrefixes
        , testCase "makes declaration failures terminal"
            makesDeclarationFailuresTerminal
        , testCase "propagates unsafe authority through local claims"
            propagatesUnsafeAuthorityThroughLocalClaims
        , testCase "rejects local claims outside their candidate"
            rejectsLocalClaimsOutsideCandidate
        , testCase "propagates unsafe authority from unused imports"
            propagatesUnsafeAuthorityFromUnusedImports
        , testCase "aggregates Vampire obligations"
            aggregatesVampireObligations
        , testCase "preserves explicit premise policy after fact exclusion"
            preservesExplicitPremisePolicyAfterExclusion
        , testCase "validates complete resolver batches before rejection"
            validatesCompleteResolverBatchesBeforeRejection
        , testCase "rejects retained-plan admission drift fatally"
            rejectsRetainedPlanAdmissionDrift
        , testCase "checks retained source dependencies outside kernel imports"
            checksRetainedSourceDependencies
        , testCase "rejects changed planned requests on fresh and cached paths"
            rejectsChangedPlannedRequests
        , testCase "preserves source-axiom safety through Vampire validation"
            preservesSourceAxiomSafetyThroughVampireValidation
        , testCase "materializes a sealed import with fresh authority"
            materializesSealedImport
        , testCase "does not promote imported theorem-shaped definitions"
            doesNotPromoteImportedTheoremShapedDefinitions
        , testCase "reconstructs exact imported global bindings"
            reconstructsImportedGlobalBindings
        , testCase "retains exact source-provider ownership"
            retainsExactSourceProviderOwnership
        , testCase "retains only whitelisted fixed intrinsic providers"
            retainsWhitelistedFixedIntrinsicProviders
        , testCase "retains written ordered-pair identity"
            retainsWrittenOrderedPairIdentity
        , testCase "retains checked equality sidecars"
            retainsCheckedEqualitySidecars
        , testCase "rejects a mismatched source-provider owner"
            rejectsMismatchedSourceProviderOwner
        , testCase "rejects undetermined decoded provider premises"
            rejectsUndeterminedDecodedProviderPremises
        , testCase "rejects an empty imported finite-set provider rule"
            rejectsEmptyFiniteSetProviderRule
        , testCase "elaborates scoped propositions"
            elaboratesScopedPropositions
        , testCase "validates datatype constructor context"
            validatesDatatypeConstructorContext
        , testCase "lowers fixed equality aliases without global support"
            lowersFixedEqualityAliases
        , testCase "scopes quantified proposition terms"
            scopesQuantifiedPropositionTerms
        , testCase "noun predicate polarity preserves negation scope from source"
            scopesNounPredicatePolarity
        , testCase "bounded nouns capture one outer endpoint and retain quantifier scope"
            scopesBoundedNouns
        , testCase "prepares claim envelopes"
            preparesClaimEnvelopes
        , testCase "elaborates separation comprehensions"
            elaboratesSeparationComprehensions
        , testCase "elaborates replacement telescopes"
            elaboratesReplacementTelescopes
        , testCase "elaborates finite sets"
            elaboratesFiniteSets
        , testCase "elaborates bounded natural numerals with validated successor"
            elaboratesBoundedNaturalNumerals
        , testCase "threads natural numeral readiness through driver runners"
            threadsNaturalNumeralReadiness
        , testCase "elaborates ordinary declarations"
            elaboratesOrdinaryDeclarations
        , testCase "publishes first-order definitions pointwise"
            publishesFirstOrderDefinitionsPointwise
        , testCase "folds transitive and diamond import evidence"
            foldsTransitiveAndDiamondEvidence
        , testCase "checks every cached local declaration in its exact scope" checksCachedLocalScope
        , testCase "checks exact imported nodes despite equal semantic identities" checksExactImportNodes
        , testCase "reuses parent preparation without ancestor admission" reusesParentPreparation
        , testCase "matches the declared scope of small import graphs"
            matchesSmallImportGraphs
        , testCase "keeps imported definition selection after a local definition"
            keepsImportedDefinitionSelection
        , testCase "authenticates predicate projection sources and selectors" authenticatesPredicateProjections
        , testCase "validates kernel construction descriptors"
            validatesKernelConstructionDescriptors
        , testCase "admits implementation equations without definition views"
            admitsImplementationDefinitions
        , testCase "rolls back a generated construction with a broken staged dependency"
            rejectsBrokenGeneratedDependency
        , testCase "rejects hidden scoped-kernel authority"
            rejectsHiddenScopedKernelAuthority
        , testCase "restricts set extensionality imports to pointwise views"
            restrictsSetExtensionalityImportsToPointwiseViews
        , testCase "reuses compiled declaration validation"
            reusesCompiledDeclarationValidation
        , testCase "keeps fatal validation lookup failures out of declarations"
            keepsFatalValidationHandlersFailuresOutOfDeclarations
        ]

data FatalValidationHandlers = FatalValidationHandlers
    deriving (Show)

instance Exception.Exception FatalValidationHandlers

keepsFatalValidationHandlersFailuresOutOfDeclarations :: Assertion
keepsFatalValidationHandlersFailuresOutOfDeclarations = do
    fixture <- makeFixture
    prepared <- makePreparedObligation
        fixture
        Foundation.EmptyCharacteristic
    let lookup = proofOnlyValidationHandlers
            (const (Exception.throwIO FatalValidationHandlers))
        action = DeclTest.admitProof
            (Semantic.proofSyntaxId "fatal-validation-lookup") []
                (Declaration.checkedCandidate (factSpec fixture "fatal-validation-lookup")
                    (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere prepared :| []) [] [])) \candidate -> do
                Declaration.authorizeVampireCandidate candidate
                    (Declaration.acceptVampireObligation prepared)
    result <- Exception.try
        (runDriverWithValidation fixture lookup action)
        :: IO
            (Either
                FatalValidationHandlers
                (Declaration.DriverResult
                    Void
                    ((), Commit.CommittedDeclarationBatch)))
    case result of
        Left FatalValidationHandlers -> pure ()
        Right _ ->
            assertFailure "fatal validation lookup became a driver result"

enforcesStagedCandidateOrder :: Assertion
enforcesStagedCandidateOrder = do
    fixture <- makeFixture
    accepted <- runSuccessful fixture do
        result <- DeclTest.admitCompiled
            (Semantic.declarationSyntaxId "staged-success") [] []
            [ Declaration.checkedCandidate (factSpec fixture "first") Declaration.checkedSourceAxiomPlanning :| []
            , fmap (\name -> Declaration.checkedCandidate (factSpec fixture name)
                (Declaration.checkedNoExternalSourceProofPlanning [Planning.PlannedCandidatePosition 0 0]))
                ("later-a" :| ["later-b"])
            ] \case
                [first :| [], later] -> do
                    Declaration.authorizeSourceAxiomCandidate first
                    traverse_
                        (\candidate ->
                            Declaration.authorizeKernelProofCandidate
                                candidate do
                                    premise <-
                                        Declaration.useStagedCandidate first
                                    pure
                                        (Kernel.importedFactDerivation premise))
                        later
                _ -> error "staged-success fixture shape"
        pure result
    let (_value, batch) = accepted
    assertEqual
        "all source-ordered candidates appended"
        3
        (length
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta batch)))

    provenance <- runDriver fixture (priorDeclarationUse fixture)
    case provenance of
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed
                    (Declaration.CandidateOutsideDeclaration slot))
                prefix -> do
            assertEqual
                "cross-declaration staged premise"
                (localFact fixture 0)
                slot
            assertSingleCompletedPrefix prefix
        _other ->
            assertFailure
                "cross-declaration staged provenance was not rejected"

    traverse_
        (\(label, action, expectedPremise, expectedCandidate) -> do
            result <- runDriver fixture action
            case result of
                Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                    (Declaration.StagedPremiseNotEarlier
                        premiseSlot premiseStage
                        candidateSlot candidateStage))
                    _prefix -> do
                    assertEqual (label <> " premise slot")
                        expectedPremise premiseSlot
                    assertEqual (label <> " candidate slot")
                        expectedCandidate candidateSlot
                    assertBool (label <> " rejected non-earlier stage")
                        (premiseStage >= candidateStage)
                Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed other)
                    _prefix ->
                    assertFailure
                        (label <> ": unexpected error " <> show other)
                Declaration.DriverFailed
                    (Declaration.DriverActionFailed _failure)
                    _prefix ->
                    assertFailure
                        (label <> ": unexpected ordinary driver failure")
                Declaration.DriverSucceeded{} ->
                    assertFailure (label <> ": invalid staged use succeeded")
                Declaration.DriverSealFailed{} ->
                    assertFailure (label <> ": invalid staged use reached sealing"))
        [ ( "self"
          , selfUse fixture
          , localFact fixture 0
          , localFact fixture 0
          )
        , ( "same stage"
          , sameStageUse fixture
          , localFact fixture 1
          , localFact fixture 0
          )
        , ( "forward"
          , forwardUse fixture
          , localFact fixture 1
          , localFact fixture 0
          )
        ]
  where
    localFact fixture ordinal =
        Semantic.factSlot
            (fixtureOwner fixture)
            (localFactOrdinal ordinal)

    selfUse fixture =
        DeclTest.admitCompiled (Semantic.declarationSyntaxId "self") [] []
            [Declaration.checkedCandidate (factSpec fixture "self")
                (Declaration.checkedNoExternalSourceProofPlanning []) :| []] \case
                [candidate :| []] ->
                    Declaration.authorizeKernelProofCandidate candidate do
                        premise <- Declaration.useStagedCandidate candidate
                        pure (Kernel.importedFactDerivation premise)
                _ -> error "self-use fixture shape"

    sameStageUse fixture =
        DeclTest.admitCompiled (Semantic.declarationSyntaxId "same-stage") [] []
            [fmap (\name -> Declaration.checkedCandidate (factSpec fixture name)
                (Declaration.checkedNoExternalSourceProofPlanning [])) ("same-a" :| ["same-b"])] \case
                [first :| [second]] ->
                    Declaration.authorizeKernelProofCandidate first do
                        premise <- Declaration.useStagedCandidate second
                        pure (Kernel.importedFactDerivation premise)
                _ -> error "same-stage fixture shape"

    forwardUse fixture =
        DeclTest.admitCompiled (Semantic.declarationSyntaxId "forward") [] []
            [Declaration.checkedCandidate (factSpec fixture name)
                (Declaration.checkedNoExternalSourceProofPlanning []) :| [] | name <- ["forward-a", "forward-b"]] \case
                [first :| [], second :| []] ->
                    Declaration.authorizeKernelProofCandidate first do
                        premise <- Declaration.useStagedCandidate second
                        pure (Kernel.importedFactDerivation premise)
                _ -> error "forward-use fixture shape"

    priorDeclarationUse fixture = do
        (premise, _batch) <- DeclTest.admitCompiled (Semantic.declarationSyntaxId "prior-stage") [] []
            [Declaration.checkedCandidate (factSpec fixture "prior-stage") Declaration.checkedSourceAxiomPlanning :| []] \case
                [candidate :| []] -> Declaration.authorizeSourceAxiomCandidate candidate >> pure candidate
                _ -> error "prior-stage fixture shape"
        void
            (DeclTest.admitCompiled (Semantic.declarationSyntaxId "later-stage") [] []
                [Declaration.checkedCandidate (factSpec fixture "later-stage")
                    (Declaration.checkedNoExternalSourceProofPlanning []) :| []] \case
                    [candidate :| []] ->
                        Declaration.authorizeKernelProofCandidate candidate do
                            imported <-
                                Declaration.useStagedCandidate premise
                            pure (Kernel.importedFactDerivation imported)
                    _ -> error "later-stage fixture shape")

retainsOnlyAppendedPrefixes :: Assertion
retainsOnlyAppendedPrefixes = do
    fixture <- makeFixture
    outcome <- runDriver fixture do
        (_value, _firstBatch) <- DeclTest.admitProof
            (Semantic.proofSyntaxId "accepted") []
                (Declaration.checkedCandidate (factSpec fixture "accepted") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                Declaration.authorizeSourceAxiomCandidate candidate
        Declaration.failModuleDriver
            ("later checker failure" :: Text)
    case outcome of
        Declaration.DriverFailed
                (Declaration.DriverActionFailed reason) prefix -> do
            assertEqual
                "driver reports the later ordinary failure"
                "later checker failure"
                reason
            assertSingleCompletedPrefix prefix
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed err) _prefix ->
            assertFailure
                ("unexpected declaration failure: " <> show err)
        Declaration.DriverSucceeded{} ->
            assertFailure "ordinary driver failure was lost"
        Declaration.DriverSealFailed{} ->
            assertFailure "ordinary driver failure became a seal failure"

makesDeclarationFailuresTerminal :: Assertion
makesDeclarationFailuresTerminal = do
    fixture <- makeFixture
    outcome <- runDriver fixture do
        void
            (DeclTest.admitProof
                (Semantic.proofSyntaxId "accepted-before-failure") []
                    (Declaration.checkedCandidate (factSpec fixture "accepted-before-failure") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                    Declaration.authorizeSourceAxiomCandidate candidate)
        void
            (DeclTest.admitCompiled (Semantic.declarationSyntaxId "rolled-back") [] []
                [Declaration.checkedCandidate (factSpec fixture "uncommitted")
                    Declaration.checkedSourceAxiomPlanning :| []] (const (pure ())))
        -- This declaration must be unreachable after the terminal failure.
        void
            (DeclTest.admitProof
                (Semantic.proofSyntaxId "must-not-publish") []
                    (Declaration.checkedCandidate (factSpec fixture "must-not-publish") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                    Declaration.authorizeSourceAxiomCandidate candidate)
    case outcome of
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed
                    Declaration.DeclarationHasUnauthorizedCandidates)
                prefix ->
            assertSingleCompletedPrefix prefix
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed other) _prefix ->
            assertFailure
                ("unexpected declaration failure: " <> show other)
        Declaration.DriverFailed
                (Declaration.DriverActionFailed _failure) _prefix ->
            assertFailure "unexpected ordinary driver failure"
        Declaration.DriverSucceeded{} ->
            assertFailure "failed declaration was skipped"
        Declaration.DriverSealFailed{} ->
            assertFailure "failed declaration reached sealing"

assertSingleCompletedPrefix
    :: Commit.PendingModulePrefix
    -> Assertion
assertSingleCompletedPrefix prefix = do
    let batches =
            Commit.pendingModulePrefixBatches prefix
    assertEqual "one completed envelope survives" 1 (length batches)
    case batches of
        [batch] -> do
            let expected =
                    Commit.committedBatchNextPrefix batch
            assertEqual
                "failed declaration did not advance the prefix"
                expected
                (Commit.pendingModulePrefixCurrent prefix)
            assertEqual
                "retained envelope ends at the exposed prefix"
                expected
                (Commit.committedBatchNextPrefix batch)
        _ -> pure ()

propagatesUnsafeAuthorityThroughLocalClaims :: Assertion
propagatesUnsafeAuthorityThroughLocalClaims = do
    fixture <- makeFixture
    result <- runSuccessful fixture do
        (_sourceValue, sourceBatch) <- DeclTest.admitProof
            (Semantic.proofSyntaxId "source-axiom") []
                (Declaration.checkedCandidate (factSpec fixture "source") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                Declaration.authorizeSourceAxiomCandidate candidate
        sourceOccurrence <- requireSingleOccurrence sourceBatch
        let
            sourceFingerprint =
                Semantic.semanticFactFingerprint sourceOccurrence
        (_derivedValue, derivedBatch) <- DeclTest.admitProof
            (Semantic.proofSyntaxId "local-claim") []
                (Declaration.checkedCandidate (factSpec fixture "derived")
                    (Declaration.checkedNoExternalSourceProofPlanningWithFacts [sourceFingerprint] [])) \candidate -> do
                Declaration.authorizeKernelProofCandidate candidate do
                    sourcePremise <-
                        Declaration.useAuthorizedFact sourceFingerprint
                    claim <- Declaration.proveLocalKernelClaim
                        (fixtureProposition fixture)
                        (Kernel.importedFactDerivation sourcePremise)
                    claimPremise <- Declaration.useLocalClaim claim
                    pure (Kernel.importedFactDerivation claimPremise)
        pure derivedBatch
    occurrence <-
        case Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta result) of
            [single] -> pure single
            facts ->
                assertFailure
                    ("unexpected fact count: " <> show (length facts))
                    >> fail "unreachable"
    let authority = Semantic.semanticFactAuthority occurrence
    assertEqual
        "local claim cannot erase source-axiom safety"
        (Authority.authoritySafety
            (Authority.singletonEscapeKind Authority.SourceAxiom))
        (Authority.factAuthoritySafety authority)
    case Commit.committedBatchProofValidations result of
        [record] ->
            assertEqual
                "local support is absent from the compact direct authorization"
                (Authority.CheckedSourceProof Authority.NoExternalProofUse)
                (Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate record))
        records ->
            assertFailure
                ("unexpected proof validation count: "
                    <> show (length records))

rejectsLocalClaimsOutsideCandidate :: Assertion
rejectsLocalClaimsOutsideCandidate = do
    fixture <- makeFixture
    let tag = Foundation.EmptyCharacteristic
    proposition <- foundationProposition fixture tag
    claimRef <- IORef.newIORef Nothing
    outcome <- runDriver fixture
        (DeclTest.admitCompiled (Semantic.declarationSyntaxId "candidate-local-claim") [] []
            [Declaration.checkedCandidate
                (Declaration.candidateSpec proposition Semantic.SearchEligible [Semantic.semanticName name])
                (Declaration.checkedNoExternalSourceProofPlanning []) :| []
            | name <- ["local-claim-owner", "local-claim-outsider"]] \case
              [first :| [], second :| []] -> do
                Declaration.authorizeKernelProofCandidate first do
                    claim <- Declaration.proveLocalKernelClaim
                        proposition
                        (Kernel.foundationFactDerivation tag)
                    liftIO (IORef.writeIORef claimRef (Just claim))
                    pure (Kernel.foundationFactDerivation tag)
                Declaration.authorizeKernelProofCandidate second do
                    claim <-
                        fromMaybe
                            (error "first candidate did not publish its claim")
                            <$> liftIO (IORef.readIORef claimRef)
                    premise <- Declaration.useLocalClaim claim
                    pure (Kernel.importedFactDerivation premise)
              _ -> error "local-claim ownership fixture shape")
    case outcome of
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed
                    Declaration.LocalClaimOutsideCandidate)
                prefix ->
            assertEqual
                "the failed declaration publishes no batch"
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Declaration.DriverFailed{} ->
            assertFailure "unexpected local-claim ownership failure"
        Declaration.DriverSucceeded{} ->
            assertFailure "a local claim crossed its candidate owner"
        Declaration.DriverSealFailed{} ->
            assertFailure "an invalid local claim reached module sealing"

propagatesUnsafeAuthorityFromUnusedImports :: Assertion
propagatesUnsafeAuthorityFromUnusedImports = do
    fixture <- makeFixture
    let tag = Foundation.EmptyCharacteristic
    proposition <- foundationProposition fixture tag
    derivedBatch <- runSuccessful fixture do
        (_sourceValue, sourceBatch) <- DeclTest.admitProof
            (Semantic.proofSyntaxId "unused-source-axiom") []
                (Declaration.checkedCandidate (factSpec fixture "unused-source-axiom") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                Declaration.authorizeSourceAxiomCandidate candidate
        sourceOccurrence <- requireSingleOccurrence sourceBatch
        let sourceFingerprint =
                Semantic.semanticFactFingerprint sourceOccurrence
        (_derivedValue, batch) <- DeclTest.admitProof
            (Semantic.proofSyntaxId "unused-kernel-import") []
                (Declaration.checkedCandidate (Declaration.candidateSpec
                        proposition
                        Semantic.SearchEligible
                        [Semantic.semanticName "unused-kernel-import"])
                    (Declaration.checkedNoExternalSourceProofPlanningWithFacts [sourceFingerprint] [])) \candidate -> do
                Declaration.authorizeKernelProofCandidate candidate do
                    void
                        (Declaration.useAuthorizedFact
                            sourceFingerprint)
                    pure (Kernel.foundationFactDerivation tag)
        pure batch
    record <-
        case Commit.committedBatchProofValidations derivedBatch of
            [single] -> pure single
            records ->
                assertFailure
                    ("unexpected proof validation count: "
                        <> show (length records))
                    >> fail "unreachable"
    assertEqual
        "an authenticated unused import still taints candidate authority"
        (Authority.authoritySafety
            (Authority.singletonEscapeKind Authority.SourceAxiom))
        (Authority.factAuthoritySafety
            (Authority.validationTarget
                (Semantic.proofValidationRecordCertificate record)))
    assertEqual
        "unused imports do not change the direct proof recipe"
        (Authority.CheckedSourceProof Authority.NoExternalProofUse)
        (Authority.validationDirectAuthorization
            (Semantic.proofValidationRecordCertificate record))

preservesExplicitPremisePolicyAfterExclusion :: Assertion
preservesExplicitPremisePolicyAfterExclusion =
    withTemporaryDirectory "felix-declaration-exclusion" \root -> do
        fixture <- makeFixture
        let executable = root Posix.</> "vampire"
            selected = fixtureSourceAxiomFingerprint fixture
            claim =
                Core.embedClosedCore []
                    (Identity.checkedPropositionTerm
                        (fixtureProposition fixture))
            function = Core.CLam Core.TySet (Core.CBound 0)
            higherOrderTerm =
                Core.CEq
                    (Core.TyArrow Core.TySet Core.TySet)
                    function
                    function
        higherOrder <-
            expectRight
                (Core.checkScopedCanonicalCore
                    (Identity.globalTypingFromClosure (fixtureClosure fixture))
                    []
                    higherOrderTerm)
        writeAcceptedVampire executable
        observed <- IORef.newIORef Nothing
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    let problem =
                            Provers.preparedTypedProverLogicalProblem prepared
                    IORef.writeIORef observed
                        (Just
                            ( Backend.typedProblemRoute problem
                            , Vector.length
                                (Backend.typedProblemGlobalPremises problem)
                            , Vector.length
                                (Backend.typedProblemLocalPremises problem)
                            ))
                    resolveAccepted executable prepared
            action :: Declaration.ModuleDriver Text ()
            action = do
                void
                    (DeclTest.admitProof
                        (Semantic.proofSyntaxId "excluded-source") []
                            (Declaration.checkedCandidate (factSpec fixture "excluded-source") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                            Declaration.authorizeSourceAxiomCandidate candidate)
                prepared <-
                    Declaration.runProspectiveLoweringDriver
                        (Declaration.prepareScopedVampireObligationExcludingLowering
                            (Set.singleton selected)
                            (Vector.empty
                                :: Vector.Vector (Void, Core.CoreType))
                            claim
                            [ Declaration.scopedVampirePremise
                                (Backend.localPremiseOrdinal 0)
                                ()
                                Vector.empty
                                higherOrder
                            ]
                            []
                            (Declaration.explicitVampirePremisePolicy
                                (selected :| [])))
                        >>= either
                            (error
                                . ("failed exclusion preparation: " <>)
                                . show)
                            pure
                void
                    (DeclTest.admitProof
                        (Semantic.proofSyntaxId "excluded-proof") []
                            (Declaration.checkedCandidate (factSpec fixture "excluded-proof")
                                (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireRequest Nowhere prepared :| []) [] [])) \candidate -> do
                            Declaration.authorizeVampireCandidate candidate
                                (Declaration.acceptPreparedVampireObligation
                                    prepared))
        outcome <- runDriverWithResolver fixture resolver action
        case outcome of
            Declaration.DriverSucceeded{} -> pure ()
            Declaration.DriverFailed failure _prefix ->
                assertFailure
                    ("excluded explicit fixture failed: " <> show failure)
            Declaration.DriverSealFailed failure _prefix ->
                assertFailure
                    ("excluded explicit fixture did not seal: " <> show failure)
        assertEqual
            "explicit-empty selection keeps first-order local filtering"
            (Just (Backend.RouteFof, 0, 0))
            =<< IORef.readIORef observed

aggregatesVampireObligations :: Assertion
aggregatesVampireObligations =
    withTemporaryDirectory "felix-declaration-vampire" \root -> do
        fixture <- makeFixture
        let executable = root Posix.</> "vampire"
        writeAcceptedVampire executable
        first <- makePreparedObligation
            fixture
            Foundation.EmptyCharacteristic
        second <- makePreparedObligation
            fixture
            Foundation.PairSetCharacteristic
        let exactResolver = acceptedResolver executable
        freshOutcome <-
            (runDriverWithResolver fixture exactResolver do
                (_value, committed) <- DeclTest.admitProof
                    (Semantic.proofSyntaxId "two-vampire-obligations") []
                        (Declaration.checkedCandidate (factSpec fixture "two-vampire-obligations")
                            (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| [Declaration.checkedPlannedVampireTask Nowhere second]) [] [])) \candidate -> do
                        Declaration.authorizeVampireCandidate candidate do
                            Declaration.acceptVampireObligation first
                            Declaration.acceptVampireObligation second
                pure committed
                :: IO
                    (Declaration.DriverResult Text
                        Commit.CommittedDeclarationBatch))
        (batch, freshPrefix) <-
            case freshOutcome of
                Declaration.DriverSucceeded value _ prefix ->
                    pure (value, prefix)
                Declaration.DriverFailed failure _ ->
                    assertFailure
                        ("fresh Vampire fixture failed: " <> show failure)
                        >> fail "unreachable"
                Declaration.DriverSealFailed failure _ ->
                    assertFailure
                        ("fresh Vampire fixture did not seal: "
                            <> show failure)
                        >> fail "unreachable"
        let expectedProofUse =
                Authority.UsesExternalProof
                ( Provers.preparedVerificationRequestId
                    (Provers.preparedTypedProverRequest first)
                :| [Provers.preparedVerificationRequestId
                    (Provers.preparedTypedProverRequest second)]
                )
        case Commit.committedBatchProofValidations batch of
            [record] ->
                assertEqual
                    "accepted requests retain source order"
                    (Authority.CheckedSourceProof expectedProofUse)
                    (Authority.validationDirectAuthorization
                        (Semantic.proofValidationRecordCertificate record))
            records ->
                assertFailure
                    ("unexpected proof validation count: "
                        <> show (length records))

        cachedRecord <-
            case Commit.committedBatchProofValidations batch of
                [record] -> pure record
                records ->
                    assertFailure
                        ("unexpected cached proof records: "
                            <> show (length records))
                    >> fail "unreachable"
        cachedLookupKey <- IORef.newIORef Nothing
        cached <- runSuccessfulWithValidation fixture
            (proofOnlyValidationHandlers
                (\key -> do
                    IORef.writeIORef cachedLookupKey (Just key)
                    pure (Just cachedRecord))) do
            (_value, committed) <- DeclTest.admitProof
                (Semantic.proofSyntaxId "two-vampire-obligations") []
                    (Declaration.checkedCandidate (factSpec fixture "two-vampire-obligations")
                        (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| [Declaration.checkedPlannedVampireTask Nowhere second]) [] [])) \candidate -> do
                    Declaration.authorizeVampireCandidate candidate do
                        Declaration.acceptVampireObligation first
                        Declaration.acceptVampireObligation second
            pure committed
        publishedRecord <-
            case Commit.committedBatchProofValidations cached of
                [record] -> pure record
                records ->
                    assertFailure
                        ("unexpected cached validation records: "
                            <> show (length records))
                        >> fail "unreachable"
        assertEqual
            "cached authorization preserves the exact direct proof"
            (Authority.CheckedSourceProof expectedProofUse)
            (Authority.validationDirectAuthorization
                (Semantic.proofValidationRecordCertificate publishedRecord))
        assertEqual
            "lookup and publication retain the same validation key"
            (Semantic.proofValidationRecordKey cachedRecord)
            (Semantic.proofValidationRecordKey publishedRecord)
        assertEqual
            "one proof syntax key governs lookup and publication"
            (Just
                (Semantic.proofValidationRecordKey cachedRecord))
            =<< IORef.readIORef cachedLookupKey

        missLookups <- IORef.newIORef (0 :: Int)
        missRuns <- IORef.newIORef (0 :: Int)
        let missLookup = proofOnlyValidationHandlers \_key -> do
                IORef.modifyIORef' missLookups (+ 1)
                pure Nothing
            missResolver = Declaration.vampireResolver \prepared -> do
                IORef.modifyIORef' missRuns (+ 1)
                resolveAccepted executable prepared
        miss <- runDriverWithValidationAndResolver
            fixture
            missLookup
            missResolver
            do
                (_value, committed) <- DeclTest.admitProof
                    (Semantic.proofSyntaxId "two-vampire-obligations") []
                        (Declaration.checkedCandidate (factSpec fixture "two-vampire-obligations")
                            (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| [Declaration.checkedPlannedVampireTask Nowhere second]) [] [])) \candidate -> do
                        Declaration.authorizeVampireCandidate candidate do
                            Declaration.acceptVampireObligation first
                            Declaration.acceptVampireObligation second
                pure committed
        case miss of
            Declaration.DriverSucceeded{} -> pure ()
            _ ->
                assertFailure "warm miss failed"
        assertEqual "warm miss performs one exact lookup"
            1
            =<< IORef.readIORef missLookups
        assertEqual "warm miss runs every reached Vampire request"
            2
            =<< IORef.readIORef missRuns

        mismatchRuns <- IORef.newIORef (0 :: Int)
        let editedSyntax =
                Semantic.proofSyntaxId "edited-proof-syntax"
            cachedCertificate =
                Semantic.proofValidationRecordCertificate cachedRecord
            corruptedKey =
                Semantic.proofValidationKey
                    (Identity.theoremId
                        (Authority.factAuthorityTheorem
                            (Authority.validationTarget
                                cachedCertificate)))
                    editedSyntax
                    (Commit.committedBatchPreviousPrefix batch)
            corruptedRecord =
                Semantic.proofValidationRecord
                    corruptedKey
                    cachedCertificate
            mismatchResolver = Declaration.vampireResolver \prepared -> do
                IORef.modifyIORef' mismatchRuns (+ 1)
                resolveAccepted executable prepared
            mismatchingLookup = proofOnlyValidationHandlers
                (const (pure (Just corruptedRecord)))
        mismatching <- Exception.try
            (runDriverWithValidationAndResolver
                fixture
                mismatchingLookup
                mismatchResolver
                do
                    DeclTest.admitProof editedSyntax []
                        (Declaration.checkedCandidate (factSpec fixture "two-vampire-obligations")
                            (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| []) [] [])) \candidate -> do
                        Declaration.authorizeVampireCandidate candidate
                            (Declaration.acceptVampireObligation first))
            :: IO
                (Either
                    Declaration.ValidationIntegrityError
                    (Declaration.DriverResult
                        Text
                        ((), Commit.CommittedDeclarationBatch)))
        case mismatching of
            Left Declaration.CachedValidationIntegrityError{} ->
                pure ()
            Right _ ->
                assertFailure "mismatching hit did not abort as corruption"
        assertEqual "mismatching hit does not fall back to Vampire"
            0
            =<< IORef.readIORef mismatchRuns

        withOpenedStore fixture root \store -> do
            storeCheck <- Store.newStoreCheck store
            expectRightIO
                (Store.writePendingModulePrefix storeCheck freshPrefix)
            warmCalls <- IORef.newIORef (0 :: Int)
            let storeLookup = proofOnlyValidationHandlers \key -> do
                    IORef.modifyIORef' warmCalls (+ 1)
                    Store.loadProofValidation storeCheck key >>= expectRight
            warm <- runSuccessfulWithValidation fixture
                storeLookup
                do
                    (_value, committed) <- DeclTest.admitProof
                        (Semantic.proofSyntaxId "two-vampire-obligations") []
                            (Declaration.checkedCandidate (factSpec fixture "two-vampire-obligations")
                                (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| [Declaration.checkedPlannedVampireTask Nowhere second]) [] [])) \candidate -> do
                            Declaration.authorizeVampireCandidate candidate do
                                Declaration.acceptVampireObligation first
                                Declaration.acceptVampireObligation second
                    pure committed
            assertEqual "warm lookup executes once through the store"
                1
                =<< IORef.readIORef warmCalls
            assertEqual "warm path retains cached request IDs"
                (Authority.CheckedSourceProof expectedProofUse)
                (case Commit.committedBatchProofValidations warm of
                    [record] ->
                        Authority.validationDirectAuthorization
                            (Semantic.proofValidationRecordCertificate record)
                    records ->
                        error
                            ("unexpected warm validation records: "
                                <> show (length records)))

        emptyProof <- runDriver fixture do
            DeclTest.admitProof
                (Semantic.proofSyntaxId "empty-vampire-proof") []
                    (Declaration.checkedCandidate (factSpec fixture "empty-vampire-proof")
                        (Declaration.checkedNoExternalSourceProofPlanning [])) \candidate -> do
                    Declaration.authorizeVampireCandidate candidate
                        (pure ())
        case emptyProof of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        Declaration.VampireProofHasNoAcceptedObligations)
                    prefix ->
                assertEqual
                    "empty Vampire proof publishes no declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed other) _prefix ->
                assertFailure
                    ("unexpected empty-proof failure: " <> show other)
            Declaration.DriverFailed
                    (Declaration.DriverActionFailed _failure) _prefix ->
                assertFailure "unexpected ordinary driver failure"
            Declaration.DriverSucceeded{} ->
                assertFailure "empty Vampire proof was authorized"
            Declaration.DriverSealFailed{} ->
                assertFailure "empty Vampire proof reached sealing"

        invalidClosure <- expectRight
            (Identity.validateObjectClosure
                (Identity.theoryId (fixtureFoundation fixture))
                [])
        invalidTarget <- expectRight
            (Identity.validatePropositionContent
                invalidClosure
                (Core.CImp Core.CFalsum Core.CFalsum))
        invalidCalls <- IORef.newIORef (0 :: Int)
        let invalidResolver =
                Declaration.vampireResolver \prepared -> do
                    IORef.modifyIORef' invalidCalls (+ 1)
                    resolveAccepted executable prepared
        invalid <- runDriverWithResolver fixture invalidResolver do
            DeclTest.admitProof
                (Semantic.proofSyntaxId "invalid-vampire-target") []
                    (Declaration.checkedCandidate (Declaration.candidateSpec
                            invalidTarget
                            Semantic.SearchEligible
                            [Semantic.semanticName
                                "invalid-vampire-target"])
                        (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| []) [] [])) \candidate -> do
                    Declaration.authorizeVampireCandidate candidate
                        (Declaration.acceptVampireObligation first)
        assertEqual
            "invalid prepared problem does not invoke Vampire"
            0
            =<< IORef.readIORef invalidCalls
        case invalid of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        Declaration.VampireTargetMismatch)
                    prefix ->
                assertEqual
                    "invalid prepared problem publishes no declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed other) _prefix ->
                assertFailure
                    ("unexpected prepared-problem failure: " <> show other)
            Declaration.DriverFailed
                    (Declaration.DriverActionFailed _failure) _prefix ->
                assertFailure "unexpected ordinary driver failure"
            Declaration.DriverSucceeded{} ->
                assertFailure "invalid prepared problem was authorized"
            Declaration.DriverSealFailed{} ->
                assertFailure "invalid prepared problem reached sealing"

        let mismatchedResolver =
                Declaration.vampireResolver \_prepared ->
                    resolveAccepted executable second
        mismatch <- runDriverWithResolver fixture mismatchedResolver do
            DeclTest.admitProof
                (Semantic.proofSyntaxId "mismatched-vampire-request") []
                    (Declaration.checkedCandidate (factSpec fixture "mismatched-vampire-request")
                        (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere first :| []) [] [])) \candidate -> do
                    Declaration.authorizeVampireCandidate candidate
                        (Declaration.acceptVampireObligation first)
        case mismatch of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        Declaration.VampireRequestMismatch)
                    prefix ->
                assertEqual
                    "mismatch publishes no declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed other) _prefix ->
                assertFailure
                    ("unexpected mismatch failure: " <> show other)
            Declaration.DriverFailed
                    (Declaration.DriverActionFailed _failure) _prefix ->
                assertFailure "unexpected ordinary driver failure"
            Declaration.DriverSucceeded{} ->
                assertFailure "mismatched request was authorized"
            Declaration.DriverSealFailed{} ->
                assertFailure "mismatched request reached sealing"

        unrecorded <- runDriver fixture do
            DeclTest.admitProof
                (Semantic.proofSyntaxId "unrecorded-omission") []
                    (Declaration.checkedCandidate (factSpec fixture "unrecorded-omission")
                        (Declaration.checkedOmittedPlanning [] [] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate
                        (pure ())
        case unrecorded of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        Declaration.OmittedProofDidNotRecordUse)
                    prefix ->
                assertEqual
                    "unrecorded omission publishes no declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed other) _prefix ->
                assertFailure
                    ("unexpected unrecorded-omission failure: "
                        <> show other)
            Declaration.DriverFailed
                    (Declaration.DriverActionFailed _failure) _prefix ->
                assertFailure "unexpected ordinary driver failure"
            Declaration.DriverSucceeded{} ->
                assertFailure "unrecorded omission was authorized"
            Declaration.DriverSealFailed{} ->
                assertFailure "unrecorded omission reached sealing"

        calls <- IORef.newIORef (0 :: Int)
        let countingResolver =
                Declaration.vampireResolver \prepared -> do
                    IORef.modifyIORef' calls (+ 1)
                    resolveAccepted executable prepared
        omittedBatch <- runSuccessfulWithResolver fixture countingResolver do
            (_value, committed) <- DeclTest.admitProof
                (Semantic.proofSyntaxId "omitted-after-obligations") []
                    (Declaration.checkedCandidate (factSpec fixture "omitted-after-obligations")
                        (Declaration.checkedOmittedPlanning [Declaration.checkedPlannedVampireTask Nowhere first, Declaration.checkedPlannedVampireTask Nowhere second] [] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate do
                        Declaration.acceptVampireObligation first
                        Declaration.acceptVampireObligation second
                        Declaration.recordOmittedUse
            pure committed
        assertEqual
            "omitted proof still checks preceding obligations"
            2
            =<< IORef.readIORef calls
        case Commit.committedBatchProofValidations omittedBatch of
            [record] ->
                assertEqual
                    "omitted direct authorization discards request IDs"
                    Authority.OmittedAuthorization
                    (Authority.validationDirectAuthorization
                        (Semantic.proofValidationRecordCertificate record))
            records ->
                assertFailure
                    ("unexpected omitted validation count: "
                        <> show (length records))

validatesCompleteResolverBatchesBeforeRejection :: Assertion
validatesCompleteResolverBatchesBeforeRejection =
    withTemporaryDirectory "felix-declaration-batch-integrity" \root -> do
        fixture <- makeFixture
        let executable = root Posix.</> "vampire"
            firstLocation = mkLocation anonymousSourceDescriptor 1 1
            secondLocation = mkLocation anonymousSourceDescriptor 2 1
        writeAcceptedVampire executable
        mismatchedTask <-
            makePreparedObligation
                fixture
                Foundation.EmptyCharacteristic
        let integrityResolver =
                Declaration.vampireBatchResolver \tasks -> do
                    mismatched <- resolveAccepted executable mismatchedTask
                    let firstTask = NonEmpty.head tasks
                    pure
                        ( Provers.rejectedVampireResolution
                            (Provers.preparedTypedProverRequest firstTask)
                            Provers.RejectedCounterexample
                        :| [mismatched]
                        )
        integrityOutcome <-
            (runDriverWithResolver fixture integrityResolver do
                prepared <- Declaration.runProspectiveLoweringDriver
                    (Declaration.prepareStagedCandidatesVampireWithFactsAndAuxiliariesLowering
                        firstLocation [] [] [] (factSpec fixture "batch-integrity-first") [])
                    >>= either Declaration.failDeclarationDriver pure
                let checked (name, location) = Declaration.checkedCandidate (factSpec fixture name)
                        (Declaration.checkedExternalSourceProofPlanning
                            (Declaration.checkedPlannedVampireRequest location prepared :| []) [])
                DeclTest.admitCompiled (Semantic.declarationSyntaxId "batch-integrity-priority") [] []
                    [checked <$> (("batch-integrity-first", firstLocation) :| [("batch-integrity-second", secondLocation)])] \case
                      [candidates] ->
                        Declaration.authorizeVampireCandidateBatch
                            ( ( firstLocation
                              , NonEmpty.head candidates
                              , Declaration.prepareCurrentCandidateVampire
                              )
                            :| [ ( secondLocation
                                 , NonEmpty.last candidates
                                 , Declaration.prepareCurrentCandidateVampire
                                 )
                               ]
                            )
                      _ -> error "resolver batch fixture shape"
                :: IO
                    (Declaration.DriverResult Text
                        ((), Commit.CommittedDeclarationBatch)))
        case integrityOutcome of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        (Declaration.ProofObligationFailedAt
                            location
                            Declaration.VampireRequestMismatch))
                    prefix -> do
                assertEqual
                    "later request mismatch retains its location"
                    secondLocation
                    location
                assertEqual
                    "integrity failure rolls back the complete declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed failure _prefix ->
                assertFailure
                    ("unexpected batch-integrity failure: " <> show failure)
            Declaration.DriverSucceeded{} ->
                assertFailure
                    "earlier ordinary rejection concealed no integrity failure"
            Declaration.DriverSealFailed{} ->
                assertFailure "invalid batch reached module sealing"

        prepared <-
            makePreparedObligation
                fixture
                Foundation.EmptyCharacteristic
        let excessResolver =
                Declaration.vampireBatchResolver \tasks ->
                    let request =
                            Provers.preparedTypedProverRequest
                                (NonEmpty.head tasks)
                        rejected =
                            Provers.rejectedVampireResolution
                                request
                                Provers.RejectedCounterexample
                    in
                    pure
                        ( rejected
                        :| [rejected]
                        )
        excessOutcome <-
            (runDriverWithResolver fixture excessResolver do
                DeclTest.admitProof
                    (Semantic.proofSyntaxId "singleton-excess-result") []
                        (Declaration.checkedCandidate (factSpec fixture "singleton-excess-result")
                            (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere prepared :| []) [] [])) \candidate -> do
                        Declaration.authorizeVampireCandidate candidate
                            (Declaration.acceptVampireObligation prepared)
                :: IO
                    (Declaration.DriverResult Text
                        ((), Commit.CommittedDeclarationBatch)))
        case excessOutcome of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        (Declaration.VampireResolverBatchSizeMismatch 1 2))
                    prefix ->
                assertEqual
                    "malformed singleton response publishes no declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed failure _prefix ->
                assertFailure
                    ("unexpected singleton-cardinality failure: "
                        <> show failure)
            Declaration.DriverSucceeded{} ->
                assertFailure "singleton resolver ignored an excess result"
            Declaration.DriverSealFailed{} ->
                assertFailure "malformed singleton reached module sealing"

rejectsChangedPlannedRequests :: Assertion
rejectsChangedPlannedRequests = do
    fixture <- makeFixture
    first <- makePreparedObligation fixture Foundation.EmptyCharacteristic
    second <- makePreparedObligation fixture Foundation.PairSetCharacteristic
    let requestId = Provers.preparedVerificationRequestId (Provers.preparedTypedProverRequest first)
        authority = Authority.factAuthority
            (Identity.theoremRef (Identity.theoryId (fixtureFoundation fixture))
                (Identity.checkedPropositionId (fixtureProposition fixture))) Authority.cleanAuthoritySafety
        checked = Declaration.checkedProofDeclaration (Semantic.proofSyntaxId "planned-request-drift")
            [] [] [] Nothing
            [Declaration.checkedCandidate (factSpec fixture "planned-request-drift")
                (Declaration.checkedExternalSourceProofPlanning
                    (Declaration.checkedPlannedVampireTask Nowhere first :| []) []) :| []] ()
        action = snd <$> Declaration.admitCheckedDeclaration checked \() -> \case
            [candidate :| []] -> Declaration.authorizeVampireCandidate candidate
                (Declaration.acceptVampireObligation second)
            _ -> error "planned request drift fixture shape"
    certificate <- expectRight (Authority.validationCertificate authority
        (Authority.CheckedSourceProof (Authority.UsesExternalProof (requestId :| []))))
    for_ [False, True] \cached -> do
        runs <- IORef.newIORef (0 :: Int)
        let handlers = proofOnlyValidationHandlers \key ->
                pure (if cached then Just (Semantic.proofValidationRecord key certificate) else Nothing)
            resolver = Declaration.vampireResolver \task -> do
                IORef.modifyIORef' runs (+ 1)
                pure (Provers.processFailedVampireResolution (Provers.preparedTypedProverRequest task)
                    (Provers.ProverLaunchFailed "unused" "request drift reached the resolver"))
        outcome <- Exception.try (runDriverWithValidationAndResolver fixture handlers resolver action)
            :: IO (Either Declaration.PlanningIntegrityError (Declaration.DriverResult Void Commit.CommittedDeclarationBatch))
        case outcome of
            Left (Declaration.PlanningIntegrityError diagnostic) ->
                assertBool "the cursor rejects the exact changed request" ("planned exact request" `Text.isInfixOf` diagnostic)
            _ -> assertFailure "a changed planned request reached proof completion"
        assertEqual "request drift does not call the prover" 0 =<< IORef.readIORef runs

checksRetainedSourceDependencies :: Assertion
checksRetainedSourceDependencies = do
    baseFixture <- makeFixture
    proposition <- foundationProposition baseFixture Foundation.EmptyCharacteristic
    let fixture = baseFixture{fixtureProposition = proposition}
    for_ [False, True] \drift -> do
        let source name = Declaration.checkedProofDeclaration (Semantic.proofSyntaxId (TextEncoding.encodeUtf8 name))
                [] [] [] Nothing
                [Declaration.checkedCandidate (factSpec fixture name) Declaration.checkedSourceAxiomPlanning :| []] ()
            authorizeSource () [candidate :| []] = Declaration.authorizeSourceAxiomCandidate candidate
            authorizeSource _ _ = error "source dependency fixture shape"
            action = do
                (_, first) <- Declaration.admitCheckedDeclaration (source "dependency-first") authorizeSource
                (_, second) <- Declaration.admitCheckedDeclaration (source "dependency-second") authorizeSource
                let fingerprint batch = case Semantic.declarationDeltaFacts (Commit.committedBatchDelta batch) of
                        [fact] -> Semantic.semanticFactFingerprint fact
                        _ -> error "source dependency occurrence fixture shape"
                    checked = Declaration.checkedProofDeclaration (Semantic.proofSyntaxId "dependency-proof")
                        [] [] [] Nothing
                        [Declaration.checkedCandidate (factSpec fixture "dependency-proof")
                            (Declaration.checkedNoExternalSourceProofPlanningWithFacts [fingerprint first] []) :| []] ()
                planned <- Declaration.runProspectiveLoweringDriver (Declaration.planCheckedDeclaration checked)
                    >>= either Declaration.failDeclarationDriver pure
                snd <$> Declaration.admitPlannedCheckedDeclaration planned \() -> \case
                    [candidate :| []] -> Declaration.authorizeKernelProofCandidate candidate do
                        Declaration.consumeAuthorizedFactDependency (fingerprint (if drift then second else first))
                        pure (Kernel.foundationFactDerivation Foundation.EmptyCharacteristic)
                    _ -> error "source dependency proof fixture shape"
        outcome <- Exception.try (runDriver fixture action)
            :: IO (Either Declaration.PlanningIntegrityError (Declaration.DriverResult Void Commit.CommittedDeclarationBatch))
        case (drift, outcome) of
            (False, Right Declaration.DriverSucceeded{}) -> pure ()
            (True, Left (Declaration.PlanningIntegrityError diagnostic)) ->
                assertBool "dependency drift retains the contract diagnostic" ("prospective contract" `Text.isInfixOf` diagnostic)
            (_, Left failure) -> assertFailure (show failure)
            _ -> assertFailure "retained dependency contract had the wrong outcome"

rejectsRetainedPlanAdmissionDrift :: Assertion
rejectsRetainedPlanAdmissionDrift = do
    fixture <- makeFixture
    let checked =
            Declaration.checkedProofDeclaration
                (Semantic.proofSyntaxId "planned-admission-drift")
                []
                []
                []
                Nothing
                [ Declaration.checkedCandidate
                    (factSpec fixture "planned-admission-drift")
                    Declaration.checkedSourceAxiomPlanning
                    :| []
                ]
                ()
        action = do
            planned <-
                Declaration.runProspectiveLoweringDriver
                    (Declaration.planCheckedDeclaration checked)
                    >>= either Declaration.failDeclarationDriver pure
            snd <$> Declaration.admitPlannedCheckedDeclaration planned
                (\() stages ->
                    case concatMap toList stages of
                        [candidate] ->
                            Declaration.authorizeOmittedCandidate candidate
                                Declaration.recordOmittedUse
                        _ -> error "planned drift fixture candidate shape")
    outcome <-
        Exception.try (runDriver fixture action)
            :: IO
                (Either
                    Declaration.PlanningIntegrityError
                    (Declaration.DriverResult
                        Void
                        Commit.CommittedDeclarationBatch))
    case outcome of
        Left (Declaration.PlanningIntegrityError diagnostic) ->
            assertBool "fatal mismatch identifies prospective contract drift"
                ("prospective contract" `Text.isInfixOf` diagnostic)
        Right _ ->
            assertFailure
                "a changed admitted authority was accepted against its plan"

preservesSourceAxiomSafetyThroughVampireValidation :: Assertion
preservesSourceAxiomSafetyThroughVampireValidation =
    withTemporaryDirectory "felix-declaration-source-axiom" \root -> do
        fixture <- makeFixture
        let executable = root Posix.</> "vampire"
        writeAcceptedVampire executable
        prepared <-
            makePreparedObligationWithPremise
                fixture
                (fixtureSourceAxiomFingerprint fixture)
        freshCalls <- IORef.newIORef (0 :: Int)
        let freshResolver = Declaration.vampireResolver \task -> do
                IORef.modifyIORef' freshCalls (+ 1)
                resolveAccepted executable task
        freshOutcome <-
            (runDriverWithResolver fixture freshResolver
                (sourceAxiomThenVampire fixture prepared)
                :: IO
                    (Declaration.DriverResult Text
                        Commit.CommittedDeclarationBatch))
        assertEqual
            "fresh source-axiom theorem invokes Vampire once"
            1
            =<< IORef.readIORef freshCalls
        freshBatch <-
            case freshOutcome of
                Declaration.DriverSucceeded batch _ _ ->
                    pure batch
                Declaration.DriverFailed failure _ ->
                    assertFailure
                        ("fresh source-axiom driver failed: "
                            <> show failure)
                        >> fail "unreachable"
                Declaration.DriverSealFailed failure _ ->
                    assertFailure
                        ("fresh source-axiom driver did not seal: "
                            <> show failure)
                        >> fail "unreachable"
        let freshRecord = singleProofValidation freshBatch
        assertEqual
            "fresh theorem retains source-axiom safety"
            sourceAxiomSafety
            (Authority.factAuthoritySafety
                (Authority.validationTarget
                    (Semantic.proofValidationRecordCertificate freshRecord)))
        separationCalls <- IORef.newIORef (0 :: Int)
        let separationResolver = Declaration.vampireResolver \task -> do
                IORef.modifyIORef' separationCalls (+ 1)
                resolveAccepted executable task
        separated <-
            (runDriverWithResolver fixture separationResolver do
                void
                    (DeclTest.admitProof
                        (Semantic.proofSyntaxId "source-axiom") []
                            (Declaration.checkedCandidate (factSpec fixture "source-axiom") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                            Declaration.authorizeSourceAxiomCandidate candidate)
                DeclTest.admitProof
                    (Semantic.proofSyntaxId "atp-does-not-import") []
                        (Declaration.checkedCandidate (factSpec fixture "atp-does-not-import")
                            (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere prepared :| []) [] [])) \candidate -> do
                        Declaration.authorizeKernelProofCandidate candidate do
                            Declaration.acceptVampireObligation prepared
                            pure
                                (Kernel.importedFactDerivation
                                    (Kernel.importIx 0))
                :: IO
                    (Declaration.DriverResult Text
                        ((), Commit.CommittedDeclarationBatch)))
        assertEqual "mixed proof executes its ATP obligation"
            1
            =<< IORef.readIORef separationCalls
        case separated of
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed
                        (Declaration.KernelCompletionFailed
                            (Kernel.KernelReplayImportOutOfBounds index)))
                    prefix -> do
                assertEqual "ATP premise is absent from kernel imports"
                    (Kernel.importIx 0)
                    index
                assertEqual "failed mixed proof retains only its prefix"
                    1
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Declaration.DriverFailed failure _prefix ->
                assertFailure
                    ("unexpected mixed-proof failure: " <> show failure)
            Declaration.DriverSucceeded{} ->
                assertFailure "ATP premise entered the kernel import inventory"
            Declaration.DriverSealFailed{} ->
                assertFailure "mixed proof unexpectedly reached sealing"
        withOpenedStore fixture root \store -> do
            storeCheck <- Store.newStoreCheck store
            freshPrefix <-
                case freshOutcome of
                    Declaration.DriverSucceeded _ _ prefix ->
                        pure prefix
                    Declaration.DriverFailed failure _ ->
                        assertFailure
                            ("fresh source-axiom driver failed: "
                                <> show failure)
                            >> fail "unreachable"
                    Declaration.DriverSealFailed failure _ ->
                        assertFailure
                            ("fresh source-axiom driver did not seal: "
                                <> show failure)
                            >> fail "unreachable"
            expectRightIO
                (Store.writePendingModulePrefix storeCheck freshPrefix)
            warmCalls <- IORef.newIORef (0 :: Int)
            let storeLookup = proofOnlyValidationHandlers \key -> do
                    IORef.modifyIORef' warmCalls (+ 1)
                    Store.loadProofValidation storeCheck key >>= expectRight
            warmBatch <- runSuccessfulWithValidation fixture
                storeLookup
                (sourceAxiomThenVampire fixture prepared)
            assertEqual
                "each prepared declaration performs one store lookup"
                2
                =<< IORef.readIORef warmCalls
            assertEqual
                "warm re-entry republishes the exact fresh validation"
                freshRecord
                (singleProofValidation warmBatch)
            assertEqual
                "warm theorem retains source-axiom safety"
                sourceAxiomSafety
                (Authority.factAuthoritySafety
                    (Authority.validationTarget
                        (Semantic.proofValidationRecordCertificate
                            (singleProofValidation warmBatch))))
  where
    sourceAxiomSafety =
        Authority.authoritySafety
            (Authority.singletonEscapeKind Authority.SourceAxiom)

    singleProofValidation batch =
        case Commit.committedBatchProofValidations batch of
            [record] -> record
            records ->
                error
                    ("unexpected proof validation count: "
                        <> show (length records))

sourceAxiomThenVampire
    :: Fixture
    -> Provers.PreparedTypedProverTask
        Semantic.SemanticFactOccurrenceFingerprint
        Void
        ()
        Identity.ObjectId
    -> Declaration.ModuleDriver failure
        Commit.CommittedDeclarationBatch
sourceAxiomThenVampire fixture prepared = do
    void
        (DeclTest.admitProof
            (Semantic.proofSyntaxId "source-axiom") []
                (Declaration.checkedCandidate (factSpec fixture "source-axiom") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                Declaration.authorizeSourceAxiomCandidate candidate)
    (_value, batch) <- DeclTest.admitProof
        (Semantic.proofSyntaxId "source-axiom-vampire") []
            (Declaration.checkedCandidate (factSpec fixture "source-axiom-vampire")
                (Declaration.checkedExternalSourceProofPlanningWithFacts (Declaration.checkedPlannedVampireTask Nowhere prepared :| []) [] [])) \candidate -> do
            Declaration.authorizeVampireCandidate candidate
                (Declaration.acceptVampireObligation prepared)
    pure batch

fixtureSourceAxiomFingerprint
    :: Fixture
    -> Semantic.SemanticFactOccurrenceFingerprint
fixtureSourceAxiomFingerprint fixture =
    Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
        (Semantic.factSlot
            (fixtureOwner fixture)
            (localFactOrdinal 0))
        (Authority.factAuthority
            (Identity.theoremRef
                (Identity.theoryId (fixtureFoundation fixture))
                (Identity.checkedPropositionId
                    (fixtureProposition fixture)))
            (Authority.authoritySafety
                (Authority.singletonEscapeKind Authority.SourceAxiom)))

makePreparedObligationWithPremise
    :: Fixture
    -> Semantic.SemanticFactOccurrenceFingerprint
    -> IO
        (Provers.PreparedTypedProverTask
            Semantic.SemanticFactOccurrenceFingerprint
            Void
            ()
            Identity.ObjectId)
makePreparedObligationWithPremise fixture fingerprint = do
    let globalTyping =
            Identity.globalTypingFromClosure
                (fixtureClosure fixture)
    claim <- expectRight
        (Backend.supportedProposition
            (Vector.empty :: Vector.Vector (Void, Core.CoreType))
            (Core.embedClosedCore
                []
                (Identity.checkedPropositionTerm
                    (fixtureProposition fixture))))
    factProposition <- expectRight
        (Backend.supportedProposition
            (Vector.empty :: Vector.Vector (Void, Core.CoreType))
            (Core.embedClosedCore
                []
                (Identity.checkedPropositionTerm
                    (fixtureProposition fixture))))
    capability <- expectRight
        (Backend.classifySupportedProposition
            globalTyping
            factProposition)
    problem <- expectRight
        (Backend.planTypedProblem
            globalTyping
            (Vector.singleton
                (Backend.typedBackendFact
                    fingerprint
                    factProposition
                    capability))
            claim
            []
            []
            Backend.FirstOrderLocals)
    expectRight
        (Provers.prepareTypedProverTask
            Provers.DirectTask
            problem)

makePreparedObligation
    :: Fixture
    -> Foundation.FoundationAxiomTag
    -> IO
        (Provers.PreparedTypedProverTask
            Semantic.SemanticFactOccurrenceFingerprint
            Void
            ()
            Identity.ObjectId)
makePreparedObligation fixture tag = do
    let globalTyping =
            Identity.globalTypingFromClosure
                (fixtureClosure fixture)
    claim <- expectRight
        (Backend.supportedProposition
            (Vector.empty :: Vector.Vector (Void, Core.CoreType))
            (Core.embedClosedCore
                []
                (Identity.checkedPropositionTerm
                    (fixtureProposition fixture))))
    problem <- expectRight
        (Backend.planTypedProblem
            globalTyping
            Vector.empty
            claim
            []
            [Backend.typedFoundationAuxiliaryInput
                (fixtureFoundation fixture)
                tag]
            Backend.CompleteLocals)
    expectRight
        (Provers.prepareTypedProverTask
            Provers.DirectTask
            problem)

acceptedResolver :: FilePath -> Declaration.VampireResolver
acceptedResolver executable =
    Declaration.vampireResolver (resolveAccepted executable)

resolveAccepted
    :: FilePath
    -> Provers.PreparedTypedProverTask
        ref local origin global
    -> IO Provers.VampireResolution
resolveAccepted executable prepared =
    Provers.runPreparedTypedProver
        (Provers.vampire
            executable
            Provers.defaultTimeLimit
            Provers.defaultMemoryLimit)
        prepared

writeAcceptedVampire :: FilePath -> IO ()
writeAcceptedVampire executable = do
    writeFile executable
        (unlines
            [ "#!/bin/sh"
            , "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for typed'"
            ])
    permissions <- Directory.getPermissions executable
    Directory.setPermissions executable
        (Directory.setOwnerExecutable True permissions)

authenticatesPredicateProjections :: Assertion
authenticatesPredicateProjections = do
    fixture <- makeFixture
    let theory = Identity.theoryId (fixtureFoundation fixture)
        object = Identity.transparentObject theory Core.TyProp (Core.CAnd Core.CTruth Core.CFalsum)
        identity = Identity.assertedObjectId object
        predicate = Core.CGlobal identity
        equation = Core.canonicalDefinitionEquationTarget identity Core.TyProp (Core.CAnd Core.CTruth Core.CFalsum)
    closure <- expectRight (Identity.validateObjectClosure theory [object])
    premise <- expectRight (Identity.validatePropositionContent closure predicate)
    equationProposition <- expectRight (Identity.validatePropositionContent closure equation)
    target <- expectRight (Identity.validatePropositionContent closure (Core.CImp predicate Core.CTruth))
    let correct = Authority.CheckedDefinitionProjection identity (Notion.ConjunctionLeft Notion.ConjunctionHere)
        run descriptor relay = runDriver fixture do
            sourceSpec <- Declaration.prepareDefinitionEquationSpecDriver [object] identity (Semantic.semanticName "source")
                >>= either Declaration.failDeclarationDriver pure
            let source = Declaration.checkedCandidate sourceSpec (Declaration.checkedDefinitionEquationPlanning identity)
                intermediate = Declaration.checkedCandidate
                    (Declaration.candidateSpec equationProposition Semantic.SearchIneligible [])
                    (Declaration.checkedNoExternalSourceProofPlanning [Planning.PlannedCandidatePosition 0 0])
                result = Declaration.checkedCandidate (Declaration.candidateSpec target Semantic.SearchIneligible [])
                    (Declaration.checkedStagedKernelPlanning descriptor [Planning.PlannedCandidatePosition (if relay then 1 else 0) 0])
                stages = [source :| []] <> [intermediate :| [] | relay] <> [result :| []]
            DeclTest.admitCompiled (Semantic.declarationSyntaxId "definition-projection") [object] [] stages \reserved -> do
                let (sourceCandidate, intermediateCandidate, resultCandidate) = case reserved of
                        [first :| [], lastCandidate :| []] -> (first, Nothing, lastCandidate)
                        [first :| [], middle :| [], lastCandidate :| []] -> (first, Just middle, lastCandidate)
                        _ -> error "predicate projection fixture shape"
                Declaration.authorizeDefinitionEquationCandidate identity sourceCandidate
                for_ intermediateCandidate \candidate ->
                    Declaration.authorizeKernelProofCandidate candidate
                        (Kernel.importedFactDerivation <$> Declaration.useStagedCandidate sourceCandidate)
                Declaration.authorizeKernelConstructionCandidate descriptor resultCandidate do
                    imported <- Declaration.useStagedCandidate (fromMaybe sourceCandidate intermediateCandidate)
                    pure (Kernel.implicationIntroductionDerivation
                        (Core.embedClosedCore [] (Identity.checkedPropositionTerm premise))
                        (Kernel.conjunctionLeftEliminationDerivation
                            (Kernel.equalityModusPonensDerivation
                                (Kernel.importedFactDerivation imported)
                                (Kernel.localHypothesisDerivation (Kernel.hypothesisIx 0)))))

    run correct False >>= \case
        Declaration.DriverSucceeded{} -> pure ()
        _ -> assertFailure "canonical equation projection failed"
    for_
        [ ("wrong selector", Authority.CheckedDefinitionProjection identity Notion.ConjunctionHere, False)
        , ("wrong object", Authority.CheckedDefinitionProjection
                (Identity.assertedObjectId (opaqueFixtureObject fixture))
                (Notion.ConjunctionLeft Notion.ConjunctionHere), False)
        , ("ordinary theorem with the same equation", correct, True)
        ] \(label, descriptor, relay) -> run descriptor relay >>= \case
            Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed Declaration.KernelConstructionDescriptorMismatch) prefix ->
                assertEqual (label <> " publishes nothing") 0 (length (Commit.pendingModulePrefixBatches prefix))
            _ -> assertFailure (label <> " did not reject the construction descriptor")

admitsImplementationDefinitions :: Assertion
admitsImplementationDefinitions = do
    fixture <- makeNamedFixture "implementation-definition"
    let object = Identity.transparentObject
            (Identity.theoryId (fixtureFoundation fixture)) Core.TySet (Core.CIntrinsic Core.Empty)
        identity = Identity.assertedObjectId object
        run :: Bool -> IO (Declaration.DriverResult Text ((), Commit.CommittedDeclarationBatch))
        run matching = runDriver fixture do
            spec <- if matching
                then Declaration.runProspectiveLoweringDriver
                    (Declaration.prepareDefinitionEquationSpecWithEligibilityLowering
                        [object] identity Semantic.SearchIneligible [])
                        >>= either Declaration.failDeclarationDriver pure
                else pure (factSpec fixture "wrong-equation")
            DeclTest.admitCompiled (Semantic.declarationSyntaxId "implementation-definition") [object] []
                [Declaration.checkedCandidate spec
                    (Declaration.checkedImplementationDefinitionPlanning identity) :| []] \case
                [candidate :| []] -> Declaration.authorizeImplementationDefinitionCandidate identity candidate
                _ -> error "implementation definition fixture shape"
    success <- run True
    case success of
        Declaration.DriverSucceeded (_, batch) _ _ -> do
            assertEqual "implementation equation registers no automatic view" []
                (Semantic.declarationDeltaDefinitionViews (Commit.committedBatchDelta batch))
            assertEqual "implementation equation retains distinct authority"
                [Authority.CheckedKernelConstruction (Authority.CheckedImplementationDefinition identity)]
                (Authority.validationDirectAuthorization <$> Commit.committedBatchValidationCertificates batch)
        Declaration.DriverFailed failure _ -> assertFailure (show failure)
        Declaration.DriverSealFailed failure _ -> assertFailure (show failure)
    failure <- run False
    case failure of
        Declaration.DriverFailed (Declaration.DriverDeclarationFailed Declaration.DefinitionEquationCandidateMismatch) prefix ->
            assertEqual "wrong equation publishes no batch" 0 (length (Commit.pendingModulePrefixBatches prefix))
        _ -> assertFailure "implementation definition did not reject a mismatched equation"

rejectsBrokenGeneratedDependency :: Assertion
rejectsBrokenGeneratedDependency = do
    fixture <- makeFixture
    source <- foundationProposition fixture Foundation.EmptyCharacteristic
    target <- foundationProposition fixture Foundation.PairSetCharacteristic
    let descriptor = Authority.CheckedDerivedConstruction
        candidate proposition references = Declaration.checkedCandidate
            (Declaration.candidateSpec proposition Semantic.SearchIneligible [])
            (Declaration.checkedStagedKernelPlanning descriptor references)
    result <- runDriver fixture
        (DeclTest.admitCompiled (Semantic.declarationSyntaxId "broken-generated-dependency") [] []
            [candidate source [] :| [], candidate target [Planning.PlannedCandidatePosition 0 0] :| []] \case
                [first :| [], second :| []] -> do
                    Declaration.authorizeKernelConstructionCandidate descriptor first
                        (pure (Kernel.foundationFactDerivation Foundation.EmptyCharacteristic))
                    Declaration.authorizeKernelConstructionCandidate descriptor second
                        (Kernel.importedFactDerivation <$> Declaration.useStagedCandidate first)
                _ -> error "generated dependency fixture shape")
    case result of
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed Declaration.KernelCompletionFailed{}) prefix ->
            assertBool "failed replay publishes none of the earlier support stage"
                (null (Commit.pendingModulePrefixBatches prefix))
        _ -> assertFailure "broken generated dependency was not rejected by kernel replay"

validatesKernelConstructionDescriptors :: Assertion
validatesKernelConstructionDescriptors = do
    fixture <- makeFixture
    proposition <- foundationProposition
        fixture
        Foundation.EmptyCharacteristic
    let declaredObject = opaqueFixtureObject fixture
        run descriptor = runDriver fixture
            (DeclTest.admitCompiled (Semantic.declarationSyntaxId "kernel-construction-descriptor") [declaredObject] []
                [Declaration.checkedCandidate
                    (Declaration.candidateSpec proposition Semantic.SearchEligible [Semantic.semanticName "kernel-construction"])
                    (Declaration.checkedKernelPlanning descriptor []) :| []] \case
                    [candidate :| []] -> Declaration.authorizeKernelConstructionCandidate descriptor candidate
                        (pure (Kernel.foundationFactDerivation Foundation.EmptyCharacteristic))
                    _ -> error "kernel construction fixture shape")

    success <- run
        (Authority.FoundationLeaf
            Foundation.EmptyCharacteristic)
    derived <- run Authority.CheckedDerivedConstruction
    case derived of
        Declaration.DriverSucceeded (_, batch) _ _ ->
            assertEqual "ordinary generated proof retains replayed authority"
                [Authority.CheckedKernelConstruction Authority.CheckedDerivedConstruction]
                (Authority.validationDirectAuthorization <$> Commit.committedBatchValidationCertificates batch)
        _ -> assertFailure "ordinary generated proof failed"
    case success of
        Declaration.DriverSucceeded (_value, batch) _interface _prefix -> do
            assertEqual
                "new object is included in the checked declaration batch"
                1
                (length (Commit.committedBatchObjects batch))
            case Commit.committedBatchDeclarationValidation batch of
                Just record ->
                    case Semantic.declarationValidationRecordCertificates
                            record of
                        [certificate] ->
                            assertEqual
                                "exact kernel descriptor is retained"
                                (Authority.CheckedKernelConstruction
                                    (Authority.FoundationLeaf
                                        Foundation.EmptyCharacteristic))
                                (Authority.validationDirectAuthorization
                                    certificate)
                        certificates ->
                            assertFailure
                                ("unexpected kernel certificate count: "
                                    <> show (length certificates))
                Nothing ->
                    assertFailure "missing declaration validation"
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed failure) _prefix ->
            assertFailure
                ("valid kernel descriptor failed: " <> show failure)
        Declaration.DriverFailed
                (Declaration.DriverActionFailed _failure) _prefix ->
            assertFailure "unexpected ordinary driver failure"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure (show failure)

    traverse_
        (\(label, descriptor) -> do
            outcome <- run descriptor
            case outcome of
                Declaration.DriverFailed
                        (Declaration.DriverDeclarationFailed
                            Declaration.KernelConstructionDescriptorMismatch)
                        prefix ->
                    assertEqual
                        (label <> " publishes no declaration")
                        0
                        (length
                            (Commit.pendingModulePrefixBatches prefix))
                Declaration.DriverFailed
                        (Declaration.DriverDeclarationFailed other)
                        _prefix ->
                    assertFailure
                        (label <> ": unexpected error " <> show other)
                Declaration.DriverFailed
                        (Declaration.DriverActionFailed _failure)
                        _prefix ->
                    assertFailure (label <> ": ordinary driver failure")
                Declaration.DriverSucceeded{} ->
                    assertFailure (label <> ": mismatch was accepted")
                Declaration.DriverSealFailed{} ->
                    assertFailure (label <> ": mismatch reached sealing"))
        [ ( "wrong foundation leaf"
          , Authority.FoundationLeaf
                Foundation.PairSetCharacteristic
          )
        , ( "wrong construction family"
          , Authority.GuardedFoundationRules
                (Authority.guardedRuleSet
                    (Foundation.SetLfpBound :| []))
          )
        ]

rejectsHiddenScopedKernelAuthority :: Assertion
rejectsHiddenScopedKernelAuthority = do
    fixture <- makeFixture
    foundationProposition' <- foundationProposition
        fixture
        Foundation.EmptyCharacteristic
    let foundationTarget =
            Core.embedClosedCore []
                (Identity.checkedPropositionTerm foundationProposition')
    for_ [Declaration.KernelImplicitObvious, Declaration.KernelDefinition Set.empty, Declaration.KernelStructuralComposition] \policy ->
        expectPolicyFailure
            "foundation leaf"
            Declaration.KernelDischargeFoundationUse
            =<< runPolicyCandidate
                policy fixture
                "scoped-foundation-leaf"
                foundationProposition'
                foundationTarget
                (Kernel.foundationFactDerivation
                    Foundation.EmptyCharacteristic)

    for_ [Foundation.DoubleNegationElim, Foundation.PropositionalExtensionality] \tag -> do
        proposition <- foundationProposition fixture tag
        let target = Core.embedClosedCore [] (Identity.checkedPropositionTerm proposition)
            derivation = Kernel.foundationFactDerivation tag
        for_ [Declaration.KernelImplicitObvious, Declaration.KernelCitedObvious Set.empty] \policy -> do
            outcome <- runPolicyCandidate policy fixture "scoped-logical-foundation" proposition target derivation
                :: IO (Declaration.DriverResult Void ((), Commit.CommittedDeclarationBatch))
            case outcome of
                Declaration.DriverSucceeded{} -> pure ()
                Declaration.DriverFailed failure _prefix ->
                    assertFailure ("confined logical foundation was rejected: " <> show (tag, failure))
                Declaration.DriverSealFailed failure _prefix ->
                    assertFailure ("confined logical foundation reached sealing: " <> show (tag, failure))
        expectPolicyFailure "foundation is not definition use" Declaration.KernelDefinitionEvidenceMissing
            =<< runPolicyCandidate (Declaration.KernelDefinition Set.empty) fixture
                "scoped-logical-foundation-definition" proposition target derivation

    let fixtureTyping =
            Identity.globalTypingFromClosure (fixtureClosure fixture)
    domain <- expectRight
        (Core.checkScopedCanonicalCore
            fixtureTyping
            []
            (Core.CIntrinsic Core.Empty))
    operator <- expectRight
        (Core.checkScopedCanonicalCore
            fixtureTyping
            []
            (Core.CLam Core.TySet (Core.CBound 0)))
    guardedTarget <- expectRight
        (KernelSetLfp.setLfpBound
            (fixtureFoundation fixture)
            fixtureTyping
            domain
            operator)
    guardedProposition <- checkedClosedProposition fixture guardedTarget
    for_ [Declaration.KernelImplicitObvious, Declaration.KernelDefinition Set.empty, Declaration.KernelStructuralComposition] \policy ->
        expectPolicyFailure
            "guarded Set-LFP rule"
            Declaration.KernelDischargeGuardedRuleUse
            =<< runPolicyCandidate
                policy fixture
                "scoped-guarded-rule"
                guardedProposition
                guardedTarget
                (Kernel.setLfpBoundDerivation domain operator)
  where
    runPolicyCandidate policy fixture syntax proposition target derivation =
        runDriver fixture
            (DeclTest.admitProof
                (Semantic.proofSyntaxId
                    (TextEncoding.encodeUtf8 syntax)) []
                    (Declaration.checkedCandidate (Declaration.candidateSpec
                            proposition
                            Semantic.SearchEligible
                            [Semantic.semanticName syntax])
                        (Declaration.checkedNoExternalSourceProofPlanning [])) \candidate -> do
                    Declaration.authorizeKernelProofCandidate
                        candidate do
                            void
                                (Declaration.acceptScopedKernelDischarge
                                    policy
                                    []
                                    Vector.empty
                                    target
                                    derivation)
                            pure derivation)

    expectPolicyFailure label expected = \case
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed actual) prefix -> do
            assertEqual label expected actual
            assertEqual
                (label <> " publishes no declaration")
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Declaration.DriverFailed
                (Declaration.DriverActionFailed _failure) _prefix ->
            assertFailure (label <> ": unexpected ordinary driver failure")
        Declaration.DriverSucceeded{} ->
            assertFailure (label <> ": hidden authority was accepted")
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure (label <> ": reached sealing: " <> show failure)

    checkedClosedProposition fixture scoped = do
        frozen <- maybe
            (assertFailure "guarded target remained open" >> fail "unreachable")
            pure
            (Core.closeScopedCore scoped)
        closure <- expectRight
            (Identity.validateObjectClosure
                (Identity.theoryId (fixtureFoundation fixture))
                [])
        expectRight
            (Identity.validatePropositionContent
                closure
                (Core.frozenCoreTerm frozen))

restrictsSetExtensionalityImportsToPointwiseViews :: Assertion
restrictsSetExtensionalityImportsToPointwiseViews = do
    traverse_ runCase
        [ ("pointwise definition", PointwisePolicyFact, Nothing)
        , ( "exact definition"
          , ExactPolicyFact
          , Just Declaration.KernelExtensionalityImportMismatch
          )
        , ( "ordinary fact"
          , OrdinaryPolicyFact
          , Just Declaration.KernelExtensionalityImportMismatch
          )
        ]
  where
    runCase (label, kind, expectedFailure) = do
        fixture <- makeNamedFixture
            (Text.pack ("setext-policy-" <> label))
        let foundation = fixtureFoundation fixture
            theory = Identity.theoryId foundation
            maybeObject = policyObject theory kind
            closure =
                expectRight
                    (Identity.validateObjectClosure theory (toList maybeObject))
        checkedClosure <- closure
        outcome <-
            (runDriver fixture do
                (fingerprint, proposition) <-
                    publishPolicyFact fixture kind maybeObject
                let target = Core.embedClosedCore []
                        (Identity.checkedPropositionTerm proposition)
                    hypothesis = policyDirection checkedClosure
                    derivation =
                        either
                            (error
                                . ("invalid set-extensionality policy proof: " <>)
                                . show)
                            KernelProof.builtProofDerivation
                            (policyProof
                                foundation checkedClosure proposition hypothesis)
                DeclTest.admitProof
                    (Semantic.proofSyntaxId
                        (TextEncoding.encodeUtf8
                            (Text.pack (label <> "-use")))) []
                        (Declaration.checkedCandidate (Declaration.candidateSpec
                                proposition
                                Semantic.SearchEligible
                                [])
                            (Declaration.checkedNoExternalSourceProofPlanningWithFacts [fingerprint] [])) \candidate -> do
                        Declaration.authorizeKernelProofCandidate
                            candidate do
                                void
                                    (Declaration.acceptScopedKernelDischarge
                                        (Declaration.KernelSetExtensionality
                                            (Set.singleton
                                                (Kernel.hypothesisIx 0)))
                                        [fingerprint]
                                        (Vector.singleton hypothesis)
                                        target
                                        derivation)
                                premise <-
                                    Declaration.useAuthorizedFact fingerprint
                                pure (Kernel.importedFactDerivation premise)
                :: IO
                    (Declaration.DriverResult
                        Void
                        ((), Commit.CommittedDeclarationBatch)))
        case (expectedFailure, outcome) of
            (Nothing, Declaration.DriverSucceeded{}) -> pure ()
            (Just expected,
                Declaration.DriverFailed
                    (Declaration.DriverDeclarationFailed actual) prefix) -> do
                assertEqual label expected actual
                assertEqual
                    (label <> " retains only its premise declaration")
                    1
                    (length (Commit.pendingModulePrefixBatches prefix))
            (Nothing, Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed failure) _prefix) ->
                assertFailure
                    (label <> ": pointwise import was rejected: "
                        <> show failure)
            (Just _expected, Declaration.DriverSucceeded{}) ->
                assertFailure (label <> ": non-pointwise import was accepted")
            (_expected, Declaration.DriverSealFailed failure _prefix) ->
                assertFailure (label <> ": reached sealing: " <> show failure)

    publishPolicyFact fixture kind maybeObject =
        case (kind, toList maybeObject) of
            (OrdinaryPolicyFact, []) -> do
                (_value, batch) <-
                    DeclTest.admitProof
                        (Semantic.proofSyntaxId "ordinary-setext-policy-fact") []
                            (Declaration.checkedCandidate (factSpec fixture "ordinary-setext-policy-fact") Declaration.checkedSourceAxiomPlanning) \candidate -> do
                            Declaration.authorizeSourceAxiomCandidate candidate
                pure (singleBatchFact batch)
            (_, [object]) -> do
                let identity = Identity.assertedObjectId object
                spec <- Declaration.prepareDefinitionEquationSpecDriver [object] identity
                    (Semantic.semanticName "definition-setext-policy-fact") >>= either Declaration.failDeclarationDriver pure
                (_value, batch) <- DeclTest.admitCompiled (Semantic.declarationSyntaxId "definition-setext-policy-fact") [object] []
                    [Declaration.checkedCandidate spec (Declaration.checkedDefinitionEquationPlanning identity) :| []] \case
                    [candidate :| []] -> Declaration.authorizeDefinitionEquationCandidate identity candidate
                    _ -> error "set extensionality definition fixture shape"

                pure (singleBatchFact batch)
            _ -> error "invalid set-extensionality policy fixture"

    singleBatchFact batch =
        case ( Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta batch)
             , Commit.committedBatchPropositions batch
             ) of
            ([fact], [proposition]) ->
                (Semantic.semanticFactFingerprint fact, proposition)
            inventory ->
                error
                    ("unexpected set-extensionality policy inventory: "
                        <> show
                            ( length (fst inventory)
                            , length (snd inventory)
                            ))

    policyObject theory = \case
        PointwisePolicyFact ->
            Just
                (Identity.transparentObject theory
                    (Core.TyArrow Core.TySet Core.TyProp)
                    (Core.CLam Core.TySet
                        (Core.CEq Core.TySet
                            (Core.CBound 0)
                            (Core.CBound 0))))
        ExactPolicyFact ->
            Just
                (Identity.transparentObject theory
                    (Core.TyArrow
                        (Core.TyArrow Core.TySet Core.TySet)
                        Core.TyProp)
                    (Core.CLam
                        (Core.TyArrow Core.TySet Core.TySet)
                        Core.CTruth))
        OrdinaryPolicyFact -> Nothing

    policyDirection closure =
        either
            (error . ("invalid set-extensionality policy hypothesis: " <>)
                . show)
            id
            (Core.checkScopedCanonicalCore
                (Identity.globalTypingFromClosure closure)
                []
                (Core.CForall Core.TySet
                    (Core.CImp
                        (member (Core.CBound 0) (Core.CIntrinsic Core.Empty))
                        (member (Core.CBound 0) (Core.CIntrinsic Core.Empty)))))

    policyProof foundation closure proposition hypothesis = do
        let globalType = Identity.globalTypingFromClosure closure
            importedTerm = Core.frozenCoreTerm
                (Identity.checkedPropositionTerm proposition)
        context <-
            KernelProof.scopedProofContext
                foundation globalType [] [hypothesis]
        emptySet <- KernelProof.scopedTerm context (Core.CIntrinsic Core.Empty)
        direction <-
            KernelProof.indexedHypothesisProof context (Kernel.hypothesisIx 0)
        extensionality <-
            KernelProof.foundationInstanceProof
                context Foundation.SetExtensionality [emptySet, emptySet]
        afterLeft <-
            KernelProof.implicationEliminationProof
                context extensionality direction
        setEquality <-
            KernelProof.implicationEliminationProof
                context afterLeft direction
        constantPredicate <-
            KernelProof.scopedTerm context
                (Core.CLam Core.TySet importedTerm)
        predicateReflexivity <-
            KernelProof.equalityReflexivityProof context constantPredicate
        propositionReflexivity <-
            KernelProof.equalityCongruenceApplicationProof
                context predicateReflexivity setEquality
        expectedReflexivity <-
            KernelProof.scopedTerm context
                (Core.CEq Core.TyProp importedTerm importedTerm)
        convertedReflexivity <-
            KernelProof.conversionProof
                context propositionReflexivity expectedReflexivity
        imported <-
            KernelProof.importedProof
                context (Kernel.importIx 0)
                (Identity.checkedPropositionTerm proposition)
        KernelProof.equalityModusPonensProof
            context convertedReflexivity imported

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

data SetExtensionalityPolicyFact
    = PointwisePolicyFact
    | ExactPolicyFact
    | OrdinaryPolicyFact

reusesCompiledDeclarationValidation :: Assertion
reusesCompiledDeclarationValidation = do
    fixture <- makeFixture
    proposition <- foundationProposition
        fixture
        Foundation.EmptyCharacteristic
    let declaredObject = opaqueFixtureObject fixture
        syntax =
            Semantic.declarationSyntaxId
                "cached-kernel-construction"
        action derivationTag =
            let descriptor = Authority.FoundationLeaf Foundation.EmptyCharacteristic
            in DeclTest.admitCompiled syntax [declaredObject] []
                [Declaration.checkedCandidate
                    (Declaration.candidateSpec proposition Semantic.SearchEligible [Semantic.semanticName "cached-kernel-construction"])
                    (Declaration.checkedKernelPlanning descriptor []) :| []] \case
                    [candidate :| []] -> Declaration.authorizeKernelConstructionCandidate descriptor candidate
                        (pure (Kernel.foundationFactDerivation derivationTag))
                    _ -> error "cached kernel construction fixture shape"

    freshBatch <- runSuccessful fixture
        (snd <$> action Foundation.EmptyCharacteristic)
    freshRecord <-
        case Commit.committedBatchDeclarationValidation freshBatch of
            Just record -> pure record
            Nothing ->
                assertFailure "fresh compiled declaration omitted validation"
                    >> fail "unreachable"

    missLookups <- IORef.newIORef (0 :: Int)
    missBatch <- runSuccessfulWithValidation fixture
        (compiledOnlyValidationHandlers \_key -> do
            IORef.modifyIORef' missLookups (+ 1)
            pure Nothing)
        (snd <$> action Foundation.EmptyCharacteristic)
    assertEqual "compiled warm miss performs one exact lookup"
        1
        =<< IORef.readIORef missLookups
    assertBool "compiled miss publishes fresh validation"
        (isJust
            (Commit.committedBatchDeclarationValidation missBatch))

    hitLookups <- IORef.newIORef []
    hitBatch <- runSuccessfulWithValidation fixture
        (compiledOnlyValidationHandlers \key -> do
            IORef.modifyIORef' hitLookups (key :)
            pure (Just freshRecord))
        (snd <$> action Foundation.PairSetCharacteristic)
    assertEqual "compiled warm hit performs one exact lookup"
        [Semantic.declarationValidationRecordKey freshRecord]
        . reverse
        =<< IORef.readIORef hitLookups
    case Commit.committedBatchDeclarationValidation hitBatch of
        Just record ->
            assertEqual
                "compiled hit republishes the exact validation"
                freshRecord
                record
        Nothing ->
            assertFailure "compiled hit omitted validation"

foundationProposition
    :: Fixture
    -> Foundation.FoundationAxiomTag
    -> IO Identity.CheckedPropositionContent
foundationProposition fixture tag = do
    closure <- expectRight
        (Identity.validateObjectClosure
            (Identity.theoryId (fixtureFoundation fixture))
            [])
    expectRight
        (Identity.validatePropositionContent
            closure
            (Core.frozenCoreTerm
                (Core.eliminateFrozenVoid
                    (Foundation.foundationAxiomFrozen
                        (fixtureFoundation fixture)
                        tag))))

opaqueFixtureObject :: Fixture -> Identity.AssertedObject
opaqueFixtureObject fixture =
    let theory = Identity.theoryId (fixtureFoundation fixture)
        seed =
            Identity.opaqueDeclarationSeed
                (fixtureOwner fixture)
                (localDeclarationOrdinal 0)
                SignatureDeclaration
                (generatedObjectSlot 0)
    in Identity.opaqueObject theory seed Core.TySet

data Fixture = Fixture
    { fixtureFoundation :: !Foundation.CheckedFoundation
    , fixtureOwner :: !ModuleName
    , fixtureProposition :: !Identity.CheckedPropositionContent
    , fixtureClosure :: !Identity.CheckedObjectClosure
    }

makeFixture :: IO Fixture
makeFixture =
    makeNamedFixture "root"

makeNamedFixture :: Text -> IO Fixture
makeNamedFixture name = do
    foundation <- expectRight Foundation.checkedFoundation
    let namespaceDigest =
            hashBlake2b256
                ("declaration-test-namespace\NUL"
                    <> TextEncoding.encodeUtf8 name)
    relative <- expectRight
        (safeRelativePath
            (Text.unpack name <> ".tex"))
    let theory = Identity.theoryId foundation
        owner =
            moduleNameFromParts
                (sourceNamespaceIdFromDigest namespaceDigest)
                relative
    closure <- expectRight
        (Identity.validateObjectClosure theory [])
    proposition <- expectRight
        (Identity.validatePropositionContent closure Core.CFalsum)
    pure
        Fixture
            { fixtureFoundation = foundation
            , fixtureOwner = owner
            , fixtureProposition = proposition
            , fixtureClosure = closure
            }

factSpec :: Fixture -> Text -> Declaration.CandidateSpec
factSpec fixture alias =
    Declaration.candidateSpec
        (fixtureProposition fixture)
        Semantic.SearchEligible
        [Semantic.semanticName alias]

runDriver
    :: Fixture
    -> Declaration.ModuleDriver failure value
    -> IO (Declaration.DriverResult failure value)
runDriver fixture =
    runDriverWithResolver fixture unavailableVampireResolver

runDriverWithResolver
    :: Fixture
    -> Declaration.VampireResolver
    -> Declaration.ModuleDriver failure value
    -> IO (Declaration.DriverResult failure value)
runDriverWithResolver fixture resolver action = do
    imports <- prepareTestImports (Identity.theoryId (fixtureFoundation fixture)) []
    result <- Declaration.runModuleDriverFreshIO
        (fixtureFoundation fixture)
        (fixtureOwner fixture)
        imports
        resolver
        action
    expectRight result

runDriverWithValidation
    :: Fixture
    -> ValidationHandlers
    -> Declaration.ModuleDriver failure value
    -> IO (Declaration.DriverResult failure value)
runDriverWithValidation fixture lookup action = do
    runDriverWithValidationAndResolver
        fixture
        lookup
        unavailableVampireResolver
        action

runDriverWithValidationAndResolver
    :: Fixture
    -> ValidationHandlers
    -> Declaration.VampireResolver
    -> Declaration.ModuleDriver failure value
    -> IO (Declaration.DriverResult failure value)
runDriverWithValidationAndResolver fixture lookup resolver action = do
    imports <- prepareTestImports (Identity.theoryId (fixtureFoundation fixture)) []
    result <- runEff
        (runValidationHandlers lookup
            (Declaration.runModuleDriverEff
                (fixtureFoundation fixture)
                (fixtureOwner fixture)
                imports
                resolver
                action))
    expectRight result

data ValidationHandlers = ValidationHandlers
    !(Semantic.ProofValidationKey
        -> IO (Maybe Semantic.ProofValidationRecord))
    !(Semantic.DeclarationValidationKey
        -> IO (Maybe Semantic.DeclarationValidationRecord))

runValidationHandlers
    :: IOE :> es
    => ValidationHandlers
    -> Eff (ValidationCache.ValidationCache : es) value
    -> Eff es value
runValidationHandlers (ValidationHandlers lookupProof lookupDeclaration) =
    ValidationCache.runValidationCacheWith
        (liftIO . lookupProof)
        (liftIO . lookupDeclaration)

proofOnlyValidationHandlers
    :: (Semantic.ProofValidationKey
        -> IO (Maybe Semantic.ProofValidationRecord))
    -> ValidationHandlers
proofOnlyValidationHandlers lookupProof =
    ValidationHandlers
        lookupProof
        (const (pure Nothing))

compiledOnlyValidationHandlers
    :: (Semantic.DeclarationValidationKey
        -> IO (Maybe Semantic.DeclarationValidationRecord))
    -> ValidationHandlers
compiledOnlyValidationHandlers lookupDeclaration =
    ValidationHandlers
        (const (pure Nothing))
        lookupDeclaration

runDriverWithDirect
    :: Fixture
    -> [Declaration.ImportedModuleEvidence]
    -> Declaration.ModuleDriver failure value
    -> IO (Declaration.DriverResult failure value)
runDriverWithDirect fixture direct action = do
    imports <- prepareTestImports (Identity.theoryId (fixtureFoundation fixture)) direct
    result <- Declaration.runModuleDriverFreshIO
        (fixtureFoundation fixture)
        (fixtureOwner fixture)
        imports
        unavailableVampireResolver
        action
    expectRight result

unavailableVampireResolver :: Declaration.VampireResolver
unavailableVampireResolver =
    Declaration.vampireResolver \prepared ->
        pure
            (Provers.processFailedVampireResolution
                (Provers.preparedTypedProverRequest prepared)
                (Provers.ProverLaunchFailed
                    "unused"
                    "Vampire resolver was not expected"))

runSuccessful
    :: Fixture
    -> Declaration.ModuleDriver failure value
    -> IO value
runSuccessful fixture =
    runSuccessfulWithResolver fixture unavailableVampireResolver

runSuccessfulWithResolver
    :: Fixture
    -> Declaration.VampireResolver
    -> Declaration.ModuleDriver failure value
    -> IO value
runSuccessfulWithResolver fixture resolver action = do
    outcome <- runDriverWithResolver fixture resolver action
    case outcome of
        Declaration.DriverSucceeded value _interface _prefix ->
            pure value
        Declaration.DriverFailed _failure _prefix ->
            assertFailure "unexpected driver failure" >> fail "unreachable"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure (show failure) >> fail "unreachable"

runSuccessfulWithValidation
    :: Fixture
    -> ValidationHandlers
    -> Declaration.ModuleDriver failure value
    -> IO value
runSuccessfulWithValidation fixture lookup action = do
    outcome <- runDriverWithValidation fixture lookup action
    case outcome of
        Declaration.DriverSucceeded value _interface _prefix ->
            pure value
        Declaration.DriverFailed _failure _prefix ->
            assertFailure "unexpected driver failure" >> fail "unreachable"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure (show failure) >> fail "unreachable"

materializesSealedImport :: Assertion
materializesSealedImport = do
    fixture <- makeFixture
    producer <- runDriver fixture do
        (_value, batch) <- DeclTest.admitProof
            (Semantic.proofSyntaxId "sealed-import-producer") []
                (Declaration.checkedCandidate (factSpec fixture "producer-fact")
                    (Declaration.checkedOmittedPlanning [] [] [])) \candidate -> do
                Declaration.authorizeOmittedCandidate candidate
                    Declaration.recordOmittedUse
        pure batch
    (_producerInterface, evidence, fingerprint) <-
        case producer of
            Declaration.DriverSucceeded _ imported _prefix ->
                let interface = Declaration.evidenceInterface imported
                in case concatMap
                        Semantic.declarationDeltaFacts
                        (Semantic.semanticInterfaceDeclarations interface) of
                    [occurrence] ->
                        pure
                            ( interface
                            , imported
                            , Semantic.semanticFactFingerprint occurrence
                            )
                    occurrences ->
                        assertFailure
                            ("unexpected producer facts: "
                                <> show (length occurrences))
                            >> fail "unreachable"
            Declaration.DriverFailed failure _prefix ->
                assertFailure
                    ("producer failed: "
                        <> show
                            (failure
                                :: Declaration.DriverFailure
                                    Declaration.DeclarationError))
                    >> fail "unreachable"
            Declaration.DriverSealFailed failure _prefix ->
                assertFailure ("producer did not seal: " <> show failure)
                    >> fail "unreachable"
    let consumerNamespace =
            hashBlake2b256 "declaration-import-consumer\NULconsumer"
    consumerPath <- expectRight (safeRelativePath "consumer.tex")
    let consumerFixture =
            fixture
                { fixtureOwner =
                    moduleNameFromParts
                        (sourceNamespaceIdFromDigest consumerNamespace)
                        consumerPath
                }
    consumer <- runDriverWithDirect consumerFixture
        [evidence]
        do
            (_value, committed) <- DeclTest.admitProof
                (Semantic.proofSyntaxId "sealed-import-consumer") []
                    (Declaration.checkedCandidate (factSpec fixture "consumer-fact")
                        (Declaration.checkedOmittedPlanning [] [fingerprint] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate do
                        _ <- Declaration.useAuthorizedFact fingerprint
                        Declaration.recordOmittedUse
            pure committed
    case consumer of
        Declaration.DriverSucceeded committed _ _ -> do
            case Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta committed) of
                [localOccurrence] -> do
                    assertEqual
                        "the first local fact keeps ordinal zero"
                        (localFactOrdinal 0)
                        (Semantic.factSlotOrdinal
                            (Semantic.semanticFactSlot localOccurrence))
                    assertEqual
                        "the local fact belongs to the consumer"
                        (fixtureOwner consumerFixture)
                        (Semantic.factSlotModule
                            (Semantic.semanticFactSlot localOccurrence))
                facts ->
                    assertFailure
                        ("unexpected consumer fact count: "
                            <> show (length facts))
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("consumer failed: "
                    <> show
                        (failure
                            :: Declaration.DriverFailure
                                Declaration.DeclarationError))
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("consumer did not seal: " <> show failure)

doesNotPromoteImportedTheoremShapedDefinitions :: Assertion
doesNotPromoteImportedTheoremShapedDefinitions = do
    producerFixture <- makeNamedFixture "definition-shaped-producer"
    consumerFixture <- makeNamedFixture "definition-shaped-consumer"
    let theory = Identity.theoryId (fixtureFoundation producerFixture)
        body = Core.CIntrinsic Core.Empty
        asserted = Identity.transparentObject theory Core.TySet body
        object = Identity.assertedObjectId asserted
    closure <- expectRight
        (Identity.validateObjectClosure theory [asserted])
    proposition <- expectRight
        (Identity.validatePropositionContent
            closure
            (Declaration.definitionEquationTarget
                object Core.TySet body))
    (batch, freshProducer) <- sealFixture producerFixture [] do
        (_value, committed) <- DeclTest.admitProof (Semantic.proofSyntaxId "ordinary-definition-shape") [asserted]
            (Declaration.checkedCandidate
                (Declaration.candidateSpec proposition Semantic.SearchEligible [Semantic.semanticName "ordinary-definition-shape"])
                Declaration.checkedSourceAxiomPlanning) \candidate ->
                Declaration.authorizeSourceAxiomCandidate candidate
        pure committed
    let FixtureSealed interface _freshEvidence = freshProducer
        certificates = Commit.committedBatchValidationCertificates batch
    cachedEvidence <- expectRightIO
        (admitTestModule
            theory
            []
            interface
            (Commit.committedBatchObjects batch)
            (Commit.committedBatchPropositions batch)
            certificates)
    let cachedProducer = FixtureSealed interface cachedEvidence
        assertNoView label producer = do
            outcome <- runFixtureDriver consumerFixture [producer]
                (Declaration.runProspectiveLoweringDriver
                    (Declaration.resolveVisibleDefinitionViewsLowering object))
            case outcome of
                Declaration.DriverSucceeded views _interface _prefix ->
                    assertBool label (null views)
                Declaration.DriverFailed failure _prefix ->
                    assertFailure (label <> ": import failed: " <> show failure)
                Declaration.DriverSealFailed failure _prefix ->
                    assertFailure
                        (label <> ": import did not seal: " <> show failure)
    assertNoView "fresh imported theorem" freshProducer
    assertNoView "cached imported theorem" cachedProducer

retainsExactSourceProviderOwnership :: Assertion
retainsExactSourceProviderOwnership = do
    fixture <- makeNamedFixture "source-provider-ownership"
    let theory = Identity.theoryId (fixtureFoundation fixture)
        x = Raw.NamedVar "x"
        y = Raw.NamedVar "y"
        makeSymbol command marker =
            Raw.mkMixfixItem
                [Just (Raw.Command command), Nothing]
                (Raw.Marker marker)
                Raw.NonAssoc
        firstSymbol = makeSymbol "providerone" "provider-one"
        secondSymbol = makeSymbol "providertwo" "provider-two"
        key symbol =
            Semantic.SemanticExpressionFunction (Raw.mixfixPattern symbol)
        providerObject = Identity.transparentObject
            theory
            (Core.TyArrow Core.TySet Core.TySet)
            (Core.CLam Core.TySet (Core.CBound 0))
        publish addObject ordinal symbol =
            DeclTest.admitCompiled
                (Semantic.declarationSyntaxId
                    ("source-provider-" <> TextEncoding.encodeUtf8 (Text.pack (show ordinal))))
                [providerObject | addObject]
                [Semantic.semanticGlobalBinding
                    (key symbol)
                    (Semantic.semanticBindingLabel ("source-provider-" <> Text.pack (show ordinal)))
                    (Semantic.GlobalReference (Identity.assertedObjectId providerObject))]
                [] (const (pure ()))
        membership symbol =
            Raw.StmtNoun Raw.Positive
                (Raw.TermExpr
                    (Raw.ExprOp Nowhere symbol [Raw.ExprVar x]) :| [])
                (Raw.NounPhrase
                    []
                    (Raw.Noun
                        Nowhere
                        Lexicon.builtinElementNoun
                        [Raw.TermExpr (Raw.ExprVar y)])
                    (Raw.unboundedNounBinder Nothing)
                    []
                    Nothing)
    context <- expectRight
        (Elaboration.extendElaborationContext
            ( (Elaboration.localId 0, x)
            :| [(Elaboration.localId 1, y)]
            )
            Elaboration.emptyElaborationContext)
    let action
            :: Declaration.ModuleDriver Text
                [ Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                ]
        action = do
            void (publish True (0 :: Natural) firstSymbol)
            void (publish False 1 secondSymbol)
            Declaration.runProspectiveLoweringDriver
                (traverse
                    (Elaboration.elaborateProposition context . membership)
                    [firstSymbol, secondSymbol])
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded results _interface _prefix -> do
            occurrences <- for results \case
                Left failure ->
                    assertFailure
                        ("source provider failed to elaborate: "
                            <> Text.unpack
                                (Elaboration.renderElaborationError failure))
                        >> fail "unreachable"
                Right proposition ->
                    case Elaboration.elaboratedPropositionAssertions proposition of
                        [assertion] ->
                            case Notion.sourceAssertionAtom assertion of
                                Semantic.MembershipAtomTemplate element _set -> pure element
                                _ -> fail "provider test did not produce a membership atom"
                        _ ->
                            assertFailure
                                "provider membership did not retain one source atom"
                                >> fail "unreachable"
            heads <- for occurrences \occurrence ->
                case SourceTerm.sourceTermOccurrenceProvider occurrence of
                    Nothing ->
                        assertFailure "eligible source provider was erased"
                            >> fail "unreachable"
                    Just provider ->
                        pure (SourceTerm.sourceTermProviderHead provider)
            let owner = fixtureOwner fixture
                reference ordinal symbol = Semantic.globalBindingRef
                    (Semantic.declarationSlot
                        owner (localDeclarationOrdinal ordinal))
                    (key symbol)
            assertEqual "equal-body providers retain distinct owners"
                [ Semantic.GlobalSourceProvider (reference 0 firstSymbol)
                , Semantic.GlobalSourceProvider (reference 1 secondSymbol)
                ]
                heads
            assertEqual "named equal-body providers may share Core"
                1
                (length
                    (nubOrd
                        ( Core.scopedCoreTerm
                            . SourceTerm.sourceTermOccurrenceCore
                            <$> occurrences
                        )))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("source-provider driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("source-provider driver did not seal: " <> show failure)

retainsWhitelistedFixedIntrinsicProviders :: Assertion
retainsWhitelistedFixedIntrinsicProviders = do
    fixture <- makeNamedFixture "fixed-intrinsic-providers"
    let x = Raw.NamedVar "x"
        symbol command =
            Raw.mkMixfixItem
                [ Just (Raw.Command command)
                , Just Raw.InvisibleBraceL
                , Nothing
                , Just Raw.InvisibleBraceR
                ]
                (Raw.Marker (command <> "-provider"))
                Raw.NonAssoc
        expression command =
            Raw.TypedExpressionExpr
                (Raw.ExprOp Nowhere (symbol command) [Raw.ExprVar x])
    context <- expectRight
        (Elaboration.extendElaborationContext
            ((Elaboration.localId 0, x) :| [])
            Elaboration.emptyElaborationContext)
    let action
            :: Declaration.ModuleDriver Text
                [Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedExpression]
        action = Declaration.runProspectiveLoweringDriver
            (traverse
                (Elaboration.elaborateExpression context)
                (fmap expression ["pow", "choice", "cumul"] <>
                    [ Raw.TypedExpressionExpr (Raw.ExprNaturalNumeral Nowhere 0)
                    , Raw.TypedExpressionExpr (Raw.ExprOp Nowhere
                        (Raw.mkMixfixItem [Just (Raw.Command "emptyset")]
                            (Raw.Marker "emptyset-provider") Raw.NonAssoc) [])
                    ]))
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded results _interface _prefix -> do
            sources <- for results \case
                Left failure ->
                    assertFailure
                        ("fixed provider failed to elaborate: "
                            <> Text.unpack
                                (Elaboration.renderElaborationError failure))
                        >> fail "unreachable"
                Right elaborated ->
                    maybe
                        (assertFailure "fixed set expression lost its source term"
                            >> fail "unreachable")
                        pure
                        (Elaboration.elaboratedExpressionSource elaborated)
            let providerHead occurrence =
                    SourceTerm.sourceTermProviderHead
                        <$> SourceTerm.sourceTermOccurrenceProvider occurrence
            assertEqual "only the exact whitelisted fixed forms are providers"
                [ Just
                    (Semantic.IntrinsicSourceProvider
                        Semantic.PowerSetProvider)
                , Just
                    (Semantic.IntrinsicSourceProvider
                        Semantic.GlobalChoiceProvider)
                , Nothing
                , Nothing
                , Just (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider)
                ]
                (providerHead <$> sources)
            assertEqual "zero and the empty-set operator share core, not source identity"
                [Core.CIntrinsic Core.Empty, Core.CIntrinsic Core.Empty]
                (Core.scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$> drop 3 sources)
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("fixed-provider driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("fixed-provider driver did not seal: " <> show failure)

retainsWrittenOrderedPairIdentity :: Assertion
retainsWrittenOrderedPairIdentity = do
    fixture <- makeFixture
    let left = Raw.NamedVarAt Nowhere "pair-left"
        right = Raw.NamedVarAt Nowhere "pair-right"
        bound = Raw.NamedVarAt Nowhere "pair-bound"
        pair = Raw.ExprPair
            Nowhere
            (Raw.ExprVar left)
            (Raw.ExprVar right)
        statement = Raw.StmtNoun Raw.Positive
            (Raw.TermExpr pair :| [])
            (Raw.NounPhrase
                []
                (Raw.Noun
                    Nowhere
                    Lexicon.builtinElementNoun
                    [Raw.TermExpr (Raw.ExprVar bound)])
                (Raw.unboundedNounBinder Nothing)
                []
                Nothing)
    context <- expectRight
        (Elaboration.extendElaborationContext
            ( (Elaboration.localId 0, left)
            :| [ (Elaboration.localId 1, right)
               , (Elaboration.localId 2, bound)
               ]
            )
            Elaboration.emptyElaborationContext)
    let action
            :: Declaration.ModuleDriver Text
                (Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition)
        action = Declaration.runProspectiveLoweringDriver
            (Elaboration.elaborateProposition context statement)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded result _interface _prefix -> do
            proposition <- either
                (assertFailure
                    . Text.unpack
                    . Elaboration.renderElaborationError)
                pure
                result
            element <- case Elaboration.elaboratedPropositionAssertions proposition of
                [assertion] ->
                    case Notion.sourceAssertionAtom assertion of
                        Semantic.MembershipAtomTemplate member _set -> pure member
                        _ -> fail "pair membership did not produce a membership atom"
                _ ->
                    assertFailure "pair membership did not retain one source atom"
                        >> fail "unreachable"
            (actualLeft, actualRight) <-
                case SourceTerm.sourceTermOccurrenceOrderedPair element of
                    Just arguments -> pure arguments
                    Nothing ->
                        assertFailure "written ordered-pair identity was erased"
                            >> fail "unreachable"
            assertEqual "left pair argument retains its binder"
                (Core.CBound 2)
                (Core.scopedCoreTerm
                    (SourceTerm.sourceTermOccurrenceCore actualLeft))
            assertEqual "right pair argument retains its binder"
                (Core.CBound 1)
                (Core.scopedCoreTerm
                    (SourceTerm.sourceTermOccurrenceCore actualRight))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("ordered-pair driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("ordered-pair driver did not seal: " <> show failure)

retainsCheckedEqualitySidecars :: Assertion
retainsCheckedEqualitySidecars = do
    fixture <- makeNamedFixture "checked-equality-sidecars"
    let x = Raw.NamedVarAt Nowhere "equality-x"
        y = Raw.NamedVarAt Nowhere "equality-y"
        z = Raw.NamedVarAt Nowhere "equality-z"
        equality left right =
            Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (Raw.ExprVar left :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (Raw.ExprVar right :| [])))
        positive = equality x y
        conjunction = Raw.StmtConnected
            Raw.Conjunction Nothing (equality x y) (equality y z)
        negated = Raw.StmtNeg Nowhere (equality x y)
        implication = Raw.StmtConnected
            Raw.Implication Nothing (equality x y) (equality y z)
        letEquality = Raw.AsmLetEq x (Raw.ExprVar y)
    context <- expectRight
        (Elaboration.extendElaborationContext
            ( (Elaboration.localId 0, x)
            :| [ (Elaboration.localId 1, y)
               , (Elaboration.localId 2, z)
               ]
            )
            Elaboration.emptyElaborationContext)
    let action
            :: Declaration.ModuleDriver Text
                ( [ Either
                        Elaboration.ElaborationError
                        Elaboration.ElaboratedProposition
                  ]
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedClaimEnvelope
                )
        action = do
            propositions <- Declaration.runProspectiveLoweringDriver
                (traverse
                    (Elaboration.elaborateProposition context)
                    [positive, conjunction, negated, implication])
            envelope <- Declaration.runProspectiveLoweringDriver
                (Elaboration.elaborateClaimEnvelope
                    [letEquality]
                    (equality x y))
            pure (propositions, envelope)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded
                (results, envelopeResult) _interface _prefix -> do
            propositions <- traverse
                (either
                    (assertFailure
                        . Text.unpack
                        . Elaboration.renderElaborationError)
                    pure)
                results
            case propositions of
                [positiveResult, conjunctionResult, negatedResult, implicationResult] -> do
                    positiveEquality <- case
                            Elaboration.elaboratedPropositionEqualities positiveResult of
                        [equalityOccurrence] -> pure equalityOccurrence
                        _ -> assertFailure
                                "positive set equality did not retain one sidecar"
                            >> fail "unreachable"
                    assertEqual "positive equality starts at the proposition root"
                        Notion.ConjunctionHere
                        (Notion.sourceEqualityPath positiveEquality)
                    assertEqual "equality left source term remains checked"
                        (Core.CBound 2)
                        (Core.scopedCoreTerm
                            (SourceTerm.sourceTermOccurrenceCore
                                (Notion.sourceEqualityLeft positiveEquality)))
                    assertEqual "equality right source term remains checked"
                        (Core.CBound 1)
                        (Core.scopedCoreTerm
                            (SourceTerm.sourceTermOccurrenceCore
                                (Notion.sourceEqualityRight positiveEquality)))
                    assertEqual "conjunction path-lifts both equalities"
                        [ Notion.ConjunctionLeft Notion.ConjunctionHere
                        , Notion.ConjunctionRight Notion.ConjunctionHere
                        ]
                        ( Notion.sourceEqualityPath
                            <$> Elaboration.elaboratedPropositionEqualities
                                conjunctionResult
                        )
                    assertBool "negation discards equality sidecars"
                        (null
                            (Elaboration.elaboratedPropositionEqualities
                                negatedResult))
                    assertBool "implication discards equality sidecars"
                        (null
                            (Elaboration.elaboratedPropositionEqualities
                                implicationResult))
                _ -> assertFailure "equality sidecar fixture result count changed"
            envelope <- either
                (assertFailure
                    . Text.unpack
                    . Elaboration.renderElaborationError)
                pure
                envelopeResult
            case Elaboration.elaboratedClaimAntecedents envelope of
                [header] ->
                    assertEqual "let-equality header retains one checked sidecar"
                        1
                        (length (Elaboration.compiledHeaderEqualities header))
                _ -> assertFailure "let-equality header alignment changed"
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("equality sidecar driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("equality sidecar driver did not seal: " <> show failure)

rejectsMismatchedSourceProviderOwner :: Assertion
rejectsMismatchedSourceProviderOwner = do
    producer <- makeNamedFixture "mismatched-source-provider-owner"
    let theory = Identity.theoryId (fixtureFoundation producer)
        owner = fixtureOwner producer
        slot = Semantic.declarationSlot owner (localDeclarationOrdinal 0)
        wrongSlot = Semantic.declarationSlot owner (localDeclarationOrdinal 1)
        providerObject = Identity.transparentObject
            theory
            (Core.TyArrow Core.TySet Core.TySet)
            (Core.CLam Core.TySet (Core.CBound 0))
        providerId = Identity.assertedObjectId providerObject
        providerPattern =
            Raw.HoleCons
                (Raw.TokenCons (Raw.Word "owner-sensitive-provider") Raw.End)
        providerKey = Semantic.SemanticExpressionFunction providerPattern
        variable = Semantic.ViewVariableIx 0
        variableTerm = Semantic.TemplateVariable variable
    closure <- expectRight
        (Identity.validateObjectClosure theory [providerObject])
    proposition <- expectRight
        (Identity.validatePropositionContent closure Core.CFalsum)
    let theorem = Identity.theoremRef
            theory (Identity.checkedPropositionId proposition)
        authority = Authority.factAuthority
            theorem Authority.cleanAuthoritySafety
        factSlot = Semantic.factSlot owner (localFactOrdinal 0)
        occurrence = Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
            factSlot authority Semantic.SearchIneligible
        fingerprint = Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
            factSlot authority
        wrongReference = Semantic.globalBindingRef wrongSlot providerKey
        rule = Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterProviderResult (Semantic.ProviderResultRule (Semantic.resultProviderTemplate
                (Semantic.GlobalSourceProvider wrongReference)
                (Vector.singleton variableTerm)) (Semantic.ProviderResultGuarded
                (Semantic.RulePremiseBundles
                    (Semantic.RulePremiseAtom
                        (Semantic.MembershipAtomTemplate
                            variableTerm variableTerm) :| []))) (Semantic.MembershipAtomTemplate
                Semantic.ResultRuleProviderValue
                (Semantic.ResultRuleTerm variableTerm))))
        binding = Semantic.semanticGlobalBinding
            providerKey
            (Semantic.semanticBindingLabel "owner-sensitive-provider")
            (Semantic.GlobalReference providerId)
    certificate <- expectRight
        (Authority.validationCertificate
            authority (Authority.CheckedSourceProof Authority.NoExternalProofUse))
    environment <- expectRight
        (Semantic.semanticEnvironmentDelta [binding])
    delta <- expectRight
        (Semantic.declarationInterfaceDelta
            slot
            [occurrence]
            []
            [providerId]
            [Identity.checkedPropositionId proposition]
            []
            [rule]
            environment)
    interface <- expectRight
        (Semantic.semanticInterface owner [] [delta])
    outcome <- admitTestModule
            theory
            []
            interface
            [providerObject]
            [proposition]
            [certificate]
    case outcome of
        Left (Declaration.ProviderResultRuleMaterializationInvalid
                actualFingerprint reason) -> do
            assertEqual "rejected provider-result fact"
                fingerprint actualFingerprint
            assertBool "owner mismatch is diagnosed"
                ("wrong owner" `Text.isInfixOf` reason)
        Left failure ->
            assertFailure ("unexpected admission failure: " <> show failure)
        Right _ ->
            assertFailure "cached admission accepted malformed provider metadata"

rejectsUndeterminedDecodedProviderPremises :: Assertion
rejectsUndeterminedDecodedProviderPremises = do
    producer <- makeNamedFixture "undetermined-provider-premise-producer"
    let theory = Identity.theoryId (fixtureFoundation producer)
        owner = fixtureOwner producer
        slot = Semantic.declarationSlot owner (localDeclarationOrdinal 0)
        providerObject = Identity.transparentObject
            theory
            (Core.TyArrow Core.TySet Core.TySet)
            (Core.CLam Core.TySet (Core.CBound 0))
        providerId = Identity.assertedObjectId providerObject
        providerPattern = Raw.HoleCons
            (Raw.TokenCons (Raw.Word "undetermined-provider") Raw.End)
        providerKey = Semantic.SemanticExpressionFunction providerPattern
        reference = Semantic.globalBindingRef slot providerKey
        determinedTerm =
            Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        undeterminedTerm =
            Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
    closure <- expectRight
        (Identity.validateObjectClosure theory [providerObject])
    proposition <- expectRight
        (Identity.validatePropositionContent closure Core.CFalsum)
    let theorem = Identity.theoremRef
            theory (Identity.checkedPropositionId proposition)
        authority = Authority.factAuthority
            theorem Authority.cleanAuthoritySafety
        factSlot = Semantic.factSlot owner (localFactOrdinal 0)
        occurrence = Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
            factSlot authority Semantic.SearchIneligible
        fingerprint = Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
            factSlot authority
        rule = Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterProviderResult (Semantic.ProviderResultRule (Semantic.resultProviderTemplate
                (Semantic.GlobalSourceProvider reference)
                (Vector.singleton
                    (Semantic.TemplateOrderedPair
                        determinedTerm determinedTerm))) (Semantic.ProviderResultGuarded
                (Semantic.RulePremiseBundles
                    (Semantic.RulePremiseAtom
                        (Semantic.MembershipAtomTemplate
                            determinedTerm undeterminedTerm) :| []))) (Semantic.MembershipAtomTemplate
                Semantic.ResultRuleProviderValue
                (Semantic.ResultRuleTerm determinedTerm))))
        binding = Semantic.semanticGlobalBinding
            providerKey
            (Semantic.semanticBindingLabel "undetermined-provider")
            (Semantic.GlobalReference providerId)
    certificate <- expectRight
        (Authority.validationCertificate
            authority (Authority.CheckedSourceProof Authority.NoExternalProofUse))
    environment <- expectRight
        (Semantic.semanticEnvironmentDelta [binding])
    delta <- expectRight
        (Semantic.declarationInterfaceDelta
            slot
            [occurrence]
            []
            [providerId]
            [Identity.checkedPropositionId proposition]
            []
            [rule]
            environment)
    interface <- expectRight
        (Semantic.semanticInterface owner [] [delta])
    decodedInterface <- expectRight
        (decodeCache
            Semantic.getSemanticInterfaceCache
            (encodeCache (Semantic.putSemanticInterfaceCache interface)))
    outcome <- admitTestModule
            theory
            []
            decodedInterface
            [providerObject]
            [proposition]
            [certificate]
    case outcome of
        Left (Declaration.ProviderResultRuleMaterializationInvalid
                actualFingerprint reason) -> do
            assertEqual "rejected provider-result fact"
                fingerprint actualFingerprint
            assertBool "undetermined premise is diagnosed"
                ("contains a fresh or growing term"
                    `Text.isInfixOf` reason)
        Left failure ->
            assertFailure ("unexpected admission failure: " <> show failure)
        Right _ ->
            assertFailure "cached admission accepted malformed provider metadata"

rejectsEmptyFiniteSetProviderRule :: Assertion
rejectsEmptyFiniteSetProviderRule = do
    producer <- makeNamedFixture "empty-finite-set-provider-rule-producer"
    let theory = Identity.theoryId (fixtureFoundation producer)
        owner = fixtureOwner producer
        slot = Semantic.declarationSlot owner (localDeclarationOrdinal 0)
        variableTerm = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
    proposition <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure producer)
            Core.CFalsum)
    let theorem = Identity.theoremRef
            theory (Identity.checkedPropositionId proposition)
        authority = Authority.factAuthority
            theorem Authority.cleanAuthoritySafety
        factSlot = Semantic.factSlot owner (localFactOrdinal 0)
        occurrence = Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
            factSlot authority Semantic.SearchIneligible
        fingerprint = Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
            factSlot authority
        rule = Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterProviderResult (Semantic.ProviderResultRule (Semantic.resultProviderTemplate
                Semantic.FiniteSetLiteralSourceProvider
                Vector.empty) (Semantic.ProviderResultGuarded
                (Semantic.RulePremiseBundles
                    (Semantic.RulePremiseAtom
                        (Semantic.MembershipAtomTemplate
                            variableTerm variableTerm) :| []))) (Semantic.MembershipAtomTemplate
                Semantic.ResultRuleProviderValue
                (Semantic.ResultRuleTerm variableTerm))))
    certificate <- expectRight
        (Authority.validationCertificate
            authority (Authority.CheckedSourceProof Authority.NoExternalProofUse))
    environment <- expectRight
        (Semantic.semanticEnvironmentDelta [])
    delta <- expectRight
        (Semantic.declarationInterfaceDelta
            slot
            [occurrence]
            []
            []
            [Identity.checkedPropositionId proposition]
            []
            [rule]
            environment)
    interface <- expectRight
        (Semantic.semanticInterface owner [] [delta])
    decodedInterface <- expectRight
        (decodeCache
            Semantic.getSemanticInterfaceCache
            (encodeCache
                (Semantic.putSemanticInterfaceCache interface)))
    outcome <- admitTestModule
            theory
            []
            decodedInterface
            []
            [proposition]
            [certificate]
    case outcome of
        Left (Declaration.ProviderResultRuleMaterializationInvalid
                actualFingerprint reason) -> do
            assertEqual "rejected finite-set provider-result fact"
                fingerprint actualFingerprint
            assertBool "empty finite-set spine is diagnosed"
                ("finite-set literal provider has an empty spine"
                    `Text.isInfixOf` reason)
        Left failure ->
            assertFailure ("unexpected admission failure: " <> show failure)
        Right _ ->
            assertFailure "cached admission accepted malformed provider metadata"

elaboratesScopedPropositions :: Assertion
elaboratesScopedPropositions = do
    fixture <- makeNamedFixture "exact-scoped-proposition"
    let x = Raw.NamedVar "x"
        y = Raw.NamedVar "y"
        statement =
            Raw.SymbolicQuantified
                Nowhere
                Raw.Universally
                (x :| [y])
                Raw.Unbounded
                Nothing
                (Raw.StmtFormula
                    (Raw.FormulaChain
                        (Raw.ChainBase
                            (Raw.ExprVar x :| [])
                            Raw.Positive
                            (Raw.Relation
                                Nowhere
                                Raw.EqSymbol
                                [])
                            (Raw.ExprVar y :| []))))
        action
            :: Declaration.ModuleDriver Text
                (Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition)
        action =
            Declaration.runProspectiveLoweringDriver
                (Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    statement)
    outcome <- runDriver fixture action
    case outcome of
        Declaration.DriverSucceeded (Right prepared) _interface _prefix ->
            assertEqual
                "source-order universal binders"
                (Core.CForall Core.TySet
                    (Core.CForall Core.TySet
                        (Core.CEq Core.TySet
                            (Core.CBound 1)
                            (Core.CBound 0))))
                (Core.scopedCoreTerm
                    (Elaboration.elaboratedPropositionCore prepared))
        Declaration.DriverSucceeded (Left failure) _interface _prefix ->
            assertFailure
                ("scoped elaboration failed: "
                    <> Text.unpack (Elaboration.renderElaborationError failure))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("scoped exact driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("scoped exact driver did not seal: " <> show failure)

validatesDatatypeConstructorContext :: Assertion
validatesDatatypeConstructorContext = do
    fixture <- makeFixture
    let theory = Identity.theoryId (fixtureFoundation fixture)
        symbol = Raw.ConsSymbol
        seed = Identity.opaqueDeclarationSeed
            (fixtureOwner fixture)
            (localDeclarationOrdinal 0)
            DatatypeDeclaration
            (generatedObjectSlot 0)
        asserted = Identity.opaqueObject theory seed
            (Core.TySet `Core.TyArrow`
                (Core.TySet `Core.TyArrow` Core.TySet))
        mistyped = Identity.opaqueObject theory seed Core.TySet
        key = Semantic.SemanticExpressionFunction (Raw.mixfixPattern symbol)
    closure <- expectRight
        (Identity.extendObjectClosure (fixtureClosure fixture) [asserted])
    mistypedClosure <- expectRight
        (Identity.extendObjectClosure (fixtureClosure fixture) [mistyped])
    case Elaboration.datatypeElaborationEnvironment
            (fixtureClosure fixture)
            ((Nowhere, symbol, asserted) :| []) [] of
        Left (Elaboration.ElaborationProspectiveObjectMissing
                location identity) -> do
            assertEqual "missing-object location" Nowhere location
            assertEqual "missing constructor object"
                (Identity.assertedObjectId asserted)
                identity
        Left failure ->
            assertFailure ("unexpected missing-object failure: " <> show failure)
        Right{} ->
            assertFailure "a datatype environment detached an object from its closure"
    case Elaboration.datatypeElaborationEnvironment closure
            ( (Nowhere, symbol, asserted)
                :| [(Nowhere, symbol, asserted)]
            ) [] of
        Left (Elaboration.ElaborationGlobalAlreadyVisible location actualKey) -> do
            assertEqual "duplicate location" Nowhere location
            assertEqual "duplicate constructor key" key actualKey
        Left failure ->
            assertFailure ("unexpected constructor failure: " <> show failure)
        Right{} ->
            assertFailure
                "one datatype preparation bound the same source constructor twice"
    case Elaboration.datatypeElaborationEnvironment mistypedClosure
            ((Nowhere, symbol, mistyped) :| []) [] of
        Left (Elaboration.ElaborationObjectTypeMismatch
                location expected actual) -> do
            assertEqual "type mismatch location" Nowhere location
            assertEqual "declared constructor type"
                (Core.TySet `Core.TyArrow`
                    (Core.TySet `Core.TyArrow` Core.TySet))
                expected
            assertEqual "actual constructor type" Core.TySet actual
        Left failure ->
            assertFailure ("unexpected constructor type failure: " <> show failure)
        Right{} ->
            assertFailure "a datatype constructor acquired a different declared type"

lowersFixedEqualityAliases :: Assertion
lowersFixedEqualityAliases = do
    fixture <- makeNamedFixture "fixed-equality-aliases"
    let x = Raw.NamedVar "x"
        y = Raw.NamedVar "y"
        z = Raw.NamedVar "z"
        term variable = Raw.TermExpr (Raw.ExprVar variable)
        equality left right =
            Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (Raw.ExprVar left :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (Raw.ExprVar right :| [])))
        quantified variables statement =
            Raw.SymbolicQuantified
                Nowhere
                Raw.Universally
                variables
                Raw.Unbounded
                Nothing
                statement
        adjective =
            Raw.Adj
                Nowhere
                Lexicon.builtinEqualityRightAdjective
                [term y]
        copular =
            Raw.StmtVerbPhrase
                (term x :| [])
                (Raw.VPAdj (adjective :| []))
        rightAttribute =
            Raw.StmtNoun Raw.Positive
                (term x :| [])
                (Raw.NounPhrase
                    []
                    (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
                    (Raw.unboundedNounBinder Nothing)
                    [ Raw.AdjR
                        Nowhere
                        Lexicon.builtinEqualityRightAdjective
                        [term y]
                    ]
                    Nothing)
        rightAttributeExpected =
            Raw.StmtNoun Raw.Positive
                (term x :| [])
                (Raw.NounPhrase
                    []
                    (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
                    (Raw.unboundedNounBinder Nothing)
                    []
                    (Just (equality x y)))
        verb argument =
            Raw.Verb
                Nowhere
                Lexicon.builtinEqualityVerb
                [term argument]
        singular =
            Raw.StmtVerbPhrase
                (term x :| [])
                (Raw.VPVerb (verb y))
        negated =
            Raw.StmtVerbPhrase
                (term x :| [])
                (Raw.VPVerbNot (verb y))
        coordinated =
            Raw.StmtVerbPhrase
                (term x :| [term y])
                (Raw.VPVerb (verb z))
        coordinatedExpected =
            Raw.StmtConnected
                Raw.Conjunction
                Nothing
                (equality x z)
                (equality y z)
        comparisons =
            [ ( "copular adjective"
              , quantified (x :| [y]) copular
              , quantified (x :| [y]) (equality x y)
              )
            , ( "right adjective"
              , quantified (x :| [y]) rightAttribute
              , quantified (x :| [y]) rightAttributeExpected
              )
            , ( "singular verb"
              , quantified (x :| [y]) singular
              , quantified (x :| [y]) (equality x y)
              )
            , ( "negated verb"
              , quantified (x :| [y]) negated
              , quantified
                    (x :| [y])
                    (Raw.StmtNeg Nowhere (equality x y))
              )
            , ( "quantified coordinated verb"
              , quantified (x :| [y, z]) coordinated
              , quantified (x :| [y, z]) coordinatedExpected
              )
            ]
        action
            :: Declaration.ModuleDriver Text
                [ ( Either
                        Elaboration.ElaborationError
                        Elaboration.ElaboratedProposition
                  , Either
                        Elaboration.ElaborationError
                        Elaboration.ElaboratedProposition
                  )
                ]
        action =
            Declaration.runProspectiveLoweringDriver
                (traverse
                    (\(_label, alias, symbolic) ->
                        (,)
                            <$> Elaboration.elaborateProposition
                                Elaboration.emptyElaborationContext alias
                            <*> Elaboration.elaborateProposition
                                Elaboration.emptyElaborationContext symbolic)
                    comparisons)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded results _interface _prefix ->
            for_ (zip comparisons results) \((label, _alias, _symbolic), result) ->
                case result of
                    (Right alias, Right symbolic) -> do
                        let aliasTerm =
                                Core.scopedCoreTerm
                                    (Elaboration.elaboratedPropositionCore alias)
                            symbolicTerm =
                                Core.scopedCoreTerm
                                    (Elaboration.elaboratedPropositionCore symbolic)
                        assertEqual
                            (label <> " checked core")
                            symbolicTerm
                            aliasTerm
                        assertEqual
                            (label <> " global support")
                            Set.empty
                            (Core.canonicalTermGlobals aliasTerm)
                        assertEqual
                            (label <> " foundation support")
                            Set.empty
                            (Foundation.foundationAxiomDependencies aliasTerm)
                    (Left failure, _) ->
                        assertFailure
                            (label <> " alias failed: "
                                <> Text.unpack
                                    (Elaboration.renderElaborationError failure))
                    (_, Left failure) ->
                        assertFailure
                            (label <> " symbolic comparison failed: "
                                <> Text.unpack
                                    (Elaboration.renderElaborationError failure))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("fixed equality driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("fixed equality driver did not seal: " <> show failure)

scopesNounPredicatePolarity :: Assertion
scopesNounPredicatePolarity = do
    fixture <- makeNamedFixture "noun-predicate-polarity"
    context <- expectRight
        (Elaboration.extendElaborationContext
            ((Elaboration.localId 0, "A") :|
                [(Elaboration.localId 1, "a"), (Elaboration.localId 2, "b")])
            Elaboration.emptyElaborationContext)
    let bound = Core.CBound
        member x y = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) y
        equality = Core.CEq Core.TySet
        allSets = Core.CForall Core.TySet
        someSet = Core.CExists Core.TySet
        notP = Core.CNot
        andP = Core.CAnd
        memberA = member (bound 0) (bound 3)
        cases =
            [ ("Every set $x$ is not an element of $A$", allSets (notP memberA))
            , ("Some set $x$ is not an element of $A$", someSet (notP memberA))
            , ("No set $x$ is not an element of $A$", notP (someSet (notP memberA)))
            , ("Every set $x$ is not equal to $A$",
                allSets (notP (equality (bound 0) (bound 3))))
            , ("Every element $x$ of $A$ is not an element of $a$",
                allSets (Core.CImp memberA (notP (member (bound 0) (bound 2)))))
            , ("For every set $x$ we have $x$ is not an element of $A$",
                allSets (notP memberA))
            , ("It is not the case that every set $x$ is an element of $A$",
                notP (allSets memberA))
            , ("It is not the case that every set $x$ is not an element of $A$",
                notP (allSets (notP memberA)))
            , ("$a$ and $b$ are not elements of $A$",
                andP (notP (member (bound 1) (bound 2)))
                    (notP (member (bound 0) (bound 2))))
            , ("It is not the case that $a$ and $b$ are elements of $A$",
                notP (andP (member (bound 1) (bound 2))
                    (member (bound 0) (bound 2))))
            , ("Every set $x$ and $a$ are not elements of $A$",
                allSets (andP (notP memberA) (notP (member (bound 2) (bound 3)))))
            , ("$a$ is not an element of $A$ equal to $b$",
                notP (andP (member (bound 1) (bound 2)) (equality (bound 1) (bound 0))))
            , ("$a$ is not an element $z$ of $A$ such that $z=b$",
                notP (andP (member (bound 1) (bound 2)) (equality (bound 1) (bound 0))))
            , ("$a$ is not an element of every set $y$",
                notP (allSets (member (bound 2) (bound 0))))
            , ("$a$ and $b$ are not elements of some set $y$",
                andP (notP (someSet (member (bound 2) (bound 0))))
                    (notP (someSet (member (bound 1) (bound 0)))))
            ]
    statements <- traverse (parseStatement . fst) cases
    groupedName <- parseStatement "$a$ and $b$ are not elements $z$ of $A$"
    let action :: Declaration.ModuleDriver Text
            ([Either Elaboration.ElaborationError Elaboration.ElaboratedProposition],
             Either Elaboration.ElaborationError Elaboration.ElaboratedProposition)
        action = Declaration.runProspectiveLoweringDriver
            ((,) <$> traverse (Elaboration.elaborateProposition context) statements
                <*> Elaboration.elaborateProposition context groupedName)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded (results, grouped) _interface _prefix -> do
            for_ (zip cases results) \((source, expected), result) -> do
                prepared <- expectRight result
                assertEqual (Text.unpack source) expected
                    (Core.scopedCoreTerm (Elaboration.elaboratedPropositionCore prepared))
                assertBool "negative predicates supply no positive notion evidence"
                    (all ((== Semantic.NegativePolarity) . Semantic.atomPolarity . Notion.sourceAssertionAtom)
                        (Elaboration.elaboratedPropositionAssertions prepared))
                assertBool "negative predicates supply no equality evidence"
                    (null (Elaboration.elaboratedPropositionEqualities prepared))
            case grouped of
                Left Elaboration.ElaborationGroupedNounNameUnsupported{} -> pure ()
                _ -> assertFailure "negative grouped nouns must still reject a shared name"
        Declaration.DriverFailed failure _prefix -> assertFailure (show failure)
        Declaration.DriverSealFailed failure _prefix -> assertFailure (show failure)
  where
    parseStatement source = do
        scanned <- expectRight (SourceScan.scanCompleteVerificationText
            anonymousSourceDescriptor "noun-polarity.tex"
            ("\\begin{axiom}\\label{noun_polarity}\n" <> source <> ".\n\\end{axiom}"))
        case SourceScan.verificationChunks scanned of
            [tokens] -> case fullParses (parser (Concrete.grammar Lexicon.builtins)) tokens of
                ([Right (Raw.BlockAxiom _ _ _ (Raw.Axiom [] statement))], _) -> pure statement
                result -> assertFailure ("expected exactly one parse for "
                    <> Text.unpack source <> ": " <> show result) >> fail "parse failed"
            _ -> assertFailure "expected one source chunk" >> fail "scan failed"

scopesQuantifiedPropositionTerms :: Assertion
scopesQuantifiedPropositionTerms = do
    fixture <- makeNamedFixture "quantified-proposition-terms"
    let x = Raw.NamedVar "x"
        y = Raw.NamedVar "y"
        term variable = Raw.TermExpr (Raw.ExprVar variable)
        zero = Raw.TermExpr (Raw.ExprOpaqueInteger Nowhere 0)
        setNoun = Raw.Noun Nowhere Lexicon.builtinSetNoun []
        setPhrase named = Raw.NounPhrase [] setNoun (Raw.unboundedNounBinder named) [] Nothing
        quantified quantifier variable =
            Raw.TermQuantified
                quantifier Nowhere (setPhrase (Just variable))
        equalityVerb argument =
            Raw.Verb Nowhere Lexicon.builtinEqualityVerb [argument]
        equalityAdjective argument =
            Raw.Adj
                Nowhere Lexicon.builtinEqualityRightAdjective [argument]
        equality left right = Core.CEq Core.TySet left right
        notP = Core.CNot
        andP = Core.CAnd
        existsP = Core.CExists Core.TySet
        truth = Core.CTruth
        member left right =
            Core.CApp
                (Core.CApp (Core.CIntrinsic Core.Member) left)
                right
        soleSubject =
            Raw.StmtNoun Raw.Positive
                (quantified Raw.Universally x :| [])
                (setPhrase Nothing)
        explicitSubject =
            Raw.SymbolicQuantified
                Nowhere Raw.Universally (x :| []) Raw.Unbounded Nothing
                (Raw.StmtNoun Raw.Positive (term x :| []) (setPhrase Nothing))
        multipleSubjects =
            Raw.StmtVerbPhrase
                ( quantified Raw.Universally x
                    :| [quantified Raw.Existentially y]
                )
                (Raw.VPVerb (equalityVerb zero))
        adjectiveArgument =
            Raw.StmtVerbPhrase
                (zero :| [])
                (Raw.VPAdj
                    (equalityAdjective
                        (quantified Raw.Universally x) :| []))
        nounArgument =
            Raw.StmtNoun Raw.Positive
                (zero :| [])
                (Raw.NounPhrase
                    []
                    (Raw.Noun
                        Nowhere Lexicon.builtinElementNoun
                        [quantified Raw.Universally x])
                    (Raw.unboundedNounBinder Nothing) [] Nothing)
        negatedSubject =
            Raw.StmtVerbPhrase
                (quantified Raw.Universally x :| [])
                (Raw.VPVerbNot (equalityVerb zero))
        negatedArgument =
            Raw.StmtVerbPhrase
                (zero :| [])
                (Raw.VPVerbNot
                    (equalityVerb (quantified Raw.Universally x)))
        nonexistentialArgument =
            Raw.StmtVerbPhrase
                (zero :| [])
                (Raw.VPVerb
                    (equalityVerb (quantified Raw.Nonexistentially x)))
        negatedStatement =
            Raw.StmtNeg Nowhere soleSubject
        siblingConstraints =
            Raw.StmtNoun Raw.Positive
                (zero :| [])
                (Raw.NounPhrase
                    []
                    (Raw.Noun
                        Nowhere Lexicon.builtinElementNoun
                        [quantified Raw.Universally x])
                    (Raw.unboundedNounBinder Nothing)
                    [Raw.AdjR
                        Nowhere Lexicon.builtinEqualityRightAdjective
                        [quantified Raw.Universally y]]
                    Nothing)
        constrainedSubject =
            Raw.TermQuantified Raw.Universally Nowhere
                (Raw.NounPhrase
                    []
                    (Raw.Noun
                        Nowhere Lexicon.builtinElementNoun [term x])
                    (Raw.unboundedNounBinder (Just x))
                    [Raw.AdjR
                        Nowhere Lexicon.builtinEqualityRightAdjective [term x]]
                    (Just
                        (Raw.StmtVerbPhrase
                            (term x :| [])
                            (Raw.VPVerb (equalityVerb (term x))))))
        constrainedStatement =
            Raw.StmtVerbPhrase
                (constrainedSubject :| [])
                (Raw.VPVerb (equalityVerb (term x)))
        xEqualsX = equality (Core.CBound 0) (Core.CBound 0)
        cases =
            [ ( "sole quantified subject"
              , soleSubject
              , Core.CForall Core.TySet truth
              )
            , ( "explicit sole quantified subject"
              , explicitSubject
              , Core.CForall Core.TySet truth
              )
            , ( "multiple quantified subjects"
              , multipleSubjects
              , Core.CForall Core.TySet
                    (existsP
                        (andP
                            (equality
                                (Core.CBound 1) (Core.COpaqueInteger 0))
                            (equality
                                (Core.CBound 0) (Core.COpaqueInteger 0))))
              )
            , ( "quantified adjective argument"
              , adjectiveArgument
              , Core.CForall Core.TySet
                    (equality (Core.COpaqueInteger 0) (Core.CBound 0))
              )
            , ( "quantified noun argument"
              , nounArgument
              , Core.CForall Core.TySet
                    (member (Core.COpaqueInteger 0) (Core.CBound 0))
              )
            , ( "quantified subject outside negation"
              , negatedSubject
              , Core.CForall Core.TySet
                    (notP
                        (equality
                            (Core.CBound 0) (Core.COpaqueInteger 0)))
              )
            , ( "quantified argument inside negation"
              , negatedArgument
              , notP
                    (Core.CForall Core.TySet
                        (equality
                            (Core.COpaqueInteger 0) (Core.CBound 0)))
              )
            , ( "nonexistential quantified verb argument"
              , nonexistentialArgument
              , notP
                    (existsP
                        (equality
                            (Core.COpaqueInteger 0)
                            (Core.CBound 0)))
              )
            , ( "statement recursion bounds a quantified subject"
              , negatedStatement
              , notP (Core.CForall Core.TySet truth)
              )
            , ( "sibling constraints own their argument quantifiers"
              , siblingConstraints
              , andP
                    (Core.CForall Core.TySet
                        (member
                            (Core.COpaqueInteger 0)
                            (Core.CBound 0)))
                    (Core.CForall Core.TySet
                        (equality
                            (Core.COpaqueInteger 0)
                            (Core.CBound 0)))
              )
            , ( "quantified noun constraints share their binder"
              , constrainedStatement
              , Core.CForall Core.TySet
                    (Core.CImp
                        (andP
                            (member (Core.CBound 0) (Core.CBound 0))
                            (andP xEqualsX xEqualsX))
                        xEqualsX)
              )
            ]
        prepare context statement =
            Elaboration.elaborateProposition context statement
    activeContext <- expectRight
        (Elaboration.extendElaborationContext
            ((Elaboration.localId 0, x) :| [])
            Elaboration.emptyElaborationContext)
    let action
            :: Declaration.ModuleDriver Text
                ( [ Either
                        Elaboration.ElaborationError
                        Elaboration.ElaboratedProposition
                  ]
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                )
        action =
            Declaration.runProspectiveLoweringDriver do
                compiled <- traverse
                    (\(_label, statement, _expected) ->
                        prepare Elaboration.emptyElaborationContext statement)
                    cases
                collision <- prepare activeContext soleSubject
                pure (compiled, collision)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded
                (compiled, collision) _interface _prefix -> do
            for_ (zip cases compiled) \
                    ((label, _statement, expected), result) ->
                case result of
                    Right prepared ->
                        assertEqual label expected
                            (Core.scopedCoreTerm
                                (Elaboration.elaboratedPropositionCore prepared))
                    Left failure ->
                        assertFailure
                            (label <> " failed: "
                                <> Text.unpack
                                    (Elaboration.renderElaborationError failure))
            case collision of
                Left (Elaboration.ElaborationDuplicateLocalBinder _location variable) ->
                    assertEqual "quantified binder collision" x variable
                Left failure ->
                    assertFailure
                        ("unexpected quantified-binder collision: "
                            <> Text.unpack
                                (Elaboration.renderElaborationError failure))
                Right{} ->
                    assertFailure "an active quantified binder was shadowed"
            case compiled of
                Right sole : Right explicit : _ ->
                    assertEqual
                        "sole-subject lowering remains byte-for-byte identical"
                        (Elaboration.elaboratedPropositionCore sole)
                        (Elaboration.elaboratedPropositionCore explicit)
                _ ->
                    assertFailure
                        "sole-subject equality comparison did not compile"
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("quantified proposition-term driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("quantified proposition-term driver did not seal: "
                    <> show failure)

preparesClaimEnvelopes :: Assertion
preparesClaimEnvelopes = do
    fixture <- makeNamedFixture "exact-claim-envelope"
    let bLocation = mkLocation anonymousSourceDescriptor 2 11
        aLocation = mkLocation anonymousSourceDescriptor 2 15
        xLocation = mkLocation anonymousSourceDescriptor 3 9
        b = Raw.NamedVarAt bLocation "b"
        a = Raw.NamedVarAt aLocation "a"
        x = Raw.NamedVarAt xLocation "x"
        c = Raw.NamedVarAt Nowhere "c"
        d = Raw.NamedVarAt Nowhere "d"
        z = Raw.NamedVarAt Nowhere "z"
        equality left right =
            Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (Raw.ExprVar left :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (Raw.ExprVar right :| [])))
        quantified variable body =
            Raw.SymbolicQuantified
                (locate variable)
                Raw.Universally
                (variable :| [])
                Raw.Unbounded
                Nothing
                body
        sourceAssumptions = [Raw.AsmSuppose (equality b a)]
        sourceConclusion = quantified x (equality x b)
        alphaAssumptions = [Raw.AsmSuppose (equality c d)]
        alphaConclusion = quantified z (equality z c)
        action
            :: Declaration.ModuleDriver Text
                ( Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedClaimEnvelope
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedClaimEnvelope
                )
        action =
            Declaration.runProspectiveLoweringDriver do
                source <- Elaboration.elaborateClaimEnvelope
                    sourceAssumptions sourceConclusion
                alpha <- Elaboration.elaborateClaimEnvelope
                    alphaAssumptions alphaConclusion
                pure (source, alpha)
        expected =
            Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CImp
                        (Core.CEq Core.TySet
                            (Core.CBound 1)
                            (Core.CBound 0))
                        (Core.CForall Core.TySet
                            (Core.CEq Core.TySet
                                (Core.CBound 0)
                                (Core.CBound 2)))))
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded
                (Right source, Right alpha)
                _interface _prefix -> do
            let sourceTarget = Elaboration.elaboratedClaimTarget source
                alphaTarget = Elaboration.elaboratedClaimTarget alpha
            assertEqual "closed claim envelope core"
                expected
                (Core.scopedCoreTerm sourceTarget)
            assertEqual "claim envelope is closed"
                []
                (Core.scopedCoreContext sourceTarget)
            assertEqual "first semantic occurrence binder order"
                [bLocation, aLocation]
                (locate <$> Elaboration.elaboratedClaimVariables source)
            assertEqual "explicit binders are not generalized"
                2
                (length (Elaboration.elaboratedClaimVariables source))
            assertEqual "header antecedent count"
                1
                (Elaboration.elaboratedClaimAntecedentCount source)
            headerEquality <- case Elaboration.elaboratedClaimAntecedents source of
                [header] -> case Elaboration.compiledHeaderEqualities header of
                    [equalityOccurrence] -> pure equalityOccurrence
                    _ -> assertFailure
                            "positive equality header lost its checked sidecar"
                        >> fail "unreachable"
                _ -> assertFailure "claim header sidecar alignment changed"
                    >> fail "unreachable"
            assertEqual "claim-header equality remains a direct conjunct"
                Notion.ConjunctionHere
                (Notion.sourceEqualityPath headerEquality)
            assertBool "quantification discards conclusion equality sidecars"
                (null (Elaboration.elaboratedClaimConclusionEqualities source))
            assertEqual "alpha-renaming preserves the checked target"
                sourceTarget alphaTarget
            assertEqual "alpha-renaming preserves proposition identity"
                (Identity.propositionIdOf
                    (Core.scopedCoreTerm sourceTarget))
                (Identity.propositionIdOf
                    (Core.scopedCoreTerm alphaTarget))
        Declaration.DriverSucceeded result _interface _prefix ->
            assertFailure
                ("exact claim envelope preparation failed: "
                    <> case result of
                        (Left failure, _) ->
                            Text.unpack
                                (Elaboration.renderElaborationError failure)
                        (_, Left failure) ->
                            Text.unpack
                                (Elaboration.renderElaborationError failure))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("claim envelope driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("claim envelope driver did not seal: " <> show failure)

elaboratesSeparationComprehensions :: Assertion
elaboratesSeparationComprehensions = do
    fixture <- makeNamedFixture "exact-separation-comprehension"
    let binderLocation = mkLocation anonymousSourceDescriptor 2 7
        ambientLocation = mkLocation anonymousSourceDescriptor 2 18
        boundOccurrenceLocation = mkLocation anonymousSourceDescriptor 3 14
        x = Raw.NamedVarAt binderLocation "x"
        a = Raw.NamedVarAt ambientLocation "A"
        equality left right =
            Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (left :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (right :| [])))
        separation bound =
            Raw.ExprSep
                binderLocation
                x
                bound
                (equality (Raw.ExprVar x) (Raw.ExprVar a))
        validStatement =
            Raw.SymbolicQuantified
                Nowhere
                Raw.Universally
                (a :| [])
                Raw.Unbounded
                Nothing
                (equality
                    (separation (Raw.ExprVar a))
                    (Raw.ExprVar a))
        boundOccurrence =
            Raw.NamedVarAt boundOccurrenceLocation "x"
        invalidStatement =
            equality
                (separation (Raw.ExprVar boundOccurrence))
                (Raw.ExprVar a)
        action
            :: Declaration.ModuleDriver Text
                ( Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                )
        action =
            Declaration.runProspectiveLoweringDriver do
                valid <- Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    validStatement
                invalid <- Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    invalidStatement
                pure (valid, invalid)
    outcome <- runDriver fixture action
    case outcome of
        Declaration.DriverSucceeded
                (Right prepared, Left failure) _interface _prefix -> do
            assertEqual
                "separation comprehension core"
                (Core.CForall Core.TySet
                    (Core.CEq Core.TySet
                        (Core.CApp
                            (Core.CApp
                                (Core.CIntrinsic Core.Sep)
                                (Core.CBound 0))
                            (Core.CLam Core.TySet
                                (Core.CEq Core.TySet
                                    (Core.CBound 0)
                                    (Core.CBound 1))))
                        (Core.CBound 0)))
                (Core.scopedCoreTerm
                    (Elaboration.elaboratedPropositionCore prepared))
            assertEqual
                "separation proposition type"
                Core.TyProp
                (Core.scopedCoreType
                    (Elaboration.elaboratedPropositionCore prepared))
            assertEqual
                "the separation binder is unavailable in its bound"
                (Elaboration.ElaborationFreeVariable
                    boundOccurrenceLocation
                    boundOccurrence)
                failure
        Declaration.DriverSucceeded result _interface _prefix ->
            case result of
                (Left validFailure, _) ->
                    assertFailure
                        ("valid separation failed: "
                            <> Text.unpack
                                (Elaboration.renderElaborationError validFailure))
                (_, Right{}) ->
                    assertFailure "invalid separation was accepted"
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("separation exact driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("separation exact driver did not seal: " <> show failure)

elaboratesReplacementTelescopes :: Assertion
elaboratesReplacementTelescopes = do
    fixture <- makeNamedFixture "exact-replacement-telescope"
    let location = mkLocation anonymousSourceDescriptor 2 1
        futureOccurrenceLocation = mkLocation anonymousSourceDescriptor 7 19
        a = Raw.NamedVarAt location "A"
        x = Raw.NamedVarAt location "x"
        y = Raw.NamedVarAt location "y"
        futureY = Raw.NamedVarAt futureOccurrenceLocation "y"
        equality left right =
            Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (left :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (right :| [])))
        replacement firstDomain =
            Raw.ExprReplace
                location
                (Raw.ExprVar y)
                ( (x, firstDomain) :|
                    [(y, Raw.ExprVar x)]
                )
                (Just (equality (Raw.ExprVar x) (Raw.ExprVar y)))
        validStatement =
            Raw.SymbolicQuantified
                Nowhere
                Raw.Universally
                (a :| [])
                Raw.Unbounded
                Nothing
                (equality
                    (replacement (Raw.ExprVar a))
                    (Raw.ExprVar a))
        invalidStatement =
            equality
                (replacement (Raw.ExprVar futureY))
                (Raw.ExprOpaqueInteger Nowhere 0)
        predicateReplacementLocation = mkLocation anonymousSourceDescriptor 9 3
        predicateReplacementStatement =
            equality
                (Raw.ExprReplacePred
                    predicateReplacementLocation
                    y
                    x
                    (Raw.ExprOpaqueInteger Nowhere 0)
                    (equality (Raw.ExprVar x) (Raw.ExprVar y)))
                (Raw.ExprOpaqueInteger Nowhere 0)
        namedPredicateReplacement =
            Raw.ExprReplacePred
                predicateReplacementLocation
                y
                x
                (Raw.ExprVar a)
                (equality (Raw.ExprVar x) (Raw.ExprVar y))
        app1 intrinsic argument =
            Core.CApp (Core.CIntrinsic intrinsic) argument
        app2 intrinsic first second =
            Core.CApp (app1 intrinsic first) second
        expected =
            Core.CForall Core.TySet $
                Core.CEq Core.TySet
                    (app1 Core.FamilyUnion $
                        app2 Core.Repl (Core.CBound 0) $
                            Core.CLam Core.TySet $
                                app2 Core.Repl
                                    (app2 Core.Sep
                                        (Core.CBound 0)
                                        (Core.CLam Core.TySet $
                                            Core.CEq Core.TySet
                                                (Core.CBound 1)
                                                (Core.CBound 0)))
                                    (Core.CLam Core.TySet
                                        (Core.CBound 0)))
                    (Core.CBound 0)
        action
            :: Declaration.ModuleDriver Text
                ( Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition
                , Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedSetExpression
                )
        action =
            Declaration.runProspectiveLoweringDriver do
                valid <- Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    validStatement
                invalid <- Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    invalidStatement
                predicateReplacement <- Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    predicateReplacementStatement
                namedContext <-
                    either
                        (impossible
                            . Text.unpack
                            . Elaboration.renderElaborationError)
                        pure
                        (Elaboration.extendElaborationContext
                            ((Elaboration.localId 0, a) :| [])
                            Elaboration.emptyElaborationContext)
                named <- Elaboration.elaborateSetExpression
                    namedContext namedPredicateReplacement
                pure (valid, invalid, predicateReplacement, named)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded
                ( Right prepared
                    , Left failure
                    , Left predicateReplacementFailure
                    , Right named
                    ) _interface _prefix -> do
            assertEqual
                "dependent replacement core"
                expected
                (Core.scopedCoreTerm
                    (Elaboration.elaboratedPropositionCore prepared))
            assertEqual
                "future replacement binder location"
                (Elaboration.ElaborationFreeVariable futureOccurrenceLocation futureY)
                failure
            assertEqual
                "predicate replacement remains unsupported at its location"
                (Elaboration.ElaborationRelationalReplacementRequiresNamedDefinition
                    predicateReplacementLocation)
                predicateReplacementFailure
            case Elaboration.elaboratedSetExpressionConstruction named of
                Just (Elaboration.ElaboratedRelationalSetConstruction construction) -> do
                    assertEqual "relational replacement canonical term"
                        expectedRelationalTerm
                        (Core.scopedCoreTerm
                            (SetConstruction.relationalSetConstructionTerm
                                construction))
                    assertEqual "relational replacement functionality"
                        expectedFunctionality
                        (Core.scopedCoreTerm
                            (SetConstruction.relationalSetConstructionFunctionality
                                construction))
                    let relationalBody =
                            SetConstruction.relationalSetConstructionClosedBody
                                construction
                        relationalAssertedObject =
                            Identity.transparentObject
                                (Identity.theoryId (fixtureFoundation fixture))
                                (Core.frozenCoreType relationalBody)
                                (Core.frozenCoreTerm relationalBody)
                        relationalObject =
                            Identity.assertedObjectId relationalAssertedObject
                        closedFunctionality =
                            SetConstruction.relationalSetConstructionClosedFunctionality
                                construction
                    relationalClosure <- expectRight
                        (Identity.extendObjectClosure
                            (fixtureClosure fixture)
                            [relationalAssertedObject])
                    let relationalTyping =
                            Identity.globalTypingFromClosure relationalClosure
                    relationalFact <-
                        maybe
                            (assertFailure
                                "exact functionality did not unlock relational extensionality"
                                >> fail "unreachable")
                            pure
                            (SetConstruction.relationalSetConstructionObjectFact
                                (SetConstruction.checkedFoundationSetConstruction
                                    (fixtureFoundation fixture))
                                relationalClosure
                                relationalObject
                                construction
                                closedFunctionality)
                    assertEqual
                        "relational replacement flattened extensional proposition"
                        (expectedRelationalExtensional relationalObject)
                        (Core.frozenCoreTerm
                            (SetConstruction.relationalSetConstructionFactProposition
                                relationalFact))
                    assertEqual
                        "unrelated functionality cannot unlock the relational view"
                        Nothing
                        (SetConstruction.relationalSetConstructionLocalViews
                            (SetConstruction.checkedFoundationSetConstruction
                                (fixtureFoundation fixture))
                            construction
                            (Core.falsumScopedCore [Core.TySet]))
                    wrongClosed <- expectRight
                        (Core.checkCanonicalCore
                            relationalTyping
                            Core.CFalsum)
                    assertBool
                        "malformed relational authority is rejected"
                        (isNothing
                            (SetConstruction.relationalSetConstructionObjectFact
                                (SetConstruction.checkedFoundationSetConstruction
                                    (fixtureFoundation fixture))
                                relationalClosure
                                relationalObject
                                construction
                                wrongClosed))
                _ ->
                    assertFailure
                        "named predicate replacement lost its relational construction"
        Declaration.DriverSucceeded
                (Left validFailure, _, _, _) _interface _prefix ->
            assertFailure
                ("valid replacement failed: "
                    <> Text.unpack
                        (Elaboration.renderElaborationError validFailure))
        Declaration.DriverSucceeded
                (_, Right{}, _, _) _interface _prefix ->
            assertFailure "invalid replacement was accepted"
        Declaration.DriverSucceeded
                (_, _, Right{}, _) _interface _prefix ->
            assertFailure "predicate replacement was accepted"
        Declaration.DriverSucceeded
                (_, _, _, Left failure) _interface _prefix ->
            assertFailure
                ("named predicate replacement failed: "
                    <> Text.unpack (Elaboration.renderElaborationError failure))
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("replacement driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("replacement driver did not seal: " <> show failure)
  where
    relApp1 intrinsic argument =
        Core.CApp (Core.CIntrinsic intrinsic) argument
    relApp2 intrinsic first second =
        Core.CApp (relApp1 intrinsic first) second
    andP = Core.CAnd
    existsP = Core.CExists Core.TySet
    relation = Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 0)
    restricted =
        relApp2 Core.Sep (Core.CBound 0)
            (Core.CLam Core.TySet (existsP relation))
    expectedRelationalTerm =
        relApp2 Core.Repl restricted
            (Core.CLam Core.TySet
                (Core.CApp
                    (Core.CLogicalSelect Core.TySet)
                    (Core.CLam Core.TySet relation)))
    expectedFunctionality =
        Core.CForall Core.TySet
            (Core.CImp
                (relApp2 Core.Member (Core.CBound 0) (Core.CBound 1))
                (Core.CForall Core.TySet
                    (Core.CForall Core.TySet
                        (Core.CImp
                            (andP
                                (Core.CEq Core.TySet
                                    (Core.CBound 2) (Core.CBound 1))
                                (Core.CEq Core.TySet
                                    (Core.CBound 2) (Core.CBound 0)))
                            (Core.CEq Core.TySet
                                (Core.CBound 1) (Core.CBound 0))))))
    expectedRelationalExtensional object =
        Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CEq Core.TyProp
                    (relApp2 Core.Member
                        (Core.CBound 0)
                        (Core.CApp
                            (Core.CGlobal object)
                            (Core.CBound 1)))
                    (existsP
                        (andP
                            (relApp2 Core.Member
                                (Core.CBound 0)
                                (Core.CBound 2))
                            (Core.CEq Core.TySet
                                (Core.CBound 0)
                                (Core.CBound 1))))))

elaboratesFiniteSets :: Assertion
elaboratesFiniteSets = do
    fixture <- makeNamedFixture "exact-finite-set"
    let location = mkLocation anonymousSourceDescriptor 2 1
        a = Raw.NamedVarAt location "a"
        b = Raw.NamedVarAt location "b"
        equality left right =
            Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (left :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (right :| [])))
        statement =
            Raw.SymbolicQuantified
                Nowhere
                Raw.Universally
                (a :| [b])
                Raw.Unbounded
                Nothing
                (equality
                    (Raw.ExprFiniteSet
                        location
                        (Raw.ExprVar a :| [Raw.ExprVar b]))
                    (Raw.ExprVar a))
        app1 intrinsic argument =
            Core.CApp (Core.CIntrinsic intrinsic) argument
        app2 intrinsic first second =
            Core.CApp (app1 intrinsic first) second
        insert element rest =
            app1 Core.FamilyUnion
                (app2 Core.PairSet
                    (app2 Core.PairSet element element)
                    rest)
        expected =
            Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CEq Core.TySet
                        (insert
                            (Core.CBound 1)
                            (insert
                                (Core.CBound 0)
                                (Core.CIntrinsic Core.Empty)))
                        (Core.CBound 1)))
        action
            :: Declaration.ModuleDriver Text
                (Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedProposition)
        action =
            Declaration.runProspectiveLoweringDriver
                (Elaboration.elaborateProposition
                    Elaboration.emptyElaborationContext
                    statement)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded
                (Right prepared) _interface _prefix ->
            assertEqual
                "source-order finite-set core"
                expected
                (Core.scopedCoreTerm
                    (Elaboration.elaboratedPropositionCore prepared))
        Declaration.DriverSucceeded
                (Left failure) _interface _prefix ->
            assertFailure
                ("valid finite set failed: "
                    <> Text.unpack
                        (Elaboration.renderElaborationError failure))
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("finite-set driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("finite-set driver did not seal: " <> show failure)

elaboratesBoundedNaturalNumerals :: Assertion
elaboratesBoundedNaturalNumerals = do
    fixture <- makeNamedFixture "natural-numeral-elaboration"
    (successorObject, basis) <- naturalNumeralFixture fixture
    let expression magnitude =
            Raw.TypedExpressionExpr
                (Raw.ExprNaturalNumeral Nowhere magnitude)
        compile magnitude =
            Elaboration.elaborateExpression
                Elaboration.emptyElaborationContext
                (expression magnitude)
        compileOpaque integer =
            Elaboration.elaborateExpression
                Elaboration.emptyElaborationContext
                (Raw.TypedExpressionExpr
                    (Raw.ExprOpaqueInteger Nowhere integer))
        absentAction
            :: Declaration.ModuleDriver
                Void
                [Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedExpression]
        absentAction =
            Declaration.runProspectiveLoweringDriver
                ((<>)
                    <$> traverse compile [0, 1, 1025]
                    <*> ((: []) <$> compileOpaque (-3)))
        checkCore label expected = \case
            Left failure ->
                assertFailure
                    (label <> ": "
                        <> Text.unpack
                            (Elaboration.renderElaborationError failure))
            Right elaborated ->
                assertEqual label expected
                    (Core.scopedCoreTerm
                        (Elaboration.elaboratedExpressionCore elaborated))

    absent <- runDriver fixture absentAction
    case absent of
        Declaration.DriverSucceeded
                [zero, one, tooLarge, opaque] _interface _prefix -> do
            checkCore "zero is the empty set" (Core.CIntrinsic Core.Empty) zero
            checkCore "opaque integer stays uninterpreted"
                (Core.COpaqueInteger (-3)) opaque
            case one of
                Left Elaboration.ElaborationNaturalNumeralBasisUnavailable{} ->
                    pure ()
                result ->
                    assertFailure
                        ("positive numeral did not report unavailable basis: "
                            <> showResult result)
            case tooLarge of
                Left
                    (Elaboration.ElaborationNaturalNumeralMagnitudeExceeded
                        _location actual supportedMaximum) -> do
                    assertEqual "rejected magnitude" 1025 actual
                    assertEqual "reported natural numeral bound"
                        1024 supportedMaximum
                result ->
                    assertFailure
                        ("oversized numeral produced the wrong result: "
                            <> showResult result)
        Declaration.DriverSucceeded results _interface _prefix ->
            assertFailure
                ("unexpected absent-basis result count: " <> show (length results))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("absent-basis driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("absent-basis driver did not seal: " <> show failure)

    let readyAction
            :: Declaration.ModuleDriver
                Void
                [Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedExpression]
        readyAction = do
            _ <- DeclTest.admitCompiled
                (Semantic.declarationSyntaxId "natural-numeral-successor")
                [successorObject] [] [] (const (pure ()))
            Declaration.runProspectiveLoweringDriver
                (traverse compile [1, 1024])
    checkedImports <- prepareTestImports (Identity.theoryId (fixtureFoundation fixture)) []
    opened <- Declaration.runModuleDriverFreshIOWithNaturalNumeralBasis
        (fixtureFoundation fixture)
        basis
        (fixtureOwner fixture)
        checkedImports
        unavailableVampireResolver
        readyAction
    ready <- expectRight opened
    case ready of
        Declaration.DriverSucceeded
                [one, maximumResult] _interface _prefix -> do
            checkNaturalSpine
                "one successor step"
                (Declaration.naturalNumeralBasisObject basis)
                1
                one
            checkNaturalSpine
                "maximum successor spine"
                (Declaration.naturalNumeralBasisObject basis)
                1024
                maximumResult
        Declaration.DriverSucceeded results _interface _prefix ->
            assertFailure
                ("unexpected ready-basis result count: " <> show (length results))
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("ready-basis driver failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("ready-basis driver did not seal: " <> show failure)
  where
    showResult = \case
        Left failure ->
            Text.unpack (Elaboration.renderElaborationError failure)
        Right _ -> "success"

    checkNaturalSpine
        :: String
        -> Identity.ObjectId
        -> Natural
        -> Either
            Elaboration.ElaborationError
            Elaboration.ElaboratedExpression
        -> Assertion
    checkNaturalSpine label successor expected = \case
        Left failure ->
            assertFailure
                (label <> ": "
                    <> Text.unpack
                        (Elaboration.renderElaborationError failure))
        Right elaborated ->
            go expected
                (Core.scopedCoreTerm
                    (Elaboration.elaboratedExpressionCore elaborated))
      where
        go 0 (Core.CIntrinsic Core.Empty) = pure ()
        go remaining (Core.CApp (Core.CGlobal actual) predecessor)
            | remaining > 0 = do
                assertEqual (label <> " successor") successor actual
                go (remaining - 1) predecessor
        go remaining term =
            assertFailure
                (label <> ": malformed spine at remaining depth "
                    <> show remaining <> ": " <> show term)

threadsNaturalNumeralReadiness :: Assertion
threadsNaturalNumeralReadiness = do
    fixture <- makeNamedFixture "natural-numeral-readiness"
    (successorObject, basis) <- naturalNumeralFixture fixture
    let observation
            :: Declaration.ModuleDriver
                Void
                (Maybe Declaration.NaturalNumeralBasis)
        observation =
            Declaration.runProspectiveLoweringDriver
                Declaration.naturalNumeralBasisLowering
        objectObservation =
            fmap Declaration.naturalNumeralBasisObject
        expectObserved label expected outcome =
            case outcome of
                Declaration.DriverSucceeded actual _interface _prefix ->
                    assertEqual label expected (objectObservation actual)
                Declaration.DriverFailed failure _prefix ->
                    assertFailure (label <> ": " <> show failure)
                Declaration.DriverSealFailed failure _prefix ->
                    assertFailure (label <> ": " <> show failure)

    legacyFresh <- runDriver fixture observation
    expectObserved "legacy fresh runner" Nothing legacyFresh

    legacyEff <- runDriverWithValidation
        fixture
        (proofOnlyValidationHandlers (const (pure Nothing)))
        observation
    expectObserved "legacy effectful runner" Nothing legacyEff

    checkedImports <- prepareTestImports (Identity.theoryId (fixtureFoundation fixture)) []
    basisFresh <- expectRight
        =<< Declaration.runModuleDriverFreshIOWithNaturalNumeralBasis
            (fixtureFoundation fixture)
            basis
            (fixtureOwner fixture)
            checkedImports
            unavailableVampireResolver
            observation
    expectObserved
        "basis-aware fresh runner"
        (Just (Declaration.naturalNumeralBasisObject basis))
        basisFresh

    basisEff <- expectRight
        =<< runEff
            (runValidationHandlers
                (proofOnlyValidationHandlers (const (pure Nothing)))
                (Declaration.runModuleDriverEffWithNaturalNumeralBasis
                    (fixtureFoundation fixture)
                    basis
                    (fixtureOwner fixture)
                    checkedImports
                    unavailableVampireResolver
                    observation))
    expectObserved
        "basis-aware effectful runner"
        (Just (Declaration.naturalNumeralBasisObject basis))
        basisEff

    let misplacedAction
            :: Declaration.ModuleDriver
                Void
                (Either
                    Elaboration.ElaborationError
                    Elaboration.ElaboratedExpression)
        misplacedAction =
            Declaration.runProspectiveLoweringDriver
                (Elaboration.elaborateExpression
                    Elaboration.emptyElaborationContext
                    (Raw.TypedExpressionExpr
                        (Raw.ExprNaturalNumeral Nowhere 1)))
        misplacedRun =
            Declaration.runModuleDriverFreshIOWithNaturalNumeralBasis
                (fixtureFoundation fixture)
                basis
                (fixtureOwner fixture)
                checkedImports
                unavailableVampireResolver
                misplacedAction
    misplaced <- Exception.try misplacedRun
        :: IO
            (Either
                Declaration.PlanningIntegrityError
                (Either
                    Declaration.DriverOpenError
                    (Declaration.DriverResult
                        Void
                        (Either
                            Elaboration.ElaborationError
                            Elaboration.ElaboratedExpression))))
    case misplaced of
        Left Declaration.PlanningIntegrityError{} -> pure ()
        Right _ ->
            assertFailure
                "basis evidence paired with a closure omitting its object"

    otherTheory <- expectRight
        (decodeCache
            Identity.getTheoryIdCache
            (ByteString.replicate 32 0x6e))
    otherClosure <- expectRight
        (Identity.validateObjectClosure otherTheory [])
    case FinalPrelude.validateFinalPreludeSuccessorObject
            (fixtureFoundation fixture)
            otherClosure
            (Identity.assertedObjectId successorObject) of
        Left FinalPrelude.FinalPreludeSemanticEnvironmentMismatch -> pure ()
        Left result ->
            assertFailure
                ("wrong-theory successor validation returned " <> show result)
        Right _ ->
            assertFailure "wrong-theory successor validation succeeded"

naturalNumeralFixture
    :: Fixture
    -> IO
        ( Identity.AssertedObject
        , Declaration.NaturalNumeralBasis
        )
naturalNumeralFixture fixture = do
    let theory = Identity.theoryId (fixtureFoundation fixture)
        successorObject =
            Identity.transparentObject
                theory
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet
                    (Core.canonicalSetInsert
                        (Core.CBound 0)
                        (Core.CBound 0)))
    closure <- expectRight
        (Identity.validateObjectClosure theory [successorObject])
    basis <- expectRight
        (FinalPrelude.validateFinalPreludeSuccessorObject
            (fixtureFoundation fixture)
            closure
            (Identity.assertedObjectId successorObject))
    pure (successorObject, basis)

elaboratesOrdinaryDeclarations :: Assertion
elaboratesOrdinaryDeclarations = do
    fixture <- makeNamedFixture "elaboration"
    level <- expectRight (Syntax.mixfixLevel 2)
    let makeSymbol command marker =
            Raw.mkMixfixItem
                [ Just (Raw.Command command)
                , Just Raw.InvisibleBraceL
                , Nothing
                , Just Raw.InvisibleBraceR
                ]
                (Raw.Marker marker)
                Raw.NonAssoc
        opaqueSymbol = makeSymbol "phasefiveopaque" "opaque-label"
        aliasSymbol = makeSymbol "phasefivealias" "alias-label"
        definitionSymbol = makeSymbol "phasefivedef" "definition-label"
        entry symbol =
            Syntax.CanonicalExpressionFunction
                (Raw.mixfixPattern symbol)
                (Raw.mixfixMarker symbol)
                (Syntax.Fixity Raw.NonAssoc level)
        parameter = Raw.NamedVar "x"
        exactSet =
            Raw.NounPhrase
                []
                (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
                (Raw.unboundedNounBinder Nothing)
                []
                Nothing
        signature =
            Raw.BlockSig
                Nowhere Nothing (Raw.Marker "opaque-declaration") []
                (Raw.SignatureSymbolic
                    (Raw.SymbolPattern opaqueSymbol [parameter])
                    exactSet)
        application symbol =
            Raw.ExprOp Nowhere symbol [Raw.ExprVar parameter]
        abbreviation =
            Raw.BlockAbbr
                Nowhere Nothing (Raw.Marker "alias-declaration")
                (Raw.AbbreviationEq
                    (Raw.SymbolPattern aliasSymbol [parameter])
                    (application opaqueSymbol))
        definition =
            Raw.BlockDefn
                Nowhere Nothing (Raw.Marker "definition-declaration")
                (Raw.DefnOp []
                    (Raw.SymbolPattern definitionSymbol [parameter])
                    (application aliasSymbol)
                    Nothing)
        compile block lexicalEntry = do
            Declaration.runProspectiveLoweringDriver
                (Binding.prepareBinding block [lexicalEntry]) >>= \case
                Left failure ->
                    Declaration.failModuleDriver
                        (Elaboration.renderElaborationError failure)
                Right prepared -> pure prepared
        admit prepared = do
            lowered <-
                Declaration.runProspectiveLoweringDriver
                    (Binding.lowerPreparedBinding prepared)
            checked <-
                either Declaration.failDeclarationDriver pure lowered
            void
                (Declaration.admitCheckedDeclaration
                    checked
                    Binding.authorizeCheckedBinding)
    outcome <- runFixtureDriver fixture [] do
        preparedSignature <-
            compile signature (entry opaqueSymbol)
        admit preparedSignature
        preparedAbbreviation <-
            compile abbreviation (entry aliasSymbol)
        admit preparedAbbreviation
        preparedDefinition <-
            compile definition (entry definitionSymbol)
        admit preparedDefinition
        pure
            ( preparedSignature
            , preparedAbbreviation
            , preparedDefinition
            )
    case outcome of
        Declaration.DriverSucceeded
                (preparedSignature, preparedAbbreviation, preparedDefinition)
                interface prefix -> do
            assertEqual "three committed declarations"
                3
                (length (Semantic.semanticInterfaceDeclarations (Declaration.evidenceInterface interface)))
            assertEqual "three committed batches"
                3
                (length (Commit.pendingModulePrefixBatches prefix))
            assertEqual "opaque signature family"
                Identity.OpaqueObject
                (Identity.objectIdFamily
                    (Binding.preparedBindingObjectId preparedSignature))
            assertEqual "transparent abbreviation family"
                Identity.TransparentObject
                (Identity.objectIdFamily
                    (Binding.preparedBindingObjectId preparedAbbreviation))
            assertEqual "transparent definition family"
                Identity.TransparentObject
                (Identity.objectIdFamily
                    (Binding.preparedBindingObjectId preparedDefinition))
            assertEqual "expanded definition coalesces with abbreviation"
                (Binding.preparedBindingObjectId preparedAbbreviation)
                (Binding.preparedBindingObjectId preparedDefinition)
            case Binding.preparedBindingObject preparedAbbreviation of
                Just object ->
                    case Identity.assertedObjectContent object of
                        Identity.TransparentObjectContent
                                _theory coreType body -> do
                            assertEqual "definition type"
                                (Core.TyArrow Core.TySet Core.TySet)
                                coreType
                            assertEqual "expanded body retains opaque seed"
                                (Core.CLam Core.TySet
                                    (Core.CApp
                                        (Core.CGlobal
                                            (Binding.preparedBindingObjectId
                                                preparedSignature))
                                        (Core.CBound 0)))
                                body
                        content ->
                            assertFailure
                                ("unexpected definition content: " <> show content)
                Nothing ->
                    assertFailure "new abbreviation object was not prepared"
            assertEqual "coalesced definition adds no object"
                Nothing
                (Binding.preparedBindingObject preparedDefinition)
            case reverse (Commit.pendingModulePrefixBatches prefix) of
                definitionBatch : _ -> do
                    case Commit.committedBatchDeclarationValidation
                            definitionBatch of
                        Just record ->
                            case Semantic.declarationValidationRecordCertificates
                                    record of
                                [certificate] -> do
                                    assertEqual "definition authority"
                                        (Authority.CheckedKernelConstruction
                                            (Authority.CheckedDefinitionEquation
                                                (Binding.preparedBindingObjectId
                                                    preparedDefinition)))
                                        (Authority.validationDirectAuthorization
                                            certificate)
                                    assertEqual "definition authority is clean"
                                        Authority.cleanAuthoritySafety
                                        (Authority.factAuthoritySafety
                                            (Authority.validationTarget
                                                certificate))
                                certificates ->
                                    assertFailure
                                        ("unexpected definition certificate count: "
                                            <> show (length certificates))
                        Nothing ->
                            assertFailure "definition has no declaration validation"
                [] -> assertFailure "definition batch is absent"
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("declaration elaboration failed: " <> show failure)
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("declaration elaboration did not seal: " <> show failure)

    let theory = Identity.theoryId (fixtureFoundation fixture)
        mismatchBody = Core.COpaqueInteger 0
        mismatchType = Core.TySet
        mismatchObject =
            Identity.transparentObject theory mismatchType mismatchBody
        mismatchId = Identity.assertedObjectId mismatchObject
    let mismatchAction
            :: Declaration.ModuleDriver Text
                ((), Commit.CommittedDeclarationBatch)
        mismatchAction =
            DeclTest.admitCompiled
                (Semantic.declarationSyntaxId "mismatched-definition-equation")
                [mismatchObject] []
                [Declaration.checkedCandidate (factSpec fixture "not-a-definition-equation")
                    (Declaration.checkedDefinitionEquationPlanning mismatchId) :| []] \case
                [candidate :| []] -> Declaration.authorizeDefinitionEquationCandidate mismatchId candidate
                _ -> error "mismatched definition fixture shape"
    mismatch <- runDriver fixture mismatchAction
    case mismatch of
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed
                    Declaration.DefinitionEquationCandidateMismatch)
                prefix ->
            assertEqual "mismatched equation publishes no batch"
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("unexpected mismatched-equation failure: " <> show failure)
        Declaration.DriverSucceeded{} ->
            assertFailure "mismatched definition equation was authorized"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("mismatched definition equation reached sealing: "
                    <> show failure)

publishesFirstOrderDefinitionsPointwise :: Assertion
publishesFirstOrderDefinitionsPointwise = do
    fixture <- makeNamedFixture "first-order-definition-equations"
    let theory = Identity.theoryId (fixtureFoundation fixture)
        publish label coreType body = do
            let object = Identity.transparentObject theory coreType body
                identity = Identity.assertedObjectId object
            (_value, batch) <- runSuccessful fixture do
                spec <- Declaration.prepareDefinitionEquationSpecDriver [object] identity (Semantic.semanticName label)
                    >>= either Declaration.failDeclarationDriver pure
                DeclTest.admitCompiled
                    (Semantic.declarationSyntaxId (TextEncoding.encodeUtf8 label)) [object] []
                    [Declaration.checkedCandidate spec (Declaration.checkedDefinitionEquationPlanning identity) :| []] \case
                    [candidate :| []] -> Declaration.authorizeDefinitionEquationCandidate identity candidate
                    _ -> error "first order definition fixture shape"
            pure (identity, batch)

        assertFirstOrder label expected batch = do
            case Commit.committedBatchPropositions batch of
                [proposition] -> do
                    assertEqual
                        (label <> " public proposition")
                        expected
                        (Core.frozenCoreTerm
                            (Identity.checkedPropositionTerm proposition))
                    assertEqual
                        (label <> " remains FOF-projectable")
                        Foundation.FoundationFofProjectable
                        (Foundation.classifyFrozenCore
                            (Identity.checkedPropositionTerm proposition))
                propositions ->
                    assertFailure
                        (label <> ": unexpected proposition count "
                            <> show (length propositions))
            case Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta batch) of
                [occurrence] ->
                    assertEqual
                        (label <> " remains implicitly searchable")
                        Semantic.SearchEligible
                        (Semantic.semanticFactSearchEligibility occurrence)
                facts ->
                    assertFailure
                        (label <> ": unexpected fact count "
                            <> show (length facts))

        predicateType =
            Core.TyArrow Core.TySet
                (Core.TyArrow Core.TySet Core.TyProp)
        predicateBody =
            Core.CLam Core.TySet
                (Core.CLam Core.TySet
                    (Core.CEq Core.TySet
                        (Core.CBound 1)
                        (Core.CBound 0)))
        functionType =
            Core.TyArrow Core.TySet
                (Core.TyArrow Core.TySet Core.TySet)
        functionValue =
            Core.CApp
                (Core.CApp
                    (Core.CIntrinsic Core.PairSet)
                    (Core.CBound 1))
                (Core.CBound 0)
        functionBody =
            Core.CLam Core.TySet
                (Core.CLam Core.TySet functionValue)
        constantBody =
            Core.CIntrinsic Core.Empty
        higherOrderArgument =
            Core.TyArrow Core.TySet Core.TyProp
        higherOrderType =
            Core.TyArrow higherOrderArgument Core.TyProp
        higherOrderBody =
            Core.CLam higherOrderArgument
                (Core.CApp
                    (Core.CBound 0)
                    (Core.CIntrinsic Core.Empty))

    (predicate, predicateBatch) <-
        publish "binary-predicate" predicateType predicateBody
    assertFirstOrder
        "binary predicate"
        (Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CEq Core.TyProp
                    (Core.CApp
                        (Core.CApp
                            (Core.CGlobal predicate)
                            (Core.CBound 1))
                        (Core.CBound 0))
                    (Core.CEq Core.TySet
                        (Core.CBound 1)
                        (Core.CBound 0)))))
        predicateBatch

    (function, functionBatch) <-
        publish "binary-function" functionType functionBody
    assertFirstOrder
        "binary function"
        (Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CEq Core.TySet
                    (Core.CApp
                        (Core.CApp
                            (Core.CGlobal function)
                            (Core.CBound 1))
                        (Core.CBound 0))
                    functionValue)))
        functionBatch

    (constant, constantBatch) <-
        publish "set-constant" Core.TySet constantBody
    assertFirstOrder
        "set constant"
        (Core.CEq Core.TySet
            (Core.CGlobal constant)
            constantBody)
        constantBatch

    (higherOrder, higherOrderBatch) <-
        publish "higher-order-definition" higherOrderType higherOrderBody
    case Commit.committedBatchPropositions higherOrderBatch of
        [proposition] -> do
            assertEqual
                "genuinely higher-order definition keeps its exact equation"
                (Core.CEq higherOrderType
                    (Core.CGlobal higherOrder)
                    higherOrderBody)
                (Core.frozenCoreTerm
                    (Identity.checkedPropositionTerm proposition))
            case Foundation.classifyFrozenCore
                    (Identity.checkedPropositionTerm proposition) of
                Foundation.FoundationRequiresTh0{} ->
                    pure ()
                Foundation.FoundationFofProjectable ->
                    assertFailure
                        "genuinely higher-order definition became FOF"
        propositions ->
            assertFailure
                ("higher-order definition: unexpected proposition count "
                    <> show (length propositions))

reconstructsImportedGlobalBindings :: Assertion
reconstructsImportedGlobalBindings = do
    producerFixture <- makeNamedFixture "global-producer"
    consumerFixture <- makeNamedFixture "global-consumer"
    equalConflictFixture <- makeNamedFixture "global-equal-conflict"
    conflictFixture <- makeNamedFixture "global-conflict"
    rootFixture <- makeNamedFixture "global-root"
    let key =
            Semantic.SemanticExpressionFunction
                (Raw.TokenCons (Raw.Command "phasefive") Raw.End)
        asserted = opaqueFixtureObject producerFixture
        target = Identity.assertedObjectId asserted
        publishWith targetMode fixture object = do
            (batch, sealed) <- sealFixture fixture [] do
                (_value, committed) <- DeclTest.admitCompiled
                    (Semantic.declarationSyntaxId "global-binding") [object]
                    [Semantic.semanticGlobalBindingWithMetadata key (Semantic.semanticBindingLabel "global-binding")
                        (targetMode (Identity.assertedObjectId object)) Nothing
                        (case (targetMode (Identity.assertedObjectId object), Identity.assertedObjectContent object) of
                            (Semantic.TransparentExpansion{}, Identity.TransparentObjectContent _ _ body) ->
                                Just (Semantic.TermExpansion (Semantic.ExpansionOpaque body))
                            _ -> Nothing)]
                    [] (const (pure ()))
                pure committed
            pure (batch, sealed)
    (producerBatch, freshProducer) <-
        publishWith Semantic.GlobalReference producerFixture asserted
    let FixtureSealed producerInterface _freshEvidence = freshProducer
        objects = Commit.committedBatchObjects producerBatch
    cachedEvidence <- expectRightIO
        (admitTestModule
            (Identity.theoryId
                (fixtureFoundation producerFixture))
            []
            producerInterface
            objects
            []
            [])
    let cachedProducer = FixtureSealed producerInterface cachedEvidence
        resolveThrough label parent = do
            expectedBinding <- expectRight
                (Semantic.materializeResolvedGlobalBinding
                    (const Nothing)
                    (const Nothing)
                    (fixtureClosure producerFixture)
                    (Semantic.declarationSlot
                        (fixtureOwner producerFixture)
                        (localDeclarationOrdinal 0))
                    (Semantic.semanticGlobalBinding
                        key
                        (Semantic.semanticBindingLabel "global-binding")
                        (Semantic.GlobalReference target)))
            outcome <- runFixtureDriver consumerFixture [parent]
                (Declaration.resolveVisibleGlobalDriver key)
            case outcome of
                Declaration.DriverSucceeded found _interface _prefix ->
                    assertEqual label
                        (Just
                            ( expectedBinding
                            , Core.TySet
                            ))
                        found
                Declaration.DriverFailed failure _prefix ->
                    assertFailure
                        ("global binding consumer failed: " <> show failure)
                Declaration.DriverSealFailed failure _prefix ->
                    assertFailure
                        ("global binding consumer did not seal: " <> show failure)
    resolveThrough "fresh-global-binding" freshProducer
    resolveThrough "cached-global-binding" cachedProducer

    (_equalConflictBatch, equalTargetConflict) <-
        publishWith
            Semantic.GlobalReference
            equalConflictFixture
            asserted
    equalTargetCollision <- prepareFixtureImports rootFixture
        [freshProducer, equalTargetConflict]
    case equalTargetCollision of
        Left (Declaration.ImportedGlobalCollision
                actualKey firstBinding secondBinding) -> do
            assertEqual "equal-target colliding key" key actualKey
            assertEqual "equal imported targets"
                (Semantic.semanticGlobalBindingTarget
                    (Semantic.resolvedBindingDeclaration firstBinding))
                (Semantic.semanticGlobalBindingTarget
                    (Semantic.resolvedBindingDeclaration secondBinding))
            assertBool "independent owners remain distinct"
                (Semantic.globalBindingRefOwner
                    (Semantic.resolvedBindingRef firstBinding)
                 /= Semantic.globalBindingRefOwner
                    (Semantic.resolvedBindingRef secondBinding))
        Left failure ->
            assertFailure
                ("unexpected equal-target collision: " <> show failure)
        Right _ ->
            assertFailure
                "independently owned equal-target bindings did not collide"

    missingEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta
            [Semantic.semanticGlobalBinding
                key
                (Semantic.semanticBindingLabel "missing-global")
                (Semantic.GlobalReference target)])
    missingDelta <- expectRight
        (Semantic.declarationInterfaceDelta
            (Semantic.declarationSlot
                (fixtureOwner producerFixture)
                (localDeclarationOrdinal 0))
            []
            []
            []
            []
            []
            []
            missingEnvironment)
    missingInterface <- expectRight
        (Semantic.semanticInterface
            (fixtureOwner producerFixture)
            []
            [missingDelta])
    admitTestModule
            (Identity.theoryId
                (fixtureFoundation producerFixture))
            []
            missingInterface
            []
            []
            [] >>= \case
        Left (Declaration.ImportedGlobalTargetInvalid
                actualKey actualTarget
                (Semantic.SemanticGlobalTargetMissing missingTarget)) -> do
            assertEqual "missing target key" key actualKey
            assertEqual "missing target mode"
                (Semantic.GlobalReference target)
                actualTarget
            assertEqual "missing target object" target missingTarget
        Left failure ->
            assertFailure
                ("unexpected missing-target failure: " <> show failure)
        Right _evidence ->
            assertFailure "cached evidence accepted a missing target object"

    expansionEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta
            [Semantic.semanticGlobalBinding
                key
                (Semantic.semanticBindingLabel "expansion-global")
                (Semantic.TransparentExpansion target)])
    expansionDelta <- expectRight
        (Semantic.declarationInterfaceDelta
            (Semantic.declarationSlot
                (fixtureOwner producerFixture)
                (localDeclarationOrdinal 0))
            []
            []
            [target]
            []
            []
            []
            expansionEnvironment)
    expansionInterface <- expectRight
        (Semantic.semanticInterface
            (fixtureOwner producerFixture) [] [expansionDelta])
    admitTestModule
            (Identity.theoryId
                (fixtureFoundation producerFixture))
            []
            expansionInterface
            [asserted]
            []
            [] >>= \case
        Left (Declaration.ImportedGlobalTargetInvalid
                actualKey actualTarget
                (Semantic.SemanticGlobalExpansionNotTransparent
                    invalidTarget)) -> do
            assertEqual "nontransparent target key" key actualKey
            assertEqual "nontransparent target mode"
                (Semantic.TransparentExpansion target)
                actualTarget
            assertEqual "nontransparent target object" target invalidTarget
        Left failure ->
            assertFailure
                ("unexpected nontransparent-target failure: "
                    <> show failure)
        Right _evidence ->
            assertFailure "cached evidence accepted a nontransparent expansion"

    let intrinsicObject = Identity.intrinsicObject
            (Identity.theoryId (fixtureFoundation producerFixture))
            Core.Empty
        intrinsicTarget = Identity.assertedObjectId intrinsicObject
    intrinsicFailure <- runFixtureDriver producerFixture []
        (DeclTest.admitCompiled (Semantic.declarationSyntaxId "intrinsic-global-binding") [intrinsicObject]
            [Semantic.semanticGlobalBinding key (Semantic.semanticBindingLabel "intrinsic-global")
                (Semantic.GlobalReference intrinsicTarget)] [] (const (pure ())))
    case intrinsicFailure of
        Declaration.DriverFailed
                (Declaration.DriverDeclarationFailed
                    (Declaration.DeclarationGlobalTargetInvalid
                        actualKey actualTarget
                        (Semantic.SemanticGlobalTargetIsIntrinsic
                            invalidTarget)))
                _prefix -> do
            assertEqual "intrinsic target key" key actualKey
            assertEqual "intrinsic target mode"
                (Semantic.GlobalReference intrinsicTarget)
                actualTarget
            assertEqual "intrinsic target object"
                intrinsicTarget invalidTarget
        other ->
            assertFailure
                (case other of
                    Declaration.DriverSucceeded{} ->
                        "ordinary binding accepted an intrinsic target"
                    Declaration.DriverFailed failure _prefix ->
                        "unexpected intrinsic-target failure: " <> show failure
                    Declaration.DriverSealFailed failure _prefix ->
                        "intrinsic target reached sealing: " <> show failure)

    conflictObject <- pure (opaqueFixtureObject conflictFixture)
    (_conflictBatch, conflicting) <-
        publishWith Semantic.GlobalReference conflictFixture conflictObject
    collision <- prepareFixtureImports rootFixture
        [freshProducer, conflicting]
    case collision of
        Left (Declaration.ImportedGlobalCollision
                actualKey firstTarget secondTarget) -> do
            assertEqual "colliding global key" key actualKey
            assertEqual "first imported target"
                (Semantic.GlobalReference target)
                (Semantic.semanticGlobalBindingTarget
                    (Semantic.resolvedBindingDeclaration firstTarget))
            assertEqual "second imported target"
                (Semantic.GlobalReference
                    (Identity.assertedObjectId conflictObject))
                (Semantic.semanticGlobalBindingTarget
                    (Semantic.resolvedBindingDeclaration secondTarget))
        Left failure ->
            assertFailure
                ("unexpected imported collision: " <> show failure)
        Right _ ->
            assertFailure "unequal imported bindings did not collide"

    let theory = Identity.theoryId (fixtureFoundation producerFixture)
        transparentBody = Core.COpaqueInteger 0
        transparentObject =
            Identity.transparentObject theory Core.TySet transparentBody
        transparentTarget = Identity.assertedObjectId transparentObject
    (_referenceBatch, referenceProducer) <-
        publishWith
            Semantic.GlobalReference
            producerFixture
            transparentObject
    (_expansionBatch, expansionProducer) <-
        publishWith
            Semantic.TransparentExpansion
            conflictFixture
            transparentObject
    modeCollision <- prepareFixtureImports rootFixture
        [referenceProducer, expansionProducer]
    case modeCollision of
        Left (Declaration.ImportedGlobalCollision
                actualKey firstTarget secondTarget) -> do
            assertEqual "mode collision key" key actualKey
            assertEqual "reference target"
                (Semantic.GlobalReference transparentTarget)
                (Semantic.semanticGlobalBindingTarget
                    (Semantic.resolvedBindingDeclaration firstTarget))
            assertEqual "expansion target"
                (Semantic.TransparentExpansion transparentTarget)
                (Semantic.semanticGlobalBindingTarget
                    (Semantic.resolvedBindingDeclaration secondTarget))
        Left failure ->
            assertFailure ("unexpected mode-collision failure: " <> show failure)
        Right _ ->
            assertFailure "different global target modes did not collide"

    let contractObject = Identity.transparentObject
            theory
            (Core.TyArrow Core.TySet Core.TyProp)
            (Core.CLam Core.TySet Core.CTruth)
        contractTarget = Identity.assertedObjectId contractObject
        contractOwner = fixtureOwner producerFixture
        firstSlot = Semantic.declarationSlot contractOwner
            (localDeclarationOrdinal 0)
        laterSlot = Semantic.declarationSlot contractOwner
            (localDeclarationOrdinal 1)
        wordPattern word = Raw.TokenCons (Raw.Word word) Raw.End
        contractHostKey = Semantic.SemanticNoun
            (wordPattern "contract-host") (wordPattern "contract-hosts")
        contractRequirementKey = Semantic.SemanticNoun
            (wordPattern "contract-requirement")
            (wordPattern "contract-requirements")
        laterReference = Semantic.globalBindingRef
            laterSlot contractRequirementKey
        sameDeltaReference = Semantic.globalBindingRef
            firstSlot contractRequirementKey
        requirement reference = Semantic.GlobalAtomTemplate
            (Semantic.NounNotionHead reference)
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
        hostBinding reference = Semantic.semanticGlobalBindingWithContract
            contractHostKey
            (Semantic.semanticBindingLabel "contract-host")
            (Semantic.GlobalReference contractTarget)
            (Just
                (Semantic.formationContract
                    (Semantic.AtomicLeaf (requirement reference) :| [])))
        requirementBinding = Semantic.semanticGlobalBinding
            contractRequirementKey
            (Semantic.semanticBindingLabel "contract-requirement")
            (Semantic.GlobalReference contractTarget)
        makeDelta slot objectIds bindings = do
            environment <- expectRight
                (Semantic.semanticEnvironmentDelta
                    (List.sortOn Semantic.semanticGlobalBindingKey bindings))
            expectRight
                (Semantic.declarationInterfaceDelta
                    slot
                    []
                    []
                    objectIds
                    []
                    []
                    []
                    environment)
    forwardHostDelta <- makeDelta firstSlot [contractTarget]
        [hostBinding laterReference]
    laterRequirementDelta <- makeDelta laterSlot [] [requirementBinding]
    forwardInterface <- expectRight
        (Semantic.semanticInterface
            contractOwner [] [forwardHostDelta, laterRequirementDelta])
    admitTestModule
            theory
            []
            forwardInterface
            [contractObject]
            []
            [] >>= \case
        Left (Declaration.GlobalFormationContractInvalid
                actualHost
                (Semantic.FormationContractGlobalBindingMissing missing)) -> do
            assertEqual "forward contract host"
                (Semantic.globalBindingRef firstSlot contractHostKey)
                actualHost
            assertEqual "later contract requirement" laterReference missing
        Left failure ->
            assertFailure
                ("unexpected forward-contract failure: " <> show failure)
        Right _evidence ->
            assertFailure
                "imported contract resolved through a later declaration"

    sameDelta <- makeDelta firstSlot [contractTarget]
        [hostBinding sameDeltaReference, requirementBinding]
    sameDeltaInterface <- expectRight
        (Semantic.semanticInterface contractOwner [] [sameDelta])
    _ <- expectRightIO
        (admitTestModule
            theory
            []
            sameDeltaInterface
            [contractObject]
            []
            [])
    pure ()

data FixtureSealed = FixtureSealed
    !Semantic.SemanticInterface
    !Declaration.ImportedModuleEvidence

checksCachedLocalScope :: Assertion
checksCachedLocalScope = do
    fixture <- makeNamedFixture "cached-local-scope"
    let theory = Identity.theoryId (fixtureFoundation fixture)
        owner = fixtureOwner fixture
        hidden = opaqueFixtureObject fixture
        hiddenId = Identity.assertedObjectId hidden
        dependent = Identity.transparentObject theory Core.TySet (Core.CGlobal hiddenId)
        makeDelta ordinal objects propositions = expectRight
            (Semantic.declarationInterfaceDelta
                (Semantic.declarationSlot owner (localDeclarationOrdinal ordinal))
                []
                []
                objects
                propositions
                []
                []
                Semantic.emptySemanticEnvironmentDelta)
        admit deltas objects propositions = do
            interface <- expectRight (Semantic.semanticInterface owner [] deltas)
            check <- Declaration.newImportCheck (fixtureFoundation fixture)
            prepared <- expectRightIO (Declaration.prepareImports check [])
            result <- Declaration.admitCachedModuleEvidence prepared interface objects propositions []
            work <- Declaration.importCheckWork check
            pure (result, work)
        candidate term = do
            reentered <- expectRight (Identity.identifyAndReenterCanonicalTerm
                (encodeCanonicalTerm Identity.objectIdBuilder term))
            expectRight (Identity.storedPropositionCandidate
                (Identity.propositionIdOf term) reentered)
    -- The additional supplied object is outside the explicit local inventory.
    onlyDependent <- makeDelta 0 [Identity.assertedObjectId dependent] []
    (outOfScope, _) <- admit [onlyDependent] [hidden, dependent] []
    case outOfScope of
        Left Declaration.DeclarationObjectValidationFailed{} -> pure ()
        Left failure -> assertFailure (show failure)
        Right _ -> assertFailure "an undeclared supplied dependency became visible"
    earlier <- makeDelta 0 [Identity.assertedObjectId dependent] []
    later <- makeDelta 1 [hiddenId] []
    (moduleWide, _) <- admit [earlier, later] [hidden, dependent] []
    case moduleWide of
        Left (Declaration.DeclarationObjectValidationFailed
                (Identity.CheckedContributionDependencyMissing actual)) ->
            assertEqual "later objects do not enter the declaration prefix" hiddenId actual
        Left failure -> assertFailure (show failure)
        Right _ -> assertFailure "a later local object became visible to an earlier declaration"
    declaredFirst <- makeDelta 0 [hiddenId] []
    declaredSecond <- makeDelta 1 [Identity.assertedObjectId dependent] []
    (ordered, _) <- admit [declaredFirst, declaredSecond] [hidden, dependent] []
    _ <- expectRight ordered
    repeated <- makeDelta 2 [Identity.assertedObjectId dependent] []
    (duplicate, _) <- admit [declaredFirst, declaredSecond, repeated] [hidden, dependent] []
    case duplicate of
        Left Declaration.DeclarationObjectValidationFailed{} -> pure ()
        Left failure -> assertFailure (show failure)
        Right _ -> assertFailure "duplicate local object declarations were coalesced"
    malformed <- candidate (Core.CApp Core.CTruth Core.CTruth)
    unused <- makeDelta 0 [] [Identity.storedPropositionCandidateId malformed]
    (badUnused, badWork) <- admit [unused] [] [malformed]
    case badUnused of
        Left Declaration.DeclarationPropositionValidationFailed{} -> pure ()
        Left failure -> assertFailure (show failure)
        Right _ -> assertFailure "an unused ill-typed declared proposition was skipped"
    assertEqual "rejected proposition check is counted at entry" 1
        (Declaration.importPropositionChecks badWork)

checksExactImportNodes :: Assertion
checksExactImportNodes = do
    fixture <- makeNamedFixture "independent-import-node"
    let theory = Identity.theoryId (fixtureFoundation fixture)
        owner = fixtureOwner fixture
        proposition = fixtureProposition fixture
        authority = Authority.factAuthority
            (Identity.theoremRef theory (Identity.checkedPropositionId proposition))
            Authority.cleanAuthoritySafety
        occurrence = Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
            (Semantic.factSlot owner (localFactOrdinal 0)) authority Semantic.SearchEligible
        fingerprint = Semantic.semanticFactFingerprint occurrence
        request = Authority.preparedRequestId Authority.PreparedRequestFof
            Authority.PreparedRequestDirect "independent-certificate"
    delta <- expectRight (Semantic.declarationInterfaceDelta
        (Semantic.declarationSlot owner (localDeclarationOrdinal 0))
        [occurrence]
        []
        []
        [Identity.checkedPropositionId proposition]
        []
        []
        Semantic.emptySemanticEnvironmentDelta)
    semantic <- expectRight (Semantic.semanticInterface owner [] [delta])
    firstCertificate <- expectRight (Authority.validationCertificate authority
        (Authority.CheckedSourceProof Authority.NoExternalProofUse))
    secondCertificate <- expectRight (Authority.validationCertificate authority
        (Authority.CheckedSourceProof (Authority.UsesExternalProof (request :| []))))
    first <- expectRightIO (admitTestModule theory [] semantic [] [proposition] [firstCertificate])
    second <- expectRightIO (admitTestModule theory [] semantic [] [proposition] [secondCertificate])
    check <- Declaration.newImportCheck (fixtureFoundation fixture)
    _ <- expectRightIO (Declaration.prepareImports check [first, first])
    Declaration.prepareImports check [first, second] >>= \case
        Left (Declaration.ImportedFactCollision actual) ->
            assertEqual "independent equal semantic IDs compare certificates" fingerprint actual
        Left failure -> assertFailure (show failure)
        Right _ -> assertFailure "semantic identity incorrectly skipped an independent node"
    -- Distinct wrappers exercise the same disagreement through a diamond.
    leftOwner <- fixtureOwner <$> makeNamedFixture "independent-left"
    rightOwner <- fixtureOwner <$> makeNamedFixture "independent-right"
    leftSemantic <- expectRight (Semantic.semanticInterface leftOwner
        [Semantic.semanticInterfaceAssertedId semantic] [])
    rightSemantic <- expectRight (Semantic.semanticInterface rightOwner
        [Semantic.semanticInterfaceAssertedId semantic] [])
    left <- expectRightIO (admitTestModule theory [first] leftSemantic [] [] [])
    right <- expectRightIO (admitTestModule theory [second] rightSemantic [] [] [])
    Declaration.prepareImports check [left, right] >>= \case
        Left Declaration.ImportedFactCollision{} -> pure ()
        Left failure -> assertFailure (show failure)
        Right _ -> assertFailure "diamond skipped independent equal-identity ancestors"

reusesParentPreparation :: Assertion
reusesParentPreparation = do
    baseFixture <- makeNamedFixture "memo-base"
    leftFixture <- makeNamedFixture "memo-left"
    rightFixture <- makeNamedFixture "memo-right"
    (base, _) <- sealFactFixture baseFixture [] "memo-base-fact"
    FixtureSealed _ left <- snd <$> sealFixture leftFixture [base] (pure ())
    FixtureSealed _ right <- snd <$> sealFixture rightFixture [base] (pure ())
    check <- Declaration.newImportCheck (fixtureFoundation baseFixture)
    _ <- expectRightIO (Declaration.prepareImports check [left, right])
    initial <- Declaration.importCheckWork check
    assertEqual "one missing diamond branch is inserted" 1
        (Declaration.importContributionInsertions initial)
    assertEqual "only direct roots and the missing branch's parent are visited" 3
        (Declaration.importNodeVisits initial)
    _ <- expectRightIO (Declaration.prepareImports check [left, right])
    repeated <- Declaration.importCheckWork check
    assertEqual "repeat adds only one memo hit"
        initial{Declaration.importParentMemoHits = 1} repeated
    -- Concurrent misses may duplicate pure work; all returned contexts agree.
    concurrent <- Declaration.newImportCheck (fixtureFoundation baseFixture)
    results <- Async.mapConcurrently
        (\_ -> Declaration.prepareImports concurrent [left, right]) [1 :: Int .. 8]
    for_ results \result -> do
        prepared <- expectRight result
        assertEqual "concurrent preparation preserves ordered inputs"
            [ Semantic.semanticInterfaceAssertedId (Declaration.evidenceInterface left)
            , Semantic.semanticInterfaceAssertedId (Declaration.evidenceInterface right)
            ] (Declaration.preparedImportIds prepared)
    worker <- Async.async (Declaration.prepareImports concurrent [right, left])
    Async.cancel worker
    _ <- Timeout.timeout 1000000 (Declaration.prepareImports concurrent [right, left])
        >>= maybe (assertFailure "cancelled preparation left the memo locked" >> fail "unreachable") pure
        >>= expectRight
    work <- Declaration.importCheckWork concurrent
    assertEqual "composition performs no object checking" 0 (Declaration.importObjectClosureChecks work)
    assertEqual "composition performs no proposition checking" 0 (Declaration.importPropositionChecks work)
    assertEqual "composition performs no occurrence checking" 0 (Declaration.importOccurrenceChecks work)
    assertEqual "composition performs no composition-metadata checking" 0 (Declaration.importCompositionChecks work)
    assertEqual "composition performs no environment materialization" 0 (Declaration.importEnvironmentMaterializations work)
    assertEqual "composition performs no structure topology checking" 0 (Declaration.importStructureChecks work)
    assertEqual "composition performs no definition checking" 0 (Declaration.importDefinitionChecks work)
    assertEqual "composition performs no registration checking" 0 (Declaration.importRegistrationChecks work)

matchesSmallImportGraphs :: Assertion
matchesSmallImportGraphs =
    for_ graphs \(label, edges) -> do
        nodes <- foldM (addNode label) [] (zip [0 :: Int ..] edges)
        for_ (zip [0 :: Int ..] edges) \(index, parents) -> do
            fixture <- makeNamedFixture (label <> "-consumer-" <> shown index)
            direct <- traverse (requireNode nodes) parents
            (observed, _) <- sealFixture fixture (fst <$> direct)
                (Declaration.runProspectiveLoweringDriver
                    (traverse
                        (\(_, fingerprint) ->
                            isJust <$> Declaration.resolveVisibleFactLowering
                                fingerprint)
                        nodes))
            let reachable = ancestors edges Set.empty parents
            assertEqual (Text.unpack label <> " node " <> show index)
                [candidate `Set.member` reachable | candidate <- [0 .. length nodes - 1]]
                observed
  where
    graphs =
        [ ("chain", [[], [0], [0, 1], [0, 2], [0, 3]])
        , ("diamonds", [[], [0], [0], [1, 2], [3], [3], [4, 5, 0]])
        , ("siblings", [[], [], [0, 1], [0, 1], [0, 1], [2, 3, 4]])
        ]
    shown = Text.pack . show
    requireNode nodes index =
        maybe (fail "invalid import graph fixture") pure
            (nth (fromIntegral index) nodes)
    addNode label nodes (index, parents) = do
        fixture <- makeNamedFixture (label <> "-" <> shown index)
        direct <- traverse (requireNode nodes) parents
        node <- sealFactFixture fixture (fst <$> direct)
            (label <> "-fact-" <> shown index)
        pure (nodes <> [node])
    ancestors edges seen = \case
        [] -> seen
        index : remaining
            | index `Set.member` seen -> ancestors edges seen remaining
            | otherwise ->
                let parents = fromMaybe (impossible "invalid import graph edge")
                        (nth (fromIntegral index) edges)
                in ancestors edges (Set.insert index seen) (parents <> remaining)

keepsImportedDefinitionSelection :: Assertion
keepsImportedDefinitionSelection = do
    producerFixture <- makeNamedFixture "retained-definition-producer"
    consumerFixture <- makeNamedFixture "retained-definition-consumer"
    let theory = Identity.theoryId (fixtureFoundation producerFixture)
        asserted = Identity.transparentObject theory Core.TySet
            (Core.CIntrinsic Core.Empty)
        object = Identity.assertedObjectId asserted
        define syntax objects name = do
            spec <- Declaration.prepareDefinitionEquationSpecDriver objects object (Semantic.semanticName name)
                >>= either Declaration.failDeclarationDriver pure
            DeclTest.admitCompiled (Semantic.declarationSyntaxId syntax) objects []
                [Declaration.checkedCandidate spec (Declaration.checkedDefinitionEquationPlanning object) :| []] \case
                [candidate :| []] -> Declaration.authorizeDefinitionEquationCandidate object candidate
                _ -> error "retained definition fixture shape"
    (producerBatch, producer) <- sealFixture producerFixture []
        (snd <$> define "retained-definition-producer" [asserted] "retained-definition-first")
    expected <- case Semantic.declarationDeltaDefinitionViews
            (Commit.committedBatchDelta producerBatch) of
        [view] -> pure (Semantic.semanticDefinitionViewTarget view)
        _ -> fail "expected one producer definition view"
    let FixtureSealed producerInterface _ = producer
    cached <- expectRightIO (admitTestModule theory [] producerInterface
        (Commit.committedBatchObjects producerBatch)
        (Commit.committedBatchPropositions producerBatch)
        (Commit.committedBatchValidationCertificates producerBatch))
    secondFixture <- makeNamedFixture "retained-definition-other"
    wrapperFixture <- makeNamedFixture "retained-definition-larger-parent"
    (otherBatch, other) <- sealFixture secondFixture []
        (snd <$> define "retained-definition-other" [asserted] "retained-definition-other")
    otherTarget <- case Semantic.declarationDeltaDefinitionViews
            (Commit.committedBatchDelta otherBatch) of
        [view] -> pure (Semantic.semanticDefinitionViewTarget view)
        _ -> fail "expected one other definition view"
    larger <- snd <$> sealFixture wrapperFixture [other] (pure ())
    -- The second parent wins the physical seed in the first two cases.
    for_ [ ([producer, larger], expected)
         , ([FixtureSealed producerInterface cached, larger], expected)
         , ([larger, producer], otherTarget)
         ] \(parents, selectedTarget) -> do
        ((consumerBatch, views), _) <- sealFixture consumerFixture parents do
            (_, batch) <- define "retained-definition-consumer" [] "retained-definition-second"
            selected <- Declaration.runProspectiveLoweringDriver
                (Declaration.resolveVisibleDefinitionViewsLowering object)
            pure (batch, selected)
        assertEqual "equivalent local definition retains imported selection"
            [selectedTarget] (Declaration.resolvedDefinitionViewFingerprint <$> views)
        assertEqual "local definition exports no replacement view" []
            (Semantic.declarationDeltaDefinitionViews
                (Commit.committedBatchDelta consumerBatch))
        assertEqual "local defining fact remains exported" 1
            (length (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta consumerBatch)))

foldsTransitiveAndDiamondEvidence :: Assertion
foldsTransitiveAndDiamondEvidence = do
    baseFixture <- makeNamedFixture "base"
    middleFixture <- makeNamedFixture "middle"
    transitiveFixture <- makeNamedFixture "transitive"
    leftFixture <- makeNamedFixture "left"
    rightFixture <- makeNamedFixture "right"
    diamondFixture <- makeNamedFixture "diamond"
    conflictLeftFixture <- makeNamedFixture "conflict-left"
    conflictRightFixture <- makeNamedFixture "conflict-right"
    conflictRootFixture <- makeNamedFixture "conflict-root"

    (base, baseFingerprint) <-
        sealFactFixture baseFixture [] "transitive-shared"
    middle <- snd <$> sealFixture middleFixture [base] (pure ())
    transitive <- sealUsingImportedFact
        transitiveFixture [middle] baseFingerprint
    assertLocalFactOrdinalZero "transitive importer" transitive

    left <- snd <$> sealFixture leftFixture [base] (pure ())
    right <- snd <$> sealFixture rightFixture [base] (pure ())
    diamond <- sealUsingImportedFact
        diamondFixture [left, right] baseFingerprint
    assertLocalFactOrdinalZero "diamond importer" diamond

    (conflictLeft, leftFingerprint) <-
        sealFactFixture conflictLeftFixture [] "diamond-conflict"
    (conflictRight, rightFingerprint) <-
        sealFactFixture conflictRightFixture [] "diamond-conflict"
    conflict <- prepareFixtureImports conflictRootFixture
        [conflictLeft, conflictRight]
    case conflict of
        Left (Declaration.ImportedAliasCollision
                        alias
                        (Declaration.ImportedAliasOrigin
                            _leftSlot firstTarget)
                        (Declaration.ImportedAliasOrigin
                            _rightSlot secondTarget)) -> do
            assertEqual "conflicting alias"
                (Semantic.semanticName "diamond-conflict")
                alias
            assertEqual "first alias origin"
                leftFingerprint
                firstTarget
            assertEqual "second alias origin"
                rightFingerprint
                secondTarget
        _ ->
            assertFailure "conflicting diamond alias was not rejected"
  where
    sealUsingImportedFact fixture parents fingerprint = do
        (batch, _sealed) <- sealFixture fixture parents do
            (_value, committed) <- DeclTest.admitProof
                (Semantic.proofSyntaxId "use-transitive-import") []
                    (Declaration.checkedCandidate (factSpec fixture "local-after-import")
                        (Declaration.checkedOmittedPlanning [] [fingerprint] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate do
                        void (Declaration.useAuthorizedFact fingerprint)
                        Declaration.recordOmittedUse
            pure committed
        pure batch

    assertLocalFactOrdinalZero label batch =
        case Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta batch) of
            [occurrence] ->
                assertEqual label
                    (localFactOrdinal 0)
                    (Semantic.factSlotOrdinal
                        (Semantic.semanticFactSlot occurrence))
            facts ->
                assertFailure
                    (label <> ": unexpected fact count "
                        <> show (length facts))

sealFactFixture
    :: Fixture
    -> [FixtureSealed]
    -> Text
    -> IO
        ( FixtureSealed
        , Semantic.SemanticFactOccurrenceFingerprint
        )
sealFactFixture fixture parents alias = do
    (batch, sealed) <- sealFixture fixture parents do
        (_value, committed) <- DeclTest.admitProof
            (Semantic.proofSyntaxId
                (TextEncoding.encodeUtf8 alias)) []
                (Declaration.checkedCandidate (factSpec fixture alias) Declaration.checkedSourceAxiomPlanning) \candidate -> do
                Declaration.authorizeSourceAxiomCandidate candidate
        pure committed
    case Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch) of
        [occurrence] ->
            pure
                ( sealed
                , Semantic.semanticFactFingerprint occurrence
                )
        facts ->
            assertFailure
                ("unexpected sealed fact count: " <> show (length facts))
                >> fail "unreachable"

sealFixture
    :: Fixture
    -> [FixtureSealed]
    -> Declaration.ModuleDriver Text value
    -> IO (value, FixtureSealed)
sealFixture fixture parents action = do
    outcome <- runFixtureDriver fixture parents action
    case outcome of
        Declaration.DriverSucceeded value evidence _prefix ->
            pure (value, FixtureSealed (Declaration.evidenceInterface evidence) evidence)
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("fixture failed: " <> show failure)
                >> fail "unreachable"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("fixture did not seal: " <> show failure)
                >> fail "unreachable"

prepareFixtureImports
    :: Fixture
    -> [FixtureSealed]
    -> IO (Either Declaration.DeclarationError Declaration.PreparedImports)
prepareFixtureImports fixture parents = do
    check <- Declaration.newImportCheck (fixtureFoundation fixture)
    Declaration.prepareImports check [evidence | FixtureSealed _ evidence <- parents]

runFixtureDriver
    :: Fixture
    -> [FixtureSealed]
    -> Declaration.ModuleDriver Text value
    -> IO (Declaration.DriverResult Text value)
runFixtureDriver fixture parents action = do
    imports <- prepareTestImports (Identity.theoryId (fixtureFoundation fixture))
        [evidence | FixtureSealed _ evidence <- parents]
    expectRight =<< Declaration.runModuleDriverFreshIO
        (fixtureFoundation fixture) (fixtureOwner fixture) imports
        unavailableVampireResolver action

requireSingleOccurrence
    :: Commit.CommittedDeclarationBatch
    -> Declaration.ModuleDriver
        Declaration.DeclarationError
        Semantic.SemanticFactOccurrence
requireSingleOccurrence batch =
    case Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch) of
        [occurrence] ->
            pure occurrence
        _ ->
            Declaration.failModuleDriver
                Declaration.ProofDeclarationMustProduceOneFact

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left err ->
        assertFailure (show err) >> fail "unreachable"
    Right value ->
        pure value

expectRightIO :: Show error => IO (Either error value) -> IO value
expectRightIO action =
    action >>= expectRight

withOpenedStore
    :: Fixture
    -> FilePath
    -> (Store.Store -> IO value)
    -> IO value
withOpenedStore fixture root action =
    bracket
        (expectRightIO
            (Store.openStore
                (root Posix.</> "store.sqlite")
                (Identity.theoryId (fixtureFoundation fixture))))
        (Store.closeStore . snd)
        (action . snd)

withTemporaryDirectory :: String -> (FilePath -> IO a) -> IO a
withTemporaryDirectory template =
    bracket create Directory.removePathForcibly
  where
    create = do
        root <- Directory.getTemporaryDirectory
        (path, handle) <- openTempFile root template
        hClose handle
        Directory.removeFile path
        Directory.createDirectory path
        pure path

scopesBoundedNouns :: Assertion
scopesBoundedNouns = do
    fixture <- makeNamedFixture "bounded-noun-scopes"
    context <- expectRight (Elaboration.extendElaborationContext
        ((Elaboration.localId 0, "F") :| []) Elaboration.emptyElaborationContext)
    let x = Raw.NamedVar "x"
        y = Raw.NamedVar "y"
        bound endpoint = Raw.Bounded Nowhere Raw.Positive
            (Raw.Relation Nowhere Raw.ElementSymbol []) endpoint
        phrase names endpoint = Raw.NounPhrase []
            (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
            (Raw.NounBinder names (bound endpoint)) [] Nothing
        member a b = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) a) b
        forallP = Core.CForall Core.TySet
        existsP = Core.CExists Core.TySet
        truth = Core.CEq Core.TySet (Core.COpaqueInteger 0) (Core.COpaqueInteger 0)
        statement = Raw.StmtFormula (Raw.FormulaChain (Raw.ChainBase
            (Raw.ExprOpaqueInteger Nowhere 0 :| []) Raw.Positive
            (Raw.Relation Nowhere Raw.EqSymbol [])
            (Raw.ExprOpaqueInteger Nowhere 0 :| [])))
        group = phrase [x,y] (Raw.ExprVar "F")
        restriction = Core.CAnd (member (Core.CBound 1) (Core.CBound 2))
            (member (Core.CBound 0) (Core.CBound 2))
        quantified q = Raw.StmtQuantPhrase Nowhere (Raw.QuantPhrase q group) statement
        setStatement = Raw.StmtNoun Raw.Positive (Raw.TermExpr (Raw.ExprVar x) :| [])
            (Raw.NounPhrase [] (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
                (Raw.unboundedNounBinder Nothing) [] Nothing)
        subject = Raw.TermQuantified Raw.Existentially Nowhere
            (phrase (Just x) (Raw.ExprVar "F"))
        distributed argument = Raw.StmtVerbPhrase (Raw.TermExpr (Raw.ExprOpaqueInteger Nowhere 0) :|
                [Raw.TermExpr (Raw.ExprOpaqueInteger Nowhere 1)])
            (Raw.VPVerb (Raw.Verb Nowhere Lexicon.builtinEqualityVerb [argument]))
        cases =
            [ ("universal shared endpoint", quantified Raw.Universally,
                forallP (forallP (Core.CImp restriction truth)))
            , ("existential whole group", quantified Raw.Existentially,
                existsP (existsP (Core.CAnd restriction truth)))
            , ("nonexistential whole group", quantified Raw.Nonexistentially,
                Core.CNot (existsP (existsP (Core.CAnd restriction truth))))
            , ("existential without a body", Raw.StmtExists Nowhere group,
                existsP (existsP restriction))
            , ("existential noun restriction retains a truth body",
                Raw.StmtQuantPhrase Nowhere (Raw.QuantPhrase Raw.Existentially group) setStatement,
                existsP (existsP (Core.CAnd restriction Core.CTruth)))
            , ("existential symbolic restriction retains a truth body",
                Raw.SymbolicExists Nowhere (x :| [y]) (bound (Raw.ExprVar "F")) setStatement,
                existsP (existsP (Core.CAnd restriction Core.CTruth)))
            , ("existing unbounded arguments have separate witnesses",
                distributed (Raw.TermQuantified Raw.Existentially Nowhere
                    (Raw.NounPhrase [] (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
                        (Raw.unboundedNounBinder (Just x)) [] Nothing)),
                Core.CAnd
                    (existsP (Core.CEq Core.TySet (Core.COpaqueInteger 0) (Core.CBound 0)))
                    (existsP (Core.CEq Core.TySet (Core.COpaqueInteger 1) (Core.CBound 0))))
            , ("bounded arguments retain a separate witness for each subject", distributed subject,
                Core.CAnd
                    (existsP (Core.CAnd (member (Core.CBound 0) (Core.CBound 1))
                        (Core.CEq Core.TySet (Core.COpaqueInteger 0) (Core.CBound 0))))
                    (existsP (Core.CAnd (member (Core.CBound 0) (Core.CBound 1))
                        (Core.CEq Core.TySet (Core.COpaqueInteger 1) (Core.CBound 0)))))
            ]
        invalid =
            [ ("self endpoint", Raw.StmtExists Nowhere (phrase [x] (Raw.ExprVar x)))
            , ("sibling endpoint", Raw.StmtExists Nowhere (phrase [x,y] (Raw.ExprVar y)))
            , ("shadow endpoint", Raw.StmtExists Nowhere (phrase ["F"] (Raw.ExprVar "F")))
            , ("duplicate names", Raw.StmtExists Nowhere (phrase [x,x] (Raw.ExprVar "F")))
            , ("nameless bound", Raw.StmtExists Nowhere (phrase [] (Raw.ExprVar "F")))
            , ("injected predicative bound", Raw.StmtNoun Raw.Positive
                (Raw.TermExpr (Raw.ExprVar "F") :| []) (phrase Nothing (Raw.ExprVar "F")))
            ]
        action :: Declaration.ModuleDriver Text
            ([Either Elaboration.ElaborationError Elaboration.ElaboratedProposition],
             [Either Elaboration.ElaborationError Elaboration.ElaboratedProposition])
        action = Declaration.runProspectiveLoweringDriver do
            positives <- traverse (\(_, raw, _) -> Elaboration.elaborateProposition context raw) cases
            negatives <- traverse (Elaboration.elaborateProposition context . snd) invalid
            pure (positives, negatives)
    runDriver fixture action >>= \case
        Declaration.DriverSucceeded (positives, negatives) _ _ -> do
            for_ (zip cases positives) \((label, _, expected), result) -> do
                compiled <- expectRight result
                assertEqual label expected
                    (Core.scopedCoreTerm (Elaboration.elaboratedPropositionCore compiled))
            for_ (zip invalid negatives) \((label, _), result) -> case result of
                Left Elaboration.ElaborationNounBoundScope{} -> pure ()
                Left Elaboration.ElaborationNounBoundUnsupported{} -> pure ()
                Left Elaboration.ElaborationDuplicateLocalBinder{} -> pure ()
                Left failure -> assertFailure (label <> ": " <> show failure)
                Right{} -> assertFailure (label <> ": unexpectedly accepted")
        Declaration.DriverFailed failure _ -> assertFailure (show failure)
        Declaration.DriverSealFailed failure _ -> assertFailure (show failure)
