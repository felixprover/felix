{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Module.Checking (fastTests, acceptanceTests) where

import Base
import Felix.Cache.Codec qualified as Cache
import Felix.Render.Html.Contracts qualified as Contracts
import Felix.Render.Html.Hints qualified as Hints
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure qualified as Structure
import Felix.Checking.Structure.Builtin qualified as Builtin
import Felix.Checking.Binding qualified as Binding
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Backend.Problem qualified as Backend
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Datatype qualified as Datatype
import Felix.Checking.Inductive qualified as Inductive
import Felix.Checking.Instance qualified as Instance
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Preparation qualified as Preparation
import Felix.Checking.LooseDeduction qualified as LooseDeduction
import Felix.Checking.FinalPrelude qualified as FinalPrelude
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping qualified as GlobalTyping
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Module
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.Catalog qualified as FormationCatalog
import Felix.Checking.Obvious qualified as Obvious
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.Structure.Predicate qualified as Predicate
import Felix.Checking.Structure.Laws qualified as StructureLaws
import Felix.Checking.Inductive.Construction qualified as TypedInductive
import Felix.Module
import Felix.Math.Codec (mathematicalDigestHex, hashBlake2b256)
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Prelude qualified as Prelude
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Report.Diagnostic qualified as Diagnostic
import Felix.Source
import Felix.Source.Content qualified as Content
import Felix.Store qualified as Store
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface qualified as Syntax
import Felix.Syntax.Phrase qualified as Phrase
import Felix.Syntax.Lexicon qualified as Lexicon
import Felix.Syntax.Pragma qualified as Pragma
import Felix.Verification qualified as Verification
import Felix.Workspace qualified as Workspace
import Paths_felix qualified as Paths
import Felix.Test.Unit.Module.Support
import Felix.Test.Support.Declarations qualified as DeclTest
import Felix.Test.Support.Imports

import Control.Concurrent.STM
    ( atomically
    , newEmptyTMVarIO
    , putTMVar
    , takeTMVar
    )
import Control.Exception (bracket)
import Control.Monad (when)
import Data.Bifunctor qualified as Bifunctor
import Data.ByteString qualified as ByteString
import Data.Text qualified as StrictText
import Data.Text.Encoding qualified as Text
import Data.IORef
    ( atomicModifyIORef'
    , modifyIORef'
    , newIORef
    , readIORef
    , writeIORef
    )
import Data.List (filter, sort)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import System.Directory
    ( createDirectoryIfMissing
    , getCurrentDirectory
    , getPermissions
    , setOwnerExecutable
    , setPermissions
    )
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import System.Timeout qualified as Timeout
import Test.Tasty
import Test.Tasty.HUnit
import UnliftIO.Async (withAsync, wait)



fastTests :: [TestTree]
fastTests =
        [ testCase "renders extension breadth observations during proof preparation" reportsObviousBreadth
        , testCase "constructs the empty bootstrap ordinarily"
            constructsEmptyBootstrap
        , testCase "preserves conversion and formation error boundaries"
            preservesConversionErrorBoundaries
        , testCase "permits ATP after kernel rejection only for explicit auto"
            preservesOptionalObviousFailure
        , testCase "retains preparation exhaustion in the ordinary ATP diagnostic"
            reportsPreparationExhaustion
        , testCase "prepares scoped logical Auto residuals"
            preparesScopedLogicalResiduals
        , testCase "prepares canonical predicate evidence with exact dependencies"
            preparesPredicateEvidence
        , testCase "rejects malformed reserved bytes at construction"
            rejectsMalformedReservedBytes
        , testCase "identifies comment-only reserved input"
            identifiesCommentOnlyInput
        , testCase "loads and parses the packaged prelude"
            parsesPackagedFinalPrelude
        , testCase "renders packaged final-prelude failures"
            rendersPackagedPreludeFailures
        , testCase "confines exact foundation-leaf completion"
            confinesFoundationLeafCompletion
        , testCase "builds the confined final prelude"
            buildsConfinedFinalPrelude
        , testCase "publishes the final prelude as an ordinary sealed root"
            publishesFinalPreludeRoot
        , testCase "retains exact omitted-proof locations"
            retainsOmittedProofLocation
        , testCase "coalesces syntax without collapsing semantic imports"
            coalescesSharedDirectSyntax
        , testCase "makes selected source errors terminal"
            rejectsUnsupportedTypedSource
        , testCase "rejects overflowing source integers"
            rejectsOverflowingSourceInteger
        , testCase "compiles declarations across an import"
            compilesDeclarationGraph
        , testCase "compiles typed symbolic expressions and binders"
            compilesTypedSymbolicExpressions
        , testCase "checks function, predicate, and argument equality entirely internally"
            compilesExtensionalEquality
        , testCase "lowers and routes set-coded map assertions"
            compilesSetMapAssertions
        , testCase "rejects logical functions in set-coded map assertions"
            rejectsLogicalFunctionInSetMapAssertion
        , testCase "rejects forward structure-field dependencies"
            rejectsForwardStructureFieldDependency
        , testCase "rejects mismatched logical-selection annotations"
            rejectsMismatchedLogicalSelectionAnnotation
        , testCase "prepares grouped and typed Fix contexts"
            preparesTypedProofContexts
        , testCase "compiles and imports structures"
            compilesStructures
        , testCase "compiles parameterized structures non-vacuously"
            compilesParameterizedStructures
        , testCase "checks carrierless structures and reuses their admitted interfaces"
            checksCarrierlessStructures
        , testCase "rejects unavailable carrier capabilities and invalid finite aggregates"
            rejectsCarrierlessMisuse
        , testCase "rejects invalid constructions without publishing pending results"
            rejectsInvalidConstructions
        , testCase "checks pair construction contracts and reopened warm admission"
            checksPairConstructionContracts
        , testCase "registers closed instance evidence and reuses warm semantic modules"
            checksClosedInstanceResults
        , testCase "retains exact closed schema descriptions in checked instance deltas"
            checksClosedValueDescriptions
        , testCase "retains canonical field identity and simultaneous replacement origins"
            retainsRecordFields
        , testCase "accounts for the complete reconstruction query without replenishing fuel"
            accountsReconstructionSearch
        , testCase "preserves reconstruction import order and diagnostic boundaries"
            checksReconstructionBoundaries
        , testCase "propagates natural numeral readiness to lowering initializers"
            propagatesNaturalNumeralReadiness
        , testCase "resolves and diagnoses structure aggregates"
            diagnosesStructureAggregates
        , testCase "preserves source occurrences beside structure resources"
            preservesStructureResourceOccurrences
        , testCase "unfolds equivalent structure predicates through their canonical occurrence"
            unfoldsEquivalentStructurePredicates
        , testCase "rejects incompatible structure diamonds atomically"
            rejectsIncompatibleStructureDiamond
        , testCase "rejects inherited structure-field overrides atomically"
            rejectsInheritedStructureFieldOverride
        , testCase "rejects mismatched structure parameter preambles"
            rejectsMismatchedStructureParameterPreamble
        , testCase "rejects forward structure parameter dependencies"
            rejectsForwardStructureParameterDependency
        , testCase "compiles and caches contextual abbreviations"
            compilesContextualAbbreviations
        , testCase "rejects an unknown structure parent atomically"
            rejectsUnknownStructureParent
        , testCase "compiles relation expressions"
            compilesRelationExpressions
        , testCase "resolves source-owned set application"
            resolvesSourceOwnedApplication
        , testCase "scopes quantified terms in proposition contexts"
            confinesQuantifiedTerms
        , testCase "closes the definition declaration boundary"
            closesDefinitionDeclarationBoundary
        , testCase "publishes canonical definition view kinds"
            publishesCanonicalDefinitionViewKinds
        , testCase "coalesces equivalent canonical definition views"
            coalescesEquivalentCanonicalDefinitionViews
        , testCase "compiles ordinary proofs"
            compilesOrdinaryProofs
        , testCase "replays set extensionality in the kernel"
            replaysSetExtensionalityInKernel
        , testCase "exposes pointwise definitions for set extensionality"
            exposesPointwiseDefinitionsForSetExtensionality
        , testCase "accepts subset observations for set extensionality"
            acceptsSubsetObservationsForSetExtensionality
        , testCase "rejects mismatched pointwise set-extensionality evidence"
            rejectsMismatchedPointwiseSetEquivalence
        , testCase "replays exact-record extensionality in the kernel"
            replaysRecordExtensionalityInKernel
        , testCase "transports exact-record evidence through local definitions"
            replaysRecordAliasNormalizationInKernel
        , testCase "does not normalize exact records through theorem equality"
            rejectsRecordTheoremEqualityNormalization
        , testCase "rejects incomplete exact-record extensionality"
            rejectsIncompleteRecordExtensionality
        , testCase "replays exact obvious discharges"
            replaysExactObviousDischarges
        , testCase "replays extended exact rules without external proof resolution"
            replaysExtendedExactRules
        , testCase "replays existing existential witnesses without external proof resolution"
            replaysExistingWitnesses
        , testCase "rejects unsupported witness bodies amid irrelevant evidence"
            rejectsUnsupportedWitnessBodies
        , testCase "replays Boolean theorem premises without external proof resolution"
            replaysBooleanTheoremPremises
        , testCase "rejects missing Boolean theorem premises amid irrelevant evidence"
            rejectsMissingBooleanPremises
        , testCase "replays universal Boolean instances without external proof resolution"
            replaysUniversalInstances
        , testCase "rejects missing universal premises amid irrelevant evidence"
            rejectsMissingUniversalPremises
        , testCase "replays universal hints across irrelevant evidence and source order"
            qualifiesUniversalHints
        , testCase "replays supplied existential elimination without external proof resolution"
            qualifiesSuppliedExistentials
        , testCase "qualifies membership extensionality without external proof resolution"
            qualifiesMembershipExtensionality
        , testCase "restores binder and witness proof forms"
            restoresElaborationBinderAndWitnessProofForms
        , testCase "restores local reasoning and calculations"
            restoresLocalReasoningAndCalculations
        , testCase "keeps a newly proved Since premise temporary"
            rejectsTemporarySincePremiseLeak
        , testCase "selects calculation link failures by source order"
            selectsCalculationLinkFailureBySourceOrder
        , testCase "verifies relation composition through direct, warm, and diamond imports"
            verifiesRelationCompositionThroughImports
        , testCase "verifies guarded generalized calculations through direct, warm, and diamond imports"
            (checkCompositionImports "test/phase7/composition-generalized-direct.tex" "test/phase7/composition-generalized-diamond-root.tex")
        , testCase "checks generalized calculation forms and rejects invalid laws without ATP"
            checksGeneralizedCalculationForms
        , testCase "compiles and reuses proof-local set definitions"
            compilesAndReusesProofLocalSetDefinitions
        , testCase "compiles and reuses proof-local function graphs"
            compilesAndReusesProofLocalFunctionGraphs
        , testCase "propagates contradiction context"
            propagatesContradictionContext
        , testCase "discharges an exact local case disjunction structurally"
            dischargesExactLocalCaseDisjunctionStructurally
        , testCase "discharges higher-order binary case exhaustiveness structurally"
            dischargesHigherOrderBinaryCaseExhaustivenessStructurally
        , testCase "compiles separation comprehensions"
            compilesSeparationComprehensions
        , testCase "compiles replacement comprehensions"
            compilesReplacementComprehensions
        , testCase "uses first-order definitions in implicit obvious inference"
            usesFirstOrderDefinitionsInImplicitObviousInference
        , testCase "compiles and reuses relational replacement"
            compilesAndReusesRelationalReplacement
        , testCase "compiles and reuses finite sets"
            compilesAndReusesFiniteSets
        , testCase "prepares deterministic datatypes"
            preparesDatatypes
        , testCase "accepts closed dependent and quantified datatype domains"
            acceptsRichDatatypeDomains
        , testCase "rejects nested datatype recursion"
            rejectsNestedDatatypeRecursion
        , testCase "rejects higher-order datatype premise domains"
            rejectsHigherOrderDatatypePremises
        , testCase "compiles and reuses datatypes"
            compilesAndReusesDatatypes
        , testCase "preserves datatype premise slots and empty carriers"
            preservesDatatypePremises
        , testCase "checks parameterized datatype domains and replays family proofs"
            checksDatatypeFamilies
        , testCase "shares datatype definitions locally and through imports"
            sharesDatatypeDefinitions
        , testCase "uses checked datatype constructor results through imports"
            checksDatatypeFormation
        , testCase "checks datatype structural induction across imports and warm caches"
            checksStructuralInduction
        , testCase "checks datatype case names and generated aliases"
            checksDatatypeNames
        , testCase "rejects forged datatype descriptions on import"
            rejectsForgedDatatypeDescriptions
        , testCase "prepares direct inductives"
            preparesDirectInductives
        , testCase "prepares nested inductive recursion"
            preparesNestedInductiveRecursion
        , testCase "compiles transparent nested inductive wrappers"
            compilesTransparentNestedInductiveWrappers
        , testCase "normalizes nested inductive contexts"
            normalizesNestedInductiveContexts
        , testCase "compiles and reuses inductives"
            compilesAndReusesInductives
        , testCase "authorizes recursive inductives"
            authorizesRecursiveInductives
        , testCase "compiles source axioms"
            compilesSourceAxioms
        , testCase "does not treat marker-only nouns as the fixed set noun"
            doesNotTreatMarkerOnlyNounAsSet
        , testCase "rejects proof-local generalization"
            rejectsProofLocalGeneralization
        , testCase "restores checked set induction"
            restoresCheckedSetInduction
        , testCase "restores checked transfinite induction"
            restoresCheckedTransfiniteInduction
        , testCase "compiles omitted proofs"
            compilesOmittedProofs
        , testCase "retains kernel facts in omitted proofs"
            compilesOmittedProofWithKernelFact
        , testCase "propagates and reuses escape authority"
            reusesEscapeAuthority
        , testCase "checks continuations after omitted subclaims"
            rejectsAfterOmittedSubclaim
        , testCase "rejects declarations of fixed semantics"
            rejectsFixedSemanticDeclaration
        , testCase "rejects inductive carriers with fixed semantics"
            rejectsFixedSemanticInductive
        , testCase "keeps semantics independent of fixity"
            keepsSemanticsIndependentOfFixity
        ]

acceptanceTests :: [TestTree]
acceptanceTests =
    [ testCase "verifies transparent structure aggregates end to end"
        verifiesTransparentStructureAggregates
    , testCase "verifies closed named structure instances end to end"
        verifiesClosedNamedStructureInstances
    , testCase "verifies closed instance formation probes with Vampire"
        verifiesClosedInstanceFormation
    , testCase "verifies closed calculus formation with broad cached imports and fresh consumers"
        verifiesClosedCalculusFormation
    , testCase "verifies closed schema values with cold dependencies and fresh and warm consumers"
        verifiesClosedValueFormation
    , testCase "verifies checked structure reducts end to end"
        verifiesCheckedStructureReducts
    , testCase "verifies structure inheritance and exactness end to end"
        verifiesStructureInheritanceMatrix
    , testCase "verifies construction families and their composed public interface"
        verifiesConstructionFamilies
    , testCase "keeps named logical graphs first-order"
        compilesBoundedLogicalGraphs
    , testCase "verifies generated wellorder graph semantics"
        verifiesGeneratedWellOrderGraphSemantics
    ]

verifiesClosedInstanceFormation :: Assertion
verifiesClosedInstanceFormation =
    for_ ["manifolds-1-instance-focus-probe", "manifolds-1-instance-parameter-probe",
            "manifolds-1-positive-instance-import", "closed-instance-results-import"] \fixture -> do
        result <- expectRightIO (checkFileFresh
            (Provers.vampire "vampire" (Provers.Seconds 20) Provers.defaultMemoryLimit)
            ("test/structure-spikes/" <> fixture <> ".tex"))
        assertTypedSuccess fixture (fst result)

verifiesClosedCalculusFormation :: Assertion
verifiesClosedCalculusFormation = Temp.withSystemTempDirectory "closed-calculus-formation" \directory -> do
    foundation <- expectRight Foundation.checkedFoundation
    let prover = Provers.vampire "vampire" (Provers.Seconds 20) Provers.defaultMemoryLimit
    bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
        (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
        let checkResult fixture = do
                graph <- Workspace.prepareDefaultSourceGraph ("test/structure-spikes/" <> fixture <> ".tex") >>= expectRight
                outcome <- expectRightIO (Verification.withVerificationSessionUsingStore store \session ->
                    Verification.checkWorkspace session Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand = Parse.NoPresentation
                        , Verification.checkStoreValidationMode = Verification.WarmStoreValidation
                        , Verification.checkModuleJobs = testSequentialJobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = ignoredVerificationRequests
                        }) >>= expectRight
                pure outcome
            check fixture = do
                outcome <- checkResult fixture
                assertTypedSuccess fixture (Verification.checkVerificationResult outcome)
                pure (Verification.checkOperationalReport outcome)
        cold <- check "manifolds-1-closed-calculus-small-probe"
        assertBool "the first producer compiles cold dependencies"
            (Verification.lookupMisses (Verification.moduleInstallationDecisions cold) > 1)
        _ <- check "manifolds-1-closed-calculus-import-probe"
        for_ ["manifolds-1-coordinate-map-formation-control", "manifolds-1-coordinate-map-pseudogroup-probe",
                "manifolds-1-coordinate-map-calculus-probe", "manifolds-1-coordinate-map-formation-probe"] \fixture -> do
            fresh <- check fixture
            let decisions = Verification.moduleInstallationDecisions fresh
            assertBool "dependency module artefacts were reused" (Verification.lookupRowsFound decisions > 1)
            Verification.lookupMisses decisions @?= 1
            -- These new consumer proofs are tautologies. In particular no
            -- prerequisite compilation can obscure an ATP formation fallback.
            Verification.liveVampireRunsStarted fresh @?= 0
            warm <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions warm) @?= 0
            Verification.liveVampireRunsStarted warm @?= 0
        _ <- check "manifolds-1-nominal-imports"
        chain <- check "manifolds-1-nominal-chain-probe"
        Verification.lookupMisses (Verification.moduleInstallationDecisions chain) @?= 1
        Verification.liveVampireRunsStarted chain @?= 0
        nominal <- check "manifolds-1-nominal-producers"
        Verification.lookupMisses (Verification.moduleInstallationDecisions nominal) @?= 1
        Verification.liveVampireRunsStarted nominal @?= 0
        warmNominal <- check "manifolds-1-nominal-producers"
        Verification.lookupMisses (Verification.moduleInstallationDecisions warmNominal) @?= 0
        Verification.liveVampireRunsStarted warmNominal @?= 0
        wrongModel <- checkResult "manifolds-1-nominal-wrong-model"
        case Verification.checkVerificationResult wrongModel of
            Verification.VerificationCheckingFailure _ (Verification.VerificationTypedModuleError _
                (Module.TypedActionFailed (Module.TypedProofFailed
                    (Proof.ProofElaborationFailed failure@Elaboration.ElaborationFormationRequirementMissing{}))) _) -> do
                        let diagnostic = Elaboration.renderElaborationError failure
                        for_ ["nominal_model_guard", "is a pseudogroup on F"] \detail ->
                            assertBool "wrong-model rejection identifies the unsatisfied contract"
                                (detail `StrictText.isInfixOf` diagnostic)
            failure -> fail ("wrong-model formation reached an unexpected boundary: " <> show failure)
        Verification.liveVampireRunsStarted (Verification.checkOperationalReport wrongModel) @?= 0
        _ <- check "manifolds-1-coordinate-map-acceptance"
        warmMaps <- check "manifolds-1-coordinate-map-acceptance"
        Verification.lookupMisses (Verification.moduleInstallationDecisions warmMaps) @?= 0
        Verification.liveVampireRunsStarted warmMaps @?= 0
        -- The map acceptance imports the restriction constructor. These new
        -- roots must still elaborate: a cached root would hide join/delivery
        -- regressions when reconstructing its guarded result and parent datum.
        for_ ["manifolds-2-restriction-formation-probe",
                "manifolds-2-restriction-broad-nominal-probe",
                "manifolds-2-restriction-membership-probe",
                "manifolds-2-openness-membership-probe"] \fixture -> do
            fresh <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions fresh) @?= 1
            assertBool "restriction dependencies are cached"
                (Verification.lookupRowsFound (Verification.moduleInstallationDecisions fresh) > 1)
            Verification.liveVampireRunsStarted fresh @?= 0
            warm <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions warm) @?= 0
            Verification.liveVampireRunsStarted warm @?= 0
        _ <- check "manifolds-2-restriction-presentation-probe"
        _ <- check "manifolds-2-restriction-broad-probe"
        for_ ["manifolds-2-transport-guard-probe", "manifolds-2-transport-probe",
                "manifolds-2-weakening-formation-probe", "manifolds-2-weakening-probe",
                "manifolds-2-raw-presentation-probe"] \fixture -> do
            fresh <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions fresh) @?= 1
            Verification.liveVampireRunsStarted fresh @?= 0
            warm <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions warm) @?= 0
            Verification.liveVampireRunsStarted warm @?= 0
        for_ ["manifolds-2-transport-closed-probe", "manifolds-2-weakening-closed-probe",
                "manifolds-2-raw-presentation-closed-probe"] \fixture -> do
            fresh <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions fresh) @?= 1
            warm <- check fixture
            Verification.lookupMisses (Verification.moduleInstallationDecisions warm) @?= 0
            Verification.liveVampireRunsStarted warm @?= 0

verifiesClosedValueFormation :: Assertion
verifiesClosedValueFormation = Temp.withSystemTempDirectory "closed-value-formation" \directory -> do
    foundation <- expectRight Foundation.checkedFoundation
    let prover = Provers.vampire "vampire" (Provers.Seconds 20) Provers.defaultMemoryLimit
    bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
        (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
        let check source = do
                graph <- Workspace.prepareDefaultSourceGraph source >>= expectRight
                outcome <- expectRightIO (Verification.withVerificationSessionUsingStore store \session ->
                    Verification.checkWorkspace session Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand = Parse.NoPresentation
                        , Verification.checkStoreValidationMode = Verification.WarmStoreValidation
                        , Verification.checkModuleJobs = testSequentialJobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = ignoredVerificationRequests
                        }) >>= expectRight
                assertTypedSuccess source (Verification.checkVerificationResult outcome)
                pure (Verification.checkOperationalReport outcome)
            consumer = "test/structure-spikes/closed-value-instances-import.tex"
        cold <- check "test/structure-spikes/closed-value-instances.tex"
        assertBool "closed-value dependencies compile cold"
            (Verification.lookupMisses (Verification.moduleInstallationDecisions cold) > 1)
        fresh <- check consumer
        Verification.lookupMisses (Verification.moduleInstallationDecisions fresh) @?= 1
        assertBool "the new consumer reuses its already checked dependencies"
            (Verification.lookupRowsFound (Verification.moduleInstallationDecisions fresh) > 1)
        Verification.liveVampireRunsStarted fresh @?= 0
        warm <- check consumer
        Verification.lookupMisses (Verification.moduleInstallationDecisions warm) @?= 0
        Verification.liveVampireRunsStarted warm @?= 0

verifiesConstructionFamilies :: Assertion
verifiesConstructionFamilies = do
    let prover = Provers.vampire "vampire" (Provers.Seconds 20) Provers.defaultMemoryLimit
    forM_ ["test/structure-spikes/manifolds-0-projection-collision.tex",
            "test/structure-spikes/construction-classification-bundle.tex",
            "test/structure-spikes/construction-header-pair-baseline.tex",
            "test/structure-spikes/construction-header-pair-import.tex",
            "test/structure-spikes/structure-parameter-sources.tex",
            "test/structure-spikes/wide-construction.tex",
            "test/structure-spikes/wide-replacements.tex",
            "test/structure-spikes/reconstruction-law-transport.tex",
            "test/structure-spikes/reconstruction-discovery.tex",
            "test/structure-spikes/reconstruction-discovery-reversed.tex",
            "test/structure-spikes/reconstruction-explicit-assertions.tex",
            "test/structure-spikes/reconstruction-account.tex",
            "test/structure-spikes/reconstruction-import-consumer.tex",
            "test/structure-spikes/reconstruction-import-expression.tex"] \source -> do
        result <- checkFileFresh prover source
        case result of
            Left failure -> assertFailure ("construction fixture did not run: " <> show failure)
            Right (verification, _slowReport) -> assertTypedSuccess "construction fixture" verification
    forM_
        [ ("construction-laws-rejected", \case
            Module.TypedInstanceFailed Instance.InstanceProofFailed{} -> True
            _ -> False)
        , ("manifolds-0-implicit-reduct-rejected", \case
            Module.TypedProofFailed{} -> True
            _ -> False)
        ] \(fixture, expectedFailure) -> do
            result <- checkFileFresh prover ("test/structure-spikes/" <> fixture <> ".tex")
            case result of
                Right (Verification.VerificationCheckingFailure _
                        (Verification.VerificationTypedModuleError _ (Module.TypedActionFailed failure) _), _) -> do
                    assertBool (fixture <> ": " <> show failure) (expectedFailure failure)
                    Module.typedPathErrorDisposition failure @?= Proof.ProofSourceRejection
                other -> assertFailure (fixture <> " did not reject its proof: " <> show other)

verifiesGeneratedWellOrderGraphSemantics :: Assertion
verifiesGeneratedWellOrderGraphSemantics = do
    result <-
        checkFileFresh
            (Provers.vampire
                "vampire"
                Provers.defaultTimeLimit
                Provers.defaultMemoryLimit)
            "test/phase5/generated-well-order.tex"
    case result of
        Left failure ->
            assertFailure
                ("generated-wellorder fixture did not run: " <> show failure)
        Right (verification, _slowReport) ->
            assertTypedSuccess "generated-wellorder fixture" verification

rejectsMalformedReservedBytes :: Assertion
rejectsMalformedReservedBytes =
    case Prelude.reservedPreludeSourceInput (ByteString.pack [0xff]) of
        Left _failure -> pure ()
        Right _source ->
            assertFailure "malformed reserved UTF-8 was accepted"

preservesConversionErrorBoundaries :: Assertion
preservesConversionErrorBoundaries = do
    let file = sourceDescriptorForPath "conversion-errors.tex"
    location <- expectRight (mkLocationChecked file 17 23)
    assertEqual "checked structure metadata failure is an integrity error"
        Proof.ProofInfrastructureFailure
        (Proof.proofErrorDisposition (Proof.ProofStructureMetadataMismatch location))
    checked <- expectRight
        (Core.checkScopedCanonicalCore GlobalTyping.emptyGlobalTyping [] Core.CTruth)
    let limit = Conversion.conversionLimit 100
        pool = Conversion.conversionPool 100
        cause = Conversion.ConversionInputFailure
            (Conversion.ConversionContextMismatch [] [Core.TyProp])
        cost = Conversion.conversionCost
            (Conversion.convertibleChecked GlobalTyping.emptyGlobalTyping limit
                checked checked)
        kernelFailures =
            [ KernelProof.ProofConversionNotConvertible
            , KernelProof.ProofConversionLimitExhausted KernelProof.ProofConversionOperationLimit limit
            , KernelProof.ProofConversionLimitExhausted KernelProof.ProofConversionAggregatePool limit
            , KernelProof.ProofConversionFailed cause
            , KernelProof.ProofConversionWitnessSourceMismatch
            , KernelProof.ProofConversionPoolAccountingInvariant
            ]
        formationFailures =
            [ Notion.FormationProofHypothesisCountMismatch 2 1
            , Notion.FormationProofHypothesisMismatch (Kernel.hypothesisIx 1)
            , Notion.FormationProofImportCountMismatch 2 1
            , Notion.FormationProofInvalidRecipe
            ] <> (Notion.FormationProofKernelError <$> kernelFailures)
        assertProofBoundary disposition message failure = do
            assertEqual "proof failure retains its location"
                location (Proof.proofErrorLocation failure)
            assertEqual "proof failure retains its disposition"
                disposition (Proof.proofErrorDisposition failure)
            assertEqual "the module adopts the proof disposition"
                disposition (Module.typedPathErrorDisposition (Module.TypedProofFailed failure))
            assertBool "rendering retains the specific failure"
                (message `StrictText.isInfixOf` Proof.renderProofError failure)
        assertFormationBoundary transient declaration failure message = do
            assertProofBoundary Proof.ProofInfrastructureFailure message failure
            assertBool "definition-result rendering retains the typed cause"
                (message `StrictText.isInfixOf` Declaration.renderDeclarationError declaration)
            let elaboration = Elaboration.ElaborationFormationReplayFailed location transient
            assertEqual "transient replay retains the existing elaboration disposition"
                Proof.ProofSourceRejection
                (Module.typedPathErrorDisposition (Module.TypedElaborationFailed elaboration))
            assertEqual "transient replay retains its location"
                location (Elaboration.elaborationErrorLocation elaboration)
            assertBool "transient replay rendering retains the typed cause"
                (message `StrictText.isInfixOf` Elaboration.renderElaborationError elaboration)
    for_ formationFailures \failure ->
        assertFormationBoundary
            (Declaration.TransientFormationProofFailed failure)
            (Declaration.DefinitionResultFormationProofFailed failure)
            (Proof.ProofNotionFormationFailed location failure)
            (StrictText.pack (show failure))
    assertProofBoundary Proof.ProofInfrastructureFailure "different goal"
        (Proof.ProofNotionFormationTargetMismatch location)
    assertProofBoundary Proof.ProofSourceRejection "exhausted"
        (Proof.ProofNotionFormationFailed location
            (Notion.FormationProofDerivationLimitExceeded
                (Notion.FormationDerivationNodeLimitExceeded 10 11)))
    assertBool "definition-result target mismatch names its premise"
        ("different premise" `StrictText.isInfixOf` Declaration.renderDeclarationError
            Declaration.DefinitionResultFormationTargetMismatch)
    let targetFailure = Elaboration.ElaborationFormationReplayFailed location
            Declaration.TransientFormationProofTargetMismatch
    assertEqual "transient target mismatch retains its location"
        location (Elaboration.elaborationErrorLocation targetFailure)
    assertBool "transient target mismatch remains distinct"
        ("TransientFormationProofTargetMismatch" `StrictText.isInfixOf`
            Elaboration.renderElaborationError targetFailure)
    for_ kernelFailures \failure ->
        assertProofBoundary Proof.ProofInfrastructureFailure (StrictText.pack (show failure))
            (Proof.ProofObviousInferenceFailed location (Obvious.ObviousIntegrityFailure failure))
    for_
        [ (Obvious.ObviousConversionFailed cause, "conversion failed")
        , (Obvious.ObviousRequiredConversionNotConvertible, "non-convertible")
        , (Obvious.ObviousConversionAccountingInvariant cost pool, "cost exceeded")
        ] \(failure, message) ->
            assertProofBoundary Proof.ProofInfrastructureFailure message
                (Proof.ProofObviousInferenceFailed location failure)
    for_
        [ (Obvious.ObviousConversionOperationLimit, "conversion operation limit")
        , (Obvious.ObviousConversionPoolLimit, "conversion pool")
        ] \(owner, message) ->
            assertProofBoundary Proof.ProofSourceRejection message
                (Proof.ProofObviousInferenceFailed location
                    (Obvious.ObviousResourceExhausted owner))

constructsEmptyBootstrap :: Assertion
constructsEmptyBootstrap = do
    foundation <- expectRight Foundation.checkedFoundation
    result <-
        Module.buildBootstrapPreludeFixture
            foundation
            unusedResolver
    session <- expectRight result
    let input = Module.bootstrapPreludeInput session
        parsed = Module.identifiedModuleParsed input
        sealed = Module.bootstrapPreludeCompleted session
        syntax = completedModuleSyntax sealed
        semantic = completedModuleSemantic sealed
    assertEqual "reserved owner"
        preludeModuleName
        (Module.identifiedModuleOwner input)
    case Module.identifiedModuleBinding input of
        Module.ReservedModuleBinding descriptor label -> do
            assertEqual "diagnostic label"
                Prelude.preludeDiagnosticLabel
                label
            assertEqual "descriptor display label"
                Prelude.preludeDiagnosticLabel
                (sourceDescriptorDisplayPath descriptor)
            assertEqual "registered identity label"
                (Just Prelude.preludeDiagnosticLabel)
                (sourceDescriptorIdentityPath descriptor)
        Module.PhysicalModuleBinding source ->
            assertFailure
                ("bootstrap acquired a physical source: " <> show source)
    assertEqual "empty parsed blocks"
        []
        (Parsed.identifiedParsedModuleBlocks parsed)
    assertEqual "exact empty source identity"
        (Content.sourceContentIdBytes ByteString.empty)
        (Parsed.identifiedParsedModuleSourceContentId parsed)
    assertEqual "no syntax imports"
        []
        (Syntax.moduleSyntaxDirectInputs syntax)
    assertEqual "empty local syntax"
        []
        (Syntax.canonicalSyntaxDeltaEntries
            (Syntax.moduleSyntaxLocalDelta syntax))
    assertEqual "semantic owner"
        preludeModuleName
        (Semantic.semanticInterfaceOwner semantic)
    assertEqual "no semantic imports"
        []
        (Semantic.semanticInterfaceDirectInputs semantic)
    assertEqual "no semantic declarations"
        []
        (Semantic.semanticInterfaceDeclarations semantic)
    expectedPrefix <-
        expectRight
            (Semantic.initialPrefixContextId
                (Identity.theoryId foundation)
                preludeModuleName
                [])
    assertEqual "empty sealed prefix"
        expectedPrefix
        (Commit.pendingModulePrefixCurrent
            (Module.completedTypedModulePrefix sealed))

identifiesCommentOnlyInput :: Assertion
identifiesCommentOnlyInput = do
    emptySource <-
        expectRight
            =<< Prelude.parseReservedPreludeSource
                Prelude.emptyBootstrapSourceInput
    source <-
        expectRight
            (Prelude.reservedPreludeSourceInput
                (Text.encodeUtf8 "% an in-memory comment\n"))
    first <-
        expectRight
            =<< Prelude.parseReservedPreludeSource source
    second <-
        expectRight
            =<< Prelude.parseReservedPreludeSource source
    let emptyParsed = Prelude.reservedParsedPreludeModule emptySource
        firstParsed = Prelude.reservedParsedPreludeModule first
        secondParsed = Prelude.reservedParsedPreludeModule second
    assertBool "reserved live source binding"
        (Parse.freshModuleInputIsReserved
            (Prelude.reservedParsedPreludeInput first))
    assertEqual "comment-only source has no blocks"
        []
        (Parsed.identifiedParsedModuleBlocks firstParsed)
    assertBool "content changes parsed identity"
        (Parsed.identifiedParsedModuleId emptyParsed
            /= Parsed.identifiedParsedModuleId firstParsed)
    assertEqual "same input has stable parsed identity"
        (Parsed.identifiedParsedModuleId firstParsed)
        (Parsed.identifiedParsedModuleId secondParsed)
    assertEqual "comments do not change syntax"
        (Syntax.moduleSyntaxAssertedId
            (Parsed.identifiedParsedModuleSyntaxInterface emptyParsed))
        (Syntax.moduleSyntaxAssertedId
            (Parsed.identifiedParsedModuleSyntaxInterface firstParsed))

parsesPackagedFinalPrelude :: Assertion
parsesPackagedFinalPrelude = do
    path <- Paths.getDataFileName Prelude.preludeDataFilePath
    expectedBytes <- ByteString.readFile path
    source <- expectRight =<< Prelude.loadReservedPreludeSourceInput
    assertEqual "exact packaged bytes"
        expectedBytes
        (Prelude.reservedPreludeSourceBytes source)
    assertEqual "reserved owner"
        preludeModuleName
        (Prelude.reservedPreludeSourceOwner source)
    assertEqual "diagnostic label"
        Prelude.preludeDiagnosticLabel
        (Prelude.reservedPreludeSourceLabel source)
    first <- expectRight =<< Prelude.parseReservedPreludeSource source
    second <- expectRight =<< Prelude.parseReservedPreludeSource source
    let firstInput = Prelude.reservedParsedPreludeInput first
        firstParsed = Prelude.reservedParsedPreludeModule first
        secondParsed = Prelude.reservedParsedPreludeModule second
    assertEqual "no textual imports"
        []
        (Parse.freshModuleInputImports firstInput)
    assertBool "declaration-bearing source"
        (not (null (Parsed.identifiedParsedModuleBlocks firstParsed)))
    assertEqual "deterministic syntax interface"
        (Syntax.moduleSyntaxAssertedId
            (Parsed.identifiedParsedModuleSyntaxInterface firstParsed))
        (Syntax.moduleSyntaxAssertedId
            (Parsed.identifiedParsedModuleSyntaxInterface secondParsed))

rendersPackagedPreludeFailures :: Assertion
rendersPackagedPreludeFailures = do
    assertEqual "load failure"
        "/missing/felix-prelude.tex: unable to read packaged prelude: not found"
        (Prelude.renderPreludeLoadError
            (Prelude.PreludeSourceReadFailed
                "/missing/felix-prelude.tex"
                "not found"))
    assertEqual "located syntax failure"
        "library/prelude.tex: syntax pragma location is out of range at 7:3"
        (Prelude.renderPreludeParseError parseFailure)
    assertEqual "authority-free API presentation"
        ("prelude parsing failed: "
            <> "library/prelude.tex: syntax pragma location is out of range at 7:3")
        (Workspace.renderAuthorityFreeParseError
            (Workspace.AuthorityFreePreludeParseFailed parseFailure))
  where
    parseFailure =
        Prelude.PreludeSyntaxPragmaFailed
            (Pragma.SyntaxPragmaLocationOutOfRange
                Prelude.preludeDiagnosticLabel
                7
                3)

confinesFoundationLeafCompletion :: Assertion
confinesFoundationLeafCompletion = do
    foundation <- expectRight Foundation.checkedFoundation
    packaged <- expectRight =<< Prelude.loadReservedPreludeSourceInput
    parsed <- expectRight =<< Prelude.parseReservedPreludeSource packaged
    matching <- sole "matching foundation claim"
        (take 1
            (Parsed.identifiedParsedModuleBlocks
                (Prelude.reservedParsedPreludeModule parsed)))
    classification <- case matching of
        Raw.BlockClaim _kind location title marker claim ->
            pure
                (Raw.BlockClaim Raw.Classification location title marker claim)
        _ -> assertFailure "foundation fixture is not a claim"
            >> fail "unreachable"
    mismatchInput <-
        expectRight
            (Prelude.reservedPreludeSourceInput
                (Text.encodeUtf8
                    "\\begin{proposition}\\label{not_foundation}\n    $\\emptyset = \\emptyset$.\n\\end{proposition}\n"))
    mismatchParsed <-
        expectRight =<< Prelude.parseReservedPreludeSource mismatchInput
    mismatch <- sole "mismatching claim"
        (Parsed.identifiedParsedModuleBlocks
            (Prelude.reservedParsedPreludeModule mismatchParsed))
    outcome <-
        runModuleDriver
            foundation
            preludeModuleName
            []
            unusedResolver
            AlwaysMissValidation do
                explicit <-
                    admitFoundationClaim
                        foundation
                        matching
                        (Just (Raw.Omitted (locate matching)))
                nonmatching <-
                    admitFoundationClaim
                        foundation
                        mismatch
                        Nothing
                classified <-
                    admitFoundationClaim
                        foundation
                        classification
                        Nothing
                committed <-
                    admitFoundationClaim
                        foundation
                        matching
                        Nothing
                pure (explicit, nonmatching, classified, committed)
    case outcome of
        Right (Declaration.DriverSucceeded
                (explicit, nonmatching, classified, committed)
                _semantic _prefix) -> do
            case explicit of
                Left Proof.ProofFoundationLeafRequiresImplicitAuto{} ->
                    pure ()
                Left other ->
                    assertFailure
                        ("explicit foundation result: " <> show other)
                Right{} ->
                    assertFailure "explicit foundation proof was accepted"
            batch <- expectRight committed
            case nonmatching of
                Left Proof.ProofFoundationLeafTargetMismatch{} ->
                    pure ()
                Left other ->
                    assertFailure
                        ("mismatching foundation result: " <> show other)
                Right{} ->
                    assertFailure "mismatching foundation claim was accepted"
            case classified of
                Left Proof.ProofUnsupportedClaim{} -> pure ()
                Left other ->
                    assertFailure
                        ("classification foundation result: " <> show other)
                Right{} ->
                    assertFailure
                        "classification entered foundation authorization"
            assertEqual "foundation tag"
                Foundation.UnivOfContains
                (case Commit.committedBatchProofValidations batch of
                    [record] ->
                        case Authority.validationDirectAuthorization
                                (Semantic.proofValidationRecordCertificate
                                    record) of
                            Authority.CheckedKernelConstruction
                                    (Authority.FoundationLeaf tag) ->
                                tag
                            authorization ->
                                error
                                    ("unexpected foundation authorization: "
                                        <> show authorization)
                    records ->
                        error
                            ("unexpected foundation validation count: "
                                <> show (length records)))
        Right Declaration.DriverFailed{} ->
            assertFailure "foundation driver failed"
        Right (Declaration.DriverSealFailed failure _prefix) ->
            assertFailure ("foundation driver did not seal: " <> show failure)
        Left failure ->
            assertFailure ("foundation driver did not open: " <> show failure)
  where
    admitFoundationClaim foundation block proof =
        Declaration.runProspectiveLoweringDriver
            (Proof.prepareFinalPreludeFoundationClaim
                foundation block proof) >>= \case
                Left failure -> pure (Left failure)
                Right prepared -> do
                    lowered <-
                        Declaration.runProspectiveLoweringDriver
                            (Proof.lowerPreparedFinalPreludeFoundationClaim
                                prepared)
                    checked <-
                        either Declaration.failDeclarationDriver pure lowered
                    (_, batch) <-
                        Declaration.admitCheckedDeclaration
                            checked
                            Proof.authorizeCheckedFinalPreludeFoundationClaim
                    pure (Right batch)

buildsConfinedFinalPrelude :: Assertion
buildsConfinedFinalPrelude = do
    foundation <- expectRight Foundation.checkedFoundation
    observations <- newIORef []
    let resolver =
            Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                modifyIORef' observations
                    (<> [ ( Backend.typedProblemRoute problem
                           , Backend.typedBackendFactReference
                                <$> Vector.toList
                                    (Backend.typedProblemGlobalPremises
                                        problem)
                           , Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                           , Vector.length
                                (Backend.typedProblemLogicalSelections
                                    problem)
                           )
                        ])
                Provers.runPreparedTypedProver
                    (Provers.vampire
                        "vampire"
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared
    FinalPrelude.buildFinalPreludeCandidate
            foundation resolver >>= \case
        FinalPrelude.FinalPreludeBuilt candidate -> do
            assertEqual "confined semantic owner"
                preludeModuleName
                (Semantic.semanticInterfaceOwner
                    (FinalPrelude.finalPreludeSemantic candidate))
            assertEqual "confined semantic imports"
                []
                (Semantic.semanticInterfaceDirectInputs
                    (FinalPrelude.finalPreludeSemantic candidate))
            let baseDeltas =
                    [ delta
                    | delta <- Semantic.semanticInterfaceDeclarations
                        (FinalPrelude.finalPreludeSemantic candidate)
                    , not
                        (null
                            (Semantic.semanticEnvironmentStructures
                                (Semantic.declarationDeltaEnvironment delta)))
                    ]
            case baseDeltas of
                [delta] -> do
                    assertEqual "the manifest publishes every distinct law and resource occurrence"
                        39 (length (Semantic.declarationDeltaFacts delta))
                    assertBool "colliding proposition contents keep distinct law occurrences"
                        (length (Semantic.declarationDeltaPropositions delta) < length (Semantic.declarationDeltaFacts delta))
                    case Declaration.evidenceLocalStructureSchemas (FinalPrelude.finalPreludeEvidence candidate) of
                        [_root, descriptor] -> do
                            let predicate = schemaPredicate descriptor
                            case schemaLocalFields
                                    descriptor of
                                [operation] -> do
                                    let fieldIdentity =
                                            Schema.resolvedFieldIdentity
                                                operation
                                        theory = Identity.theoryId foundation
                                        expectedSelector =
                                            Record.fieldSelectorObjectId
                                                theory fieldIdentity
                                        expectedProjection =
                                            Record.fieldProjectionObjectId
                                                theory fieldIdentity
                                        objects =
                                            FinalPrelude.finalPreludeObjects
                                                candidate
                                    assertEqual
                                        "base carrier selector follows its field identity"
                                        expectedSelector
                                        (Schema.resolvedFieldSelector
                                            operation)
                                    assertEqual
                                        "base carrier projection follows its field identity"
                                        expectedProjection
                                        (Schema.resolvedFieldProjection
                                            operation)
                                    assertEqual
                                        "base carrier selector is transparent"
                                        (Just
                                            (Identity.assertedObjectContent
                                                (Record.fieldSelectorObject
                                                    theory fieldIdentity)))
                                        (Identity.lookupCheckedObjectContent
                                            expectedSelector objects)
                                    assertEqual
                                        "base carrier projection is transparent"
                                        (Just
                                            (Identity.assertedObjectContent
                                                (Record.fieldProjectionObject
                                                    theory fieldIdentity)))
                                        (Identity.lookupCheckedObjectContent
                                            expectedProjection objects)
                                    let expectedPredicateObject =
                                            Identity.transparentObject
                                                theory
                                                (Core.TyArrow
                                                    Core.TySet Core.TyProp)
                                                (Core.CLam Core.TySet
                                                    (Record.recordOpenShape
                                                        [Core.CGlobal
                                                            expectedSelector]
                                                        (Core.CBound 0)))
                                    assertEqual
                                        "base structure predicate is the carrier-record test"
                                        (Identity.assertedObjectId
                                            expectedPredicateObject)
                                        predicate
                                    assertEqual
                                        "base structure predicate is transparent"
                                        (Just
                                            (Identity.assertedObjectContent
                                                expectedPredicateObject))
                                        (Identity.lookupCheckedObjectContent
                                            predicate objects)
                                operations ->
                                    assertFailure
                                        ("expected one base operation, got "
                                            <> show operations)
                        descriptors ->
                            assertFailure
                                ("expected one base descriptor, got "
                                    <> show descriptors)
                deltas ->
                    assertFailure
                        ("expected one base structure delta, got "
                            <> show (length deltas))
            let role roleName =
                    maybe
                        (assertFailure
                            ("missing final-prelude role "
                                <> show roleName))
                        pure
                        (FinalPrelude.finalPreludePublicRole
                            candidate roleName)
            omega <- role FinalPrelude.PreludeOmegaObject
            naturals <- role FinalPrelude.PreludeNaturalsObject
            assertEqual "naturals expands to Omega"
                omega naturals
            traverse_
                (void . role)
                (Set.toList FinalPrelude.expectedFinalPreludePublicRoles)
            let foundationTags = Set.fromList
                    [ tag
                    | batch <-
                        Commit.pendingModulePrefixBatches
                            (FinalPrelude.finalPreludePrefix candidate)
                    , record <-
                        Commit.committedBatchProofValidations batch
                    , Authority.CheckedKernelConstruction
                        (Authority.FoundationLeaf tag) <-
                            [ Authority.validationDirectAuthorization
                                (Semantic.proofValidationRecordCertificate
                                    record)
                            ]
                    ]
            assertBool "protected foundation presentation"
                ( Set.fromList
                    [ Foundation.SetExtensionality
                    , Foundation.EmptyCharacteristic
                    , Foundation.PairSetCharacteristic
                    , Foundation.FamilyUnionCharacteristic
                    , Foundation.GlobalChoiceMember
                    ]
                    `Set.isSubsetOf` foundationTags
                )
            assertFinalPreludeFoundationAlias
                candidate
                "pairset_iff"
                Foundation.PairSetCharacteristic
            assertFinalPreludeFoundationAlias
                candidate
                "pair_eq_iff"
                Foundation.OrderedPairInjective
            assertFinalPreludeFoundationAlias
                candidate
                "fst_eq"
                Foundation.OrderedPairFirst
            assertFinalPreludeFoundationAlias
                candidate
                "snd_eq"
                Foundation.OrderedPairSecond
            assertFinalPreludeFoundationAlias
                candidate
                "pow_iff"
                Foundation.PowerSetCharacteristic
            assertFinalPreludeFoundationAlias
                candidate
                "universe_replacement_closed"
                Foundation.UnivOfReplacementClosed
            assertFinalPreludeFoundationAlias
                candidate
                "universe_minimal"
                Foundation.UnivOfMinimal
            assertFinalPreludeFactEligibility
                candidate
                "universe_replacement_closed"
                Semantic.SearchIneligible
            assertFinalPreludeFactEligibility
                candidate
                "universe_minimal"
                Semantic.SearchIneligible
            traverse_
                (\(name, tag) -> do
                    assertFinalPreludeGuardedRuleAlias
                        candidate name tag
                    assertFinalPreludeFactEligibility
                        candidate name Semantic.SearchIneligible)
                [ ("lfp_bound", Foundation.SetLfpBound)
                , ("lfp_least", Foundation.SetLfpLeast)
                , ("lfp_fixed", Foundation.SetLfpFixed)
                , ("lfp_induct", Foundation.SetLfpInduct)
                ]
            expectedUniversePremises <-
                traverse
                    (factFingerprintByAlias
                        (FinalPrelude.finalPreludePrefix candidate))
                    [ "universe_transitive"
                    , "universe_union_closed"
                    , "universe_power_closed"
                    , "universe_replacement_closed"
                    , "universe_minimal"
                    ]
            observed <- readIORef observations
            assertEqual
                "universe nesting uses source premises and operational axioms"
                [ ( Backend.RouteTh0
                  , expectedUniversePremises
                  , [ Foundation.FamilyUnionCharacteristic
                    , Foundation.PowerSetCharacteristic
                    , Foundation.ReplacementCharacteristic
                    ]
                  , 0
                  )
                ]
                [ observation
                | observation@(route, _facts, _auxiliaries, _selections) <-
                    observed
                , route == Backend.RouteTh0
                ]
            assertFinalPreludeSourceProof candidate "universe_nested"
            assertRejectsAdditionalOmegaFact candidate
            assertCachedSuccessorRecovery foundation candidate
        FinalPrelude.FinalPreludeBuildFailed failure prefix ->
            assertFailure
                ("final prelude failed after "
                    <> show
                        (length
                            (Commit.pendingModulePrefixBatches prefix))
                    <> " declarations: "
                    <> show failure)
        FinalPrelude.FinalPreludeBuildOpenFailed failure ->
            assertFailure ("final prelude did not open: " <> show failure)
        FinalPrelude.FinalPreludeSourceLoadFailed failure ->
            assertFailure ("final prelude did not load: " <> show failure)
        FinalPrelude.FinalPreludeSourceParseFailed failure ->
            assertFailure ("final prelude did not parse: " <> show failure)

assertCachedSuccessorRecovery
    :: Foundation.CheckedFoundation
    -> FinalPrelude.FinalPreludeCandidate
    -> Assertion
assertCachedSuccessorRecovery foundation candidate = do
    let parsed = FinalPrelude.finalPreludeParsed candidate
        semantic = FinalPrelude.finalPreludeSemantic candidate
        closure = FinalPrelude.finalPreludeObjects candidate
        basis = FinalPrelude.finalPreludeNaturalNumeralBasis candidate
        expected = Declaration.naturalNumeralBasisObject basis
        deltas = Semantic.semanticInterfaceDeclarations semantic
        sourceBlocks =
            [ block
            | block <- Parsed.identifiedParsedModuleBlocks
                (Prelude.reservedParsedPreludeModule parsed)
            , case block of
                Raw.BlockProof{} -> False
                _ -> True
            ]
        sucIndices =
            [ index
            | (index, block) <- zip [0 :: Int ..] sourceBlocks
            , case block of
                Raw.BlockDefn _location _title (Raw.Marker "suc") _definition ->
                    True
                _ -> False
            ]
    sucIndex <- case sucIndices of
        [single] -> pure single
        indices ->
            assertFailure
                ("unexpected packaged successor source count: " <> show indices)
                >> fail "unreachable"
    sucDelta <- case drop sucIndex deltas of
        delta : _ -> pure delta
        [] ->
            assertFailure "packaged successor has no aligned semantic delta"
                >> fail "unreachable"
    let sucEnvironment = Semantic.declarationDeltaEnvironment sucDelta
        sucBindings = Semantic.semanticEnvironmentBindings sucEnvironment
    sucBinding <- case sucBindings of
        [single] -> pure single
        bindings ->
            assertFailure
                ("unexpected packaged successor binding count: "
                    <> show (length bindings))
                >> fail "unreachable"

    recovered <- expectRight
        (FinalPrelude.recoverCachedFinalPreludeSuccessor
            foundation parsed semantic closure)
    assertEqual "cached recovery retains the validated successor"
        expected
        (Declaration.naturalNumeralBasisObject recovered)

    sourceInput <- expectRight =<< Prelude.loadReservedPreludeSourceInput
    let sourceText = Prelude.reservedPreludeSourceText sourceInput
        parseVariant label candidateText = do
            variantInput <- expectRight
                (Prelude.reservedPreludeSourceInput
                    (Text.encodeUtf8 candidateText))
            variant <- expectRight =<<
                Prelude.parseReservedPreludeSource variantInput
            pure (label, variant)
        assertParsedRejected expectedFailure (label, variant) =
            case FinalPrelude.recoverCachedFinalPreludeSuccessor
                    foundation variant semantic closure of
                Left actualFailure ->
                    assertEqual label expectedFailure actualFailure
                Right accepted ->
                    assertFailure
                        (label <> " recovered successor "
                            <> show
                                (Declaration.naturalNumeralBasisObject accepted))
    missingText <- replaceTextExactlyOnce
        "successor marker for missing-marker recovery"
        "\\label{suc}"
        "\\label{suc_missing}"
        sourceText
    duplicateText <- replaceTextExactlyOnce
        "transitive-set marker for duplicate-marker recovery"
        "\\label{transitiveset}"
        "\\label{suc}"
        sourceText
    nonDefinitionText <- replaceTextExactlyOnce
        "successor definition block for shape recovery"
        (StrictText.unlines
            [ "\\begin{definition}[Successor]\\label{suc}"
            , "    $\\suc{x} = \\unions{\\upair{\\upair{x}{x}}{x}}$."
            , "\\end{definition}"
            ])
        (StrictText.unlines
            [ "\\begin{abbreviation}[Successor]\\label{suc}"
            , "    $\\suc{x} = \\unions{\\upair{\\upair{x}{x}}{x}}$."
            , "\\end{abbreviation}"
            ])
        sourceText
    missing <- parseVariant "cached successor marker is missing" missingText
    duplicate <- parseVariant "cached successor marker is duplicated" duplicateText
    nonDefinition <- parseVariant
        "cached successor block is not a definition"
        nonDefinitionText
    assertParsedRejected
        (FinalPrelude.FinalPreludeDeclarationMissing "suc")
        missing
    assertParsedRejected
        (FinalPrelude.FinalPreludeDeclarationDuplicate "suc")
        duplicate
    assertParsedRejected
        (FinalPrelude.FinalPreludeDeclarationShapeMismatch "suc")
        nonDefinition

    let assertRejected label candidateSemantic candidateClosure =
            case FinalPrelude.recoverCachedFinalPreludeSuccessor
                    foundation parsed candidateSemantic candidateClosure of
                Left{} -> pure ()
                Right accepted ->
                    assertFailure
                        (label <> " recovered successor "
                            <> show
                                (Declaration.naturalNumeralBasisObject accepted))
        replaceAt index value values =
            take index values <> [value] <> drop (index + 1) values
        rebuildSemantic candidateDeltas =
            expectRight
                (Semantic.semanticInterface
                    (Semantic.semanticInterfaceOwner semantic)
                    (Semantic.semanticInterfaceDirectInputs semantic)
                    candidateDeltas)
        rebuildDelta template bindings structures = do
            environment <- expectRight
                (Semantic.semanticEnvironmentWithStructures bindings structures)
            expectRight
                (Semantic.declarationInterfaceDelta
                    (Semantic.declarationDeltaSlot template)
                    (Semantic.declarationDeltaFacts template)
                    (Semantic.declarationDeltaAliases template)
                    (Semantic.declarationDeltaObjects template)
                    (Semantic.declarationDeltaPropositions template)
                    (Semantic.declarationDeltaDefinitionViews template)
                    (Semantic.declarationDeltaRegistrations template)
                    environment)
        withSucBindings bindings = do
            altered <- rebuildDelta
                sucDelta
                bindings
                (Semantic.semanticEnvironmentStructures sucEnvironment)
            rebuildSemantic (replaceAt sucIndex altered deltas)
        retarget target binding =
            Semantic.semanticGlobalBindingWithMetadata
                (Semantic.semanticGlobalBindingKey binding)
                (Semantic.semanticGlobalBindingLabel binding)
                target
                (Semantic.semanticGlobalBindingContract binding)
                (Semantic.semanticGlobalBindingExpansion binding)

    (declarationDeltas, baseDelta) <- case reverse deltas of
        base : reversedDeclarations ->
            pure (reverse reversedDeclarations, base)
        [] ->
            assertFailure "packaged prelude has no semantic declarations"
                >> fail "unreachable"
    tooFew <- rebuildSemantic declarationDeltas
    assertRejected "declaration-count mismatch" tooFew closure

    invalidBase <- rebuildDelta baseDelta [] []
    invalidBaseSemantic <- rebuildSemantic
        (declarationDeltas <> [invalidBase])
    assertRejected "invalid trailing base structure"
        invalidBaseSemantic closure

    noBinding <- withSucBindings []
    assertRejected "successor without a binding" noBinding closure

    nonReference <- withSucBindings
        [retarget (Semantic.TransparentExpansion expected) sucBinding]
    assertRejected "successor with a non-reference binding"
        nonReference closure

    otherBinding <- case
        [ binding
        | (index, delta) <- zip [0 :: Int ..] deltas
        , index /= sucIndex
        , binding <- Semantic.semanticEnvironmentBindings
            (Semantic.declarationDeltaEnvironment delta)
        , Semantic.semanticGlobalBindingKey binding
            /= Semantic.semanticGlobalBindingKey sucBinding
        ] of
        binding : _ -> pure binding
        [] ->
            assertFailure "packaged prelude has no second global binding"
                >> fail "unreachable"
    multipleBindings <- withSucBindings
        (List.sortOn Semantic.semanticGlobalBindingKey
            [sucBinding, otherBinding])
    assertRejected "successor with multiple bindings"
        multipleBindings closure

    misaligned <- withSucBindings [otherBinding]
    assertRejected "successor aligned to another declaration delta"
        misaligned closure

    let theory = Identity.theoryId foundation
        wrongTyped =
            Identity.transparentObject
                theory Core.TySet (Core.CIntrinsic Core.Empty)
        opaque =
            Identity.opaqueObject
                theory
                (Identity.opaqueDeclarationSeed
                    preludeModuleName
                    (localDeclarationOrdinal 4096)
                    SignatureDeclaration
                    (generatedObjectSlot 0))
                (Core.TyArrow Core.TySet Core.TySet)
        wrongBodied =
            Identity.transparentObject
                theory
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet (Core.CBound 0))
        absent =
            Identity.transparentObject
                theory
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet (Core.CIntrinsic Core.Empty))
    malformedClosure <- expectRight
        (Identity.extendObjectClosure
            closure
            [wrongTyped, opaque, wrongBodied])
    for_
        [ ("absent successor object", absent, closure)
        , ("wrong-typed successor object", wrongTyped, malformedClosure)
        , ("opaque successor object", opaque, malformedClosure)
        , ("wrong-bodied successor object", wrongBodied, malformedClosure)
        ]
        \(label, object, candidateClosure) -> do
            alteredSemantic <- withSucBindings
                [retarget
                    (Semantic.GlobalReference
                        (Identity.assertedObjectId object))
                    sucBinding]
            assertRejected label alteredSemantic candidateClosure

replaceTextExactlyOnce
    :: String
    -> StrictText.Text
    -> StrictText.Text
    -> StrictText.Text
    -> IO StrictText.Text
replaceTextExactlyOnce label needle replacement source = do
    let (before, matched) = StrictText.breakOn needle source
    when (StrictText.null matched)
        (assertFailure (label <> ": source fragment is absent"))
    let suffix = StrictText.drop (StrictText.length needle) matched
    when (needle `StrictText.isInfixOf` suffix)
        (assertFailure (label <> ": source fragment is not unique"))
    pure (before <> replacement <> suffix)

assertRejectsAdditionalOmegaFact
    :: FinalPrelude.FinalPreludeCandidate
    -> Assertion
assertRejectsAdditionalOmegaFact candidate = do
    omegaId <-
        case FinalPrelude.finalPreludePublicRole
                candidate FinalPrelude.PreludeOmegaObject of
            Just (FinalPrelude.FinalPreludeObjectRole identity) ->
                pure identity
            role ->
                assertFailure ("unexpected Omega role " <> show role)
                    >> fail "unreachable"
    batch <- batchByAlias
        (FinalPrelude.finalPreludePrefix candidate)
        "omega"
    let delta = Commit.committedBatchDelta batch
        facts = Semantic.declarationDeltaFacts delta
        aliases = Semantic.declarationDeltaAliases delta
        propositions = Commit.committedBatchPropositions batch
    certificates <-
        maybe
            (assertFailure "Omega declaration validation is absent"
                >> fail "unreachable")
            (pure . Semantic.declarationValidationRecordCertificates)
            (Commit.committedBatchDeclarationValidation batch)
    (omegaBody, extensional, descriptor, extraFact, extraProposition,
            extraCertificate) <-
        case (facts, propositions, certificates) of
            ( [_equationFact, extensionalFact]
              , [equationProposition, extensionalProposition]
              , [ _equationCertificate
                , extensionalCertificate
                ]
              ) -> do
                body <- case Core.frozenCoreTerm
                        (Identity.checkedPropositionTerm equationProposition) of
                    Core.CEq Core.TySet
                            (Core.CGlobal identity) candidateBody
                        | identity == omegaId -> pure candidateBody
                    target ->
                        assertFailure
                            ("unexpected Omega equation " <> show target)
                            >> fail "unreachable"
                constructionDescriptor <-
                    case Authority.validationDirectAuthorization
                            extensionalCertificate of
                        Authority.CheckedKernelConstruction
                                (Authority.CheckedSetConstructionExtensionality
                                    identity candidateDescriptor)
                            | identity == omegaId -> pure candidateDescriptor
                        authorization ->
                            assertFailure
                                ("unexpected Omega extensional authority "
                                    <> show authorization)
                                >> fail "unreachable"
                pure
                    ( body
                    , Identity.checkedPropositionTerm extensionalProposition
                    , constructionDescriptor
                    , extensionalFact
                    , extensionalProposition
                    , extensionalCertificate
                    )
            (candidateFacts, candidatePropositions, candidateCertificates) ->
                assertFailure
                    ("unexpected Omega inventory shape "
                        <> show
                            ( length candidateFacts
                            , length candidatePropositions
                            , length candidateCertificates
                            ))
                    >> fail "unreachable"
    case FinalPrelude.validateOmegaFactInventory
            omegaId omegaBody extensional descriptor
            (facts <> [extraFact])
            aliases
            (propositions <> [extraProposition])
            (certificates <> [extraCertificate]) of
        Left (FinalPrelude.FinalPreludeFactContentMismatch
                "omega") ->
            pure ()
        result ->
            assertFailure
                ("additional Omega construction fact was accepted: "
                    <> show result)

publishesFinalPreludeRoot :: Assertion
publishesFinalPreludeRoot = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-final-prelude-root" \directory -> do
        let path = directory Posix.</> "store.sqlite"
            theory = Identity.theoryId foundation
            open = do
                (_startup, store) <-
                    Store.openStore path theory >>= expectRight
                pure store
        bracket open Store.closeStore \store -> do
            freshCheck <- Store.newStoreCheck store
            importCheck <- Declaration.newImportCheck foundation
            session <-
                expectRight
                    =<< Module.acquireFinalPreludeSession
                        importCheck freshCheck foundation finalPreludeResolver
            let input = Module.finalPreludeInput session
                sealed = Module.finalPreludeModule session
                syntax = Module.sealedTypedModuleSyntax sealed
                semantic = Module.sealedTypedModuleSemantic sealed
            assertEqual "empty store constructs the final-prelude root"
                Module.ModuleRootMiss
                (Module.finalPreludeAcquisition session)
            assertEqual "final prelude owner"
                preludeModuleName
                (Module.identifiedModuleOwner input)
            assertEqual "final prelude has no semantic parents"
                []
                (Semantic.semanticInterfaceDirectInputs semantic)
            warmCheck <- Store.newStoreCheck store
            warmSession <- expectRight
                =<< Module.acquireFinalPreludeSession
                    importCheck warmCheck foundation unusedResolver
            let cached = Module.finalPreludeModule warmSession
            assertEqual "persisted final-prelude root is a cache hit"
                Module.ModuleRootHit
                (Module.finalPreludeAcquisition warmSession)
            assertEqual "generic root syntax"
                syntax
                (Module.sealedTypedModuleSyntax cached)
            assertEqual "generic root semantics"
                semantic
                (Module.sealedTypedModuleSemantic cached)
            assertEqual "cached base structure descriptor"
                (Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence sealed))
                (Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence cached))
            repository <- getCurrentDirectory
            mounts <- exactFixtureMounts repository
            for_
                [ ("fresh", session)
                , ("cached", warmSession)
                ]
                \(label, readySession) -> do
                    numeralWorkspace <- parseFinalWorkspace
                        readySession
                        mounts
                        "test/phase8/natural-numeral-propagation.tex"
                    numeralModules <- compileFinalParsedWorkspaceWithResolver
                        foundation
                        readySession
                        unusedResolver
                        numeralWorkspace
                    assertEqual
                        (label <> " prelude carries usable numeral readiness")
                        1
                        (length numeralModules)
            checkedImports <- prepareTestImports (Identity.theoryId foundation)
                [Module.sealedTypedModuleEvidence cached]
            imported <- expectRight
                =<< Declaration.runModuleDriverFreshIO
                    foundation
                    (Module.sealedTypedModuleOwner cached)
                    checkedImports
                    unusedResolver
                    do
                        Declaration.resolveVisibleStructureDriver
                            (Schema.structurePhrase Lexicon._Onesorted)
            resolvedBase <-
                case imported of
                    Declaration.DriverSucceeded (Just structure) _ _ ->
                        pure structure
                    other ->
                        other `seq`
                            assertFailure
                                "cached base structure did not re-enter"
                            >> fail "unreachable"
            let baseSchema = Declaration.resolvedStructureSchema resolvedBase
            baseField <- sole "base structure field" (schemaLocalFields baseSchema)
            assertEqual "base definition retains its one-selector open shape"
                [Record.recordOpenShape [Core.CGlobal (Schema.resolvedFieldSelector baseField)] (Core.CBound 0)]
                (Predicate.structurePredicateComponents baseSchema)
            assertEqual "unbounded base carrier has no specification conjunct"
                Map.empty (Schema.resolvedSchemaRequirements baseSchema)
            assertEqual "generic root final prefix"
                (Declaration.evidenceFinalPrefix (Module.sealedTypedModuleEvidence sealed))
                (Declaration.evidenceFinalPrefix (Module.sealedTypedModuleEvidence cached))
            visits <- Store.storeCheckMemoVisits warmCheck
            assertEqual "cached prelude decodes one artefact root"
                1
                (Store.storeArtefactRowsDecoded visits)

checkedStructureSchemas :: Module.CompletedTypedModule -> [Schema.ResolvedStructureSchema]
checkedStructureSchemas = Declaration.evidenceLocalStructureSchemas . completedModuleEvidence

schemaLocalFields :: Schema.ResolvedStructureSchema -> [Schema.ResolvedField]
schemaLocalFields schema = List.sortOn Schema.resolvedFieldSlot
    [field | field <- Map.elems (Schema.resolvedSchemaFields schema), Schema.resolvedFieldOwner field == Schema.resolvedSchemaId schema]

schemaPredicate :: Schema.ResolvedStructureSchema -> Identity.ObjectId
schemaPredicate schema = Identity.transparentObjectId (Schema.resolvedSchemaTheory schema)
    (Predicate.structurePredicateType schema) (Predicate.structurePredicateBody schema)

schemaPreamble :: Schema.ResolvedStructureSchema -> [Core.CanonicalTerm Identity.ObjectId]
schemaPreamble schema = [Schema.resolvedRequirementBody requirement
    | requirement <- Map.elems (Schema.resolvedSchemaRequirements schema), Schema.requirementIsAdmissibility requirement]

schemaParents :: Schema.ResolvedStructureSchema -> [Schema.StructureApplicationKey]
schemaParents = Schema.resolvedPresentationParentOrder . Schema.resolvedSchemaPresentation

-- Integration checks associate facts by semantic law/resource keys. Candidate
-- scheduling is intentionally absent from this mathematical contract test.
assertGeneratedStructureInterface
    :: Declaration.ImportedModuleEvidence -> [Semantic.SemanticInterface]
    -> [Schema.ResolvedStructureSchema]
    -> Schema.ResolvedStructureSchema -> Commit.CommittedDeclarationBatch -> Assertion
assertGeneratedStructureInterface evidence interfaces schemas schema batch = do
    let closure = Declaration.evidenceClosure evidence
    registrations <- traverse (\candidate -> expectRight
        (Predicate.checkPendingStructureRegistration closure candidate (schemaPredicate candidate))) schemas
    let registrationMap = Map.fromList [(Schema.resolvedSchemaId (Predicate.pendingStructureSchema candidate), candidate)
            | candidate <- registrations]
        owner = Schema.resolvedSchemaId schema
        registration = fromMaybe (impossible "fixture lost its local registration") (Map.lookup owner registrationMap)
    catalogue <- expectRight (StructureLaws.checkStructureCatalogue closure (Set.singleton owner)
        (`Map.lookup` registrationMap) registration)
    wire <- sole "local checked interface wire"
        (Semantic.semanticEnvironmentStructures (Semantic.declarationDeltaEnvironment (Commit.committedBatchDelta batch)))
    let allFacts = concatMap (concatMap Semantic.declarationDeltaFacts . Semantic.semanticInterfaceDeclarations) interfaces
        facts = Map.fromList [(Semantic.semanticFactFingerprint fact, fact) | fact <- allFacts]
        localFacts = Semantic.declarationDeltaFacts (Commit.committedBatchDelta batch)
        certificates = maybe [] Semantic.declarationValidationRecordCertificates (Commit.committedBatchDeclarationValidation batch)
    assertEqual "one certificate per exact occurrence" (length localFacts) (length certificates)
    let certificatesByFingerprint = Map.fromList [(Semantic.semanticFactFingerprint fact, certificate)
            | (fact, certificate) <- zip localFacts certificates]
        factTarget fingerprint = do
            fact <- maybe (assertFailure "indexed fact missing" >> fail "unreachable") pure (Map.lookup fingerprint facts)
            proposition <- maybe (assertFailure "indexed proposition missing" >> fail "unreachable") pure
                (Declaration.evidenceFactTarget evidence fingerprint)
            pure (fact, proposition)
        assertTarget label expected fact proposition = do
            assertEqual (label <> " identity") (Identity.checkedPropositionId expected) (Semantic.semanticFactProposition fact)
            assertEqual label (Identity.checkedPropositionTerm expected) proposition
    assertEqual "complete law-key inventory" (Map.keysSet (StructureLaws.structureCatalogueLaws catalogue))
        (Map.keysSet (Semantic.structureWireLawIndex wire))
    for_ (Map.toAscList (StructureLaws.structureCatalogueLaws catalogue)) \(law, spec) -> do
        let fingerprint = fromMaybe (impossible "checked inventory lost a law") (Map.lookup law (Semantic.structureWireLawIndex wire))
        (fact, proposition) <- factTarget fingerprint
        certificate <- maybe (assertFailure "local law certificate missing" >> fail "unreachable") pure
            (Map.lookup fingerprint certificatesByFingerprint)
        assertTarget ("exact target for " <> show law) (StructureLaws.generatedLawProposition spec) fact proposition
        assertEqual "actual structural purpose" (Semantic.structureLawPurpose (Schema.StructureLawId owner law)) (Semantic.semanticFactPurpose fact)
        assertEqual "exact generated mechanism" (Authority.CheckedKernelConstruction
            (Authority.CheckedStructureLaw (StructureLaws.structureLawFamily law))) (Authority.validationDirectAuthorization certificate)
        assertEqual "certificate addresses the actual occurrence" (Semantic.semanticFactAuthority fact) (Authority.validationTarget certificate)
        assertEqual "search eligibility follows source presentation" (fst (StructureLaws.structureLawPresentation schema law))
            (Semantic.semanticFactSearchEligibility fact)
    assertEqual "complete resource-key inventory" (Map.keysSet (StructureLaws.structureCatalogueResources catalogue))
        (Map.keysSet (Semantic.structureWireResourceIndex wire))
    for_ (Map.toAscList (StructureLaws.structureCatalogueResources catalogue)) \(key, expected) -> do
        let fingerprint = fromMaybe (impossible "checked inventory lost a resource") (Map.lookup key (Semantic.structureWireResourceIndex wire))
        (fact, proposition) <- factTarget fingerprint
        assertTarget ("exact resource target for " <> show key) expected fact proposition
        assertEqual "resources remain ordinary facts" Semantic.GeneralFactPurpose (Semantic.semanticFactPurpose fact)

assertTransparentObjectAlias
    :: Module.CompletedTypedModule
    -> Text
    -> Assertion
assertTransparentObjectAlias sealed name = do
    target <- localObjectAliasTarget sealed name
    assertEqual
        ("transparent object for " <> StrictText.unpack name)
        Identity.TransparentObject
        (Identity.objectIdFamily target)

localObjectKeyTarget
    :: Module.CompletedTypedModule
    -> Semantic.SemanticGlobalKey
    -> IO Identity.ObjectId
localObjectKeyTarget sealed key = do
    binding <- sole
        ("semantic binding for " <> show key)
        [ candidate
        | delta <- localSemanticDeltas sealed
        , candidate <- Semantic.semanticEnvironmentBindings
            (Semantic.declarationDeltaEnvironment delta)
        , Semantic.semanticGlobalBindingKey candidate == key
        ]
    pure
        (Semantic.semanticGlobalTargetObject
            (Semantic.semanticGlobalBindingTarget binding))

localObjectAliasTarget
    :: Module.CompletedTypedModule
    -> Text
    -> IO Identity.ObjectId
localObjectAliasTarget sealed name = do
    delta <- localDeltaByAlias sealed name
    binding <- sole
        ("semantic binding for " <> StrictText.unpack name)
        (Semantic.semanticEnvironmentBindings
            (Semantic.declarationDeltaEnvironment delta))
    pure
        (Semantic.semanticGlobalTargetObject
            (Semantic.semanticGlobalBindingTarget binding))

checkedPropositionTermByAlias
    :: Module.CompletedTypedModule
    -> Text
    -> IO (Core.FrozenCheckedCore Identity.ObjectId)
checkedPropositionTermByAlias sealed name = do
    batch <- batchByAlias
        (Module.completedTypedModulePrefix sealed)
        name
    alias <- sole
        ("semantic alias for " <> StrictText.unpack name)
        [ candidate
        | candidate <- Semantic.declarationDeltaAliases
            (Commit.committedBatchDelta batch)
        , Semantic.semanticAliasName candidate
            == Semantic.semanticName name
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

batchByAlias
    :: Commit.PendingModulePrefix
    -> Text
    -> IO Commit.CommittedDeclarationBatch
batchByAlias prefix name =
    sole
        ("declaration batch for " <> StrictText.unpack name)
        [ batch
        | batch <- Commit.pendingModulePrefixBatches prefix
        , alias <- Semantic.declarationDeltaAliases
            (Commit.committedBatchDelta batch)
        , Semantic.semanticAliasName alias
            == Semantic.semanticName name
        ]


assertFinalPreludeFoundationAlias
    :: FinalPrelude.FinalPreludeCandidate
    -> Text
    -> Foundation.FoundationAxiomTag
    -> Assertion
assertFinalPreludeFoundationAlias candidate name tag = do
    batch <- batchByAlias
        (FinalPrelude.finalPreludePrefix candidate)
        name
    fact <- sole
        ("foundation fact " <> StrictText.unpack name)
        (Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch))
    assertEqual
        ("foundation safety for " <> StrictText.unpack name)
        Authority.cleanAuthoritySafety
        (Authority.factAuthoritySafety
            (Semantic.semanticFactAuthority fact))
    validation <- sole
        ("foundation validation for " <> StrictText.unpack name)
        (Commit.committedBatchProofValidations batch)
    assertEqual
        ("exact foundation authority for " <> StrictText.unpack name)
        (Authority.CheckedKernelConstruction
            (Authority.FoundationLeaf tag))
        (Authority.validationDirectAuthorization
            (Semantic.proofValidationRecordCertificate validation))

assertFinalPreludeGuardedRuleAlias
    :: FinalPrelude.FinalPreludeCandidate
    -> Text
    -> Foundation.KernelRuleTag
    -> Assertion
assertFinalPreludeGuardedRuleAlias candidate name tag = do
    batch <- batchByAlias
        (FinalPrelude.finalPreludePrefix candidate)
        name
    fact <- sole
        ("guarded-rule fact " <> StrictText.unpack name)
        (Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch))
    assertEqual
        ("guarded-rule safety for " <> StrictText.unpack name)
        Authority.cleanAuthoritySafety
        (Authority.factAuthoritySafety
            (Semantic.semanticFactAuthority fact))
    validation <- sole
        ("guarded-rule validation for " <> StrictText.unpack name)
        (Commit.committedBatchProofValidations batch)
    assertEqual
        ("exact guarded-rule authority for " <> StrictText.unpack name)
        (Authority.CheckedKernelConstruction
            (Authority.GuardedFoundationRules
                (Authority.guardedRuleSet (tag :| []))))
        (Authority.validationDirectAuthorization
            (Semantic.proofValidationRecordCertificate validation))

assertFinalPreludeFactEligibility
    :: FinalPrelude.FinalPreludeCandidate
    -> Text
    -> Semantic.FactSearchEligibility
    -> Assertion
assertFinalPreludeFactEligibility candidate name expected = do
    batch <- batchByAlias
        (FinalPrelude.finalPreludePrefix candidate)
        name
    fact <- sole
        ("prelude fact " <> StrictText.unpack name)
        (Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch))
    assertEqual
        ("search eligibility for " <> StrictText.unpack name)
        expected
        (Semantic.semanticFactSearchEligibility fact)

assertFinalPreludeSourceProof
    :: FinalPrelude.FinalPreludeCandidate
    -> Text
    -> Assertion
assertFinalPreludeSourceProof candidate name = do
    batch <- batchByAlias
        (FinalPrelude.finalPreludePrefix candidate)
        name
    validation <- sole
        ("source proof validation for " <> StrictText.unpack name)
        (Commit.committedBatchProofValidations batch)
    case Authority.validationDirectAuthorization
            (Semantic.proofValidationRecordCertificate validation) of
        Authority.CheckedSourceProof
                (Authority.UsesExternalProof (_request :| [])) ->
            pure ()
        authorization ->
            assertFailure
                ("unexpected source proof authority for "
                    <> StrictText.unpack name
                    <> ": "
                    <> show authorization)

factFingerprintByAlias
    :: Commit.PendingModulePrefix
    -> Text
    -> IO Semantic.SemanticFactOccurrenceFingerprint
factFingerprintByAlias prefix name = do
    batch <- batchByAlias prefix name
    alias <- sole
        ("fact alias for " <> StrictText.unpack name)
        [ candidate
        | candidate <- Semantic.declarationDeltaAliases
            (Commit.committedBatchDelta batch)
        , Semantic.semanticAliasName candidate == Semantic.semanticName name
        ]
    pure (Semantic.semanticAliasTarget alias)

localDeltaByAlias
    :: Module.CompletedTypedModule
    -> Text
    -> IO Semantic.DeclarationInterfaceDelta
localDeltaByAlias sealed name =
    sole
        ("declaration delta for " <> StrictText.unpack name)
        [ delta
        | delta <- localSemanticDeltas sealed
        , any
            ((== Semantic.semanticName name)
                . Semantic.semanticAliasName)
            (Semantic.declarationDeltaAliases delta)
        ]

localSemanticDeltas
    :: Module.CompletedTypedModule
    -> [Semantic.DeclarationInterfaceDelta]
localSemanticDeltas =
    Semantic.semanticInterfaceDeclarations
        . completedModuleSemantic

retainsOmittedProofLocation :: Assertion
retainsOmittedProofLocation = do
    foundation <- expectRight Foundation.checkedFoundation
    source <-
        expectRight
            (Prelude.reservedPreludeSourceInput
                (Text.encodeUtf8
                    (StrictText.unlines
                        [ "\\begin{proposition}\\label{omitted_location}"
                        , "    For all $x$ we have $x = x$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "    Omitted."
                        , "\\end{proof}"
                        ])))
    parsed <- expectRight =<< Prelude.parseReservedPreludeSource source
    let blocks =
            Parsed.identifiedParsedModuleBlocks
                (Prelude.reservedParsedPreludeModule parsed)
    claim <- sole "omitted claim"
        [ block
        | block@Raw.BlockClaim{} <- blocks
        ]
    proof <- sole "omitted proof"
        [ sourceProof
        | Raw.BlockProof _location sourceProof _end <- blocks
        ]
    outcome <-
        runModuleDriver
            foundation
            preludeModuleName
            []
            unusedResolver
            AlwaysMissValidation do
                Declaration.runProspectiveLoweringDriver
                    (Proof.prepareProof claim (Just proof))
                    >>= either Declaration.failModuleDriver pure
    case outcome of
        Right (Declaration.DriverSucceeded
                prepared _semantic prefix) -> do
            location <-
                maybe
                    (assertFailure "prepared omitted proof lost its location")
                    pure
                    (Proof.preparedProofFirstOmission prepared)
            assertEqual "omitted source line" 5 (locLine location)
            assertBool "preparation publishes no declaration"
                (null (Commit.pendingModulePrefixBatches prefix))
        Right (Declaration.DriverFailed failure _prefix) ->
            assertFailure ("omitted preparation failed: " <> show failure)
        Right (Declaration.DriverSealFailed failure _prefix) ->
            assertFailure ("omitted preparation did not seal: " <> show failure)
        Left failure ->
            assertFailure ("omitted preparation did not open: " <> show failure)

coalescesSharedDirectSyntax :: Assertion
coalescesSharedDirectSyntax = do
    foundation <- expectRight Foundation.checkedFoundation
    session <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    root <- getCurrentDirectory
    mounts <-
        expectRight
            =<< prepareSourceMounts
                [ (sourceMountId "project", root)
                , (sourceMountId "library", root Posix.</> "library")
                , (sourceMountId "debug", root Posix.</> "debug")
                ]
    let bootstrapSyntax =
            completedModuleSyntax
                (Module.bootstrapPreludeCompleted session)
        syntaxInputs _source = [bootstrapSyntax]
    request <-
        expectRight
            (searchedRoot "test/phase3/typed-shared-root.tex")
    workspace <-
        expectRight
            =<< Parse.parseSourceWorkspaceWithSyntaxInputs
                mounts
                request
                syntaxInputs
    case Parsed.parsedWorkspaceModules workspace of
        [firstParsed, secondParsed, rootParsed] -> do
            first <- seal foundation session firstParsed []
            second <- seal foundation session secondParsed []
            assertEqual "distinct modules share one syntax interface"
                (Syntax.moduleSyntaxAssertedId
                    (completedModuleSyntax first))
                (Syntax.moduleSyntaxAssertedId
                    (completedModuleSyntax second))
            assertBool "semantic module owners remain distinct"
                (completedModuleOwner first
                    /= completedModuleOwner second)
            assertBool "semantic interfaces remain distinct"
                (Semantic.semanticInterfaceAssertedId
                    (completedModuleSemantic first)
                    /= Semantic.semanticInterfaceAssertedId
                        (completedModuleSemantic second))
            let rootSyntax = Parsed.parsedModuleSyntaxInterface rootParsed
            assertEqual "root coalesces the shared direct syntax"
                [ Syntax.moduleSyntaxAssertedId bootstrapSyntax
                , Syntax.moduleSyntaxAssertedId
                    (completedModuleSyntax first)
                ]
                (Syntax.moduleSyntaxDirectInputs rootSyntax)
            sealedRoot <-
                seal foundation session rootParsed [first, second]
            assertEqual "root retains both semantic imports"
                [ Semantic.semanticInterfaceAssertedId
                    (completedModuleSemantic
                        (Module.bootstrapPreludeCompleted session))
                , Semantic.semanticInterfaceAssertedId
                    (completedModuleSemantic first)
                , Semantic.semanticInterfaceAssertedId
                    (completedModuleSemantic second)
                ]
                (Semantic.semanticInterfaceDirectInputs
                    (completedModuleSemantic sealedRoot))
        modules ->
            assertFailure
                ("unexpected shared-syntax module count: "
                    <> show (length modules))
  where
    seal foundation session parsed direct = do
        input <-
            expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness session)
                    unusedResolver
                    AlwaysMissValidation
                    parsed
                    direct)
        runTypedModule input >>= \case
            Module.TypedModuleSucceeded sealed ->
                pure sealed
            Module.TypedModuleOpenFailed{} ->
                assertFailure "empty typed module did not open"
                    >> fail "unreachable"
            Module.TypedModuleFailed{} ->
                assertFailure "empty typed module did not seal"
                    >> fail "unreachable"

rejectsUnsupportedTypedSource :: Assertion
rejectsUnsupportedTypedSource = do
    result <-
            (checkFileFresh
                (Provers.vampire
                    "vampire"
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                "test/phase3/typed-unsupported.tex")
    case result of
        Right
            ( Verification.VerificationCheckingFailure _report
                (failure@(Verification.VerificationTypedModuleError
                source
                (Module.TypedActionFailed
                    (Module.TypedElaborationFailed
                        (Elaboration.ElaborationGuardedOpaqueSignature location)))
                prefix))
            , _slowReport
            ) -> do
            assertEqual "failed source"
                "test/phase3/typed-unsupported.tex"
                (safeRelativePathFilePath
                    (resolvedSourceRelativePath source))
            assertEqual "unsupported source location line"
                2
                (locLine location)
            assertEqual "failure retains the initial module prefix"
                0
                (length
                    (Commit.pendingModulePrefixBatches prefix))
            let diagnostic =
                    Verification.renderVerificationDriverError failure
            assertBool "diagnostic retains resolved source"
                ("project:test/phase3/typed-unsupported.tex"
                    `StrictText.isInfixOf` diagnostic)
            assertBool "diagnostic retains best location"
                ("typed-unsupported.tex 2:14"
                    `StrictText.isInfixOf` diagnostic)
            assertBool "diagnostic explains the typed failure"
                ("opaque signature cannot have a header assumption"
                    `StrictText.isInfixOf` diagnostic)
        Left err ->
            assertFailure ("unexpected verification driver error: " <> show err)
        Right{} ->
            assertFailure "unsupported typed source was admitted"

rejectsOverflowingSourceInteger :: Assertion
rejectsOverflowingSourceInteger =
    Temp.withSystemTempDirectory "felix-large-integer" \root -> do
        let relative = "large-integer.tex"
            sourcePath = root Posix.</> relative
            source = StrictText.unlines
                [ "\\begin{proposition}\\label{large_literal_collision}"
                , "    $18446744073709551616 = 0$."
                , "\\end{proposition}"
                , "\\begin{proof}"
                , "    Follows."
                , "\\end{proof}"
                ]
        ByteString.writeFile sourcePath (Text.encodeUtf8 source)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        parsed <- sole "large integer module"
            (toList
                (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                (Declaration.vampireResolver \_prepared ->
                    assertFailure "large integer proof invoked Vampire"
                        >> fail "unreachable")
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofElaborationFailed
                                (Elaboration.ElaborationNaturalNumeralMagnitudeExceeded
                                    _location actual supportedMaximum))))
                    _prefix -> do
                assertEqual "overflow diagnostic magnitude"
                    18446744073709551616 actual
                assertEqual "overflow diagnostic maximum"
                    1024 supportedMaximum
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("large numeral produced the wrong failure: "
                        <> show failure)
            Module.TypedModuleSucceeded{} ->
                assertFailure
                    "overflowed source integer was admitted as a reflexive equality"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("large integer module did not reach checking: "
                        <> show failure)

propagatesNaturalNumeralReadiness :: Assertion
propagatesNaturalNumeralReadiness =
    Temp.withSystemTempDirectory "felix-natural-numeral-propagation" \root -> do
        foundation <- expectRight Foundation.checkedFoundation
        (_startup, store) <-
            Store.openStore
                (root Posix.</> "store.sqlite")
                (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <- expectRight
                =<< acquireFinalPreludeSession
                    opened foundation finalPreludeResolver
            repository <- getCurrentDirectory
            mounts <- exactFixtureMounts repository
            workspace <- parseFinalWorkspace
                prelude mounts "test/phase8/natural-numeral-propagation.tex"
            sealedModules <- compileFinalParsedWorkspaceWithResolver
                foundation prelude unusedResolver workspace
            assertEqual
                "natural-numeral propagation fixture seals one module"
                1
                (length sealedModules)

compilesDeclarationGraph :: Assertion
compilesDeclarationGraph = do
    (_foundation, _bootstrap, workspace, sealedModules) <-
        compileFixture "test/phase5/exact-importer.tex"
    assertEqual "dependency-closed module count" 2 (length sealedModules)
    assertEqual "imported-before-importer source order"
        [ "test/phase5/exact-producer.tex"
        , "test/phase5/exact-importer.tex"
        ]
        [ safeRelativePathFilePath
            (resolvedSourceRelativePath
                (Parsed.parsedModuleResolved parsed))
        | parsed <- toList
            (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
        ]
    case sealedModules of
        [producer, importer] -> do
            let producerPrefix = Module.completedTypedModulePrefix producer
                importerPrefix = Module.completedTypedModulePrefix importer
                producerBatches =
                    Commit.pendingModulePrefixBatches producerPrefix
                importerBatches =
                    Commit.pendingModulePrefixBatches importerPrefix
            assertEqual "producer declaration batches" 3
                (length producerBatches)
            assertEqual "importer declaration batches" 1
                (length importerBatches)
            assertEqual "producer declaration order"
                [0, 1, 2]
                [ localDeclarationOrdinalValue
                    (Semantic.declarationSlotOrdinal
                        (Commit.committedBatchSlot batch))
                | batch <- producerBatches
                ]

            let producerDeltas =
                    Semantic.semanticInterfaceDeclarations
                        (completedModuleSemantic producer)
                importerDeltas =
                    Semantic.semanticInterfaceDeclarations
                        (completedModuleSemantic importer)
            assertEqual "one exact binding per producer declaration"
                [1, 1, 1]
                (bindingCount <$> producerDeltas)
            assertEqual "one exact importer binding"
                [1]
                (bindingCount <$> importerDeltas)
            assertEqual "producer object families"
                ["opaque", "transparent"]
                [ objectFamilyName
                    (Identity.assertedObjectContent object)
                | batch <- producerBatches
                , object <- Commit.committedBatchObjects batch
                ]

            definitionDelta <- sole "producer definition delta"
                (drop 2 producerDeltas)
            definitionBinding <- sole "producer definition binding"
                (bindings definitionDelta)
            definitionFact <- sole "producer definition fact"
                (Semantic.declarationDeltaFacts definitionDelta)
            definitionAlias <- sole "producer definition alias"
                (Semantic.declarationDeltaAliases definitionDelta)
            assertEqual "definition alias"
                (Semantic.semanticName "phase5_definition")
                (Semantic.semanticAliasName definitionAlias)
            assertEqual "definition is proof-search eligible"
                Semantic.SearchEligible
                (Semantic.semanticFactSearchEligibility definitionFact)
            assertEqual "definition authority is clean"
                Authority.cleanAuthoritySafety
                (Authority.factAuthoritySafety
                    (Semantic.semanticFactAuthority definitionFact))
            definitionBatch <- sole "producer definition batch"
                (drop 2 producerBatches)
            validation <-
                maybe
                    (assertFailure "definition declaration validation is absent"
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation
                        definitionBatch)
            certificate <- sole "definition validation certificate"
                (Semantic.declarationValidationRecordCertificates validation)
            assertEqual "direct defining-equation authority"
                (Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionEquation
                        (Semantic.semanticGlobalTargetObject
                            (Semantic.semanticGlobalBindingTarget
                                definitionBinding))))
                (Authority.validationDirectAuthorization
                    certificate)

            aliasDelta <- sole "producer abbreviation delta"
                (take 1 (drop 1 producerDeltas))
            aliasBinding <- sole "producer abbreviation binding"
                (bindings aliasDelta)
            seedDelta <- sole "producer signature delta"
                (take 1 producerDeltas)
            seedBinding <- sole "producer signature binding"
                (bindings seedDelta)
            let seedTarget =
                    Semantic.semanticGlobalTargetObject
                        (Semantic.semanticGlobalBindingTarget seedBinding)
                aliasTarget =
                    Semantic.semanticGlobalTargetObject
                        (Semantic.semanticGlobalBindingTarget aliasBinding)
                definitionTarget =
                    Semantic.semanticGlobalTargetObject
                        (Semantic.semanticGlobalBindingTarget
                            definitionBinding)
            assertEqual "abbreviation expands transparently"
                (Semantic.TransparentExpansion
                    aliasTarget)
                (Semantic.semanticGlobalBindingTarget aliasBinding)
            assertEqual "definition remains a named global"
                (Semantic.GlobalReference definitionTarget)
                (Semantic.semanticGlobalBindingTarget definitionBinding)
            assertEqual "definition content coalesces with its expansion"
                aliasTarget
                definitionTarget
            assertEqual "coalesced definition adds no object"
                []
                (Commit.committedBatchObjects definitionBatch)
            aliasBatch <- sole "producer abbreviation batch"
                (take 1 (drop 1 producerBatches))
            aliasObject <- sole "producer abbreviation object"
                (Commit.committedBatchObjects aliasBatch)
            case Identity.assertedObjectContent aliasObject of
                Identity.TransparentObjectContent _theory _coreType body ->
                    assertEqual
                        "expanded body retains only the opaque seed"
                        (Set.singleton seedTarget)
                        (Core.canonicalTermGlobals body)
                content ->
                    assertFailure
                        ("abbreviation object is not transparent: "
                            <> show content)
            importerBatch <- sole "importer declaration batch" importerBatches
            importerDelta <- sole "importer semantic delta" importerDeltas
            importerBinding <- sole "importer binding"
                (bindings importerDelta)
            assertEqual "equal transparent content reuses the producer object"
                (Semantic.semanticGlobalBindingTarget definitionBinding)
                (Semantic.semanticGlobalBindingTarget importerBinding)
            assertEqual "reused transparent content adds no object"
                []
                (Commit.committedBatchObjects importerBatch)
        modules ->
            assertFailure
                ("unexpected exact module count: " <> show (length modules))
  where
    bindingCount = length . bindings

    bindings =
        Semantic.semanticEnvironmentBindings
            . Semantic.declarationDeltaEnvironment

    objectFamilyName :: Identity.ObjectContent -> String
    objectFamilyName = \case
        Identity.OpaqueObjectContent{} -> "opaque"
        Identity.TransparentObjectContent{} -> "transparent"
        Identity.IntrinsicObjectContent{} -> "intrinsic"

compilesExtensionalEquality :: Assertion
compilesExtensionalEquality = do
    (_, _, _, modules) <- compileFixture "test/phase8/eta-equality.tex"
    sealed <- sole "extensional equality source module" modules
    let batches = Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)
        validations = concatMap Commit.committedBatchProofValidations batches
    assertEqual "three internally sealed proofs" 3 (length validations)
    for_ validations \validation -> assertEqual "no external proof authority"
        (Authority.CheckedSourceProof Authority.NoExternalProofUse)
        (Authority.validationDirectAuthorization (Semantic.proofValidationRecordCertificate validation))

compilesTypedSymbolicExpressions :: Assertion
compilesTypedSymbolicExpressions = do
    (_foundation, _bootstrap, _workspace, sealedModules) <-
        compileFixture "test/phase8/typed-signature.tex"
    sealed <- sole "typed symbolic fixture module" sealedModules
    let declaredKeys =
            [ Semantic.semanticGlobalBindingKey binding
            | delta <- localSemanticDeltas sealed
            , binding <-
                Semantic.semanticEnvironmentBindings
                    (Semantic.declarationDeltaEnvironment delta)
            ]
    assertBool
        "set predicate retains its exact type"
        (Semantic.SemanticTypedConstant
            (Raw.Command "mathcalP")
            (Core.TyArrow Core.TySet Core.TyProp)
            `elem` declaredKeys)
    assertBool
        "function predicate retains its higher-order argument"
        (Semantic.SemanticTypedConstant
            (Raw.Command "mathcalH")
            (Core.TyArrow
                (Core.TyArrow Core.TySet Core.TySet)
                Core.TyProp)
            `elem` declaredKeys)
    let identityKey =
            Semantic.SemanticTypedConstant
                (Raw.Command "mathcalI")
                (Core.TyArrow Core.TySet Core.TySet)
    assertBool
        "typed definition retains its exact type"
        (identityKey `elem` declaredKeys)
    identity <- localObjectKeyTarget sealed identityKey
    assertEqual
        "typed definition is transparent"
        Identity.TransparentObject
        (Identity.objectIdFamily identity)
    explicitSelection <-
        checkedPropositionTermByAlias sealed "typed_select_explicit"
    nestedApplication <-
        checkedPropositionTermByAlias sealed "typed_nested_application"
    compactApplication <-
        checkedPropositionTermByAlias sealed "typed_compact_application"
    assertEqual
        "compact application preserves the checked curried term"
        (Core.frozenCoreTerm nestedApplication)
        (Core.frozenCoreTerm compactApplication)
    case Core.frozenCoreTerm explicitSelection of
        Core.CEq Core.TySet inferred explicit -> do
            assertEqual
                "inferred and explicitly typed selection are canonical-equal"
                inferred
                explicit
            case inferred of
                Core.CApp (Core.CLogicalSelect Core.TySet) _predicate ->
                    pure ()
                term ->
                    assertFailure
                        ("unexpected inferred selection term: " <> show term)
        term ->
            assertFailure
                ("unexpected explicit selection proposition: " <> show term)


compilesSetMapAssertions :: Assertion
compilesSetMapAssertions =
    withAcceptedFixtureVampire "set-map-assertion" \vampire -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace
            bootstrap mounts "test/phase8/set-map-assertion.tex"
        observations <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    request =
                        Provers.preparedTypedProverRequest prepared
                modifyIORef' observations
                    (<> [ ( Backend.typedProblemRoute problem
                           , Provers.preparedVerificationDialect request
                           , Provers.preparedVerificationText request
                           )
                        ])
                Provers.runPreparedTypedProver vampire prepared
        modules <- compileParsedWorkspaceWithResolver
            foundation bootstrap resolver workspace
        sealed <- sole "set-map assertion module" modules
        arrow <- checkedPropositionTermByAlias sealed "set_map_arrow"
        expanded <- checkedPropositionTermByAlias sealed "set_map_expanded"
        assertEqual
            "set-map arrow lowers to function-set membership"
            expanded
            arrow
        assertEqual
            "set-map assertion is structurally first-order"
            Foundation.FoundationFofProjectable
            (Foundation.classifyFrozenCore arrow)
        readIORef observations >>= \case
            [(Backend.RouteFof, Provers.VerificationFof, problemText)] ->
                assertBool
                    "complete exported problem contains no TH0 declarations"
                    (not ("thf(" `StrictText.isInfixOf` problemText))
            observed ->
                assertFailure
                    ("unexpected set-map backend observations: "
                        <> show observed)


rejectsLogicalFunctionInSetMapAssertion :: Assertion
rejectsLogicalFunctionInSetMapAssertion = do
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
            bootstrap
            mounts
            "test/phase8/set-map-logical-function.tex"
    parsed <- sole "ill-typed set-map module"
        (toList
            (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
    input <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            parsed
            [])
    runTypedModule input >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedElaborationFailed
                        (Elaboration.ElaborationExpressionExpectedSet
                            location actual)))
                prefix -> do
            assertEqual "logical-function source line" 11 (locLine location)
            assertEqual
                "logical function retains its concrete type"
                (Core.TyArrow Core.TySet Core.TyProp)
                actual
            assertEqual
                "failure retains both preceding signatures"
                2
                (length
                    (Commit.pendingModulePrefixBatches prefix))
        _result ->
            assertFailure
                "checking did not reject the logical function as a set"

rejectsMismatchedLogicalSelectionAnnotation :: Assertion
rejectsMismatchedLogicalSelectionAnnotation = do
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
            bootstrap
            mounts
            "test/phase8/typed-select-mismatch.tex"
    parsed <- sole "mismatched selection module"
        (toList
            (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
    input <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            parsed
            [])
    runTypedModule input >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedElaborationFailed
                        (Elaboration.ElaborationSelectionTypeMismatch
                            location expected actual)))
                prefix -> do
            assertEqual "mismatch source line" 6 (locLine location)
            assertEqual "annotated selection type" Core.TyProp expected
            assertEqual "predicate-selected type" Core.TySet actual
            assertEqual
                "mismatch retains only the preceding signature"
                1
                (length
                    (Commit.pendingModulePrefixBatches prefix))
        _result ->
            assertFailure
                "checking did not report the selection-type mismatch"

preparesTypedProofContexts :: Assertion
preparesTypedProofContexts = do
    foundation <- expectRight Foundation.checkedFoundation
    source <-
        expectRight
            (Prelude.reservedPreludeSourceInput
                (Text.encodeUtf8
                    (StrictText.unlines
                        [ "\\begin{proposition}\\label{typed_explicit_fix}"
                        , "  $\\forall p:\\Prop.\\ p \\implies p$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "  Fix $p:\\Prop$."
                        , "  Assume $p$."
                        , "  Follows by assumption."
                        , "\\end{proof}"
                        , "\\begin{proposition}\\label{typed_inferred_fix}"
                        , "  $\\forall p:\\Prop.\\ p \\iff p$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "  Fix $p$."
                        , "  Follows."
                        , "\\end{proof}"
                        , "\\begin{proposition}\\label{typed_local_definition}"
                        , "  $\\forall p:\\Prop.\\ p \\iff p$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "  Fix $p:\\Prop$."
                        , "  Let $q:\\Prop = p$."
                        , "  Follows by definition."
                        , "\\end{proof}"
                        , "\\begin{proposition}\\label{typed_take}"
                        , "  $\\exists p:\\Prop.\\ p \\iff p$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "  Take $p:\\Prop$ such that $p \\iff p$ by \\auto."
                        , "  Follows by \\auto."
                        , "\\end{proof}"
                        , "\\begin{proposition}\\label{grouped_fix}"
                        , "  $\\forall A. \\forall x. x\\in A \\implies (x\\neq\\emptyset \\implies x\\in A)$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "  Fix $A$ and $x\\in A$ such that $x\\neq\\emptyset$."
                        , "  Follows by assumption."
                        , "\\end{proof}"
                        , "\\begin{proposition}\\label{grouped_typed_fix}"
                        , "  $\\forall P:\\Set\\to\\Prop. \\forall x:\\Set. \\Apply{P}{x} \\implies \\Apply{P}{x}$."
                        , "\\end{proposition}"
                        , "\\begin{proof}"
                        , "  Fix $P:\\Set\\to\\Prop$ and $x:\\Set$ such that"
                        , "      $\\Apply{P}{x}$."
                        , "  Follows by assumption."
                        , "\\end{proof}"
                        ])))
    parsed <- expectRight =<< Prelude.parseReservedPreludeSource source
    pairs <- pairClaims
        (Parsed.identifiedParsedModuleBlocks
            (Prelude.reservedParsedPreludeModule parsed))
    assertEqual "grouped and typed proof pair count" 6 (length pairs)
    for_ pairs \(claim, proof) -> do
        outcome <-
            runModuleDriver
                foundation
                preludeModuleName
                []
                unusedResolver
                AlwaysMissValidation do
                    Declaration.runProspectiveLoweringDriver
                        (Proof.prepareProof claim (Just proof))
                        >>= either Declaration.failModuleDriver pure
        case outcome of
            Right (Declaration.DriverSucceeded
                    prepared _semantic _prefix) ->
                assertEqual
                    "typed proof has no omission"
                    Nothing
                    (Proof.preparedProofFirstOmission prepared)
            Right (Declaration.DriverFailed failure _prefix) ->
                assertFailure ("typed proof preparation failed: " <> show failure)
            Right (Declaration.DriverSealFailed failure _prefix) ->
                assertFailure ("typed proof preparation did not seal: " <> show failure)
            Left failure ->
                assertFailure ("typed proof driver did not open: " <> show failure)
  where
    pairClaims = \case
        [] -> pure []
        claim@Raw.BlockClaim{}
                : Raw.BlockProof _location proof _end
                : remaining ->
            ((claim, proof) :) <$> pairClaims remaining
        blocks ->
            assertFailure
                ("unexpected typed proof blocks: " <> show blocks)
                >> fail "unreachable"

compilesStructures :: Assertion
compilesStructures = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-exact-structures" \directory -> do
        let path = directory Posix.</> "store.sqlite"
            executable = directory Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        runs <- newIORef (0 :: Int)
        let resolver = countingAcceptedResolver executable runs
        (_startup, store) <-
            Store.openStore path (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            carrierOperation <- sole "base carrier operation"
                [ operation
                | descriptor <- Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude))
                , operation <-
                    schemaLocalFields descriptor
                ]
            assertEqual "legacy carrier field identity"
                "dd2367fbf1a837006ecfd16b12e01f2fe58803e437d8ad39ab4c67cb50e52db2"
                (mathematicalDigestHex (Identity.fieldIdDigest
                    (Schema.resolvedFieldIdentity carrierOperation)))
            -- Object identities include the theory's calculus manifest; the
            -- field identity and structural selector encoding do not.
            assertEqual "carrier selector content identity"
                "0365944b99ac8881004fed3c0505673f0f87ddfe64ec717eab39f47a83c8201a"
                (mathematicalDigestHex (Identity.objectIdDigest
                    (Schema.resolvedFieldSelector carrierOperation)))
            assertEqual "carrier projection content identity"
                "1bb2a559789e71ca277b92fbf28422f71ea39c05c85da9a4db62423db926ad67"
                (mathematicalDigestHex (Identity.objectIdDigest
                    (Schema.resolvedFieldProjection carrierOperation)))
            basePredicate <- sole "base structure predicate"
                [ predicate
                | descriptor <- Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude))
                , Schema.resolvedSchemaPhrase descriptor
                    == Schema.structurePhrase Lexicon._Onesorted
                , let predicate = schemaPredicate descriptor
                ]
            assertEqual "one-sorted predicate type and body identity"
                "1a47273a4d611c7e5b27d78d1a4a7ebf2bb5a3b906e6aaf741c3ea79d0a8a3c9"
                (mathematicalDigestHex (Identity.objectIdDigest basePredicate))
            let baselineCarrierSelector = Core.CGlobal
                    (Schema.resolvedFieldSelector carrierOperation)
                emptySet = Core.CIntrinsic Core.Empty
                entry = Core.CApp
                    (Core.CApp (Core.CIntrinsic Core.OrderedPair) baselineCarrierSelector) emptySet
            assertEqual "legacy carrier-only aggregate graph"
                (Core.CApp (Core.CIntrinsic Core.FamilyUnion)
                    (Core.CApp
                        (Core.CApp (Core.CIntrinsic Core.PairSet)
                            (Core.CApp
                                (Core.CApp (Core.CIntrinsic Core.PairSet) entry) entry))
                        emptySet))
                (Record.recordAggregate [(baselineCarrierSelector, emptySet)])
            mounts <- exactFixtureMounts repository
            workspace <- parseFinalWorkspace
                prelude mounts "test/phase5/exact-structure-child.tex"
            sealed <- compileFinalParsedWorkspaceWithResolver
                foundation prelude resolver workspace
            freshRuns <- readIORef runs
            warm <- installAndLoadStructures
                opened foundation prelude workspace sealed
            warmRuns <- readIORef runs
            assertEqual "warm structures preserve descriptors"
                (structureDescriptors <$> sealed)
                (Declaration.evidenceLocalStructureSchemas . Module.sealedTypedModuleEvidence <$> warm)
            assertEqual "warm structures make no prover calls"
                freshRuns warmRuns
            case sealed of
                [parent, child] -> do
                    let parentBatches =
                            Commit.pendingModulePrefixBatches
                                (Module.completedTypedModulePrefix parent)
                        parentDeltas =
                            Semantic.semanticInterfaceDeclarations
                                (completedModuleSemantic parent)
                        childBatches =
                            Commit.pendingModulePrefixBatches
                                (Module.completedTypedModulePrefix child)
                        childDeltas =
                            Semantic.semanticInterfaceDeclarations
                                (completedModuleSemantic child)
                    parentBatch <- sole "parent structure batch"
                        (take 1 parentBatches)
                    parentDelta <- sole "parent structure delta"
                        (take 1 parentDeltas)
                    parentDescriptor <- sole "parent structure schema" (checkedStructureSchemas parent)
                    parentOperation <- sole "parent structure operation"
                        (schemaLocalFields
                            parentDescriptor)
                    let parentSlot =
                            Semantic.declarationDeltaSlot parentDelta
                        expectedParentField =
                            Identity.fieldId
                                (Semantic.declarationSlotModule parentSlot)
                                (Semantic.declarationSlotOrdinal parentSlot)
                                (structureFieldSlot 0)
                    assertEqual "structure field identity follows its source slot"
                        expectedParentField
                        (Schema.resolvedFieldIdentity
                            parentOperation)
                    assertBool "inherited and locally declared fields are distinct"
                        ( Schema.resolvedFieldIdentity
                                carrierOperation
                            /= Schema.resolvedFieldIdentity
                                parentOperation
                        )
                    let parentPredicate = schemaPredicate parentDescriptor
                    assertEqual "structure object family order"
                        ["transparent", "transparent", "transparent"]
                        [ objectFamilyName
                            (Identity.assertedObjectContent object)
                        | object <- Commit.committedBatchObjects parentBatch
                        ]
                    assertEqual "field selector follows its stable identity"
                        (Record.fieldSelectorObjectId
                            (Identity.theoryId foundation)
                            (Schema.resolvedFieldIdentity parentOperation))
                        (Schema.resolvedFieldSelector parentOperation)
                    assertEqual "field projection follows its selector identity"
                        (Record.fieldProjectionObjectId
                            (Identity.theoryId foundation)
                            (Schema.resolvedFieldIdentity parentOperation))
                        (Schema.resolvedFieldProjection parentOperation)
                    assertEqual "structure fact alias inventory"
                        (sort [ Semantic.semanticName "pointed_set"
                        , Semantic.semanticName "pointed_setshape"
                        , Semantic.semanticName "pointed_refl"
                        , Semantic.semanticName "pointed_setexactgraph"
                        , Semantic.semanticName "pointed_setreductmembership"
                        , Semantic.semanticName
                            "pointed_setselectordistinctpair_carrier_and_pick"
                        , Semantic.semanticName "pointed_setprojectionentry_carrier"
                        , Semantic.semanticName "pointed_setprojectionentry_pick"
                        , Semantic.semanticName "pointed_setaggregatepaircoded"
                        , Semantic.semanticName "pointed_setaggregateentry_carrier"
                        , Semantic.semanticName "pointed_setaggregateentry_pick"
                        , Semantic.semanticName "pointed_setaggregateselectorclosed"
                        , Semantic.semanticName "pointed_setreductexact"
                        , Semantic.semanticName
                            "pointed_setprojectionagreement_carrier"
                        , Semantic.semanticName
                            "pointed_setprojectionagreement_pick"
                        , Semantic.semanticName "pointed_setreductidentity"
                        , Semantic.semanticName "pointed_setreductprojection_carrier"
                        , Semantic.semanticName "pointed_setreductprojection_pick"
                        , Semantic.semanticName "pointed_setselectordistinct"
                        , Semantic.semanticName "pointed_setaggregatevalueunique_carrier"
                        , Semantic.semanticName "pointed_setaggregatevalueunique_pick"
                        , Semantic.semanticName
                            "pointed_setaggregateprojectionapplication_carrier"
                        , Semantic.semanticName
                            "pointed_setaggregateprojectionapplication_pick"
                        , Semantic.semanticName
                            "pointed_setprojectionentryagreement"
                        , Semantic.semanticName "pointed_setaggregatefunctional"
                        , Semantic.semanticName
                            "pointed_setprojectiongraphagreement"
                        , Semantic.semanticName
                            "pointed_setprojectionextensionality"
                        , Semantic.semanticName "pointed_setaggregateexact"
                        , Semantic.semanticName "pointed_setaggregateprojection_carrier"
                        , Semantic.semanticName "pointed_setaggregateprojection_pick"
                        , Semantic.semanticName "pointed_setinherit_onesorted_structure"
                        , Semantic.semanticName "pointed_setinherit_record"
                        ])
                        (sort (Semantic.semanticAliasName
                            <$> Semantic.declarationDeltaAliases parentDelta))
                    definitionFingerprint <- factFingerprintByAlias (Module.completedTypedModulePrefix parent) "pointed_set"
                    definitionFact <- sole "structure definition fact"
                        [fact | fact <- Semantic.declarationDeltaFacts parentDelta,
                            Semantic.semanticFactFingerprint fact == definitionFingerprint]
                    definitionTarget <-
                        targetForOccurrence parentBatch definitionFact
                    let parentShape = Record.recordOpenShape
                            [Core.CGlobal (Schema.resolvedFieldSelector field)
                            | field <- Map.elems (Schema.resolvedSchemaFields parentDescriptor)] (Core.CBound 0)
                        parentLaw =
                            Core.CEq Core.TySet
                                (Core.CBound 0)
                                (Core.CBound 0)
                    assertEqual "pointwise structure definition"
                        (Core.CForall Core.TySet
                            (Core.CEq Core.TyProp
                                (Core.CApp
                                    (Core.CGlobal parentPredicate)
                                    (Core.CBound 0))
                                (canonicalAnd parentShape parentLaw)))
                        definitionTarget
                    assertGeneratedStructureInterface (completedModuleEvidence parent)
                        [Module.sealedTypedModuleSemantic (Module.finalPreludeModule prelude), completedModuleSemantic parent]
                        (Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude)) <> checkedStructureSchemas parent)
                        parentDescriptor
                        parentBatch
                    assertBool "all parent structure facts are clean"
                        (all
                            ((== Authority.cleanAuthoritySafety)
                                . Authority.factAuthoritySafety
                                . Semantic.semanticFactAuthority)
                            (Semantic.declarationDeltaFacts parentDelta))

                    let claimGlobals marker = do
                            batch <- batchWithAlias marker parentBatches
                            occurrence <- sole (marker <> " occurrence")
                                (Semantic.declarationDeltaFacts
                                    (Commit.committedBatchDelta batch))
                            Core.canonicalTermGlobals
                                <$> targetForOccurrence batch occurrence
                    carrierGlobals <- claimGlobals "pointed_carrier"
                    operationGlobals <- claimGlobals "pointed_operation"
                    assertBool "membership uses inherited carrier"
                        (Schema.resolvedFieldProjection carrierOperation
                            `Set.member` carrierGlobals)
                    assertBool "implicit and explicit operation share one object"
                        (Schema.resolvedFieldProjection parentOperation
                            `Set.member` operationGlobals)

                    let assertEquivalentClaim surface explicit = do
                            surfaceTerm <-
                                checkedPropositionTermByAlias parent surface
                            explicitTerm <-
                                checkedPropositionTermByAlias parent explicit
                            assertEqual
                                (StrictText.unpack surface
                                    <> " uses the inherited carrier")
                                explicitTerm
                                surfaceTerm
                    assertEquivalentClaim
                        "pointed_self_member"
                        "pointed_self_member_explicit"
                    assertEquivalentClaim
                        "pointed_self_not_member"
                        "pointed_self_not_member_explicit"
                    assertEquivalentClaim
                        "pointed_self_element"
                        "pointed_self_element_explicit"
                    assertEquivalentClaim
                        "pointed_header_member"
                        "pointed_header_member_explicit"

                    childBatch <- sole "child structure batch" childBatches
                    _childDelta <- sole "child structure delta" childDeltas
                    childDescriptor <- sole "child structure schema" (checkedStructureSchemas child)
                    assertEqual "child allocates no replacement operation"
                        []
                        (schemaLocalFields
                            childDescriptor)
                    assertEqual "child owns only its transparent predicate"
                        ["transparent"]
                        [ objectFamilyName
                            (Identity.assertedObjectContent object)
                        | object <- Commit.committedBatchObjects childBatch
                        ]
                modules ->
                    assertFailure
                        ("expected parent and child structures, got "
                            <> show (length modules))
  where
    installAndLoadStructures store foundation prelude workspace sealed = do
        storeCheck <- Store.newStoreCheck store
        case
            ( toList
                (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
            , sealed
            ) of
            ([parentParsed, childParsed], [parent, child]) -> do
                cachedParent <-
                    persistAndLoad storeCheck [] parentParsed parent
                cachedChild <- persistAndLoad
                    storeCheck [cachedParent] childParsed child
                pure [cachedParent, cachedChild]
            (parsed, modules) ->
                assertFailure
                    ("expected two structure installations, got "
                        <> show (length parsed)
                        <> " parsed and "
                        <> show (length modules)
                        <> " checked modules")
                    >> fail "unreachable"
      where
        preludeModule = Module.finalPreludeModule prelude

        persistAndLoad storeCheck parents parsed sealedModule = do
            let input = Module.identifiedPhysicalModule parsed
                syntax = completedModuleSyntax sealedModule
                semantic = completedModuleSemantic sealedModule
            key <- expectRight
                (Semantic.moduleArtefactKey
                    (Module.identifiedModuleOwner input)
                    (Parsed.identifiedParsedModuleId
                        (Module.identifiedModuleParsed input))
                    (Semantic.semanticInterfaceDirectInputs semantic)
                    (Identity.theoryId foundation))
            expectRight =<< Store.writeSealedModule storeCheck key
                (Module.completedTypedModulePrefix sealedModule) syntax semantic
            loaded <- expectRight
                =<< Store.loadCachedModuleCandidate
                    storeCheck
                    key
                    (Syntax.moduleSyntaxAssertedId
                        (Parsed.parsedModuleSyntaxInterface parsed))
            installation <- maybe
                (assertFailure "cached structure installation is absent"
                    >> fail "unreachable")
                pure
                loaded
            checkedImports <- prepareTestImports (Identity.theoryId foundation)
                (Module.sealedTypedModuleEvidence <$> (preludeModule : parents))
            expectRightIO
                (Module.cachedSealedTypedModule checkedImports installation)

    structureDescriptors = checkedStructureSchemas

    objectFamilyName :: Identity.ObjectContent -> String
    objectFamilyName = \case
        Identity.OpaqueObjectContent{} -> "opaque"
        Identity.TransparentObjectContent{} -> "transparent"
        Identity.IntrinsicObjectContent{} -> "intrinsic"

    targetForOccurrence batch occurrence =
        maybe
            (assertFailure "structure proposition is absent"
                >> fail "unreachable")
            (pure . Core.frozenCoreTerm . Identity.checkedPropositionTerm)
            (find
                ((== Semantic.semanticFactProposition occurrence)
                    . Identity.checkedPropositionId)
                (Commit.committedBatchPropositions batch))

    batchWithAlias marker batches =
        maybe
            (assertFailure ("missing batch alias " <> marker)
                >> fail "unreachable")
            pure
            (find
                (elem (Semantic.semanticName (StrictText.pack marker))
                    . fmap Semantic.semanticAliasName
                    . Semantic.declarationDeltaAliases
                    . Commit.committedBatchDelta)
                batches)


compilesParameterizedStructures :: Assertion
compilesParameterizedStructures = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-parameterized-structure" \directory -> do
        let storePath = directory Posix.</> "store.sqlite"
            executable = directory Posix.</> "vampire"
            relative = "test/phase8/parameterized-structure.tex"
        writeAcceptedFixtureVampire executable
        observedRoutes <- newIORef []
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    modifyIORef' observedRoutes
                        (<> [ Backend.typedProblemRoute
                                (Provers.preparedTypedProverLogicalProblem
                                    prepared)
                            ])
                    Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            carrierOperation <- sole "base carrier operation"
                [ operation
                | descriptor <- Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude))
                , operation <-
                    schemaLocalFields descriptor
                ]
            writeIORef observedRoutes []
            mounts <- exactFixtureMounts repository
            workspace <- parseFinalWorkspace prelude mounts relative
            sealed <- sole "parameterized structure module"
                =<< compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver workspace
            let descriptors =
                    checkedStructureSchemas sealed
            named <- descriptorByMarker "named_biaction" descriptors
            for_ ["named_biaction_left", "named_biaction_right"] \name -> do
                _ <- checkedPropositionTermByAlias sealed name
                assertBool "explicit label belongs to a complete direct application"
                    (any (elem (Raw.Marker name))
                        [ Map.findWithDefault [] application
                            (Schema.resolvedPresentationParentAliases (Schema.resolvedSchemaPresentation named))
                        | application <- schemaParents named])
            scalar <- descriptorByMarker "scalar_base" descriptors
            action <- descriptorByMarker "left_action" descriptors
            unital <- descriptorByMarker
                "unital_left_action" descriptors
            biaction <- descriptorByMarker "biaction" descriptors
            typedFields <- descriptorByMarker
                "typed_field_schema" descriptors
            let scalarPredicate = schemaPredicate scalar
                actionPredicate = schemaPredicate action
            assertEqual "scalar structure arity" 0
                (Schema.resolvedSchemaParameterCount scalar)
            assertEqual "left action parameter arity" 1
                (Schema.resolvedSchemaParameterCount action)
            assertEqual
                "subject precedes the ordered parameter in the predicate type"
                (Core.TyArrow Core.TySet
                    (Core.TyArrow Core.TySet Core.TyProp))
                (Predicate.structurePredicateType action)
            parameterPremise <- sole "left action parameter premise"
                (schemaPreamble action)
            assertEqual
                "the parameter premise is a positive conjunct over R"
                (Core.CApp
                    (Core.CGlobal scalarPredicate)
                    (Core.CBound 0))
                parameterPremise
            unitalParent <- sole "parameterized parent application"
                (schemaParents unital)
            assertEqual "parent schema is preserved"
                (Schema.resolvedSchemaId action)
                (Schema.structureApplicationId unitalParent)
            assertEqual "parent receives R in declaration order"
                [Core.CBound 0]
                (Schema.structureApplicationArguments unitalParent)
            assertEqual "two structure parameters retain their arity" 2
                (Schema.resolvedSchemaParameterCount biaction)
            assertEqual
                "two parameters extend the subject-first predicate type in order"
                (Core.TyArrow Core.TySet
                    (Core.TyArrow Core.TySet
                        (Core.TyArrow Core.TySet Core.TyProp)))
                (Predicate.structurePredicateType biaction)
            assertEqual
                "normalized parameter premises preserve both de Bruijn scopes"
                [ Core.CApp
                    (Core.CGlobal scalarPredicate)
                    (Core.CBound 0)
                , Core.CApp
                    (Core.CGlobal scalarPredicate)
                    (Core.CBound 1)
                ]
                (schemaPreamble biaction)
            biactionParent <- sole "two-parameter parent application"
                (schemaParents biaction)
            assertEqual "a parent can receive an earlier parameter"
                [Core.CBound 1]
                (Schema.structureApplicationArguments biactionParent)

            let batches =
                    Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix sealed)
            for_ [ interface
                 | batch <- batches
                 , interface <- Semantic.semanticEnvironmentStructures
                    (Semantic.declarationDeltaEnvironment (Commit.committedBatchDelta batch))] \interface -> do
                decoded <- expectRight (Cache.decodeCache Semantic.getStructureInterfaceWireCache
                    (Cache.encodeCache (Semantic.putStructureInterfaceWireCache interface)))
                assertEqual "parent labels survive semantic cache encoding" interface decoded
            let deltas = Commit.committedBatchDelta <$> batches
            notationBindings <- expectRight (Contracts.checkedNotationBindings deltas)
            funsPattern <- sole "checked function-space operator binding"
                [ pattern'
                | delta <- deltas
                , binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)
                , Semantic.semanticBindingLabelText (Semantic.semanticGlobalBindingLabel binding) == "parameterized_funs"
                , Semantic.SemanticExpressionFunction pattern' <- [Semantic.semanticGlobalBindingKey binding]]
            renderHints <- expectRight (Hints.parseRenderHints "operator\tparameterized_funs\t2\t<x2/><x1/>\noperator\temptyset\t0\t<mi>empty</mi>")
            let contracts = Contracts.resolveNotationContracts renderHints notationBindings
                operator pattern' = Raw.MixfixItem pattern' "parameterized_funs" Raw.NonAssoc
                wrongPattern = Raw.TokenCons (Raw.Word "different") funsPattern
            assertEqual "the checked operand slots drive rendering"
                (Just [Right ("B" :: Text), Right "A"])
                (Contracts.applyNotationContract contracts (Contracts.operatorNotation (operator funsPattern)) ["A", "B"])
            assertBool "matching marker and arity do not authorize another operand binding"
                (not (Contracts.hasNotationContract contracts (Contracts.operatorNotation (operator wrongPattern)) 2))
            assertEqual "fixed intrinsic operators use the compiler meaning inventory"
                (Just [Left "<mi>empty</mi>"])
                (Contracts.applyNotationContract contracts
                    (Contracts.operatorNotation (Raw.MixfixItem (Raw.TokenCons (Raw.Command "emptyset") Raw.End) "emptyset" Raw.NonAssoc))
                    ([] :: [Text]))
            assertBool "checked binding arity is enforced"
                (not (Contracts.hasNotationContract contracts (Contracts.operatorNotation (operator funsPattern)) 1))
            relationHints <- expectRight (Hints.parseRenderHints
                "relation\tpresentation_relation\t1\t<x1/>\npredicate\tpresentation_predicate\t2\t<x2/><x1/>")
            let relationContracts = Contracts.resolveNotationContracts relationHints notationBindings
                relation token arity = Contracts.relationNotation (Raw.RelationSymbol (Raw.Command token) arity "presentation_relation")
                predicate command arity = Contracts.predicateNotation (Raw.PrefixPredicate command arity) "presentation_predicate"
            let oneParameter = Raw.ParameterArity 1
            assertEqual "relation templates receive parameters, not the flanking operands"
                (Just [Right ("A" :: Text)])
                (Contracts.applyNotationContract relationContracts (relation "presentationRelation" oneParameter) ["A"])
            assertBool "a relation token lookalike is not its checked binding"
                (not (Contracts.hasNotationContract relationContracts (relation "different" oneParameter) 1))
            assertEqual "prefix templates retain every checked operand slot"
                (Just [Right ("y" :: Text), Right "x"])
                (Contracts.applyNotationContract relationContracts (predicate "presentationPredicate" 2) ["x", "y"])
            for_ [predicate "different" 2, predicate "presentationPredicate" 1, predicate "presentationPredicate" (-1)] \wrong ->
                assertBool "command and declared arity belong to prefix predicate identity"
                    (not (Contracts.hasNotationContract relationContracts wrong 2))
            adjectivePattern <- sole "checked symbolic adjective binding"
                [ pattern'
                | delta <- deltas
                , binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)
                , Semantic.semanticBindingLabelText (Semantic.semanticGlobalBindingLabel binding) == "presentation_adjective"
                , Semantic.SemanticLeftAdjective Semantic.OrdinaryAdjectiveReading pattern' <- [Semantic.semanticGlobalBindingKey binding]]
            let adjective side = Phrase.nativePhraseBinding
                    (Syntax.CanonicalUserAdjective side (Raw.AdjectiveSurfaceKey adjectivePattern))
            phraseBinding <- maybe (assertFailure "symbolic adjective lost its phrase identity" >> fail "missing phrase") pure
                (adjective Raw.LeftAdjectiveSide)
            otherSide <- maybe (assertFailure "symbolic adjective lost its other side" >> fail "missing phrase") pure
                (adjective Raw.RightAdjectiveSide)
            phraseHints <- expectRight (Hints.parseRenderHints
                "phrase\tpresentation_adjective\t0\t<mi>bound</mi>\nphrase\tpresentationClass\t0\t<mi>unbound</mi>")
            let phraseContracts = Contracts.resolveNotationContracts phraseHints notationBindings
                phraseNotation = Contracts.phraseNotation phraseBinding
            assertEqual "a user adjective carries no fabricated declaration marker" Nothing
                (Phrase.nativePhraseMarker phraseBinding)
            assertEqual "phrase templates resolve through the checked declaration label"
                (Just [Left "<mi>bound</mi>"])
                (Contracts.applyNotationContract phraseContracts phraseNotation ([] :: [Text]))
            assertEqual "missing phrase diagnostics retain the checked label" "presentation_adjective"
                (Contracts.notationContractMarker contracts phraseNotation)
            assertBool "an unchecked adjective side cannot borrow the phrase template"
                (not (Contracts.hasNotationContract phraseContracts (Contracts.phraseNotation otherSide) 0))
            symbolicSchema <- descriptorByMarker "symbolic_schema" descriptors
            structureBindings <- expectRight (Contracts.withStructurePhraseBindings descriptors notationBindings)
            assertEqual "repeated checked schema imports preserve the same phrase owner"
                (Right structureBindings)
                (Contracts.withStructurePhraseBindings (reverse descriptors <> descriptors) notationBindings)
            let schemaPhrase = Schema.resolvedSchemaPhrase symbolicSchema
            schemaBinding <- maybe (assertFailure "symbolic schema lost its phrase identity" >> fail "missing phrase") pure
                (Phrase.nativePhraseBinding (Syntax.CanonicalStructureNoun
                    (Schema.structurePhraseSingular schemaPhrase) (Schema.structurePhrasePlural schemaPhrase)
                    (Schema.structurePhraseMarker schemaPhrase)))
            schemaHints <- expectRight (Hints.parseRenderHints "phrase\tsymbolic_schema\t0\t<mi>schema</mi>")
            assertEqual "structure phrases resolve through checked schema ownership"
                (Just [Left "<mi>schema</mi>"])
                (Contracts.applyNotationContract (Contracts.resolveNotationContracts schemaHints structureBindings)
                    (Contracts.phraseNotation schemaBinding) ([] :: [Text]))
            assertBool "a structure template alone supplies no checked owner"
                (not (Contracts.hasNotationContract (Contracts.resolveNotationContracts schemaHints notationBindings)
                    (Contracts.phraseNotation schemaBinding) 0))
            secondaryFields <- descriptorByMarker "secondary_field_schema" descriptors
            let firstOwnerBindings = Contracts.withFieldBindings [typedFields] notationBindings
                secondOwnerBindings = Contracts.withFieldBindings [secondaryFields] notationBindings
                bothOwnerBindings = Contracts.withFieldBindings [secondaryFields] firstOwnerBindings
            assertBool "equal field spellings do not erase their different checked owners"
                (firstOwnerBindings /= secondOwnerBindings && bothOwnerBindings /= firstOwnerBindings
                    && bothOwnerBindings /= secondOwnerBindings)
            assertEqual "adding field owners is independent of declaration traversal"
                bothOwnerBindings (Contracts.withFieldBindings [typedFields] secondOwnerBindings)
            fieldHints <- expectRight (Hints.parseRenderHints
                "structop\tfieldPoint\t1\t<x1/>\noperator\tfieldPoint\t0\t<mi>not-a-field-contract</mi>")
            let fieldBindings = Contracts.withFieldBindings descriptors notationBindings
                fieldContracts = Contracts.resolveNotationContracts fieldHints fieldBindings
                explicitField = Contracts.fieldNotation (Raw.StructSymbol "fieldPoint") (Just ())
                omittedField = Contracts.fieldNotation (Raw.StructSymbol "fieldPoint") (Nothing :: Maybe ())
            assertEqual "inherited field occurrences do not duplicate or reorder owners" fieldBindings
                (Contracts.withFieldBindings (reverse descriptors <> descriptors) notationBindings)
            assertEqual "the explicit receiver occupies the hosted template's sole slot"
                (Just [Right ("M" :: Text)])
                (Contracts.applyNotationContract fieldContracts explicitField ["M"])
            assertBool "a hosted contract cannot invent a second receiver slot"
                (not (Contracts.hasNotationContract fieldContracts explicitField 2))
            assertBool "omitted receivers require their own explicit hosted template"
                (not (Contracts.hasNotationContract fieldContracts omittedField 0))
            assertBool "a template alone cannot invent a checked field declaration"
                (not (Contracts.hasNotationContract
                    (Contracts.resolveNotationContracts fieldHints notationBindings) explicitField 1))
            funsDelta <- sole "function-space binding declaration"
                [delta | delta <- deltas, any
                    ((== "parameterized_funs") . Semantic.semanticBindingLabelText . Semantic.semanticGlobalBindingLabel)
                    (Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta))]
            let oldSlot = Semantic.declarationDeltaSlot funsDelta
                otherSlot = Semantic.declarationSlot (Semantic.declarationSlotModule oldSlot) (localDeclarationOrdinal 4096)
            duplicate <- expectRight (Semantic.declarationInterfaceDelta
                otherSlot
                []
                []
                []
                []
                []
                []
                (Semantic.declarationDeltaEnvironment funsDelta))
            case Contracts.checkedNotationBindings [funsDelta, duplicate] of
                Left{} -> pure ()
                Right{} -> assertFailure "one operator contract selected two declaration owners"
            actionObject <- sole "left action predicate object"
                [ object
                | batch <- batches
                , object <- Commit.committedBatchObjects batch
                , Identity.assertedObjectId object == actionPredicate
                ]
            case Identity.assertedObjectContent actionObject of
                Identity.TransparentObjectContent _theory actualType body -> do
                    let subjectLaw =
                            Core.CEq Core.TySet
                                (Core.CBound 1)
                                (Core.CBound 1)
                        openShape =
                            Record.recordOpenShape
                                [ Core.CGlobal
                                    (Schema.resolvedFieldSelector
                                        carrierOperation)
                                ]
                                (Core.CBound 1)
                        conjunction =
                            canonicalAnd
                                (canonicalAnd parameterPremise openShape)
                                subjectLaw
                        expectedBody =
                            Core.CLam Core.TySet
                                (Core.CLam Core.TySet conjunction)
                    assertEqual "parameterized predicate object type"
                        (Predicate.structurePredicateType action)
                        actualType
                    assertEqual
                        "parameter premise is conjoined, not used as a vacuous guard"
                        expectedBody
                        body
                content ->
                    assertFailure
                        ("left action predicate is not transparent: "
                            <> show content)
            parameterTheorem <-
                checkedPropositionTermByAlias
                    sealed
                    "left_action_parameter"
            assertEqual
                "parameter elimination remains first-order"
                Foundation.FoundationFofProjectable
                (Foundation.classifyFrozenCore parameterTheorem)
            secondParameterTheorem <-
                checkedPropositionTermByAlias
                    sealed
                    "biaction_second_parameter"
            assertEqual
                "ordered multi-parameter elimination remains first-order"
                Foundation.FoundationFofProjectable
                (Foundation.classifyFrozenCore secondParameterTheorem)
            let fields =
                    schemaLocalFields typedFields
            assertEqual "typed fields retain declaration order"
                [Raw.StructSymbol "fieldPoint", Raw.StructSymbol "fieldMap"]
                (Schema.resolvedFieldSymbol <$> fields)
            assertBool "typed fields retain checked specifications"
                (all (\field -> any
                    (Map.member (Schema.RequirementProvenanceKey
                        (Schema.FieldSpecificationOrigin (Schema.resolvedSchemaId typedFields) (Schema.resolvedFieldIdentity field))
                        (Schema.structureApplicationKey (Schema.resolvedSchemaId typedFields) []))
                        . Schema.resolvedRequirementOccurrences)
                    (Map.elems (Schema.resolvedSchemaRequirements typedFields))) fields)
            pointSpecification <-
                checkedPropositionTermByAlias sealed "typed_field_point"
            mapSpecification <-
                checkedPropositionTermByAlias sealed "typed_field_map"
            assertBool "generated field specifications remain first-order"
                (all
                    ((== Foundation.FoundationFofProjectable)
                        . Foundation.classifyFrozenCore)
                    [pointSpecification, mapSpecification])
            let aliases =
                    [ Semantic.semanticAliasName alias
                    | batch <- batches
                    , alias <-
                        Semantic.declarationDeltaAliases
                            (Commit.committedBatchDelta batch)
                    ]
            assertBool
                "record-core facts are generated for each new selector presentation"
                (all
                    (`elem` aliases)
                    [ Semantic.semanticName "scalar_baseexactgraph"
                    , Semantic.semanticName "scalar_basereductexact"
                    , Semantic.semanticName "scalar_basereductmembership"
                    , Semantic.semanticName "typed_field_schemaexactgraph"
                    , Semantic.semanticName "typed_field_schemareductexact"
                    , Semantic.semanticName
                        "typed_field_schemareductmembership"
                    ])
            assertBool
                "each descendant retains its own complete law occurrence inventory"
                (all
                    (`elem` aliases)
                    [ Semantic.semanticName "left_actionexactgraph"
                    , Semantic.semanticName "left_actionreductexact"
                    , Semantic.semanticName "left_actionreductmembership"
                    , Semantic.semanticName "unital_left_actionexactgraph"
                    , Semantic.semanticName "unital_left_actionreductexact"
                    , Semantic.semanticName
                        "unital_left_actionreductmembership"
                    , Semantic.semanticName "biactionexactgraph"
                    , Semantic.semanticName "biactionreductexact"
                    , Semantic.semanticName "biactionreductmembership"
                    ])
            baseExact <- checkedPropositionTermByAlias sealed "scalar_baseexactgraph"
            childExact <- checkedPropositionTermByAlias sealed "left_actionexactgraph"
            assertEqual "equal record cores share proposition content" baseExact childExact
            baseOccurrence <- factFingerprintByAlias (Module.completedTypedModulePrefix sealed) "scalar_baseexactgraph"
            childOccurrence <- factFingerprintByAlias (Module.completedTypedModulePrefix sealed) "left_actionexactgraph"
            assertBool "distinct owners retain distinct structural law occurrences" (baseOccurrence /= childOccurrence)

            routes <- readIORef observedRoutes
            assertBool
                "generated record-interface laws require no TH0 prover work"
                (all (/= Backend.RouteTh0) routes)
  where
    descriptorByMarker marker descriptors =
        maybe
            (assertFailure
                ("missing structure descriptor " <> StrictText.unpack marker)
                >> fail "unreachable")
            pure
            (find
                ((== Raw.Marker marker)
                    . Schema.structurePhraseMarker
                    . Schema.resolvedSchemaPhrase)
                descriptors)

checksCarrierlessStructures :: Assertion
checksCarrierlessStructures =
    Temp.withSystemTempDirectory "felix-carrierless-structures" \root -> do
        let executable = root Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        let prover = Provers.vampire executable
                Provers.defaultTimeLimit Provers.defaultMemoryLimit
            resolver = Declaration.vampireResolver
                (Provers.runPreparedTypedProver prover)
        bracket
            (snd <$> (Store.openStore (root Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore \store -> do
                prelude <- expectRightIO
                    (acquireFinalPreludeSession store foundation resolver)
                mounts <- exactFixtureMounts =<< getCurrentDirectory
                diamondWorkspace <- parseFinalWorkspace prelude mounts
                    "test/structure-spikes/inheritance-diamond.tex"
                diamondModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver diamondWorkspace
                let schemas = Declaration.evidenceLocalStructureSchemas
                        (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude))
                        <> concatMap checkedStructureSchemas diamondModules
                    schemaNamed name = sole (StrictText.unpack name)
                        [ schema
                        | schema <- schemas
                        , Schema.structurePhraseMarker
                            (Schema.resolvedSchemaPhrase schema) == Raw.Marker name
                        ]
                rootSchema <- schemaNamed "record"
                assertEqual "record root has precisely the open empty shape"
                    (Core.CLam Core.TySet (Record.recordOpenShape [] (Core.CBound 0)))
                    (Predicate.structurePredicateBody rootSchema)
                forM_ [("coordinate_record", 1), ("reflexive_record", 0),
                        ("coordinate_diamond", 1)] \(name, count) -> do
                    schema <- schemaNamed name
                    assertEqual (StrictText.unpack name <> " field count") count
                        (Map.size (Schema.resolvedSchemaFields schema))
                    assertBool "carrierless fields never acquire the carrier role"
                        (all ((/= Raw.CarrierSymbol) . Schema.resolvedFieldSymbol)
                            (Map.elems (Schema.resolvedSchemaFields schema)))
                mixed <- schemaNamed "mixed_coordinate"
                reverseMixed <- schemaNamed "reverse_mixed_coordinate"
                assertEqual "parent order preserves semantic field order"
                    (Schema.resolvedSchemaSemanticFieldOrder mixed)
                    (Schema.resolvedSchemaSemanticFieldOrder reverseMixed)
                assertBool "mixed inheritance includes the canonical carrier"
                    (any ((== Raw.CarrierSymbol) . Schema.resolvedFieldSymbol)
                        (Map.elems (Schema.resolvedSchemaFields mixed)))
                basic <- sole "carrierless basic module"
                    [ candidate
                    | candidate <- diamondModules
                    , any ((== Raw.Marker "coordinate_record")
                            . Schema.structurePhraseMarker . Schema.resolvedSchemaPhrase)
                        (checkedStructureSchemas candidate)
                    ]
                let prefix = Module.completedTypedModulePrefix basic
                forM_ ["empty_record_extensionality",
                        "empty_record_generic_extensionality",
                        "coordinate_extensionality"] \name ->
                    batchByAlias prefix name >>= assertDirectExtensionality
                        (StrictText.unpack name)
                emptyInstance <- batchByAlias prefix "empty_record"
                assertBool "the empty instance publishes no projection aliases"
                    (all (not . StrictText.isPrefixOf "empty_recordprojection"
                            . Semantic.semanticNameText . Semantic.semanticAliasName)
                        (Semantic.declarationDeltaAliases
                            (Commit.committedBatchDelta emptyInstance)))
                aliasWorkspace <- parseFinalWorkspace prelude mounts
                    "test/structure-spikes/carrierless-aliases.tex"
                aliasModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver aliasWorkspace
                aliasModule <- sole "carrierless alias module"
                    (take 1 (reverse aliasModules))
                traverse_ (assertDirectExtensionality "carrierless local aliases")
                    (Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix aliasModule))

                reconstructionWorkspace <- parseFinalWorkspace prelude mounts
                    "test/structure-spikes/reconstruction.tex"
                reconstructionModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver reconstructionWorkspace
                constructionWorkspace <- parseFinalWorkspace prelude mounts
                    "test/structure-spikes/construction.tex"
                constructionModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver constructionWorkspace
                familyWorkspace <- parseFinalWorkspace prelude mounts
                    "test/structure-spikes/manifolds-0.tex"
                familyModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver familyWorkspace
                familyModule <- sole "manifold construction module" (take 1 (reverse familyModules))
                forM_ [("underlying_topological_space", 1, 1, ["carrier", "opens"]),
                        ("open_restriction", 2, 2, ["carrier", "opens", "atlas"]),
                        ("generated_coordinate_structure", 2, 2, ["atlas"]),
                        ("equip", 2, 2, ["carrier", "opens", "atlas"]),
                        ("weaken_coordinate_structure", 2, 3, ["carrier", "opens", "atlas"])]
                    \(name, arity, premiseCount, roles) -> do
                        batch <- batchByAlias (Module.completedTypedModulePrefix familyModule) name
                        let delta = Commit.committedBatchDelta batch
                        assertEqual "every construction registers exactly one provider result" 1
                            (length [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations delta])
                        assertEqual "construction arguments retain nearest-first de Bruijn order"
                            [Vector.fromList (Semantic.TemplateVariable . Semantic.ViewVariableIx
                                <$> reverse (take arity [0..]))]
                            (Semantic.resultProviderTemplateArguments . Semantic.providerResultProvider
                                <$> (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) delta)
                        assertEqual "construction results select the whole public theorem"
                            [Notion.ConjunctionHere]
                            (Semantic.registrationPath <$> Semantic.declarationDeltaRegistrations delta)
                        result <- checkedPropositionTermByAlias familyModule name
                        let (types, premises) = consequenceEnvelope (Core.frozenCoreTerm result)
                        length types @?= arity
                        length premises @?= premiseCount
                        forM_ ("shape" : (("projection_" <>) <$> roles)) \suffix -> do
                            consequence <- checkedPropositionTermByAlias familyModule (name <> suffix)
                            assertEqual "consequences retain every parameter and ordered premise"
                                (types, premises) (consequenceEnvelope (Core.frozenCoreTerm consequence))
                manifoldWorkspace <- parseFinalWorkspace prelude mounts
                    "test/structure-spikes/manifolds-0-reconstruction.tex"
                manifoldModules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver manifoldWorkspace
                forM_ ["underlying_topological_space_result", "open_restriction_result",
                        "generated_coordinate_structure_result", "equip_result",
                        "weaken_coordinate_structure_result"] \name -> do
                    batch <- sole ("provider-result classification " <> StrictText.unpack name)
                        [ candidate
                        | sealed <- manifoldModules
                        , candidate <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)
                        , any ((== Semantic.semanticName name) . Semantic.semanticAliasName)
                            (Semantic.declarationDeltaAliases (Commit.committedBatchDelta candidate))
                        ]
                    assertEqual "the baseline uses the required provider-result registration" 1
                        (length [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations (Commit.committedBatchDelta batch)])

                -- Re-enter the normal Store path from encoded, admitted modules.
                -- The fake prover above tests routing only; real spike checks
                -- establish the mathematical proofs in these same source files.
                storeCheck <- Store.newStoreCheck store
                traverse_ (expectRightIO . Store.writePendingModulePrefix storeCheck
                        . Module.completedTypedModulePrefix)
                    (diamondModules <> aliasModules <> reconstructionModules <> constructionModules
                        <> familyModules <> manifoldModules)
                requests <- newIORef (0 :: Int)
                let observer = Verification.verificationRequestObserver \_ _ ->
                        modifyIORef' requests (+ 1)
                forM_ ["test/structure-spikes/inheritance-diamond.tex",
                        "test/structure-spikes/carrierless-aliases.tex",
                        "test/structure-spikes/reconstruction.tex",
                        "test/structure-spikes/construction.tex",
                        "test/structure-spikes/manifolds-0.tex",
                        "test/structure-spikes/manifolds-0-reconstruction.tex"] \source -> do
                    result <- expectRightIO (checkResultWithStore store
                        Verification.WarmStoreValidation observer prover source)
                    assertTypedSuccess "cached carrierless structure fixture" result
                assertEqual "warm carrierless imports issue no proof requests" 0
                    =<< readIORef requests
  where
    consequenceEnvelope = binders []
      where
        binders reversed (Core.CForall coreType body) = binders (coreType : reversed) body
        binders reversed body = (reverse reversed, hypotheses body)
        hypotheses (Core.CImp premise conclusion) = premise : hypotheses conclusion
        hypotheses _ = []

checksReconstructionBoundaries :: Assertion
checksReconstructionBoundaries = Temp.withSystemTempDirectory "reconstruction-boundaries" \directory ->
    withAcceptedFixtureVampire "reconstruction-boundaries-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            let compile source = do
                    workspace <- parseFinalWorkspace prelude mounts ("test/structure-spikes/" <> source <> ".tex")
                    modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
                    pure (workspace, modules)
            (workspace, forward) <- compile "reconstruction-discovery"
            (_, backward) <- compile "reconstruction-discovery-reversed"
            (_, explicit) <- compile "reconstruction-explicit-assertions"
            (_, collision) <- compile "manifolds-0-projection-collision"
            let parsed = Parsed.parsedWorkspaceRootModule workspace
            (assumptions, conclusion, expression) <- sole "discovery assertion"
                [(assumptions, conclusion, expression)
                | Raw.BlockClaim _ _ _ (Raw.Marker "discovery_result")
                    (Raw.Claim assumptions conclusion@(Raw.StmtFormula
                        (Raw.FormulaChain (Raw.ChainBase (expression :| []) _ _ _))))
                    <- Parsed.parsedModuleBlocks parsed]
            observations <- for [forward, backward] \modules -> do
                driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                    (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> modules))
                    unusedResolver AlwaysMissValidation
                    (Declaration.runProspectiveLoweringDriver do
                        envelope <- Elaboration.elaborateClaimEnvelopeWithFormationObservation id assumptions conclusion
                        case envelope of
                            Left failure -> pure (Left failure)
                            Right (_, context) -> Elaboration.elaborateReconstructionWithBudget
                                (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits) context expression)
                (fields, candidates, attempts, budget) <- case driven of
                    Declaration.DriverSucceeded result _ _ -> expectRight result
                    _ -> fail "import-order query failed"
                pure ([(Schema.resolvedFieldIdentity (Elaboration.elaboratedRecordField entry),
                    Elaboration.elaboratedRecordValue entry) | entry <- fields], candidates, attempts, budget)
            case observations of
                [forwardObservation, backwardObservation] -> forwardObservation @?= backwardObservation
                _ -> fail "missing import-order observation"
            let available = Map.fromList [(completedModuleOwner sealed, sealed)
                    | sealed <- forward <> backward <> explicit <> collision]
                checks =
                    [("reconstruction-undetermined-rejected", 5, \case
                        Elaboration.UndeterminedResultParameters{} -> True; _ -> False),
                    ("reconstruction-identity-rejected", 5, (== Elaboration.NoRecordEvidence)),
                    ("reconstruction-alias-rejected", 9, (== Elaboration.NoRecordEvidence)),
                    ("reconstruction-scope-rejected", 14, (== Elaboration.NoRecordEvidence)),
                    ("reconstruction-missing-atlas-rejected", 5, \case
                        Elaboration.MissingCopiedFields Elaboration.CheckedRecordInterface interface fields ->
                            fields == [Raw.StructSymbol "atlas"]
                                && Set.fromList (snd <$> Elaboration.reconstructionInterfaceFields interface)
                                    == Set.fromList [Raw.CarrierSymbol, Raw.StructSymbol "opens"]
                        _ -> False)]
            for_ checks \(source, line, check) -> do
                rejected <- parseFinalWorkspace prelude mounts ("test/structure-spikes/" <> source <> ".tex")
                let root = Parsed.parsedWorkspaceRootModule rejected
                direct <- for (nubOrd (Parsed.parsedImportedAddress <$> Parsed.parsedModuleImports root)) \address ->
                    maybe (fail "missing boundary-control import") pure (Map.lookup (moduleName address) available)
                input <- expectRightIO (typedModuleInput foundation (Module.finalPreludeReadiness prelude)
                    resolver AlwaysMissValidation root direct)
                failure <- runTypedModule input >>= \case
                    Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedElaborationFailed error')) _ -> pure error'
                    Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed error'))) _ -> pure error'
                    _ -> fail (source <> " did not reject at elaboration")
                case failure of
                    Elaboration.ElaborationReconstructionBaseUnavailable location _ _ reason -> do
                        locLine location @?= line
                        assertBool (source <> ": " <> show reason) (check reason)
                    _ -> fail (source <> ": " <> show failure)

accountsReconstructionSearch :: Assertion
accountsReconstructionSearch = Temp.withSystemTempDirectory "reconstruction-account" \directory ->
    withAcceptedFixtureVampire "reconstruction-account-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/reconstruction-account.tex"
            let parsed = Parsed.parsedWorkspaceRootModule workspace
                blocks = Parsed.parsedModuleBlocks parsed
                entries index = [Parsed.parsedSyntaxOccurrenceEntry occurrence
                    | occurrence <- Parsed.parsedModuleSyntaxOccurrences parsed
                    , Parsed.parsedSyntaxOccurrenceBlockIndex occurrence == index]
            (assumptions, conclusion, expression) <- sole "discovery assertion"
                [(assumptions, conclusion, expression)
                | Raw.BlockClaim _ _ _ (Raw.Marker "discovery_result")
                    (Raw.Claim assumptions conclusion@(Raw.StmtFormula
                        (Raw.FormulaChain (Raw.ChainBase (expression :| []) _ _ _))))
                    <- Parsed.parsedModuleBlocks parsed]
            relative <- expectRight (safeRelativePath "reconstruction-account.tex")
            -- With the beta-eta calculus identity, namespace 5 puts the
            -- underdetermined and failing candidates before the usable result,
            -- independently of the checkout path.
            let owner = moduleNameFromParts (sourceNamespaceIdFromDigest (hashBlake2b256 "reconstruction-account-5")) relative
                evidence = [Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude)]
                isProbe (_, Raw.BlockClaim _ _ _ (Raw.Marker "discovery_result") _, _) = True
                isProbe _ = False
                admitPrefix expanded = for_ ((if expanded then id else takeWhile (not . isProbe))
                        (zip3 [0..] blocks (drop 1 blocks))) \(index, block, following) ->
                    case block of
                        Raw.BlockStruct{} -> do
                            prepared <- Declaration.runProspectiveLoweringDriver (Structure.prepareStructure block (entries index))
                                >>= either (Declaration.failModuleDriver . show) pure
                            lowered <- Declaration.runProspectiveLoweringDriver (Structure.lowerPreparedStructure prepared)
                                >>= either Declaration.failDeclarationDriver pure
                            void (Declaration.admitCheckedDeclaration lowered Structure.authorizeCheckedStructure)
                        Raw.BlockDefn{} -> do
                            prepared <- Declaration.runProspectiveLoweringDriver (Binding.prepareBinding block (entries index))
                                >>= either (Declaration.failModuleDriver . show) pure
                            lowered <- Declaration.runProspectiveLoweringDriver (Binding.lowerPreparedBinding prepared)
                                >>= either Declaration.failDeclarationDriver pure
                            void (Declaration.admitCheckedDeclaration lowered Binding.authorizeCheckedBinding)
                        Raw.BlockClaim _ _ _ marker _ | marker /= Raw.Marker "discovery_result" -> do
                            let proof = case following of Raw.BlockProof _ value _ -> Just value; _ -> Nothing
                            prepared <- Declaration.runProspectiveLoweringDriver (Proof.prepareProof block proof)
                                >>= either (Declaration.failModuleDriver . show) pure
                            lowered <- Declaration.runProspectiveLoweringDriver (Proof.lowerPreparedProof prepared)
                                >>= either Declaration.failDeclarationDriver pure
                            void (Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof)
                        _ -> pure ()
                run expanded = runModuleDriver foundation owner evidence resolver AlwaysMissValidation do
                    admitPrefix expanded
                    Declaration.runProspectiveLoweringDriver do
                        envelope <- Elaboration.elaborateClaimEnvelopeWithFormationObservation id assumptions conclusion
                        case envelope of
                            Left failure -> pure (Left failure)
                            Right (_, context) -> do
                                let allowance = 1000000
                                    limits n = fromMaybe (error "invalid reconstruction test limits")
                                        (Notion.formationSearchLimitsWithEqualityChain
                                            65536 131072 65536 n 100000 1024 1024)
                                    query n = Elaboration.elaborateReconstructionWithBudget
                                        (Notion.initialFormationSearchBudget (limits n)) context expression
                                ample <- query allowance
                                case ample of
                                    Left failure -> pure (Left failure)
                                    Right (_, candidates, attempts, remaining) -> do
                                        let work = allowance - Notion.formationInferenceWorkRemaining remaining
                                        exact <- query work
                                        short <- query (work - 1)
                                        let outer = case expression of
                                                Raw.ExprStructReconstruction at schema _ _ ->
                                                    Raw.ExprStructReconstruction at schema expression []
                                                _ -> error "account fixture lost its reconstruction"
                                        nested <- Elaboration.elaborateReconstructionWithBudget
                                            (Notion.initialFormationSearchBudget (limits work)) context outer
                                        pure (Right (work, candidates, attempts, exact, short, nested))
            driven <- expectRight =<< run False
            (work, candidates, attempts, exact, short, nested) <- case driven of
                Declaration.DriverSucceeded result _ _ -> expectRight result
                _ -> fail "reconstruction query driver failed"
            assertBool "full query consumes structural work" (work > 0)
            assertBool ("a genuinely failed attempt precedes success: " <> show attempts <> "; candidates: " <> show candidates)
                (case attempts of
                    failed : _ : _ -> case Elaboration.reconstructionAttemptOutcome failed of
                        Left _ -> Elaboration.reconstructionAttemptWork failed > 0
                        _ -> False
                    _ -> False)
            assertBool ("undetermined candidate precedes the successful candidate: " <> show candidates)
                (case reverse candidates of
                    successful : earlier -> isJust (Elaboration.reconstructionCandidateAssertion successful)
                        && any (isNothing . Elaboration.reconstructionCandidateAssertion) earlier
                    _ -> False)
            case (candidates, attempts) of
                ([undetermined, failed, selected], [failedAttempt, successfulAttempt]) -> do
                    Elaboration.reconstructionAttemptCandidate failedAttempt @?=
                        Just (Elaboration.reconstructionCandidateBranch failed)
                    Elaboration.reconstructionAttemptCandidate successfulAttempt @?=
                        Just (Elaboration.reconstructionCandidateBranch selected)
                    Elaboration.reconstructionAttemptOutcome successfulAttempt @?=
                        Right (Just (Elaboration.reconstructionCandidateBranch undetermined))
                _ -> fail "account fixture lost its three distinct results and two formation attempts"
            (_, exactCandidates, exactAttempts, remaining) <- expectRight exact
            exactCandidates @?= candidates
            exactAttempts @?= attempts
            Notion.formationInferenceWorkRemaining remaining @?= 0
            case short of
                Left Elaboration.ElaborationFormationSearchFailed{} -> pure ()
                Left failure -> fail ("one-short query hid exhaustion: " <> show failure)
                Right _ -> fail "one-short query replenished its work account"
            (_, nestedCandidates, nestedAttempts, nestedBudget) <- expectRight nested
            nestedCandidates @?= candidates
            nestedAttempts @?= attempts
            Notion.formationInferenceWorkRemaining nestedBudget @?= 0
            expanded <- expectRight =<< run True
            case expanded of
                Declaration.DriverSucceeded (Right (expandedWork, expandedCandidates, expandedAttempts, _, _, _)) _ _ -> do
                    expandedCandidates @?= candidates
                    let routing attempt = (Elaboration.reconstructionAttemptCandidate attempt,
                            Elaboration.reconstructionAttemptAssertion attempt,
                            Bifunctor.first (const ()) (Elaboration.reconstructionAttemptOutcome attempt))
                        discoveryWork total queries = total - sum (Elaboration.reconstructionAttemptWork <$> queries)
                    (routing <$> expandedAttempts) @?= (routing <$> attempts)
                    -- General formation may pay for a larger registry index;
                    -- unrelated providers must not enlarge discovery's bucket.
                    discoveryWork expandedWork expandedAttempts @?= discoveryWork work attempts
                _ -> fail "unrelated provider registration changed reconstruction admission"

retainsRecordFields :: Assertion
retainsRecordFields = Temp.withSystemTempDirectory "record-fields" \directory ->
    withAcceptedFixtureVampire "record-fields-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/wide-replacements.tex"
            modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
            let parsed = Parsed.parsedWorkspaceRootModule workspace
            (assumptions, conclusion, left, right) <- sole "swap assertion"
                [(assumptions, conclusion, left, right)
                | Raw.BlockClaim _ _ _ (Raw.Marker "wide_swap_entry_order")
                    (Raw.Claim assumptions conclusion@(Raw.StmtFormula
                        (Raw.FormulaChain (Raw.ChainBase (left :| []) _ _ (right :| [])))))
                    <- Parsed.parsedModuleBlocks parsed]
            driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> modules))
                unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    envelope <- Elaboration.elaborateClaimEnvelopeWithFormationObservation id assumptions conclusion
                    case envelope of
                        Left failure -> pure (Left failure)
                        Right (_, context) -> do
                            first <- Elaboration.elaborateRecordAggregate context left
                            second <- Elaboration.elaborateRecordAggregate context right
                            pure ((,) <$> first <*> second))
            (first, second) <- case driven of
                Declaration.DriverSucceeded result _ _ -> expectRight result
                _ -> fail "swap aggregate preparation failed"
            Elaboration.elaboratedAggregateCore first @?= Elaboration.elaboratedAggregateCore second
            let entries = Elaboration.elaboratedAggregateFields first
                identities = Schema.resolvedFieldIdentity . Elaboration.elaboratedRecordField <$> entries
                projections = Map.fromList [(Schema.resolvedFieldSymbol field, Schema.resolvedFieldProjection field)
                    | entry <- entries, let field = Elaboration.elaboratedRecordField entry]
            identities @?= Set.toAscList (Set.fromList identities)
            length entries @?= 10
            for_ entries \entry -> do
                let symbol = Schema.resolvedFieldSymbol (Elaboration.elaboratedRecordField entry)
                    original = case symbol of
                        Raw.StructSymbol "north" -> Raw.StructSymbol "south"
                        Raw.StructSymbol "south" -> Raw.StructSymbol "north"
                        _ -> symbol
                projection <- maybe (fail "original projection is missing") pure (Map.lookup original projections)
                Core.scopedCoreTerm (Elaboration.elaboratedRecordValue entry) @?=
                    Core.CApp (Core.CGlobal projection) (Core.CBound 0)
                case (symbol, Elaboration.elaboratedRecordOrigin entry) of
                    (Raw.StructSymbol "north", Elaboration.WrittenRecordField location) -> locLine location @?= 7
                    (Raw.StructSymbol "south", Elaboration.WrittenRecordField location) -> locLine location @?= 7
                    (_, Elaboration.CopiedRecordField location) -> locLine location @?= 7
                    _ -> fail "copied and written field origins were confused"

checksClosedValueDescriptions :: Assertion
checksClosedValueDescriptions = Temp.withSystemTempDirectory "closed-value-descriptions" \directory ->
    withAcceptedFixtureVampire "closed-value-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            open = snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)
        bracket open Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/closed-value-instances-import.tex"
            modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
            let deltas = [Commit.committedBatchDelta batch | sealed <- modules,
                    batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)]
                named name = sole (StrictText.unpack name)
                    [delta | delta <- deltas, any ((== Semantic.semanticName name) . Semantic.semanticAliasName)
                        (Semantic.declarationDeltaAliases delta)]
                closed = \case Semantic.TemplateClosed{} -> True; _ -> False
                singleton = \case
                    Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider values ->
                        Vector.length values == 1 && all closed values
                    _ -> False
            for_ ["closed_value_zero", "closed_value_two", "closed_value_singleton", "closed_value_nested",
                    "closed_value_comprehension", "closed_value_aggregate"] \name -> do
                delta <- named name
                (registration, rule) <- sole "closed-value result registration"
                    [(entry, rule) | entry@(Semantic.Registration _ _ (Semantic.RegisterProviderResult rule)) <- Semantic.declarationDeltaRegistrations delta]
                Semantic.providerResultPremises rule @?= Semantic.ProviderResultUnconditional
                Semantic.resultProviderTemplateArguments (Semantic.providerResultProvider rule) @?= Vector.empty
                public <- sole "exact public instance fact"
                    [Semantic.semanticAliasTarget alias | alias <- Semantic.declarationDeltaAliases delta,
                        Semantic.semanticAliasName alias == Semantic.semanticName name]
                Semantic.registrationSource registration @?= public
                Semantic.registrationPath registration @?= Notion.ConjunctionHere
                argument <- case Semantic.providerResultConclusion rule of
                    Semantic.StructureAtomTemplate _ values -> case toList values of
                        [Semantic.ResultRuleProviderValue,Semantic.ResultRuleTerm term] -> pure term
                        _ -> fail "a closed-value instance lost its exact schema argument"
                    _ -> fail "a closed-value instance lost its declared structure head"
                case name of
                    "closed_value_singleton" -> assertBool "literal syntax retains its rigid element" (singleton argument)
                    "closed_value_nested" -> case argument of
                        Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider values ->
                            assertBool "nested literal retains both displayed children" (Vector.length values == 2)
                        _ -> fail "a nested literal was flattened into a provider-free value"
                    _ -> assertBool "provider-free schema arguments are distinct rigid values" (closed argument)
                Cache.decodeCache Semantic.getDeclarationInterfaceDeltaCache
                    (Cache.encodeCache (Semantic.putDeclarationInterfaceDeltaCache delta)) @?= Right delta
            weaker <- named "closed_value_weaker"
            base <- named "empty_record"
            (Semantic.providerResultConclusion <$> (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) weaker) @?=
                (Semantic.providerResultConclusion <$> (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) base)
            for_ ["closed-value-wrong-parameter", "closed-value-unregistered"] \fixture -> do
                rejected <- parseFinalWorkspace prelude mounts ("test/structure-spikes/" <> fixture <> ".tex")
                let root = Parsed.parsedWorkspaceRootModule rejected
                    available = Map.fromList [(Semantic.semanticInterfaceOwner (completedModuleSemantic sealed),sealed)
                        | sealed <- modules]
                direct <- for (nubOrd (Parsed.parsedImportedAddress <$> Parsed.parsedModuleImports root)) \address ->
                    maybe (fail "negative closed-value fixture lost an imported module") pure (Map.lookup (moduleName address) available)
                input <- expectRightIO (typedModuleInput foundation (Module.finalPreludeReadiness prelude)
                    resolver AlwaysMissValidation root direct)
                runTypedModule input >>= \case
                    Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed Elaboration.ElaborationFormationRequirementMissing{}))) _ -> pure ()
                    Module.TypedModuleFailed failure _ -> fail ("closed-value negative failed at another boundary: " <> show failure)
                    _ -> fail "a closed-value negative did not fail at formation"

checksClosedInstanceResults :: Assertion
checksClosedInstanceResults = Temp.withSystemTempDirectory "closed-instance" \directory ->
    withAcceptedFixtureVampire "closed-instance-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            source = "test/structure-spikes/closed-instance-results-import.tex"
            open = snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)
        bracket open Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts source
            modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
            let deltas = [Commit.committedBatchDelta batch | sealed <- modules,
                    batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)]
                named name = sole (StrictText.unpack name)
                    [delta | delta <- deltas, any ((== Semantic.semanticName name) . Semantic.semanticAliasName)
                        (Semantic.declarationDeltaAliases delta)]
            for_ ["empty_record", "empty_coordinate_record", "closed_refined_instance",
                    "closed_weaker_instance", "closed_parameter_instance", "closed_finite_instance"] \name -> do
                delta <- named name
                (registration, rule) <- sole "closed structure registration"
                    [(entry, rule) | entry@(Semantic.Registration _ _ (Semantic.RegisterProviderResult rule)) <- Semantic.declarationDeltaRegistrations delta]
                binding <- sole "instance binding"
                    (Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta))
                public <- sole "public structure theorem"
                    [Semantic.semanticAliasTarget alias | alias <- Semantic.declarationDeltaAliases delta,
                        Semantic.semanticAliasName alias == Semantic.semanticName name]
                let provider = Semantic.providerResultProvider rule
                Semantic.resultProviderTemplateHead provider @?= Semantic.GlobalSourceProvider
                    (Semantic.globalBindingRef (Semantic.declarationDeltaSlot delta) (Semantic.semanticGlobalBindingKey binding))
                Semantic.resultProviderTemplateArguments provider @?= Vector.empty
                Semantic.providerResultPremises rule @?= Semantic.ProviderResultUnconditional
                Semantic.registrationSource registration @?= public
                Semantic.registrationPath registration @?= Notion.ConjunctionHere
                Cache.decodeCache Semantic.getDeclarationInterfaceDeltaCache
                    (Cache.encodeCache (Semantic.putDeclarationInterfaceDeltaCache delta)) @?= Right delta
            weaker <- named "closed_weaker_instance"
            emptyRecord <- named "empty_record"
            let conclusion delta = Semantic.providerResultConclusion
                    <$> (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) delta
            assertEqual "a richer aggregate registers only its declared record result"
                (conclusion emptyRecord) (conclusion weaker)
            refined <- named "closed_refined_instance"
            refinedRule <- sole "refined rule" [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations refined]
            let refinedHead = Semantic.resultProviderTemplateHead (Semantic.providerResultProvider refinedRule)
            parameterDelta <- named "closed_parameter_instance"
            parameterRule <- sole "parameter rule" [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations parameterDelta]
            case Semantic.providerResultConclusion parameterRule of
                Semantic.StructureAtomTemplate _ arguments -> toList arguments @?=
                    [Semantic.ResultRuleProviderValue,
                     Semantic.ResultRuleTerm (Semantic.TemplateProvider refinedHead Vector.empty)]
                _ -> fail "closed result lost its declared structure head"
            -- Inspect the written typed name independently of its equal Core
            -- denotation. Formation success alone cannot establish this property.
            let parsed = Parsed.parsedWorkspaceRootModule workspace
            (assumptions, target) <- sole "imported notion statement"
                [(headers, target) | Raw.BlockClaim _ _ _ (Raw.Marker "closed_instance_import_notion")
                    (Raw.Claim headers target) <- Parsed.parsedModuleBlocks parsed]
            driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> modules))
                unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver (Elaboration.elaborateClaimEnvelope assumptions target))
            envelope <- case driven of
                Declaration.DriverSucceeded result _ _ -> expectRight result
                _ -> fail "closed instance statement did not elaborate"
            assertion <- sole "closed assertion" (Elaboration.elaboratedClaimConclusionAssertions envelope)
            arguments <- case Notion.sourceAssertionAtom assertion of
                Semantic.StructureAtomTemplate _head args -> pure args
                _ -> fail "expected structure assertion"
            parameter <- sole "written closed parameter" (drop 1 (toList arguments))
            occurrence <- maybe (fail "typed constant lost provider metadata") pure
                (SourceTerm.sourceTermOccurrenceProvider parameter)
            SourceTerm.sourceTermProviderHead occurrence @?= refinedHead
            assertBool "a typed constant has no source arguments"
                (Vector.null (SourceTerm.sourceTermProviderArguments occurrence))
            case Notion.compileSourceRuleTermTemplate 0
                    (SourceTerm.sourceTermOccurrence (SourceTerm.sourceTermOccurrenceCore parameter) Core.TySet ()) of
                Right (Semantic.TemplateClosed value) -> Semantic.closedSetValueTerm value @?=
                    Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore parameter)
                _ -> fail "a provider-free closed value did not remain distinct from written provider identity"
            catalogResult <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> modules))
                unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    catalog <- Declaration.formationCatalogLowering
                    FormationCatalog.providerStructureResults (const (pure ())) refinedHead catalog)
            case catalogResult of
                Declaration.DriverSucceeded [Left (Notion.FormationProviderRule runtime)] _ _ -> do
                    Notion.visibleProviderResultRuleBinderArity runtime @?= 0
                    Notion.visibleProviderResultRulePayload runtime @?= refinedRule
                _ -> fail "the closed provider did not acquire exactly one replayable result"
            -- A new check session rules out a session-local memo hit. Require
            -- actual module artefacts, not merely cached ATP certificates.
            assertTypedSuccess "cold closed-instance producer" =<< expectRightIO
                (checkResultWithStore store Verification.WarmStoreValidation ignoredVerificationRequests prover
                    "test/structure-spikes/closed-instance-results.tex")
            graph <- Workspace.prepareDefaultSourceGraph source >>= expectRight
            let check = Verification.withVerificationSessionUsingStore store \session ->
                    Verification.checkWorkspace session Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand = Parse.NoPresentation
                        , Verification.checkStoreValidationMode = Verification.WarmStoreValidation
                        , Verification.checkModuleJobs = testSequentialJobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = ignoredVerificationRequests
                        }
            cold <- expectRightIO check >>= expectRight
            assertTypedSuccess "cold imported closed instance" (Verification.checkVerificationResult cold)
            warm <- expectRightIO check >>= expectRight
            assertTypedSuccess "warm imported closed instance" (Verification.checkVerificationResult warm)
            let report = Verification.checkOperationalReport warm
                decisions = Verification.moduleInstallationDecisions report
            assertBool "warm semantic module hits occurred" (Verification.lookupRowsFound decisions > 1)
            Verification.lookupMisses decisions @?= 0
            Verification.lookupBypasses decisions @?= 0
            Verification.liveVampireRunsStarted report @?= 0
            reader <- Store.newStoreCheck store
            for_ [(parsedModule, sealed) | parsedModule <- toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace),
                    sealed <- modules, moduleName (Parsed.parsedModuleAddress parsedModule) ==
                        Semantic.semanticInterfaceOwner (completedModuleSemantic sealed)] \(parsedModule, sealed) -> do
                let semantic = completedModuleSemantic sealed
                key <- expectRight (Semantic.moduleArtefactKey (Semantic.semanticInterfaceOwner semantic)
                    (Parsed.parsedModuleId parsedModule) (Semantic.semanticInterfaceDirectInputs semantic)
                    (Identity.theoryId foundation))
                candidate <- expectRightIO (Store.loadCachedModuleCandidate reader key
                    (Syntax.moduleSyntaxAssertedId (Parsed.parsedModuleSyntaxInterface parsedModule)))
                    >>= maybe (fail "warm module artefact missing") pure
                Store.cachedCandidateSemantic candidate @?= semantic
            for_ ["manifolds-1-instance-focus-probe", "manifolds-1-instance-parameter-probe"] \probe ->
                assertTypedSuccess probe =<< expectRightIO (checkResultWithStore store
                    Verification.WarmStoreValidation ignoredVerificationRequests prover
                    ("test/structure-spikes/" <> probe <> ".tex"))
            rejected <- parseFinalWorkspace prelude mounts
                "test/structure-spikes/closed-instance-unregistered.tex"
            let rejectedRoot = Parsed.parsedWorkspaceRootModule rejected
                available = Map.fromList [(Semantic.semanticInterfaceOwner (completedModuleSemantic sealed), sealed)
                    | sealed <- modules]
            direct <- for (nubOrd (Parsed.parsedImportedAddress <$> Parsed.parsedModuleImports rejectedRoot)) \address ->
                maybe (fail "missing negative fixture import") pure (Map.lookup (moduleName address) available)
            input <- expectRightIO (typedModuleInput foundation (Module.finalPreludeReadiness prelude)
                resolver AlwaysMissValidation rejectedRoot direct)
            runTypedModule input >>= \case
                Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed Elaboration.ElaborationFormationRequirementMissing{}))) prefix -> do
                    assertBool "ordinary theorems do not publish instance registrations"
                        (all (null . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) . Commit.committedBatchDelta)
                            (Commit.pendingModulePrefixBatches prefix))
                Module.TypedModuleFailed failure _ -> fail ("wrong formation failure: " <> show failure)
                _ -> fail "an ordinary theorem crossed the formation boundary"
            for_ ["closed-instance-omitted", "closed-instance-failed"] \fixture -> do
                failedWorkspace <- parseFinalWorkspace prelude mounts ("test/structure-spikes/" <> fixture <> ".tex")
                failedInput <- expectRightIO (typedModuleInput foundation (Module.finalPreludeReadiness prelude)
                    unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule failedWorkspace) direct)
                runTypedModule failedInput >>= \case
                    Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedInstanceFailed failure)) prefix -> do
                        case failure of
                            Instance.InstanceProofOmitted{} -> pure ()
                            Instance.InstanceProofFailed{} -> pure ()
                            _ -> fail ("unexpected failed instance: " <> show failure)
                        assertBool "a failed instance publishes neither definition nor evidence"
                            (null (Commit.pendingModulePrefixBatches prefix))
                    Module.TypedModuleFailed failure _ -> fail ("wrong instance failure: " <> show failure)
                    _ -> fail "an unproved instance was admitted"

checksPairConstructionContracts :: Assertion
checksPairConstructionContracts = Temp.withSystemTempDirectory "pair-construction" \directory ->
    withAcceptedFixtureVampire "pair-construction-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            open = snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)
            source = "test/structure-spikes/construction-header-pair-import.tex"
            batchNamed modules name = sole (StrictText.unpack name)
                [ (sealed, batch)
                | sealed <- modules
                , batch <- Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)
                , any ((== Semantic.semanticName name) . Semantic.semanticAliasName)
                    (Semantic.declarationDeltaAliases (Commit.committedBatchDelta batch))]
            ruleOf batch = sole "provider result"
                [(entry, rule) | entry@(Semantic.Registration _ _ (Semantic.RegisterProviderResult rule)) <-
                    Semantic.declarationDeltaRegistrations (Commit.committedBatchDelta batch)]
            envelope = binders []
              where
                binders types (Core.CForall ty body) = binders (ty : types) body
                binders types body = (reverse types, headers body)
                headers (Core.CImp premise body) = premise : headers body
                headers _ = []
            loadSnapshot store keys = do
                reader <- Store.newStoreCheck store
                for keys \(key, syntax) -> do
                    candidate <- expectRightIO (Store.loadCachedModuleCandidate reader key syntax)
                        >>= maybe (fail "pair module artefact is missing") pure
                    let semantic = Store.cachedCandidateSemantic candidate
                    pure (Semantic.semanticInterfaceAssertedId semantic,
                        concatMap (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) (Semantic.semanticInterfaceDeclarations semantic),
                        [(Identity.storedPropositionCandidateId p, Identity.storedPropositionCandidateTerm p)
                            | p <- Store.cachedCandidatePropositions candidate])
        (keys, cold) <- bracket open Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts source
            modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
            (constructedModule, constructed) <- batchNamed modules "copy_pair_coordinate"
            (baselineModule, classified) <- batchNamed modules "copy_pair_coordinate_classification"
            constructionRule <- ruleOf constructed
            classificationRule <- ruleOf classified
            let variable index = Semantic.TemplateVariable (Semantic.ViewVariableIx index)
                pair = Semantic.TemplateOrderedPair (variable 2) (variable 1)
            for_ [constructionRule, classificationRule] \(registration, rule) -> do
                toList (Semantic.resultProviderTemplateArguments (Semantic.providerResultProvider rule))
                    @?= [variable 2, variable 1, variable 0]
                Semantic.registrationPath registration @?= Notion.ConjunctionHere
                case Semantic.providerResultPremises rule of
                    Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles
                            (Semantic.RulePremiseAtom (Semantic.StructureAtomTemplate _ arguments) :| [])) ->
                        toList arguments @?= [variable 0, pair]
                    _ -> fail "pair registration lost its single structure header"
                case Semantic.providerResultConclusion rule of
                    Semantic.StructureAtomTemplate _ arguments -> toList arguments @?=
                        [Semantic.ResultRuleProviderValue, Semantic.ResultRuleTerm pair]
                    _ -> fail "pair registration lost its parameterized result"
            Semantic.providerResultPremises (snd constructionRule) @?=
                Semantic.providerResultPremises (snd classificationRule)
            Semantic.providerResultConclusion (snd constructionRule) @?=
                Semantic.providerResultConclusion (snd classificationRule)
            baseline <- checkedPropositionTermByAlias baselineModule "copy_pair_coordinate_classification"
            for_ ["copy_pair_coordinate", "copy_pair_coordinateshape", "copy_pair_coordinateprojection_atlas"] \name -> do
                proposition <- checkedPropositionTermByAlias constructedModule name
                envelope (Core.frozenCoreTerm proposition) @?= envelope (Core.frozenCoreTerm baseline)
            -- These failures reach mandatory registration or term representability,
            -- not parsing, the mathematical proof, or an annotation mismatch.
            for_ [("construction-header-fresh-pair-rejected", 5, 10, "fresh or growing term"),
                    ("construction-header-opaque-term-rejected", 5, 10, "rule terms must be theorem variables"),
                    ("definition-header-pair-rejected", 3, 1, "")] \(name, line, column, diagnostic) -> do
                rejected <- parseFinalWorkspace prelude mounts ("test/structure-spikes/" <> name <> ".tex")
                let parsed = Parsed.parsedWorkspaceRootModule rejected
                    available = Map.fromList [(Semantic.semanticInterfaceOwner (completedModuleSemantic sealed), sealed)
                        | sealed <- modules]
                direct <- for (nubOrd (Parsed.parsedImportedAddress <$> Parsed.parsedModuleImports parsed)) \address ->
                    maybe (fail "missing header-control import") pure (Map.lookup (moduleName address) available)
                input <- expectRightIO (typedModuleInput foundation (Module.finalPreludeReadiness prelude)
                    unusedResolver AlwaysMissValidation parsed direct)
                runTypedModule input >>= \case
                    Module.TypedModuleFailed (Module.TypedActionFailed failure) prefix -> do
                        location <- case failure of
                            Module.TypedInstanceFailed (Instance.ConstructionInvalid location reason) -> do
                                assertBool ("registration rejection: " <> StrictText.unpack reason)
                                    (diagnostic `StrictText.isInfixOf` reason)
                                pure location
                            Module.TypedElaborationFailed (Elaboration.ElaborationGuardedTransparentDefinition location) -> pure location
                            _ -> fail ("unexpected header rejection: " <> show failure)
                        (locLine location, locColumn location) @?= (line, column)
                        assertBool "a rejected header publishes no declaration"
                            (null (Commit.pendingModulePrefixBatches prefix))
                    _ -> fail (name <> " was not rejected")
            assertTypedSuccess "cold pair import" =<< expectRightIO
                (checkResultWithStore store Verification.WarmStoreValidation
                    (Verification.verificationRequestObserver (\_ _ -> pure ())) prover source)
            keys <- for [ (parsed, sealed)
                    | parsed <- toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
                    , sealed <- modules
                    , moduleName (Parsed.parsedModuleAddress parsed) ==
                        Semantic.semanticInterfaceOwner (completedModuleSemantic sealed)] \(parsed, sealed) -> do
                key <- expectRight (Semantic.moduleArtefactKey (moduleName (Parsed.parsedModuleAddress parsed))
                    (Parsed.parsedModuleId parsed)
                    (Semantic.semanticInterfaceDirectInputs (completedModuleSemantic sealed))
                    (Identity.theoryId foundation))
                pure (key, Syntax.moduleSyntaxAssertedId (Parsed.parsedModuleSyntaxInterface parsed))
            snapshot <- loadSnapshot store keys
            pure (keys, snapshot)
        bracket open Store.closeStore \store -> do
            requests <- newIORef (0 :: Int)
            assertTypedSuccess "reopened warm pair import" =<< expectRightIO
                (checkResultWithStore store Verification.WarmStoreValidation
                    (Verification.verificationRequestObserver (\_ _ -> modifyIORef' requests (+ 1))) prover source)
            assertEqual "unchanged warm admission starts no external proof requests" 0 =<< readIORef requests
            warm <- loadSnapshot store keys
            assertEqual "warm templates and public propositions agree with cold admission" cold warm

rejectsInvalidConstructions :: Assertion
rejectsInvalidConstructions =
    Temp.withSystemTempDirectory "felix-construction-errors" \root -> do
        foundation <- expectRight Foundation.checkedFoundation
        let executable = root Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        let resolver = Declaration.vampireResolver
                (Provers.runPreparedTypedProver
                    (Provers.vampire executable Provers.defaultTimeLimit Provers.defaultMemoryLimit))
        bracket (snd <$> (Store.openStore (root Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            mounts <- exactFixtureMounts root
            forM_ cases \(name, headers, head', body, proof) -> do
                let source = unlines
                        [ "\\begin{construction}\\label{bad_constructor}"
                        , headers
                        , "The record $" <> head' <> "=" <> body <> "$."
                        , "\\end{construction}"
                        , proof
                        ]
                    path = name <> ".tex"
                ByteString.writeFile (root Posix.</> path) (Text.encodeUtf8 (StrictText.pack source))
                workspace <- parseFinalWorkspace prelude mounts path
                input <- expectRightIO (typedModuleInput foundation (Module.finalPreludeReadiness prelude)
                    unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule workspace) [])
                runTypedModule input >>= \case
                    Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedInstanceFailed _)) prefix ->
                        assertBool "a rejected construction publishes no equation, result, or registration"
                            (null (Commit.pendingModulePrefixBatches prefix))
                    Module.TypedModuleFailed failure _ -> assertFailure (name <> ": " <> show failure)
                    Module.TypedModuleOpenFailed failure -> assertFailure (name <> ": " <> show failure)
                    Module.TypedModuleSucceeded{} -> assertFailure (name <> " was unexpectedly accepted")
  where
    checkedProof = "\\begin{proof} Follows. \\end{proof}"
    cases =
        [ ("missing-proof", "Let $X$ be a set.", "\\Bad{X}", "\\structure{}", "")
        , ("omitted-proof", "Let $X$ be a set.", "\\Bad{X}", "\\structure{}",
            "\\begin{proof} Omitted. \\end{proof}")
        , ("nullary", "", "\\Bad", "\\structure{}", checkedProof)
        , ("repeated-parameter", "Let $X$ be a set.", "\\Bad{X}{X}", "\\structure{}", checkedProof)
        , ("implicit-parameter", "Let $X,Y$ be sets.", "\\Bad{X}", "\\structure{}", checkedProof)
        , ("parameter-order", "Let $X,Y$ be sets.", "\\Bad{Y}{X}", "\\structure{}", checkedProof)
        , ("non-record-body", "Let $X$ be a set.", "\\Bad{X}", "X", checkedProof)
        , ("recursive-body", "Let $X$ be a set.", "\\Bad{X}", "record based on \\Bad{X}", checkedProof)
        , ("mismatched-schema", "Let $X$ be a set.", "\\Bad{X}", "\\structure[onesorted structure]{\\carrier=X}", checkedProof)
        , ("pending-result", "Let $X$ be a set.", "\\Bad{X}", "\\structure{}",
            "\\begin{proof} Follows by \\obv{bad_constructor}. \\end{proof}")
        , ("pending-shape", "Let $X$ be a set.", "\\Bad{X}", "\\structure{}",
            "\\begin{proof} Follows by \\obv{bad_constructorshape}. \\end{proof}")
        ]

rejectsCarrierlessMisuse :: Assertion
rejectsCarrierlessMisuse =
    Temp.withSystemTempDirectory "felix-carrierless-errors" \root -> do
        foundation <- expectRight Foundation.checkedFoundation
        let executable = root Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        let preludeResolver = Declaration.vampireResolver
                (Provers.runPreparedTypedProver
                    (Provers.vampire executable
                        Provers.defaultTimeLimit Provers.defaultMemoryLimit))
        bracket
            (snd <$> (Store.openStore (root Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore \store -> do
                prelude <- expectRightIO
                    (acquireFinalPreludeSession store foundation preludeResolver)
                mounts <- exactFixtureMounts root
                forM_ cases \(label, source, checkFailure) -> do
                    let path = label <> ".tex"
                    ByteString.writeFile (root Posix.</> path)
                        (Text.encodeUtf8 (StrictText.pack source))
                    workspace <- parseFinalWorkspace prelude mounts path
                    input <- expectRightIO (typedModuleInput foundation
                        (Module.finalPreludeReadiness prelude) unusedResolver
                        AlwaysMissValidation
                        (Parsed.parsedWorkspaceRootModule workspace) [])
                    runTypedModule input >>= \case
                        Module.TypedModuleFailed
                                (Module.TypedActionFailed
                                    (Module.TypedElaborationFailed failure)) _ ->
                            checkFailure failure
                        Module.TypedModuleFailed
                                (Module.TypedActionFailed
                                    (Module.TypedProofFailed
                                        (Proof.ProofElaborationFailed failure))) _ ->
                            checkFailure failure
                        Module.TypedModuleSucceeded{} ->
                            assertFailure (label <> " was unexpectedly accepted")
                        Module.TypedModuleOpenFailed failure ->
                            assertFailure (label <> " did not open: " <> show failure)
                        Module.TypedModuleFailed failure _ ->
                            assertFailure (label <> " failed unexpectedly: " <> show failure)
  where
    recordSource = unlines
        [ "\\begin{struct}\\label{carrierless_fixture}"
        , "A carrierless fixture $R$ is a record equipped with"
        , "\\begin{enumerate}"
        , "\\item a set $\\atlas[R]$;"
        , "\\end{enumerate}."
        , "\\end{struct}"
        ]
    claim body = recordSource <> unlines
        [ "\\begin{proposition}\\label{invalid_use}"
        , "Let $R$ be a carrierless fixture."
        , body
        , "\\end{proposition}"
        ]
    capability = \case
        Elaboration.ElaborationStructureCarrierUnavailable location phrase -> do
            assertBool "capability error retains its source location" (locLine location > 0)
            assertEqual "capability error identifies its receiver"
                (Raw.Marker "carrierless_fixture") (Schema.structurePhraseMarker phrase)
        failure -> assertFailure ("unexpected capability error: " <> show failure)
    reconstructionFailure = \case
        Elaboration.ElaborationReconstructionBaseUnavailable location _ _ _ ->
            assertBool "reconstruction error retains the base location" (locLine location > 0)
        failure -> assertFailure ("unexpected reconstruction error: " <> show failure)
    cases =
        [ ("untyped-reconstruction-base",
            claim "Then $(carrierless fixture based on A)=R$.", reconstructionFailure)
        , ("all-replaced-untyped-base",
            claim "Then $(carrierless fixture based on A with \\atlas=B)=R$.", reconstructionFailure)
        , ("empty-target-untyped-base",
            claim "Then $(record based on A)=R$.", reconstructionFailure)
        , ("missing-copied-field",
            claim "Then $(carrierless fixture based on \\structure[record]{})=R$.", reconstructionFailure)
        , ("unjustified-reduct-base",
            claim "Then $(carrierless fixture based on \\reduct[carrierless fixture]{A})=R$.", reconstructionFailure)
        , ("duplicate-replacement",
            claim "Then $(carrierless fixture based on R with \\atlas=A and \\atlas=B)=R$.", \case
                Elaboration.ElaborationStructureAggregateDuplicateField _ _ (Raw.StructSymbol "atlas") -> pure ()
                failure -> assertFailure ("unexpected duplicate error: " <> show failure))
        , ("foreign-replacement",
            claim "Then $(carrierless fixture based on R with \\carrier=A)=R$.", \case
                Elaboration.ElaborationStructureAggregateUnknownField _ _ Raw.CarrierSymbol -> pure ()
                failure -> assertFailure ("unexpected foreign-field error: " <> show failure))
        , ("explicit-carrier", claim "Then $\\carrier[R]=\\carrier[R]$.", capability)
        , ("implicit-carrier", claim "Let $x\\in R$. Then $x=x$.", capability)
        , ("carrier-adjective", recordSource <> unlines
            [ "\\begin{definition}\\label{carrierless_inhabited}"
            , "Let $R$ be a carrierless fixture."
            , "$R$ is inhabited iff there exists $x\\in R$ such that $x=x$."
            , "\\end{definition}"
            ], capability)
        , ("empty-nonempty-aggregate",
            claim "Then $\\structure[carrierless fixture]{}=R$.", \case
                Elaboration.ElaborationStructureAggregateFieldArityMismatch _ _ 1 0 -> pure ()
                failure -> assertFailure ("unexpected arity error: " <> show failure))
        , ("fresh-carrier", unlines
            [ "\\begin{struct}\\label{forged_carrier}"
            , "A forged carrier $R$ is a record equipped with"
            , "\\begin{enumerate}"
            , "\\item a set $\\carrier[R]$;"
            , "\\end{enumerate}."
            , "\\end{struct}"
            ], \case
                Elaboration.ElaborationStructureSchemaInvalid _
                        Schema.LocalStructureReservedCarrier{} -> pure ()
                failure -> assertFailure ("unexpected carrier-role error: " <> show failure))
        ]

compilesBoundedLogicalGraphs :: Assertion
compilesBoundedLogicalGraphs = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-bounded-logical-graphs" \directory -> do
        let storePath = directory Posix.</> "store.sqlite"
            executable = directory Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        observedRoutes <- newIORef []
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    modifyIORef' observedRoutes
                        (<> [ Backend.typedProblemRoute
                                (Provers.preparedTypedProverLogicalProblem
                                    prepared)
                            ])
                    Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts repository
            writeIORef observedRoutes []
            fixtureWorkspace <- parseFinalWorkspace
                prelude mounts "test/phase5/exact-logical-graph.tex"
            fixtureModules <- compileFinalParsedWorkspaceWithResolver
                foundation prelude resolver fixtureWorkspace
            graphModule <- sole "bounded logical graph module"
                [ candidate
                | candidate <- fixtureModules
                , batch <- Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix candidate)
                , alias <- Semantic.declarationDeltaAliases
                    (Commit.committedBatchDelta batch)
                , Semantic.semanticAliasName alias
                    == Semantic.semanticName "logical_graph_on_function"
                ]
            genericBridge <- checkedPropositionTermByAlias
                graphModule "logical_graph_on_function"
            case Foundation.classifyFrozenCore genericBridge of
                Foundation.FoundationRequiresTh0 _exclusions -> pure ()
                classification ->
                    assertFailure
                        ("generic logical graph bridge unexpectedly classified "
                            <> show classification)
            fixtureModule <- case reverse fixtureModules of
                rootModule : _ -> pure rootModule
                [] ->
                    assertFailure "named logical graph root is absent"
                        >> fail "unreachable"
            namedFunction <- checkedPropositionTermByAlias
                fixtureModule "phase5_named_identity_graph_function"
            namedApplication <- checkedPropositionTermByAlias
                fixtureModule "phase5_named_identity_graph_application"
            downstream <- checkedPropositionTermByAlias
                fixtureModule "phase5_named_identity_graph_downstream"
            namedRelationMembership <- checkedPropositionTermByAlias
                fixtureModule "phase5_named_diagonal_relation_membership"
            namedRelationSubset <- checkedPropositionTermByAlias
                fixtureModule "phase5_named_diagonal_relation_subseteq"
            relationDownstream <- checkedPropositionTermByAlias
                fixtureModule "phase5_named_diagonal_relation_downstream"
            assertBool
                "named graph, relation, and downstream interfaces remain FOF-projectable"
                (all
                    ((== Foundation.FoundationFofProjectable)
                        . Foundation.classifyFrozenCore)
                    [ namedFunction
                    , namedApplication
                    , downstream
                    , namedRelationMembership
                    , namedRelationSubset
                    , relationDownstream
                    ])

            routes <- readIORef observedRoutes
            let rootRoutes = take 7 (reverse routes)
            assertEqual "seven named graph and relation proof obligations" 7
                (length rootRoutes)
            assertEqual "four higher-order construction obligations" 4
                (length (filter (== Backend.RouteTh0) rootRoutes))
            assertEqual "three first-order named/downstream obligations" 3
                (length (filter (== Backend.RouteFof) rootRoutes))

diagnosesStructureAggregates :: Assertion
diagnosesStructureAggregates = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory
            "felix-structure-aggregate-diagnostics" \root -> do
        let storePath = root Posix.</> "store.sqlite"
            executable = root Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        let resolver =
                Declaration.vampireResolver
                    (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit))
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts root
            traverse_
                (runCase foundation prelude resolver mounts root)
                cases
  where
    cases =
        [ ( "contextual"
          , "$\\structure{A,x}$ is an aggregate syntax structure."
          , Nothing
          )
        , ( "annotated-positional"
          , "$\\structure[aggregate syntax structure]{A,x}=T$."
          , Nothing
          )
        , ( "annotated-named"
          , "$\\structure[aggregate syntax structure]{\\aggregatePoint=x,\\carrier=A}=T$."
          , Nothing
          )
        , ( "schema-required"
          , "$\\structure{A,x}=T$."
          , Just \case
                Elaboration.ElaborationStructureAggregateSchemaRequired{} ->
                    pure ()
                failure -> unexpected "uncontextualized aggregate" failure
          )
        , ( "mixed-fields"
          , "$\\structure[aggregate syntax structure]{A,\\aggregatePoint=x}=T$."
          , Just \case
                Elaboration.ElaborationStructureAggregateMixedEntries{} ->
                    pure ()
                failure -> unexpected "mixed aggregate" failure
          )
        , ( "positional-arity"
          , "$\\structure[aggregate syntax structure]{A}=T$."
          , Just \case
                Elaboration.ElaborationStructureAggregateFieldArityMismatch
                        _location _phrase 2 1 ->
                    pure ()
                failure -> unexpected "short positional aggregate" failure
          )
        , ( "unknown-field"
          , "$\\structure[aggregate syntax structure]{\\carrier=A,\\unknownAggregateField=x}=T$."
          , Just \case
                Elaboration.ElaborationStructureAggregateUnknownField
                        _location _phrase
                        (Raw.StructSymbol "unknownAggregateField") ->
                    pure ()
                failure -> unexpected "unknown named field" failure
          )
        , ( "duplicate-field"
          , "$\\structure[aggregate syntax structure]{\\carrier=A,\\carrier=x}=T$."
          , Just \case
                Elaboration.ElaborationStructureAggregateDuplicateField
                        _location _phrase Raw.CarrierSymbol ->
                    pure ()
                failure -> unexpected "duplicate named field" failure
          )
        , ( "missing-field"
          , "$\\structure[aggregate syntax structure]{\\carrier=A}=T$."
          , Just \case
                Elaboration.ElaborationStructureAggregateMissingFields
                        _location _phrase
                        (Raw.StructSymbol "aggregatePoint" :| []) ->
                    pure ()
                failure -> unexpected "incomplete named aggregate" failure
          )
        ]

    unexpected label failure =
        assertFailure
            (label <> " produced the unexpected failure " <> show failure)

    runCase foundation prelude resolver mounts root
            (label, claim, maybeCheckFailure) = do
        let relative = label <> ".tex"
            path = root Posix.</> relative
        ByteString.writeFile path
            (Text.encodeUtf8
                (StrictText.pack (aggregateSource claim)))
        workspace <-
            parseFinalWorkspace prelude mounts relative
        input <-
            expectRightIO
                (typedModuleInput
                    foundation
                    (Module.finalPreludeReadiness prelude)
                    resolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule workspace)
                    [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed failure))
                    _prefix ->
                case maybeCheckFailure of
                    Nothing -> unexpected label failure
                    Just checkFailure -> checkFailure failure
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofElaborationFailed failure)))
                    _prefix ->
                case maybeCheckFailure of
                    Nothing -> unexpected label failure
                    Just checkFailure -> checkFailure failure
            Module.TypedModuleSucceeded{}
                | isNothing maybeCheckFailure -> pure ()
                | otherwise ->
                    assertFailure (label <> " was unexpectedly accepted")
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    (label <> " did not open: " <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    (label <> " failed unexpectedly: " <> show failure)

    aggregateSource claim =
        unlines
            [ "\\begin{struct}\\label{aggregate_syntax_structure}"
            , "    An aggregate syntax structure $X$ is a onesorted structure equipped with"
            , "    \\begin{enumerate}"
            , "        \\item\\label{aggregate_syntax_point}"
            , "            a point $\\aggregatePoint[X]\\in\\carrier[X]$;"
            , "    \\end{enumerate}"
            , "    ."
            , "\\end{struct}"
            , ""
            , "\\begin{proposition}\\label{aggregate_syntax_case}"
            , "    " <> claim
            , "\\end{proposition}"
            , "\\begin{proof}"
            , "    Follows by \\auto."
            , "\\end{proof}"
            ]

verifiesTransparentStructureAggregates :: Assertion
verifiesTransparentStructureAggregates = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-transparent-structure-aggregates"
        \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
            observedRoutes <- newIORef []
            let resolver =
                    Declaration.vampireResolver \prepared -> do
                        modifyIORef' observedRoutes
                            (<> [ Backend.typedProblemRoute
                                    (Provers.preparedTypedProverLogicalProblem
                                        prepared)
                                ])
                        Provers.runPreparedTypedProver
                            (Provers.vampire
                                "vampire"
                                (Provers.Seconds 20)
                                Provers.defaultMemoryLimit)
                            prepared
            (_startup, store) <-
                Store.openStore storePath (Identity.theoryId foundation)
                    >>= expectRight
            bracket (pure store) Store.closeStore \opened -> do
                prelude <-
                    expectRight
                        =<< acquireFinalPreludeSession
                            opened foundation resolver
                mounts <- exactFixtureMounts repository
                writeIORef observedRoutes []
                workspace <- parseFinalWorkspace
                    prelude mounts
                    "test/phase5/exact-structure-aggregate-syntax.tex"
                modules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver workspace
                sealed <- sole "transparent aggregate module" modules
                claims <- traverse
                    (checkedPropositionTermByAlias sealed)
                    [ "aggregate_syntax_contextual"
                    , "aggregate_syntax_contextual_exact"
                    , "aggregate_syntax_named"
                    , "aggregate_syntax_carrier"
                    , "aggregate_syntax_point_value"
                    ]
                assertBool
                    "aggregate structure, equality, and projection interfaces stay first-order"
                    (all
                        ((== Foundation.FoundationFofProjectable)
                            . Foundation.classifyFrozenCore)
                        claims)
                assertBool "all transparent aggregate facts have clean authority"
                    (all
                        ((== Authority.cleanAuthoritySafety)
                            . Authority.factAuthoritySafety
                            . Semantic.semanticFactAuthority)
                        [ fact
                        | batch <- Commit.pendingModulePrefixBatches
                            (Module.completedTypedModulePrefix sealed)
                        , fact <- Semantic.declarationDeltaFacts
                            (Commit.committedBatchDelta batch)
                        ])
                routes <- readIORef observedRoutes
                -- Exact-structure children enter preparation as well. All
                -- remaining aggregate residuals must stay first-order.
                assertEqual "five aggregate residuals remain FOF"
                    (replicate 5 Backend.RouteFof)
                    routes

verifiesClosedNamedStructureInstances :: Assertion
verifiesClosedNamedStructureInstances = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-closed-structure-instances"
        \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
            observedRoutes <- newIORef []
            let resolver =
                    Declaration.vampireResolver \prepared -> do
                        modifyIORef' observedRoutes
                            (<> [ Backend.typedProblemRoute
                                    (Provers.preparedTypedProverLogicalProblem
                                        prepared)
                                ])
                        Provers.runPreparedTypedProver
                            (Provers.vampire
                                "vampire"
                                (Provers.Seconds 20)
                                Provers.defaultMemoryLimit)
                            prepared
            (_startup, store) <-
                Store.openStore storePath (Identity.theoryId foundation)
                    >>= expectRight
            bracket (pure store) Store.closeStore \opened -> do
                prelude <-
                    expectRight
                        =<< acquireFinalPreludeSession
                            opened foundation resolver
                mounts <- exactFixtureMounts repository
                writeIORef observedRoutes []
                workspace <- parseFinalWorkspace
                    prelude mounts
                    "test/phase5/exact-structure-instance.tex"
                modules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver workspace
                sealed <- sole "closed instance module" modules
                structureFact <- checkedPropositionTermByAlias
                    sealed "instance_equation_surface"
                downstream <- checkedPropositionTermByAlias
                    sealed "instance_projection_available"
                parameterized <- checkedPropositionTermByAlias
                    sealed "instance_parameterized_object"
                parameterNotStored <- checkedPropositionTermByAlias
                    sealed "instance_parameter_is_not_stored"
                assertEqual "instance theorem remains first-order"
                    Foundation.FoundationFofProjectable
                    (Foundation.classifyFrozenCore structureFact)
                assertEqual "named projection interface remains first-order"
                    Foundation.FoundationFofProjectable
                    (Foundation.classifyFrozenCore downstream)
                assertEqual "parameterized instance theorem remains first-order"
                    Foundation.FoundationFofProjectable
                    (Foundation.classifyFrozenCore parameterized)
                assertEqual "structure parameters are not aggregate fields"
                    Foundation.FoundationFofProjectable
                    (Foundation.classifyFrozenCore parameterNotStored)
                instanceBatch <- batchByAlias
                    (Module.completedTypedModulePrefix sealed)
                    "instance_equation_surface"
                let delta = Commit.committedBatchDelta instanceBatch
                    facts = Semantic.declarationDeltaFacts delta
                    aliases = Semantic.declarationDeltaAliases delta
                    bindings =
                        Semantic.semanticEnvironmentBindings
                            (Semantic.declarationDeltaEnvironment delta)
                assertEqual "the public instance consequences have stable names"
                    (sort [ Semantic.semanticName "instance_equation_surface"
                    , Semantic.semanticName "instance_equation_surfaceshape"
                    , Semantic.semanticName
                        "instance_equation_surfaceprojection_carrier"
                    , Semantic.semanticName
                        "instance_equation_surfaceprojection_instancePoint"
                    ])
                    (sort (Semantic.semanticAliasName <$> aliases))
                assertEqual "one transparent instance object binding"
                    1 (length bindings)
                assertEqual
                    "equation, mathematical, shape, and aggregate proofs stay hidden; structure and projections are searchable"
                    (replicate 5 Semantic.SearchIneligible
                        <> replicate 4 Semantic.SearchEligible)
                    (Semantic.semanticFactSearchEligibility <$> facts)
                assertBool "every instance consequence has clean authority"
                    (all
                        ((== Authority.cleanAuthoritySafety)
                            . Authority.factAuthoritySafety
                            . Semantic.semanticFactAuthority)
                        facts)
                validation <-
                    maybe
                        (assertFailure
                            "closed instance declaration validation is absent"
                            >> fail "unreachable")
                        pure
                        (Commit.committedBatchDeclarationValidation
                            instanceBatch)
                let directAuthorizations =
                        Authority.validationDirectAuthorization
                            <$> Semantic.declarationValidationRecordCertificates
                                validation
                assertEqual "one declaration certificate per instance fact"
                    9 (length directAuthorizations)
                case directAuthorizations of
                    _equation : _mathematical : aggregateShape : _ ->
                        assertEqual
                            "aggregate exact shape is a kernel specialization"
                            (Authority.CheckedSourceProof Authority.NoExternalProofUse)
                            aggregateShape
                    _ ->
                        assertFailure
                            "closed instance validation lost its aggregate-shape certificate"
                assertEqual
                    "generated structure, exactness, and projection consequences are kernel-composed source proofs"
                    (replicate 4 (Authority.CheckedSourceProof Authority.NoExternalProofUse))
                    (drop 5 directAuthorizations)
                routes <- readIORef observedRoutes
                let instanceRoutes = routes
                assertBool
                    ("all named-instance and downstream obligations remain FOF: "
                        <> show instanceRoutes)
                    (all (== Backend.RouteFof) instanceRoutes)

verifiesCheckedStructureReducts :: Assertion
verifiesCheckedStructureReducts = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-checked-structure-reducts"
        \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
            observedProblems <- newIORef []
            let resolver =
                    Declaration.vampireResolver \prepared -> do
                        let problem =
                                Provers.preparedTypedProverLogicalProblem
                                    prepared
                        modifyIORef' observedProblems
                            (<>
                                [ ( Backend.supportedPropositionTerm
                                        (Backend.typedProblemClaim problem)
                                  , Backend.typedBackendFactReference
                                        <$> Vector.toList
                                            (Backend.typedProblemGlobalPremises
                                                problem)
                                  , Backend.typedLocalPremiseOrdinal
                                        <$> Vector.toList
                                            (Backend.typedProblemLocalPremises
                                                problem)
                                  , Backend.typedProblemRoute problem
                                  )
                                ])
                        Provers.runPreparedTypedProver
                            (Provers.vampire
                                "vampire"
                                (Provers.Seconds 20)
                                Provers.defaultMemoryLimit)
                            prepared
            (_startup, store) <-
                Store.openStore storePath (Identity.theoryId foundation)
                    >>= expectRight
            bracket (pure store) Store.closeStore \opened -> do
                prelude <-
                    expectRight
                        =<< acquireFinalPreludeSession
                            opened foundation resolver
                mounts <- exactFixtureMounts repository
                writeIORef observedProblems []
                workspace <- parseFinalWorkspace
                    prelude mounts
                    "test/phase5/exact-structure-reduct.tex"
                modules <- compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver workspace
                sealed <- sole "checked reduct module" modules
                parent <- checkedPropositionTermByAlias
                    sealed "reduct_is_parent"
                exactParent <- checkedPropositionTermByAlias
                    sealed "reduct_is_exact_parent"
                projection <- checkedPropositionTermByAlias
                    sealed "reduct_preserves_carrier"
                reductProjection <- checkedPropositionTermByAlias
                    sealed "reduct_basereductprojection_carrier"
                (exactStructureTerm, exactShapeTerm) <-
                    case Core.frozenCoreTerm exactParent of
                        Core.CAnd actualParent exactShape ->
                            assertEqual
                                "exact structure means the full parent predicate plus exact shape"
                                (Core.frozenCoreTerm parent)
                                actualParent
                                >> pure (actualParent, exactShape)
                        target ->
                            assertFailure
                                ("unexpected exact-structure target: "
                                    <> show target)
                                >> fail "unreachable"
                traverse_
                    (\(label, term) ->
                        case Foundation.classifyFrozenCore term of
                            Foundation.FoundationRequiresTh0 _ -> pure ()
                            classification ->
                                assertFailure
                                    (label <> " unexpectedly classified "
                                        <> show classification))
                    [ ("parent reduct theorem", parent)
                    , ("exact parent reduct theorem", exactParent)
                    , ("reduct projection theorem", projection)
                    , ("generated reduct projection law", reductProjection)
                    ]
                reductBatch <- batchByAlias
                    (Module.completedTypedModulePrefix sealed)
                    "reduct_basereductprojection_carrier"
                reductAlias <- sole "reduct projection alias"
                    [ alias
                    | alias <- Semantic.declarationDeltaAliases
                        (Commit.committedBatchDelta reductBatch)
                    , Semantic.semanticAliasName alias
                        == Semantic.semanticName
                            "reduct_basereductprojection_carrier"
                    ]
                reductFact <- sole "reduct projection fact"
                    [ fact
                    | fact <- Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta reductBatch)
                    , Semantic.semanticFactFingerprint fact
                        == Semantic.semanticAliasTarget reductAlias
                    ]
                assertEqual "generated reduct equations remain opt-in"
                    Semantic.SearchIneligible
                    (Semantic.semanticFactSearchEligibility reductFact)
                assertEqual "generated reduct equation has clean authority"
                    Authority.cleanAuthoritySafety
                    (Authority.factAuthoritySafety
                        (Semantic.semanticFactAuthority reductFact))
                problems <- readIORef observedProblems
                headDefinition <-
                    factFingerprintByAlias
                        (Module.completedTypedModulePrefix sealed)
                        "reduct_base"
                headInheritance <- factFingerprintByAlias
                    (Module.completedTypedModulePrefix sealed) "reduct_baseinherit_onesorted_structure"
                retainedParentFacts <-
                    traverse
                        (factFingerprintByAlias
                            (Module.completedTypedModulePrefix sealed))
                        [ "reduct_baseshape"
                        , "reduct_basereductexact"
                        , "reduct_extensioninherit_reduct_base"
                        , "reduct_extension_object"
                        ]
                parentBatch <- batchByAlias (Module.completedTypedModulePrefix sealed) "reduct_is_parent"
                parentCertificate <- sole "parent proof certificate"
                    (Commit.committedBatchValidationCertificates parentBatch)
                assertEqual "the standalone parent proof now closes internally"
                    (Authority.CheckedSourceProof Authority.NoExternalProofUse)
                    (Authority.validationDirectAuthorization parentCertificate)

                -- Keep the shallow export boundary covered even when the
                -- optional internal attempt can close the entire parent goal.
                (parentClaim, parentProof) <- sole "standalone parent source"
                    [ (Raw.BlockClaim kind location title (Raw.Marker "reduct_parent_export_control") body, proof)
                    | parsed <- toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
                    , (Raw.BlockClaim kind location title (Raw.Marker "reduct_is_parent") body,
                        Raw.BlockProof _ proof _) <- zip (Parsed.parsedModuleBlocks parsed)
                            (drop 1 (Parsed.parsedModuleBlocks parsed)) ]
                closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
                let globalTyping = Identity.globalTypingFromClosure closure
                truth <- expectRight (Core.checkScopedCanonicalCore globalTyping [] Core.CTruth)
                forcedMiss <- maybe (fail "zero-work fixture unexpectedly proved truth") pure
                    (Obvious.obviousRunFailure (Obvious.obviousProofReport
                        Obvious.defaultObviousBudget {Obvious.obviousFocusedWorkLimit = 0, Obvious.obviousRefutationWorkLimit = 0}
                        Obvious.AnyObviousProof foundation globalTyping [] [] [] truth))
                relative <- expectRight (safeRelativePath "reduct-export-control.tex")
                let owner = moduleNameFromParts
                        (sourceNamespaceIdFromDigest (hashBlake2b256 "reduct-export-control")) relative
                writeIORef observedProblems []
                fallback <- expectRight =<< runModuleDriver foundation owner
                    ([Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude), completedModuleEvidence sealed])
                    resolver AlwaysMissValidation do
                        prepared <- Declaration.runProspectiveLoweringDriver
                            (Proof.prepareProofWithObviousFailureFixture forcedMiss parentClaim (Just parentProof))
                            >>= either Declaration.failModuleDriver pure
                        lowered <- Declaration.runProspectiveLoweringDriver (Proof.lowerPreparedProof prepared)
                            >>= either Declaration.failDeclarationDriver pure
                        Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof
                case fallback of
                    Declaration.DriverSucceeded{} -> pure ()
                    Declaration.DriverFailed failure _ -> assertFailure (show failure)
                    Declaration.DriverSealFailed failure _ -> assertFailure (show failure)
                fallbackProblems <- readIORef observedProblems
                assertEqual "the standalone fallback retains two component residuals"
                    2 (length fallbackProblems)
                for_ fallbackProblems \(_claim, facts, _locals, route) ->
                    assertEqual "residuals preserve the selected abstraction when still higher order"
                        (Set.fromList (retainedParentFacts <>
                            [fact | route == Backend.RouteTh0, fact <- [headDefinition, headInheritance]]))
                        (Set.fromList facts)
                -- Force the same fallback below a fresh binder. An exact
                -- projection of the earlier conjunction must be replayed in
                -- the kernel; without that local evidence it remains an ATP
                -- residual. The shape obligation still goes to the prover.
                -- Uncited introduction must retain the proved local components
                -- needed for predicate substitution in every residual scope.
                localResiduals <- forM [("reduct_local_projection", 1), ("reduct_local_missing", 2),
                        ("reduct_wide_local_projection", 1),
                        ("reduct_predicate_substitution", 2),
                        ("reduct_predicate_substitution_plain", 2),
                        ("reduct_local_alias_chain", 0)]
                    \(sourceName, expectedCount) -> do
                        (localClaim, localProof) <- sole "local residual source"
                            [ (Raw.BlockClaim kind location title
                                    (Raw.Marker (sourceName <> "_control")) body, proof)
                            | parsed <- toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
                            , (Raw.BlockClaim kind location title (Raw.Marker name) body,
                                Raw.BlockProof _ proof _) <- zip (Parsed.parsedModuleBlocks parsed)
                                    (drop 1 (Parsed.parsedModuleBlocks parsed))
                            , name == sourceName
                            ]
                        writeIORef observedProblems []
                        let runLocal preparation = do
                                result <- expectRight =<< runModuleDriver foundation owner
                                    ([Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude), completedModuleEvidence sealed])
                                    resolver AlwaysMissValidation do
                                        prepared <- Declaration.runProspectiveLoweringDriver preparation
                                            >>= either Declaration.failModuleDriver pure
                                        lowered <- Declaration.runProspectiveLoweringDriver
                                            (Proof.lowerPreparedProof prepared)
                                            >>= either Declaration.failDeclarationDriver pure
                                        _ <- Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof
                                        pure (Proof.preparedProofPreparationStatistics prepared)
                                case result of
                                    Declaration.DriverSucceeded statistics _ _ -> pure statistics
                                    Declaration.DriverFailed failure _ -> fail (show failure)
                                    Declaration.DriverSealFailed failure _ -> fail (show failure)
                        _ <- runLocal (Proof.prepareProofWithObviousFailureFixture
                            forcedMiss localClaim (Just localProof))
                        localProblems <- readIORef observedProblems
                        assertEqual (StrictText.unpack sourceName <> " external residuals")
                            expectedCount (length localProblems)
                        when (sourceName == "reduct_predicate_substitution_plain") do
                            assertBool "canonical introduction does not broaden plain Auto's global selection"
                                (all (\(_claim, facts, _locals, _route) -> null facts) localProblems)
                        when (sourceName == "reduct_predicate_substitution_plain") do
                            exhaustedRefinements <- forM [0, 2000, 8000, 32000, 128000] \work -> do
                                writeIORef observedProblems []
                                statistics <- runLocal (Proof.prepareProofWithPreparationWork
                                    work localClaim (Just localProof))
                                residuals <- readIORef observedProblems
                                assertBool "bounded plain Auto keeps its empty global selection"
                                    (all (\(_claim, facts, _locals, _route) -> null facts) residuals)
                                pure (any (Preparation.preparationExhausted . snd) statistics
                                    && length residuals > 1)
                            assertBool "an expanded predicate survives subsequent preparation exhaustion"
                                (or exhaustedRefinements)
                        pure (sourceName, [claim | (claim, _facts, _locals, _route) <- localProblems])
                assertEqual "seventeen supplied laws leave exactly the same shape residual as one"
                    (List.lookup "reduct_local_projection" localResiduals)
                    (List.lookup "reduct_wide_local_projection" localResiduals)
                assertEqual "plain and cited Auto use the same representation refinement"
                    (List.lookup "reduct_predicate_substitution" localResiduals)
                    (List.lookup "reduct_predicate_substitution_plain" localResiduals)
                exactSelection <- traverse
                    (factFingerprintByAlias (Module.completedTypedModulePrefix sealed))
                    ["reduct_is_parent", "reduct_baseshape", "reduct_basereductexact",
                     "reduct_extensioninherit_reduct_base", "reduct_extension_object"]
                let exactChildren = [(claim, locals, route)
                        | (claim, facts, locals, route) <- problems
                        , Set.fromList facts == Set.fromList exactSelection]
                assertEqual "the cited predicate proof leaves only exact shape"
                    1 (length exactChildren)
                assertEqual "exact shape remains its own obligation" 1
                    (length [() | (claim, _, _) <- exactChildren, claim == exactShapeTerm])
                assertBool "the predicate is refined through its canonical equation"
                    (all (\(claim, _, _) -> claim /= exactStructureTerm) exactChildren)
                assertBool "exact children retain the authorized higher-order selection"
                    (all (\(_, locals, route) -> null locals && route == Backend.RouteTh0) exactChildren)
                assertBool
                    "the monolithic exact pair is not submitted"
                    (all
                        (\(claim, _facts, _locals, _route) ->
                            claim /= Core.frozenCoreTerm exactParent)
                        problems)

verifiesStructureInheritanceMatrix :: Assertion
verifiesStructureInheritanceMatrix = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-structure-inheritance" \directory -> do
        let storePath = directory Posix.</> "store.sqlite"
        observedRoutes <- newIORef []
        observedProblems <- newIORef []
        observedSelections <- newIORef Map.empty
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    let problem =
                            Provers.preparedTypedProverLogicalProblem prepared
                    modifyIORef' observedRoutes
                        (<> [Backend.typedProblemRoute problem])
                    modifyIORef' observedSelections (Map.insert
                        (Provers.preparedVerificationRequestId (Provers.preparedTypedProverRequest prepared))
                        (Backend.typedBackendFactReference <$> Vector.toList (Backend.typedProblemGlobalPremises problem)))
                    modifyIORef' observedProblems
                        (<>
                            [ ( Backend.supportedPropositionTerm
                                    (Backend.typedProblemClaim problem)
                              , Backend.typedBackendFactReference
                                    <$> Vector.toList
                                        (Backend.typedProblemGlobalPremises
                                            problem)
                              , Backend.typedProblemRoute problem
                              )
                            ])
                    Provers.runPreparedTypedProver
                        (Provers.vampire
                            "vampire"
                            (Provers.Seconds 20)
                            Provers.defaultMemoryLimit)
                        prepared
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts repository
            writeIORef observedRoutes []
            writeIORef observedProblems []
            workspace <- parseFinalWorkspace
                prelude mounts
                "test/phase5/exact-structure-inheritance.tex"
            sealed <- sole "structure inheritance module"
                =<< compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver workspace
            claims <- traverse
                (checkedPropositionTermByAlias sealed)
                [ "matrix_diamond_is_open_base"
                , "matrix_diamond_is_exact_diamond"
                , "matrix_diamond_is_not_exact_base"
                , "matrix_annotation_is_not_a_tag"
                , "matrix_family_is_diamond"
                ]
            assertBool
                "open-parent, exact-child, annotation, and family interfaces stay first-order"
                (all
                    ((== Foundation.FoundationFofProjectable)
                        . Foundation.classifyFrozenCore)
                    claims)
            assertTransparentObjectAlias sealed "matrix_diamond_object"
            assertTransparentObjectAlias sealed "matrix_family"

            let descriptors = checkedStructureSchemas sealed
            base <- descriptor "matrix_base" descriptors
            left <- descriptor "matrix_left" descriptors
            right <- descriptor "matrix_right" descriptors
            diamond <- descriptor "matrix_diamond" descriptors
            let prefix = Module.completedTypedModulePrefix sealed
            citedViews <- traverse (factFingerprintByAlias prefix)
                ["matrix_diamond", "matrix_diamondinherit_matrix_left", "matrix_diamondinherit_matrix_right"]
            witnessBatch <- batchByAlias prefix "matrix_cited_parent_witness"
            witnessValidation <- sole "cited parent witness validation"
                (Commit.committedBatchProofValidations witnessBatch)
            selections <- readIORef observedSelections
            case Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate witnessValidation) of
                Authority.CheckedSourceProof requests ->
                    assertEqual "a cited definition exposes exactly its direct-parent laws"
                        [Just (sort citedViews)]
                        [sort <$> Map.lookup request selections | request <- Authority.externalProofUseRequests requests]
                other -> assertFailure ("unexpected cited witness authority: " <> show other)
            parentBatch <- batchByAlias prefix "matrix_cited_parent"
            parentValidation <- sole "cited parent validation"
                (Commit.committedBatchProofValidations parentBatch)
            case Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate parentValidation) of
                Authority.CheckedSourceProof requests ->
                    assertBool "cited obvious inheritance replays without ATP"
                        (null (Authority.externalProofUseRequests requests))
                other -> assertFailure ("unexpected cited parent authority: " <> show other)
            assertEqual "a carrier-only native schema adds no local fields"
                []
                (schemaLocalFields base)
            leftField <- sole "left branch local field"
                (schemaLocalFields left)
            assertEqual "the branch-local field keeps its declared role"
                (Raw.StructSymbol "matrixPoint")
                (Schema.resolvedFieldSymbol leftField)
            assertEqual "the carrier-only sibling adds no local fields"
                []
                (schemaLocalFields right)
            assertEqual "the compatible diamond allocates no replacement fields"
                []
                (schemaLocalFields diamond)
            assertEqual "the diamond retains both parent applications in order"
                [ Raw.Marker "matrix_left"
                , Raw.Marker "matrix_right"
                ]
                ( parentMarker descriptors
                    <$> schemaParents diamond
                )

            diamondGoal <- checkedPropositionTermByAlias
                sealed "matrix_family_is_diamond"
            subject <-
                case Core.frozenCoreTerm diamondGoal of
                    Core.CForall Core.TySet
                        (Core.CApp (Core.CGlobal predicate) argument)
                        | schemaPredicate diamond
                            == predicate -> pure argument
                    target ->
                        assertFailure
                            ("unexpected matrix diamond target: " <> show target)
                            >> fail "unreachable"
            let expectedResiduals =
                    Record.recordOpenShape
                        [Core.CGlobal (Schema.resolvedFieldSelector field)
                        | field <- Map.elems (Schema.resolvedSchemaFields diamond)] subject
                    : [Core.instantiateCanonical subject (Schema.requirementBodyTerm key)
                      | key <- Map.keys (Schema.resolvedSchemaRequirements diamond)]
            selectedFamilyFacts <-
                traverse
                    (factFingerprintByAlias
                        (Module.completedTypedModulePrefix sealed))
                    [ "matrix_family"
                    , "matrix_diamond"
                    , "matrix_left"
                    , "matrix_right"
                    , "matrix_base"
                    , "matrix_leftaggregateexact"
                    , "matrix_leftaggregateprojection_carrier"
                    , "matrix_leftaggregateprojection_matrixPoint"
                    , "matrix_leftinherit_matrix_base"
                    , "matrix_rightinherit_matrix_base"
                    , "matrix_baseinherit_onesorted_structure"
                    ]
            diamondDefinition <-
                factFingerprintByAlias
                    (Module.completedTypedModulePrefix sealed)
                    "matrix_diamond"
            let retainedFamilyFacts =
                    filter (/= diamondDefinition) selectedFamilyFacts
            problems <- readIORef observedProblems
            let familyResiduals =
                    [ (claim, route)
                    | (claim, facts, route) <- problems
                    , Set.fromList facts == Set.fromList retainedFamilyFacts
                    ]
            assertEqual "diamond residuals are the normalized shape and unique requirements"
                (sort expectedResiduals) (sort (fst <$> familyResiduals))
            assertBool "all normalized diamond residuals remain first-order"
                (all ((== Backend.RouteFof) . snd) familyResiduals)

            let batches = Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix sealed)
                facts =
                    [ fact
                    | batch <- batches
                    , fact <- Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta batch)
                    ]
                targets =
                    [ Core.frozenCoreTerm
                        (Identity.checkedPropositionTerm proposition)
                    | batch <- batches
                    , proposition <- Commit.committedBatchPropositions batch
                    ]
            assertBool "every inheritance consequence has clean authority"
                (all
                    ((== Authority.cleanAuthoritySafety)
                        . Authority.factAuthoritySafety
                        . Semantic.semanticFactAuthority)
                    facts)
            assertBool "structure declarations generate no inhabitation theorem"
                (all (not . isTopLevelExistential) targets)
            routes <- readIORef observedRoutes
            assertBool "the public inheritance interfaces finish in FOF"
                (all (== Backend.RouteFof) routes)
  where
    descriptor marker descriptors =
        maybe
            (assertFailure ("missing structure descriptor " <> marker)
                >> fail "unreachable")
            pure
            (find
                ((== Raw.Marker (StrictText.pack marker))
                    . Schema.structurePhraseMarker
                    . Schema.resolvedSchemaPhrase)
                descriptors)

    parentMarker schemas application =
        Schema.structurePhraseMarker (Schema.resolvedSchemaPhrase (fromMaybe
            (impossible "checked parent presentation lost its schema")
            (find ((== Schema.structureApplicationId application) . Schema.resolvedSchemaId) schemas)))

    isTopLevelExistential = \case
        Core.CExists _type _body -> True
        _ -> False

unfoldsEquivalentStructurePredicates :: Assertion
unfoldsEquivalentStructurePredicates = withAcceptedFixtureVampire "canonical-structure" \executable ->
  Temp.withSystemTempDirectory "canonical-structure-store" \directory -> do
    foundation <- expectRight Foundation.checkedFoundation
    let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver executable)
    prelude <- bracket (snd <$> (Store.openStore (directory Posix.</> "store.sqlite")
            (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store ->
        expectRight =<< acquireFinalPreludeSession store foundation resolver
    mounts <- exactFixtureMounts =<< getCurrentDirectory
    workspace <- parseFinalWorkspace prelude mounts "test/phase9/notion-classification-bundle.tex"
    let parsed = Parsed.parsedWorkspaceRootModule workspace
        blocks = Parsed.parsedModuleBlocks parsed
        entries index = [Parsed.parsedSyntaxOccurrenceEntry occurrence
            | occurrence <- Parsed.parsedModuleSyntaxOccurrences parsed
            , Parsed.parsedSyntaxOccurrenceBlockIndex occurrence == index]
    (structureIndex, structureBlock@(Raw.BlockStruct _ _ _ rawStructure)) <- sole "carrier alias"
        [(index, block) | (index, block@(Raw.BlockStruct _ _ (Raw.Marker "notion_bundle_carrier") _))
            <- zip [0..] blocks]
    (definitionIndex, definitionBlock) <- sole "aggregate definition"
        [(index, block) | (index, block@Raw.BlockDefn{}) <- zip [0..] blocks]
    (claim, proof) <- sole "exact carrier claim"
        [(block, proof) | (block@(Raw.BlockClaim _ _ _ (Raw.Marker "notion_bundle_exact") _),
            Raw.BlockProof _ proof _) <- zip blocks (drop 1 blocks)]
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    let typing = Identity.globalTypingFromClosure closure
    truth <- expectRight (Core.checkScopedCanonicalCore typing [] Core.CTruth)
    forcedMiss <- maybe (fail "zero-work fixture unexpectedly proved truth") pure
        (Obvious.obviousRunFailure (Obvious.obviousProofReport
            Obvious.defaultObviousBudget {Obvious.obviousFocusedWorkLimit = 0, Obvious.obviousRefutationWorkLimit = 0}
            Obvious.AnyObviousProof foundation typing [] [] [] truth))
    relative <- expectRight (safeRelativePath "canonical-structure.tex")
    -- Fixed namespaces put the alias on either side of the built-in ID;
    -- filesystem roots and temporary directory names must not choose the case.
    for_ [("canonical-structure-0", GT), ("canonical-structure-2", LT)] \(namespace, ordering) -> do
        let owner = moduleNameFromParts (sourceNamespaceIdFromDigest (hashBlake2b256 namespace)) relative
            action :: Bool -> Declaration.ModuleDriver String ()
            action misuseResource = do
                preparedStructure <- Declaration.runProspectiveLoweringDriver
                    (Structure.prepareStructure structureBlock (entries structureIndex))
                    >>= either (Declaration.failModuleDriver . show) pure
                loweredStructure <- Declaration.runProspectiveLoweringDriver
                    (Structure.lowerPreparedStructure preparedStructure)
                    >>= either Declaration.failDeclarationDriver pure
                _ <- Declaration.admitCheckedDeclaration loweredStructure Structure.authorizeCheckedStructure
                (alias, builtin, resource, builtinResource, canonical) <- Declaration.runProspectiveLoweringDriver do
                    alias <- Declaration.resolveVisibleStructureLowering (Schema.structurePhrase (Raw.structPhrase rawStructure))
                        >>= maybe (impossible "missing carrier alias") pure
                    builtin <- Declaration.resolveVisibleStructureLowering Builtin.builtinOnesortedPhrase
                        >>= maybe (impossible "missing built-in carrier") pure
                    resource <- Declaration.lookupStructureFactLowering
                        (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema alias))
                        (Schema.StructureResourceFact Schema.PredicateDefinitionResource)
                        >>= maybe (impossible "missing predicate resource") pure
                    builtinResource <- Declaration.lookupStructureFactLowering
                        (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema builtin))
                        (Schema.StructureResourceFact Schema.PredicateDefinitionResource)
                        >>= maybe (impossible "missing built-in resource") pure
                    lookupCanonical <- Declaration.pointwiseDefinitionLookupLowering
                    canonical <- maybe (impossible "missing canonical equation") pure
                        (lookupCanonical (Declaration.resolvedStructurePredicate alias))
                    pure (alias, builtin, resource, builtinResource, canonical)
                liftIO do
                    assertEqual (show namespace <> " schema order") ordering
                        (compare (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema alias))
                            (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema builtin)))
                    assertEqual "equivalent schemas share a predicate object"
                        (Declaration.resolvedStructurePredicate builtin) (Declaration.resolvedStructurePredicate alias)
                    assertEqual "the canonical and resource equations agree"
                        (snd resource) (Declaration.resolvedDefinitionViewProposition canonical)
                    assertBool "the later resource is not the canonical occurrence"
                        (fst resource /= Declaration.resolvedDefinitionViewFingerprint canonical)
                    assertEqual "the earlier built-in occurrence remains canonical"
                        (fst builtinResource) (Declaration.resolvedDefinitionViewFingerprint canonical)
                preparedBinding <- Declaration.runProspectiveLoweringDriver
                    (Binding.prepareBinding definitionBlock (entries definitionIndex))
                    >>= either (Declaration.failModuleDriver . show) pure
                loweredBinding <- Declaration.runProspectiveLoweringDriver (Binding.lowerPreparedBinding preparedBinding)
                    >>= either Declaration.failDeclarationDriver pure
                _ <- Declaration.admitCheckedDeclaration loweredBinding Binding.authorizeCheckedBinding
                prepared <- Declaration.runProspectiveLoweringDriver
                    (Proof.prepareProofWithObviousFailureFixture forcedMiss claim (Just proof))
                    >>= either (Declaration.failModuleDriver . show) pure
                lowered <- Declaration.runProspectiveLoweringDriver (Proof.lowerPreparedProof prepared)
                    >>= either Declaration.failDeclarationDriver pure
                _ <- Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof
                when misuseResource do
                    void (DeclTest.admitProof (Semantic.proofSyntaxId "noncanonical-resource") []
                        (Declaration.checkedCandidate (Declaration.candidateSpec (snd resource) Semantic.SearchEligible [])
                            (Declaration.checkedNoExternalSourceProofPlanning [])) \candidate -> do
                        Declaration.authorizeKernelProofCandidate candidate do
                            let derivation = Kernel.importedFactDerivation (Kernel.importIx 0)
                            _ <- Declaration.acceptScopedKernelDischarge Declaration.KernelImplicitObvious
                                [fst resource] Vector.empty
                                (Core.embedClosedCore [] (Identity.checkedPropositionTerm (snd resource))) derivation
                            pure derivation)
        for_ [False, True] \misuseResource -> do
            result <- expectRight =<< runModuleDriver foundation owner
                [Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude)] resolver AlwaysMissValidation
                (action misuseResource)
            case (misuseResource, result) of
                (False, Declaration.DriverSucceeded () _ _) -> pure ()
                (True, Declaration.DriverFailed (Declaration.DriverDeclarationFailed
                        Declaration.KernelObviousImportPolicyMismatch) _) -> pure ()
                (_, Declaration.DriverFailed failure _) -> assertFailure (show failure)
                (_, Declaration.DriverSealFailed failure _) -> assertFailure (show failure)
                _ -> assertFailure "an equivalent, noncanonical occurrence gained implicit authority"

preservesStructureResourceOccurrences :: Assertion
preservesStructureResourceOccurrences =
    Temp.withSystemTempDirectory "felix-structure-residual-dependency" \root -> do
        let executable = root Posix.</> "vampire"
            relative = "exact-structure-inheritance-source-proof.tex"
            sourcePath = root Posix.</> relative
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        observedProblems <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                modifyIORef' observedProblems
                    (<> [ ( Backend.supportedPropositionTerm
                                (Backend.typedProblemClaim problem)
                          , Backend.typedBackendFactReference
                                <$> Vector.toList
                                    (Backend.typedProblemGlobalPremises
                                        problem)
                          , Backend.typedProblemRoute problem
                          ) ])
                Provers.runPreparedTypedProver
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared
        let storePath = root Posix.</> "store.sqlite"
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        originalSource <- ByteString.readFile
            "test/phase5/exact-structure-inheritance.tex"
        let syntheticSource = StrictText.unlines
                [ ""
                , "\\begin{proposition}\\label{matrix_family_source_axiom_regression}"
                , "    $\\matrixFamily{A}$ is a matrix diamond."
                , "\\end{proposition}"
                , "\\begin{proof}"
                , "    Follows by \\auto{matrix_diamond_source_axiom}."
                , "\\end{proof}"
                ]
        ByteString.writeFile sourcePath
            (originalSource <> Text.encodeUtf8 syntheticSource)
        (prelude, originalSealed, sourceClaim, sourceProof) <-
            bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            repositoryMounts <- exactFixtureMounts =<< getCurrentDirectory
            originalWorkspace <- parseFinalWorkspace
                prelude repositoryMounts
                "test/phase5/exact-structure-inheritance.tex"
            originalSealed <- sole "structure residual dependency module"
                =<< compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver originalWorkspace
            syntheticMounts <- exactFixtureMounts root
            syntheticWorkspace <- parseFinalWorkspace
                prelude syntheticMounts relative
            let syntheticBlocks = Parsed.parsedModuleBlocks
                    (Parsed.parsedWorkspaceRootModule syntheticWorkspace)
            sourceClaim <- sole "matrix family source claim"
                [ block
                | block@Raw.BlockClaim{} <- syntheticBlocks
                , case block of
                    Raw.BlockClaim _kind _location _title marker _claim ->
                        marker == Raw.Marker
                            "matrix_family_source_axiom_regression"
                    _ -> False
                ]
            sourceProof <- sole "matrix family source proof"
                [ proof
                | (block, Raw.BlockProof _location proof _end) <-
                    zip syntheticBlocks (drop 1 syntheticBlocks)
                , block == sourceClaim
                ]
            pure (prelude, originalSealed, sourceClaim, sourceProof)
        definitionTarget <- checkedPropositionTermByAlias
            originalSealed "matrix_diamond"
        writeIORef observedProblems []
        checkedImports <- prepareTestImports (Identity.theoryId foundation)
            ([Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude), completedModuleEvidence originalSealed])
        result <- expectRight
            =<< Declaration.runModuleDriverFreshIO
                foundation
                (completedModuleOwner originalSealed)
                checkedImports
                resolver
                do
                    -- The generated structure equation contains internal
                    -- selector terms that ordinary source syntax cannot
                    -- reproduce.  Import the real fixture and add the
                    -- exact source-axiom occurrence through the checked
                    -- declaration boundary; the proof below still follows
                    -- the ordinary source-level preparation path.
                    sourceSpec <-
                        either Declaration.failDeclarationDriver pure
                            =<< Declaration.prepareFrozenCandidateSpecDriver
                                []
                                definitionTarget
                                Semantic.SearchEligible
                                [Semantic.semanticName "matrix_diamond_source_axiom"]
                    let sourceCandidate = Declaration.checkedCandidate
                            sourceSpec
                            Declaration.checkedSourceAxiomPlanning
                    _ <- Declaration.admitCheckedDeclaration
                        (Declaration.checkedCompiledDeclaration
                            (Semantic.declarationSyntaxId
                                (Text.encodeUtf8
                                    (StrictText.pack
                                        "synthetic-structure-source-axiom")))
                            []
                            []
                            []
                            Nothing
                            [sourceCandidate :| []]
                            ())
                        \() -> \case
                            [source :| []] -> do
                                Declaration.authorizeSourceAxiomCandidate
                                    source
                            _ -> impossible
                                "synthetic structure candidates changed shape"
                    prepared <-
                        Declaration.runProspectiveLoweringDriver
                            (Proof.prepareProof sourceClaim (Just sourceProof))
                            >>= either
                                (Declaration.failModuleDriver . show)
                                pure
                    checked <-
                        Declaration.runProspectiveLoweringDriver
                            (Proof.lowerPreparedProof prepared)
                            >>= either Declaration.failDeclarationDriver pure
                    _ <- Declaration.admitCheckedDeclaration
                        checked Proof.authorizeCheckedProof
                    pure ()
        prefix <- case result of
            Declaration.DriverSucceeded () _ finalPrefix ->
                pure finalPrefix
            Declaration.DriverFailed failure _ ->
                assertFailure
                    ("synthetic structure residualization failed: "
                        <> show failure)
                    >> fail "unreachable"
            Declaration.DriverSealFailed failure _ ->
                assertFailure
                    ("synthetic structure residualization did not seal: "
                        <> show failure)
                    >> fail "unreachable"
        let allFacts =
                concatMap
                    (Semantic.declarationDeltaFacts
                        . Commit.committedBatchDelta)
                    (Commit.pendingModulePrefixBatches prefix)
            originalFacts =
                concatMap
                    (Semantic.declarationDeltaFacts
                        . Commit.committedBatchDelta)
                    (Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix originalSealed))
            factFor facts fingerprint =
                sole "synthetic fact occurrence"
                    [ fact
                    | fact <- facts
                    , Semantic.semanticFactFingerprint fact == fingerprint
                    ]
        cleanFingerprint <- factFingerprintByAlias
            (Module.completedTypedModulePrefix originalSealed)
            "matrix_diamond"
        sourceFingerprint <- factFingerprintByAlias
            prefix "matrix_diamond_source_axiom"
        cleanFact <- factFor originalFacts cleanFingerprint
        sourceFact <- factFor allFacts sourceFingerprint
        sourceProposition <- sole "source duplicate proposition"
            [ Identity.checkedPropositionTerm proposition
            | batch <- Commit.pendingModulePrefixBatches prefix
            , proposition <- Commit.committedBatchPropositions batch
            , Identity.checkedPropositionId proposition
                == Semantic.semanticFactProposition sourceFact
            ]
        assertBool
            "the clean and source-axiom candidates have distinct occurrences"
            (cleanFingerprint /= sourceFingerprint)
        assertEqual
            "the source axiom has the generated structure target"
            definitionTarget sourceProposition
        assertEqual "the generated definition remains searchable"
            Semantic.SearchEligible
            (Semantic.semanticFactSearchEligibility cleanFact)
        assertEqual "the source duplicate is searchable"
            Semantic.SearchEligible
            (Semantic.semanticFactSearchEligibility sourceFact)
        assertEqual "the source duplicate is a source axiom"
            [Authority.SourceAxiom]
            (Authority.escapeKindsToList
                (Authority.authoritySafetyEscapeKinds
                    (Authority.factAuthoritySafety
                        (Semantic.semanticFactAuthority sourceFact))))
        problems <- readIORef observedProblems
        assertEqual "canonical introduction is independent of the selected source copy"
            3 (length problems)
        uncitedViews <- traverse (factFingerprintByAlias (Module.completedTypedModulePrefix originalSealed))
            ["matrix_diamondinherit_matrix_left", "matrix_diamondinherit_matrix_right"]
        assertBool "an equal-target source axiom does not expose checked structure views"
            (all (\(_, facts, _) -> all (`notElem` facts) uncitedViews) problems)
        assertBool
            "the original task retains only the cited source occurrence"
            (all
                (\(_claim, facts, route) ->
                    sourceFingerprint `elem` facts
                    && cleanFingerprint `notElem` facts
                    && route == Backend.RouteFof)
                problems)
        theoremBatch <- batchByAlias prefix
            "matrix_family_source_axiom_regression"
        theoremFact <- sole "source-dependent structure theorem fact"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta theoremBatch))
        assertEqual "source-dependent structure theorem safety"
            [Authority.SourceAxiom]
            (Authority.escapeKindsToList
                (Authority.authoritySafetyEscapeKinds
                    (Authority.factAuthoritySafety
                        (Semantic.semanticFactAuthority theoremFact))))
        record <- sole "source-dependent structure theorem validation"
            (Commit.committedBatchProofValidations theoremBatch)
        case Authority.validationDirectAuthorization
                (Semantic.proofValidationRecordCertificate record) of
            Authority.CheckedSourceProof requests ->
                assertEqual "component authorization covers the executed residuals"
                    (length problems)
                    (length (Authority.externalProofUseRequests requests))
            direct ->
                assertFailure
                    ("unexpected structure authorization: "
                        <> show direct)

rejectsIncompatibleStructureDiamond :: Assertion
rejectsIncompatibleStructureDiamond =
    withStructureCompileFailure
        "test/phase5/exact-structure-incompatible-diamond.tex"
        \failure prefix ->
            case failure of
                Elaboration.ElaborationStructureFieldConflict
                        _location
                        (Raw.StructSymbol "incompatiblePoint")
                        first
                        second -> do
                    assertEqual "conflict retains the first parent origin"
                        (Raw.Marker "incompatible_left")
                        (Schema.structurePhraseMarker first)
                    assertEqual "conflict retains the second parent origin"
                        (Raw.Marker "incompatible_right")
                        (Schema.structurePhraseMarker second)
                    assertEqual "the incompatible child publishes no batch"
                        2
                        (length (Commit.pendingModulePrefixBatches prefix))
                other ->
                    assertFailure
                        ("unexpected incompatible-diamond failure: "
                            <> show other)

rejectsInheritedStructureFieldOverride :: Assertion
rejectsInheritedStructureFieldOverride =
    withStructureCompileFailure
        "test/phase5/exact-structure-field-override.tex"
        \failure prefix ->
            case failure of
                Elaboration.ElaborationStructureFieldAlreadyInherited
                        _location
                        (Raw.StructSymbol "overridePoint") ->
                    assertEqual "the overriding child publishes no batch"
                        1
                        (length (Commit.pendingModulePrefixBatches prefix))
                other ->
                    assertFailure
                        ("unexpected inherited-field override failure: "
                            <> show other)

rejectsMismatchedStructureParameterPreamble :: Assertion
rejectsMismatchedStructureParameterPreamble =
    withStructureCompileFailure
        "test/phase8/parameterized-structure-preamble-mismatch.tex"
        \failure prefix ->
            case failure of
                Elaboration.ElaborationStructureParameterPreambleMismatch{} -> do
                    assertEqual "mismatch is reported at the structure declaration"
                        1
                        (locLine (Elaboration.elaborationErrorLocation failure))
                    assertBool "mismatch publishes no partial declaration"
                        (null (Commit.pendingModulePrefixBatches prefix))
                    assertBool "diagnostic distinguishes head and preamble parameters"
                        ("preamble introduces"
                            `StrictText.isInfixOf`
                                Elaboration.renderElaborationError failure)
                _ ->
                    assertFailure
                        ("unexpected parameter mismatch failure: "
                            <> show failure)

rejectsForwardStructureParameterDependency :: Assertion
rejectsForwardStructureParameterDependency =
    withStructureCompileFailure
        "test/phase8/parameterized-structure-forward-reference.tex"
        \failure prefix ->
            case failure of
                Elaboration.ElaborationStructureParameterDependencyViolation{} -> do
                    assertEqual "forward dependency is reported at its premise"
                        2
                        (locLine (Elaboration.elaborationErrorLocation failure))
                    assertBool "forward dependency publishes no declaration"
                        (null (Commit.pendingModulePrefixBatches prefix))
                    assertBool "diagnostic explains the ordered telescope"
                        ("already introduced parameters"
                            `StrictText.isInfixOf`
                                Elaboration.renderElaborationError failure)
                _ ->
                    assertFailure
                        ("unexpected parameter dependency failure: "
                            <> show failure)

rejectsForwardStructureFieldDependency :: Assertion
rejectsForwardStructureFieldDependency =
    withStructureCompileFailure
        "test/phase8/typed-structure-field-forward-reference.tex"
        \failure prefix ->
            case failure of
                Elaboration.ElaborationStructureFieldNotAvailable
                        _location (Raw.StructSymbol "fieldLater") -> do
                    assertEqual "forward field reference is located at its use"
                        4
                        (locLine (Elaboration.elaborationErrorLocation failure))
                    assertBool "forward field dependency publishes no declaration"
                        (null (Commit.pendingModulePrefixBatches prefix))
                    assertBool "diagnostic names the unavailable field"
                        ("fieldLater"
                            `StrictText.isInfixOf`
                                Elaboration.renderElaborationError failure)
                _ ->
                    assertFailure
                        ("unexpected field dependency failure: "
                            <> show failure)

withStructureCompileFailure
    :: FilePath
    -> (Elaboration.ElaborationError -> Commit.PendingModulePrefix -> IO ())
    -> IO ()
withStructureCompileFailure relative checkFailure = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory
            "felix-parameterized-structure-failure" \directory -> do
        let storePath = directory Posix.</> "store.sqlite"
            executable = directory Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        let resolver =
                Declaration.vampireResolver
                    (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit))
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts repository
            workspace <- parseFinalWorkspace prelude mounts relative
            let parsed = Parsed.parsedWorkspaceRootModule workspace
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.finalPreludeReadiness prelude)
                    resolver
                    AlwaysMissValidation
                    parsed
                    [])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed
                            (Module.TypedElaborationFailed failure))
                        prefix ->
                    checkFailure failure prefix
                Module.TypedModuleSucceeded{} ->
                    assertFailure
                        (relative <> " was unexpectedly accepted")
                Module.TypedModuleOpenFailed failure ->
                    assertFailure
                        (relative <> " did not open: " <> show failure)
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        (relative <> " failed unexpectedly: " <> show failure)

compilesContextualAbbreviations :: Assertion
compilesContextualAbbreviations = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    Temp.withSystemTempDirectory "felix-contextual-abbreviation" \directory -> do
        let storePath = directory Posix.</> "store.sqlite"
            executable = directory Posix.</> "vampire"
            relative = "test/phase5/exact-contextual-abbreviation.tex"
        writeAcceptedFixtureVampire executable
        runs <- newIORef (0 :: Int)
        let resolver = countingAcceptedResolver executable runs
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts repository
            workspace <- parseFinalWorkspace prelude mounts relative
            sealed <- sole "contextual abbreviation module"
                =<< compileFinalParsedWorkspaceWithResolver
                    foundation prelude resolver workspace
            let deltas =
                    Semantic.semanticInterfaceDeclarations
                        (completedModuleSemantic sealed)
                contextualTargets =
                    [ (identity, requirements)
                    | delta <- deltas
                    , binding <- Semantic.semanticEnvironmentBindings
                        (Semantic.declarationDeltaEnvironment delta)
                    , Semantic.ContextualTransparentExpansion
                            identity requirements <-
                        [Semantic.semanticGlobalBindingTarget binding]
                    ]
            assertEqual "contextual target count" 2
                (length contextualTargets)
            requirements <-
                sole "canonical contextual requirement set"
                    (nubOrd (snd <$> contextualTargets))
            assertEqual "one structure operation requirement" 1
                (Map.size requirements)
            let batches =
                    Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix sealed)
            traverse_
                (assertReflexiveFact batches)
                [ "phase5_context_dot_explicit"
                , "phase5_context_indexed_dot_explicit"
                , "phase5_context_indexed_plus_explicit"
                , "phase5_context_indexed_zero_explicit"
                , "phase5_context_indexed_negation_explicit"
                , "phase5_context_inherited"
                , "phase5_context_nested"
                , "phase5_context_explicit_unique"
                ]

            parsed <- pure (Parsed.parsedWorkspaceRootModule workspace)
            let syntax = completedModuleSyntax sealed
                semantic = completedModuleSemantic sealed
            key <- expectRight
                (Semantic.moduleArtefactKey
                    (moduleName (Parsed.parsedModuleAddress parsed))
                    (Parsed.parsedModuleId parsed)
                    (Semantic.semanticInterfaceDirectInputs semantic)
                    (Identity.theoryId foundation))
            storeCheck <- Store.newStoreCheck opened
            expectRight =<< Store.writeSealedModule storeCheck key
                (Module.completedTypedModulePrefix sealed) syntax semantic
            loaded <- expectRight
                =<< Store.loadCachedModuleCandidate
                    storeCheck key
                    (Syntax.moduleSyntaxAssertedId
                        (Parsed.parsedModuleSyntaxInterface parsed))
            installation <- maybe
                (assertFailure "contextual cached installation is absent"
                    >> fail "unreachable")
                pure
                loaded
            checkedImports <- prepareTestImports (Identity.theoryId foundation)
                [Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude)]
            cached <- expectRightIO
                (Module.cachedSealedTypedModule checkedImports installation)
            assertEqual "cached contextual semantic target"
                semantic
                (Module.sealedTypedModuleSemantic cached)

            runsBeforeConsumer <- readIORef runs
            consumerWorkspace <-
                parseFinalWorkspace prelude mounts
                    "test/phase5/exact-contextual-abbreviation-consumer.tex"
            let consumerParsed =
                    Parsed.parsedWorkspaceRootModule consumerWorkspace
            consumerInput <- expectRightIO
                (typedSealedModuleInput
                    foundation
                    (Module.finalPreludeReadiness prelude)
                    resolver
                    AlwaysMissValidation
                    consumerParsed
                    [cached])
            consumer <- runTypedModule consumerInput >>= \case
                Module.TypedModuleSucceeded sealedConsumer ->
                    pure sealedConsumer
                Module.TypedModuleOpenFailed failure ->
                    assertFailure
                        ("contextual consumer did not open: " <> show failure)
                        >> fail "unreachable"
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        ("contextual consumer did not seal: " <> show failure)
                        >> fail "unreachable"
            let consumerTargets =
                    [ Semantic.semanticGlobalTargetObject
                        (Semantic.semanticGlobalBindingTarget binding)
                    | delta <- localSemanticDeltas consumer
                    , binding <- Semantic.semanticEnvironmentBindings
                        (Semantic.declarationDeltaEnvironment delta)
                    ]
            assertEqual "two contextual consumer declarations" 2
                (length consumerTargets)
            void
                (sole
                    "quantified contextual binder matches its explicit parameter"
                    (nubOrd consumerTargets))

            groupedWorkspace <-
                parseFinalWorkspace prelude mounts
                    "test/phase5/grouped-structure-assumption.tex"
            let groupedParsed =
                    Parsed.parsedWorkspaceRootModule groupedWorkspace
            groupedInput <- expectRightIO
                (typedSealedModuleInput
                    foundation
                    (Module.finalPreludeReadiness prelude)
                    resolver
                    AlwaysMissValidation
                    groupedParsed
                    [cached])
            grouped <- runTypedModule groupedInput >>= \case
                Module.TypedModuleSucceeded sealedGrouped ->
                    pure sealedGrouped
                Module.TypedModuleOpenFailed failure ->
                    assertFailure
                        ("grouped structure consumer did not open: "
                            <> show failure)
                        >> fail "unreachable"
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        ("grouped structure consumer did not seal: "
                            <> show failure)
                        >> fail "unreachable"
            void
                (checkedPropositionTermByAlias
                    grouped "phase5_grouped_structure_assumption")
            assertGroupedClaimEnvelope
                foundation prelude resolver sealed groupedParsed

            filteredWorkspace <-
                parseFinalWorkspace prelude mounts
                    "test/phase5/structure-receiver-filtered.tex"
            let filteredParsed =
                    Parsed.parsedWorkspaceRootModule filteredWorkspace
            filteredInput <- expectRightIO
                (typedSealedModuleInput
                    foundation
                    (Module.finalPreludeReadiness prelude)
                    resolver
                    AlwaysMissValidation
                    filteredParsed
                    [cached])
            filtered <- runTypedModule filteredInput >>= \case
                Module.TypedModuleSucceeded sealedFiltered ->
                    pure sealedFiltered
                Module.TypedModuleOpenFailed failure ->
                    assertFailure
                        ("filtered structure consumer did not open: "
                            <> show failure)
                        >> fail "unreachable"
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        ("filtered structure consumer did not seal: "
                            <> show failure)
                        >> fail "unreachable"
            void
                (checkedPropositionTermByAlias
                    filtered "phase5_structure_receiver_filtered")

            runsAfterConsumer <- readIORef runs
            assertEqual "contextual abbreviations require no prover call"
                runsBeforeConsumer runsAfterConsumer

            verifyFailure foundation resolver prelude mounts sealed
                "test/phase5/exact-contextual-abbreviation-missing.tex"
                (\case
                    Elaboration.ElaborationContextualExpansionNotAvailable location _key ->
                        assertEqual "missing context line" 5 (locLine location)
                    failure ->
                        assertFailure
                            ("unexpected missing-context failure: "
                                <> show failure))
            verifyFailure foundation resolver prelude mounts sealed
                "test/phase5/exact-contextual-abbreviation-ambiguous.tex"
                (\case
                    Elaboration.ElaborationStructureFieldAmbiguous
                            location _symbol objects -> do
                        assertEqual "ambiguous operation line" 16
                            (locLine location)
                        assertEqual "two distinct operation objects" 2
                            (length objects)
                    failure ->
                        assertFailure
                            ("unexpected operation ambiguity failure: "
                                <> show failure))
            verifyFailure foundation resolver prelude mounts sealed
                "test/phase5/structure-receiver-ambiguous.tex"
                (\case
                    Elaboration.ElaborationStructureReceiverAmbiguous
                            location
                            (Raw.StructSymbol "phasefivecombine")
                            receivers -> do
                        assertEqual "ambiguous receiver line" 7
                            (locLine location)
                        assertEqual "both active receivers are reported"
                            ["B", "A"]
                            (toList receivers)
                    failure ->
                        assertFailure
                            ("unexpected receiver ambiguity failure: "
                                <> show failure))
            verifyFailure foundation resolver prelude mounts sealed
                "test/phase5/contextual-receiver-ambiguous.tex"
                (\case
                    Elaboration.ElaborationContextualReceiverAmbiguous
                            location _key receivers -> do
                        assertEqual "contextual receiver line" 7
                            (locLine location)
                        assertEqual "both contextual receivers are reported"
                            ["B", "A"]
                            (toList receivers)
                    failure ->
                        assertFailure
                            ("unexpected contextual receiver ambiguity failure: "
                                <> show failure))
            verifyFailure foundation resolver prelude mounts sealed
                "test/phase5/grouped-structure-receiver-ambiguous.tex"
                (\case
                    Elaboration.ElaborationStructureReceiverAmbiguous
                            location
                            (Raw.StructSymbol "phasefivecombine")
                            receivers -> do
                        assertEqual "grouped ambiguous receiver line" 6
                            (locLine location)
                        assertEqual "both grouped receivers are reported"
                            ["B", "A"]
                            (toList receivers)
                    failure ->
                        assertFailure
                            ("unexpected grouped receiver failure: "
                                <> show failure))
            verifyFailure foundation resolver prelude mounts sealed
                "test/phase5/grouped-structure-duplicate.tex"
                (\case
                    Elaboration.ElaborationDuplicateStructureAnnotation
                            location (Raw.NamedVar "A") ->
                        assertEqual "grouped duplicate variable line" 4
                            (locLine location)
                    failure ->
                        assertFailure
                            ("unexpected grouped duplicate failure: "
                                <> show failure))
  where
    assertGroupedClaimEnvelope foundation prelude resolver imported parsed = do
        Raw.Claim assumptions conclusion <-
            sole "grouped structure source claim"
                [ claim
                | Raw.BlockClaim _kind _location _title marker claim <-
                    Parsed.parsedModuleBlocks parsed
                , marker == "phase5_grouped_structure_assumption"
                ]
        (variables, application, trailingAssumptions) <-
            case assumptions of
                Raw.AsmLetStruct variables'
                        (Raw.StructNounPhrase
                            _modifiers application' _right _residual)
                        : remaining ->
                    pure (variables', application', remaining)
                _ ->
                    assertFailure
                        "grouped fixture does not start with a structure assumption"
                        >> fail "unreachable"
        let plainPhrase = Raw.StructNounPhrase [] application [] Nothing
            groupedAssumptions =
                Raw.AsmLetStruct variables plainPhrase
                    : trailingAssumptions
            repeatedAssumptions =
                [ Raw.AsmLetStruct (pure variable) plainPhrase
                | variable <- toList variables
                ] <> trailingAssumptions
            action
                :: Declaration.ModuleDriver Text
                    ( Either
                        Elaboration.ElaborationError
                        Elaboration.ElaboratedClaimEnvelope
                    , Either
                        Elaboration.ElaborationError
                        Elaboration.ElaboratedClaimEnvelope
                    )
            action = do
                Declaration.runProspectiveLoweringDriver do
                    grouped <- Elaboration.elaborateClaimEnvelope
                        groupedAssumptions conclusion
                    repeated <- Elaboration.elaborateClaimEnvelope
                        repeatedAssumptions conclusion
                    pure (grouped, repeated)
        checkedImports <- prepareTestImports (Identity.theoryId foundation)
            [Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude), completedModuleEvidence imported]
        result <- expectRight
            =<< Declaration.runModuleDriverFreshIO
                foundation
                (moduleName (Parsed.parsedModuleAddress parsed))
                checkedImports
                resolver
                action
        case result of
            Declaration.DriverSucceeded
                    (Right grouped, Right repeated)
                    _interface _prefix -> do
                assertEqual
                    "grouped and repeated structure headers have one target"
                    (Elaboration.elaboratedClaimTarget repeated)
                    (Elaboration.elaboratedClaimTarget grouped)
                let groupedHeaders =
                        Elaboration.elaboratedClaimAntecedents grouped
                    repeatedHeaders =
                        Elaboration.elaboratedClaimAntecedents repeated
                assertEqual "one grouped antecedent per subject"
                    2 (length groupedHeaders)
                assertEqual "grouped subjects share the source ordinal"
                    [0, 0]
                    (Elaboration.compiledHeaderSourceOrdinal
                        <$> groupedHeaders)
                assertEqual "grouped subjects retain variable ordinals"
                    [Just 0, Just 1]
                    (Elaboration.compiledHeaderVariableOrdinal
                        <$> groupedHeaders)
                assertEqual "repeated headers retain separate source ordinals"
                    [0, 1]
                    (Elaboration.compiledHeaderSourceOrdinal
                        <$> repeatedHeaders)
                assertEqual "each subject has one structure assertion bundle"
                    [1, 1]
                    (length . Elaboration.compiledHeaderAssertions
                        <$> groupedHeaders)
                assertEqual "grouped and repeated antecedent cores agree"
                    (Elaboration.compiledHeaderCore <$> repeatedHeaders)
                    (Elaboration.compiledHeaderCore <$> groupedHeaders)
                assertEqual "grouped and repeated source assertions agree"
                    (fmap assertionShape
                        . Elaboration.compiledHeaderAssertions
                        <$> repeatedHeaders)
                    (fmap assertionShape
                        . Elaboration.compiledHeaderAssertions
                        <$> groupedHeaders)
            Declaration.DriverSucceeded outcomes _interface _prefix ->
                assertFailure
                    ("grouped claim-envelope elaboration failed: "
                        <> case outcomes of
                            (Left failure, _) ->
                                StrictText.unpack
                                    (Elaboration.renderElaborationError failure)
                            (_, Left failure) ->
                                StrictText.unpack
                                    (Elaboration.renderElaborationError failure))
            Declaration.DriverFailed failure _prefix ->
                assertFailure
                    ("grouped claim-envelope driver failed: " <> show failure)
            Declaration.DriverSealFailed failure _prefix ->
                assertFailure
                    ("grouped claim-envelope driver did not seal: "
                        <> show failure)
      where
        assertionShape assertion =
            ( Notion.sourceAssertionHead assertion
            , Notion.sourceAssertionFormula assertion
            , Notion.sourceAssertionPath assertion
            )

    assertReflexiveFact batches marker = do
        batch <- maybe
            (assertFailure ("missing contextual fact " <> marker)
                >> fail "unreachable")
            pure
            (find
                (elem (Semantic.semanticName (StrictText.pack marker))
                    . fmap Semantic.semanticAliasName
                    . Semantic.declarationDeltaAliases
                    . Commit.committedBatchDelta)
                batches)
        proposition <- sole (marker <> " proposition")
            (Commit.committedBatchPropositions batch)
        let body = stripClaimEnvelope
                (Core.frozenCoreTerm
                    (Identity.checkedPropositionTerm proposition))
        case body of
            Core.CEq _ left right ->
                assertEqual (marker <> " canonical sides") left right
            _ ->
                assertFailure
                    (marker <> " did not elaborate to reflexive equality: "
                        <> show body)

    stripClaimEnvelope = \case
        Core.CForall _ body -> stripClaimEnvelope body
        Core.CImp _ body -> stripClaimEnvelope body
        term -> term

    verifyFailure foundation resolver prelude mounts imported relative checkFailure = do
        workspace <- parseFinalWorkspace prelude mounts relative
        let parsed = Parsed.parsedWorkspaceRootModule workspace
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.finalPreludeReadiness prelude)
                resolver
                AlwaysMissValidation
                parsed
                [imported])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed failure))
                    _prefix ->
                checkFailure failure
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofElaborationFailed failure)))
                    _prefix ->
                checkFailure failure
            Module.TypedModuleSucceeded{} ->
                assertFailure (relative <> " was unexpectedly accepted")
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    (relative <> " did not open: " <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    (relative <> " failed unexpectedly: " <> show failure)

rejectsUnknownStructureParent :: Assertion
rejectsUnknownStructureParent =
    Temp.withSystemTempDirectory "felix-exact-structure-parent" \root -> do
        let relative = "entry.tex"
            path = root Posix.</> relative
            source =
                "\\begin{struct}\\label{known_structure}\n"
                    <> "    A known structure $X$ is a onesorted structure.\n"
                    <> "\\end{struct}\n\n"
                    <> "\\begin{struct}\\label{invalid_structure}\n"
                    <> "    An invalid structure $X$ is a future structure.\n"
                    <> "\\end{struct}\n\n"
                    <> "\\begin{struct}\\label{future_structure}\n"
                    <> "    A future structure $X$ is a onesorted structure.\n"
                    <> "\\end{struct}\n"
        ByteString.writeFile path
            (Text.encodeUtf8 (StrictText.pack source))
        foundation <- expectRight Foundation.checkedFoundation
        Temp.withSystemTempDirectory "felix-exact-structure-store" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
                executable = directory Posix.</> "vampire"
            writeAcceptedFixtureVampire executable
            runs <- newIORef (0 :: Int)
            let resolver = countingAcceptedResolver executable runs
            (_startup, store) <-
                Store.openStore storePath (Identity.theoryId foundation)
                    >>= expectRight
            bracket (pure store) Store.closeStore \opened -> do
                prelude <-
                    expectRight
                        =<< acquireFinalPreludeSession
                            opened foundation resolver
                mounts <- exactFixtureMounts root
                workspace <- parseFinalWorkspace prelude mounts relative
                let parsed = Parsed.parsedWorkspaceRootModule workspace
                input <- expectRightIO
                    (typedModuleInput
                        foundation
                        (Module.finalPreludeReadiness prelude)
                        resolver
                        AlwaysMissValidation
                        parsed
                        [])
                runTypedModule input >>= \case
                    Module.TypedModuleFailed
                            (Module.TypedActionFailed
                                (Module.TypedElaborationFailed
                                    (Elaboration.ElaborationStructureNotVisible
                                        location _phrase)))
                            prefix -> do
                        assertEqual "unknown parent line" 5 (locLine location)
                        assertEqual "only the valid structure was published"
                            1
                            (length
                                (Commit.pendingModulePrefixBatches prefix))
                    Module.TypedModuleSucceeded{} ->
                        assertFailure "unknown structure parent was accepted"
                    Module.TypedModuleOpenFailed failure ->
                        assertFailure
                            ("invalid structure module did not open: "
                                <> show failure)
                    Module.TypedModuleFailed failure _prefix ->
                        assertFailure
                            ("unexpected invalid structure failure: "
                                <> show failure)

compilesRelationExpressions :: Assertion
compilesRelationExpressions = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation unusedResolver
    repository <- getCurrentDirectory
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase5/exact-relation-expression.tex"
    observed <- newIORef []
    withAcceptedFixtureVampire "felix-exact-relation-expression" \prover -> do
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    claim = Backend.typedProblemClaim problem
                    locals = Backend.typedProblemLocalPremises problem
                modifyIORef' observed
                    (<> [ [ Backend.supportedPropositionTerm
                                (Backend.typedLocalPremiseProposition premise)
                            == Backend.supportedPropositionTerm claim
                           | premise <- Vector.toList locals
                           ]
                        ])
                (Provers.runPreparedTypedProver prover prepared)
        void
            (compileParsedWorkspaceWithResolver
                foundation bootstrap resolver workspace)
    assertEqual
        "identical relation syntax closes by structural hypothesis reuse"
        []
        =<< readIORef observed

    fixedPair <-
        withAcceptedFixtureVampire "felix-exact-relation-expression-missing-pair" \prover ->
                (checkFileFresh
                    prover
                    "test/phase5/exact-relation-expression-missing-pair.tex")
    case fixedPair of
        Right (outcome, _slowReport) ->
            assertTypedSuccess
                "relation expression with the fixed ordered-pair primitive"
                outcome
        Left err ->
            assertFailure
                ("unexpected relation-expression failure: " <> show err)

resolvesSourceOwnedApplication :: Assertion
resolvesSourceOwnedApplication = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    withAcceptedFixtureVampire "felix-exact-application" \prover ->
        Temp.withSystemTempDirectory "felix-exact-application" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
                resolver = Declaration.vampireResolver
                    (Provers.runPreparedTypedProver prover)
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                \store -> do
                    prelude <-
                        expectRight
                            =<< acquireFinalPreludeSession
                                store foundation resolver
                    mounts <- exactFixtureMounts repository
                    workspace <- parseFinalWorkspace
                        prelude mounts "test/phase5/exact-application.tex"
                    sealed <- compileFinalParsedWorkspaceWithResolver
                        foundation prelude resolver workspace
                    root <- case reverse sealed of
                        rootModule : _ -> pure rootModule
                        [] ->
                            assertFailure "application fixture root is absent"
                                >> fail "unreachable"
                    assertTransparentObjectAlias root "phase5_apply"
                    let applyKey = Semantic.SemanticExpressionFunction
                            (Raw.mixfixPattern Raw.ApplySymbol)
                    applyObject <- localObjectKeyTarget root applyKey
                    surface <- checkedPropositionTermByAlias
                        root "phase5_application_surface"
                    explicit <- checkedPropositionTermByAlias
                        root "phase5_application_explicit"
                    assertEqual
                        "surface and explicit application lower identically"
                        explicit
                        surface
                    assertBool
                        "surface application resolves through the declared object"
                        (applyObject `Set.member` Core.frozenCoreGlobals surface)

    missing <-
        withAcceptedFixtureVampire "felix-exact-application-missing"
            \prover ->
                    (checkFileFresh
                        prover
                        "test/phase5/exact-application-missing.tex")
    case missing of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                _source
                (Module.TypedActionFailed
                    (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed
                            (Elaboration.ElaborationGlobalNotVisible location key))))
                prefix)
            , _slowReport
            ) -> do
            assertEqual "unresolved application line" 2 (locLine location)
            assertEqual "unresolved application key"
                (Semantic.SemanticExpressionFunction
                    (Raw.mixfixPattern Raw.ApplySymbol))
                key
            assertEqual "unresolved application publishes no declaration"
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Left failure ->
            assertFailure
                ("unexpected unresolved application failure: " <> show failure)
        Right{} ->
            assertFailure "application without its source binding was admitted"

confinesQuantifiedTerms :: Assertion
confinesQuantifiedTerms = do
    foundation <- expectRight Foundation.checkedFoundation
    repository <- getCurrentDirectory
    withAcceptedFixtureVampire "felix-exact-quantified-subject" \prover ->
        Temp.withSystemTempDirectory "felix-quantified-subject" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
                resolver = Declaration.vampireResolver
                    (Provers.runPreparedTypedProver prover)
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                \store -> do
                    prelude <-
                        expectRight
                            =<< acquireFinalPreludeSession
                                store foundation resolver
                    mounts <- exactFixtureMounts repository
                    workspace <- parseFinalWorkspace
                        prelude mounts
                        "test/phase5/exact-quantified-subject.tex"
                    sealed <- compileFinalParsedWorkspaceWithResolver
                        foundation prelude resolver workspace
                    root <- case reverse sealed of
                        rootModule : _ -> pure rootModule
                        [] ->
                            assertFailure "quantified-subject root is absent"
                                >> fail "unreachable"
                    quantified <- checkedPropositionTermByAlias root
                        "phase5_quantified_subject"
                    explicit <- checkedPropositionTermByAlias root
                        "phase5_explicit_quantifier"
                    assertEqual
                        "quantified noun subject retains its domain constraint"
                        explicit
                        quantified

                    propositionWorkspace <- parseFinalWorkspace
                        prelude mounts
                        "test/phase5/exact-quantified-proposition-terms.tex"
                    observations <- newIORef []
                    let observingResolver =
                            Declaration.vampireResolver \prepared -> do
                                let problem =
                                        Provers.preparedTypedProverLogicalProblem
                                            prepared
                                    request =
                                        Provers.preparedTypedProverRequest
                                            prepared
                                modifyIORef' observations
                                    (<> [ ( Provers.preparedVerificationRequestId
                                                request
                                           , Backend.supportedPropositionTerm
                                                (Backend.typedProblemClaim problem)
                                           , Backend.typedProblemRoute problem
                                           , Backend.typedProblemAuxiliaryTag
                                                <$> Vector.toList
                                                    (Backend.typedProblemAuxiliaries
                                                        problem)
                                           )
                                        ])
                                (Provers.runPreparedTypedProver
                                        prover prepared)
                    freshModules <-
                        compileFinalParsedWorkspaceWithResolver
                            foundation prelude observingResolver
                            propositionWorkspace
                    freshRoot <- case reverse freshModules of
                        rootModule : _ -> pure rootModule
                        [] ->
                            assertFailure
                                "quantified proposition-term root is absent"
                                >> fail "unreachable"
                    let member left right =
                            Core.CApp
                                (Core.CApp
                                    (Core.CIntrinsic Core.Member) left)
                                right
                        memberAtX =
                            member (Core.CBound 0) (Core.CBound 1)
                        expectedFunctionTarget =
                            Core.CForall Core.TySet
                                (Core.CEq Core.TySet
                                    (Core.CBound 0)
                                    (Core.CBound 0))
                        expectedVerbProposition =
                            Core.CForall Core.TySet
                                (Core.CForall Core.TySet
                                    (Core.CImp memberAtX memberAtX))
                        expectedTargets = [expectedFunctionTarget]
                    freshObservations <- readIORef observations
                    assertEqual
                        "only the unsolved quantified target reaches FOF without unused auxiliaries"
                        [ ( target
                          , Backend.RouteFof
                          , []
                          )
                        | target <- expectedTargets
                        ]
                        [ (target, route, auxiliaries)
                        | (_request, target, route, auxiliaries) <-
                            freshObservations
                        ]
                    functionTarget <- checkedPropositionTermByAlias freshRoot
                        "phase5_quantified_function_argument"
                    verbTarget <- checkedPropositionTermByAlias freshRoot
                        "phase5_quantified_verb_argument"
                    assertEqual "nested function proposition core"
                        expectedFunctionTarget
                        (Core.frozenCoreTerm functionTarget)
                    assertEqual "nested verb proposition core"
                        expectedVerbProposition
                        (Core.frozenCoreTerm verbTarget)
                    let proofRecords moduleValue =
                            concatMap
                                Commit.committedBatchProofValidations
                                (Commit.pendingModulePrefixBatches
                                    (Module.completedTypedModulePrefix moduleValue))
                        proofAuthorizations moduleValue =
                            Authority.validationDirectAuthorization
                                . Semantic.proofValidationRecordCertificate
                                <$> proofRecords moduleValue
                    case proofAuthorizations freshRoot of
                        [ Authority.CheckedSourceProof
                            (Authority.UsesExternalProof
                                (_functionRequest :| []))
                          , Authority.CheckedSourceProof Authority.NoExternalProofUse
                          ] -> pure ()
                        authorizations ->
                            assertFailure
                                ("unexpected quantified-term authority: "
                                    <> show authorizations)
                    assertBool
                        "quantified terms add no escape-backed authority"
                        (all
                            ((== Authority.cleanAuthoritySafety)
                                . Authority.factAuthoritySafety
                                . Semantic.semanticFactAuthority)
                            (concatMap
                                (Semantic.declarationDeltaFacts
                                    . Commit.committedBatchDelta)
                                (Commit.pendingModulePrefixBatches
                                    (Module.completedTypedModulePrefix freshRoot))))

                    storeCheck <- Store.newStoreCheck store
                    traverse_
                        (expectRightIO
                            . Store.writePendingModulePrefix storeCheck
                            . Module.completedTypedModulePrefix)
                        freshModules
                    let validation = storeValidationPolicy storeCheck
                    warmModules <-
                        compileParsedWorkspaceWithReadiness
                            foundation
                            (Module.finalPreludeReadiness prelude)
                            unusedResolver
                            validation
                            propositionWorkspace
                    warmRoot <- case reverse warmModules of
                        rootModule : _ -> pure rootModule
                        [] ->
                            assertFailure
                                "warm quantified proposition-term root is absent"
                                >> fail "unreachable"
                    assertEqual "fresh and warm quantified semantic interface"
                        (completedModuleSemantic freshRoot)
                        (completedModuleSemantic warmRoot)
                    assertEqual "fresh and warm quantified request authority"
                        (proofAuthorizations freshRoot)
                        (proofAuthorizations warmRoot)
                    assertEqual "fresh and warm quantified prefix"
                        (Commit.pendingModulePrefixCurrent
                            (Module.completedTypedModulePrefix freshRoot))
                        (Commit.pendingModulePrefixCurrent
                            (Module.completedTypedModulePrefix warmRoot))

    negative <-
        withAcceptedFixtureVampire "felix-exact-quantified-term-valued"
            \prover ->
                    (checkFileFresh
                        prover
                        "test/phase5/exact-quantified-term-valued.tex")
    case negative of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                _source
                (Module.TypedActionFailed
                    (Module.TypedElaborationFailed
                        (Elaboration.ElaborationQuantifiedTermRequiresPropositionContext
                            location)))
                prefix)
            , _slowReport
            ) -> do
            assertEqual "term-valued quantified term line"
                2 (locLine location)
            assertBool "failed term-valued abbreviation publishes no prefix"
                (null (Commit.pendingModulePrefixBatches prefix))
        Left failure ->
            assertFailure
                ("unexpected term-valued quantified-term failure: "
                    <> show failure)
        Right{} ->
            assertFailure "term-valued quantified exact term was admitted"

closesDefinitionDeclarationBoundary :: Assertion
closesDefinitionDeclarationBoundary = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    repositoryMounts <- exactFixtureMounts repository
    Temp.withSystemTempDirectory "felix-definition-boundary" \directory -> do
        mounts <- exactFixtureMounts directory
        annotatedText <-
            readFile
                (repository Posix.</>
                    "test/phase5/exact-definition-boundary.tex")
        let relative = "entry.tex"
            sourcePath = directory Posix.</> relative
        writeFile sourcePath annotatedText
        annotatedWorkspace <-
            parseWorkspace bootstrap mounts relative
        annotated <- sole "annotated definition module"
            =<< compileParsedWorkspace
                foundation bootstrap annotatedWorkspace
        assertEqual "annotated definition declaration count"
            4
            (length
                (Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix annotated)))
        assertBool "annotated definitions prepare no Vampire validations"
            (null (proofValidationRecords annotated))
        let annotatedBatches =
                Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix annotated)
        symbolicBatch <- sole "symbolic primary declaration"
            (take 1 (drop 2 annotatedBatches))
        wrapperBatch <- sole "functional wrapper declaration"
            (take 1 (drop 3 annotatedBatches))
        symbolicObject <- bindingObject "symbolic primary" symbolicBatch
        wrapperObject <- bindingObject "functional wrapper" wrapperBatch
        wrapperContent <- sole "functional wrapper transparent object"
            [ Identity.assertedObjectContent object
            | batch <-
                Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix annotated)
            , object <- Commit.committedBatchObjects batch
            , Identity.assertedObjectId object == wrapperObject
            ]
        case wrapperContent of
            Identity.TransparentObjectContent _theory _type body ->
                assertEqual
                    "functional wrapper applies the primary symbolic object"
                    (Set.singleton symbolicObject)
                    (Core.canonicalTermGlobals body)
            content ->
                assertFailure
                    ("functional wrapper is not transparent: " <> show content)

        let storePath = directory Posix.</> "store.sqlite"
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix annotated))
                let validation = storeValidationPolicy storeCheck
                warm <- sole "warm annotated definition module"
                    =<< compileParsedWorkspaceWithValidation
                        foundation bootstrap unusedResolver validation
                        annotatedWorkspace
                assertEqual "warm annotated semantic interface"
                    (completedModuleSemantic annotated)
                    (completedModuleSemantic warm)
                assertEqual "warm annotated declaration identity"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix annotated))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))
                assertEqual "warm annotated direct authority"
                    (directDeclarationAuthorizations annotated)
                    (directDeclarationAuthorizations warm)
                assertBool "warm annotated definitions run no prover"
                    (null (proofValidationRecords warm))

        aliasFailure <- exactFailure foundation bootstrap repositoryMounts
            "test/phase5/exact-definition-alias-failure.tex"
        case aliasFailure of
            (Elaboration.ElaborationDefinitionCombinedSymbolicAlias location, prefix) -> do
                assertEqual "combined symbolic alias line" 2 (locLine location)
                assertBool "combined symbolic alias publishes no prefix"
                    (null (Commit.pendingModulePrefixBatches prefix))
                assertBool "combined alias diagnostic gives the wrapper migration"
                    ("define the symbolic operator first"
                        `StrictText.isInfixOf`
                            Elaboration.renderElaborationError (fst aliasFailure))
            (failure, _prefix) ->
                assertFailure
                    ("unexpected combined-alias failure: " <> show failure)

        guardFailure <- exactFailure foundation bootstrap repositoryMounts
            "test/phase5/exact-definition-guard-failure.tex"
        case guardFailure of
            (Elaboration.ElaborationGuardedTransparentDefinition location, prefix) -> do
                assertEqual "guarded definition line" 2 (locLine location)
                assertBool "guarded definition publishes no prefix"
                    (null (Commit.pendingModulePrefixBatches prefix))
                assertBool "guard diagnostic gives the total-definition migration"
                    ("use only noun, symbolic membership, or open structure assumptions"
                        `StrictText.isInfixOf`
                            Elaboration.renderElaborationError (fst guardFailure))
            (failure, _prefix) ->
                assertFailure
                    ("unexpected guarded-definition failure: " <> show failure)

  where
    proofValidationRecords moduleValue =
        concatMap
            Commit.committedBatchProofValidations
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix moduleValue))

    directDeclarationAuthorizations moduleValue =
        [ Authority.validationDirectAuthorization certificate
        | batch <-
            Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix moduleValue)
        , validation <-
            maybeToList
                (Commit.committedBatchDeclarationValidation batch)
        , certificate <-
            Semantic.declarationValidationRecordCertificates validation
        ]

    bindingObject label batch = do
        binding <- sole (label <> " semantic binding")
            (Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta batch)))
        pure
            (Semantic.semanticGlobalTargetObject
                (Semantic.semanticGlobalBindingTarget binding))

    exactFailure foundation bootstrap mounts relative = do
        workspace <- parseWorkspace bootstrap mounts relative
        parsed <- sole "failed exact definition module"
            (toList
                (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed failure))
                    prefix ->
                pure (failure, prefix)
            result ->
                assertFailure
                    (case result of
                        Module.TypedModuleSucceeded{} ->
                            "expected exact definition failure, but the module succeeded"
                        Module.TypedModuleOpenFailed{} ->
                            "expected exact definition failure, but the module did not open"
                        Module.TypedModuleFailed{} ->
                            "expected an exact compile failure, but checking failed differently")
                    >> fail "unreachable"

coalescesEquivalentCanonicalDefinitionViews :: Assertion
coalescesEquivalentCanonicalDefinitionViews = do
    (_foundation, _bootstrap, _workspace, sealedModules) <-
        compileFixture
            "test/phase5/exact-equivalent-definition-view-consumer.tex"
    assertEqual
        "equivalent-view producer and consumer both seal"
        2
        (length sealedModules)

reportsObviousBreadth :: Assertion
reportsObviousBreadth = do
    foundation <- expectRight Foundation.checkedFoundation
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    let globalTyping = Identity.globalTypingFromClosure closure
    relative <- expectRight (safeRelativePath "breadth-diagnostic.tex")
    let owner = moduleNameFromParts
            (sourceNamespaceIdFromDigest (hashBlake2b256 "breadth-diagnostic")) relative
        member x set = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) set
        atom n = member (Core.COpaqueInteger n) (Core.CIntrinsic Core.Empty)
        assumptions facts target = foldr Core.CImp target facts
        pointwise a b = Core.CForall Core.TySet
            (Core.CImp (member (Core.CBound 0) (Core.CBound a))
                (member (Core.CBound 0) (Core.CBound b)))
        schema guards = Core.CForall Core.TySet (Core.CForall Core.TySet
            (assumptions (guards <> [pointwise 2 1, pointwise 1 2])
                (Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 0))))
        deferrals =
            [ ("existing-witness search", foldr (const (Core.CForall Core.TySet))
                (assumptions [Core.CEq Core.TySet (Core.CBound n) (Core.CBound n) | n <- [0 .. 4]]
                    (Core.CExists Core.TySet (member (Core.CBound 0) (Core.CIntrinsic Core.Empty)))) [1 .. 5 :: Int])
            , ("theorem-premise queries", assumptions
                [Core.CImp (Core.COr (atom n) (atom (n + 1))) (atom 0) | n <- [1,3,5]] (atom 0))
            , ("generic universal instances", assumptions
                (Core.CForall Core.TySet (Core.CNot (member (Core.CBound 0) (Core.CIntrinsic Core.Empty)))
                    : [Core.CEq Core.TySet (Core.COpaqueInteger n) (Core.COpaqueInteger n) | n <- [1 .. 40]]) Core.CFalsum)
            , ("supplied-existential openings", assumptions
                [Core.CExists Core.TySet (member (Core.CBound 0) (Core.COpaqueInteger n)) | n <- [1 .. 3]] Core.CFalsum)
            , ("membership-extensionality applications", assumptions [schema [], schema [Core.CTruth]]
                (Core.CForall Core.TySet (Core.CForall Core.TySet
                    (Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 0)))))
            ]
        controls =
            [ ("universal hint effort:", ["generic universal instances: breadth deferral"],
                [Obvious.ObviousUniversalBreadth 32 30 False, Obvious.ObviousUniversalHintEffort 128 128], assumptions
                (Core.CForall Core.TySet (Core.CNot (atom 0))
                    : [Core.CEq Core.TySet (Core.COpaqueInteger n) (Core.COpaqueInteger n) | n <- [1 .. 3]]) (Core.COr Core.CFalsum Core.CFalsum))
            , ("focused tier:", ["breadth deferral"], [Obvious.ObviousWitnessBreadth 4 32 4 False], foldr (const (Core.CForall Core.TySet))
                (assumptions [Core.CEq Core.TySet (Core.CBound n) (Core.CBound n) | n <- [0 .. 2]]
                    (Core.CExists Core.TySet (member (Core.CBound 0) (Core.CIntrinsic Core.Empty)))) [1 .. 3 :: Int])
            ]
        claim = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "breadth_diagnostic")
            (Raw.Claim [] (Raw.StmtFormula (Raw.PropositionalConstant Nowhere Raw.IsTop)))
        proof = Raw.Qed Nothing Raw.JustificationImplicit
    for_ ([(label <> ": breadth deferral observed", [], [], goal) | (label, goal) <- deferrals] <> controls) $ \(label, absent, observations, goal) -> do
        target <- expectRight (Core.checkScopedCanonicalCore globalTyping [] goal)
        let run = Obvious.obviousProofReport Obvious.defaultObviousBudget Obvious.AnyObviousProof
                foundation globalTyping [] [] [] target
        for_ observations $ \observation -> assertBool (show (Obvious.obviousBreadthObservations (Obvious.obviousRunStatistics run)))
            (observation `elem` Obvious.obviousBreadthObservations (Obvious.obviousRunStatistics run))
        failure <- maybe (assertFailure (label <> " unexpectedly proved") >> fail "missing failure") pure
            (Obvious.obviousRunFailure run)
        let prepare :: Declaration.ModuleDriver Void (Either Proof.ProofError Proof.PreparedProof)
            prepare = Declaration.runProspectiveLoweringDriver
                (Proof.prepareProofWithObviousFailureFixture failure claim (Just proof))
        outcome <- expectRight =<< runModuleDriver foundation owner [] unusedResolver AlwaysMissValidation prepare
        case outcome of
            Declaration.DriverSucceeded (Left actual@Proof.ProofObviousInferenceReported{}) _ _ -> do
                diagnostic <- maybe (fail "missing normal diagnostic") pure (Proof.proofErrorDiagnostic actual)
                let notes = unlines (show <$> Diagnostic.diagnosticNotes diagnostic)
                assertBool (label <> ": " <> notes <> "\n" <> show (Obvious.obviousBreadthObservations (Obvious.obviousRunStatistics run)))
                    (label `List.isInfixOf` notes)
                for_ absent $ \unwanted -> assertBool ("unexpected deferral: " <> notes)
                    (not (unwanted `List.isInfixOf` notes))
                assertEqual "breadth observations preserve the source failure disposition"
                    Proof.ProofSourceRejection (Proof.proofErrorDisposition actual)
            Declaration.DriverSucceeded (Left failure') _ _ -> assertFailure (show failure')
            _ -> assertFailure "the failure-only preparation fixture did not report its request"

preparesPredicateEvidence :: Assertion
preparesPredicateEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts =<< getCurrentDirectory
    workspace <- parseWorkspace bootstrap mounts "test/phase5/prepared-predicate-evidence.tex"
    observed <- newIORef []
    let resolver = Declaration.vampireResolver \prepared -> do
            let problem = Provers.preparedTypedProverLogicalProblem prepared
            modifyIORef' observed (<> [(Backend.supportedPropositionTerm (Backend.typedProblemClaim problem),
                Backend.typedProblemRoute problem)])
            Provers.runPreparedTypedProver
                (Provers.vampire "vampire" (Provers.Seconds 20) Provers.defaultMemoryLimit) prepared
    sealed <- sole "predicate evidence module" =<< compileParsedWorkspaceWithResolver
        foundation bootstrap resolver workspace
    assertEqual "only the unsupported reflexivity clause reaches ATP"
        [(Core.CForall Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)), Backend.RouteFof)]
        =<< readIORef observed
    for_ ["prepared_evidence_closed", "prepared_evidence_transport", "prepared_evidence_transport_binder"] \alias -> do
        closed <- batchByAlias (Module.completedTypedModulePrefix sealed) alias
        certificate <- sole "predicate evidence certificate" (Commit.committedBatchValidationCertificates closed)
        assertEqual "canonical equations and supplied equalities give ordinary kernel proofs"
            (Authority.CheckedSourceProof Authority.NoExternalProofUse)
            (Authority.validationDirectAuthorization certificate)
    Temp.withSystemTempDirectory "felix-predicate-preparation-cache" \root -> do
        bracket (snd <$> (Store.openStore (root Posix.</> "store.sqlite")
            (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO (Store.writePendingModulePrefix storeCheck (Module.completedTypedModulePrefix sealed))
                warm <- sole "warm predicate evidence module" =<< compileParsedWorkspaceWithValidation
                    foundation bootstrap unusedResolver (storeValidationPolicy storeCheck) workspace
                assertEqual "exact definition dependencies survive warm validation"
                    (completedModuleSemantic sealed) (completedModuleSemantic warm)

preparesScopedLogicalResiduals :: Assertion
preparesScopedLogicalResiduals = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts =<< getCurrentDirectory
    workspace <- parseWorkspace bootstrap mounts "test/phase5/prepared-logical-scopes.tex"
    observed <- newIORef []
    let resolver = Declaration.vampireResolver \prepared -> do
            let problem = Provers.preparedTypedProverLogicalProblem prepared
                claim = Backend.typedProblemClaim problem
            modifyIORef' observed (<> [( Vector.length (Backend.supportedPropositionSupport claim)
                , Backend.supportedPropositionTerm claim
                , Backend.supportedPropositionTerm . Backend.typedLocalPremiseProposition
                    <$> Vector.toList (Backend.typedProblemLocalPremises problem)
                , Vector.length . Backend.supportedPropositionSupport . Backend.typedLocalPremiseProposition
                    <$> Vector.toList (Backend.typedProblemLocalPremises problem)
                , Backend.typedProblemRoute problem)])
            Provers.runPreparedTypedProver
                (Provers.vampire "vampire" (Provers.Seconds 20) Provers.defaultMemoryLimit) prepared
    sealed <- sole "scoped preparation module" =<< compileParsedWorkspaceWithResolver
        foundation bootstrap resolver workspace
    let eq = Core.CEq Core.TySet
        var = Core.CBound
    assertEqual "only scoped symmetry and transitivity remain for ATP"
        [ (2, eq (var 1) (var 0), [eq (var 0) (var 1)], [2], Backend.RouteFof)
        , (2, eq (var 1) (var 0), [Core.CAnd (eq (var 1) (var 2)) (eq (var 0) (var 1))],
            [3], Backend.RouteFof)
        ] =<< readIORef observed
    for_ ["prepared_logical_closed", "prepared_logical_supplied_clause"] \alias -> do
        closed <- batchByAlias (Module.completedTypedModulePrefix sealed) alias
        certificate <- sole "closed preparation certificate" (Commit.committedBatchValidationCertificates closed)
        assertEqual "closed local preparation needs no ATP"
            (Authority.CheckedSourceProof Authority.NoExternalProofUse)
            (Authority.validationDirectAuthorization certificate)
    Temp.withSystemTempDirectory "felix-scoped-preparation-cache" \root -> do
        bracket (snd <$> (Store.openStore (root Posix.</> "store.sqlite")
            (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO (Store.writePendingModulePrefix storeCheck (Module.completedTypedModulePrefix sealed))
                warm <- sole "warm scoped preparation module" =<< compileParsedWorkspaceWithValidation
                    foundation bootstrap unusedResolver (storeValidationPolicy storeCheck) workspace
                assertEqual "scoped preparation reuses its validated proof contract"
                    (completedModuleSemantic sealed) (completedModuleSemantic warm)

reportsPreparationExhaustion :: Assertion
reportsPreparationExhaustion = do
    foundation <- expectRight Foundation.checkedFoundation
    relative <- expectRight (safeRelativePath "preparation-exhaustion.tex")
    let owner = moduleNameFromParts
            (sourceNamespaceIdFromDigest (hashBlake2b256 "preparation-exhaustion")) relative
        claim = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "preparation_exhaustion")
            (Raw.Claim [] (Raw.StmtFormula (Raw.PropositionalConstant Nowhere Raw.IsTop)))
        proof = Raw.Qed Nothing (Raw.JustificationAuto Nothing)
        resolver = Declaration.vampireResolver (pure . counterexampleResolution)
        action :: Declaration.ModuleDriver String ()
        action = do
            prepared <- Declaration.runProspectiveLoweringDriver
                (Proof.prepareProofWithPreparationWork 0 claim (Just proof))
                >>= either (Declaration.failModuleDriver . show) pure
            liftIO (assertEqual "the actual preparation report is retained"
                [(Nowhere, Preparation.PreparationStatistics 0 0 (Just Preparation.PreparationWorkLimit))]
                (Proof.preparedProofPreparationStatistics prepared))
            lowered <- Declaration.runProspectiveLoweringDriver (Proof.lowerPreparedProof prepared)
                >>= either Declaration.failDeclarationDriver pure
            void (Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof)
    outcome <- expectRight =<< runModuleDriver foundation owner [] resolver AlwaysMissValidation action
    case outcome of
        Declaration.DriverFailed (Declaration.DriverDeclarationFailed failure) prefix -> do
            (location, resolution, statistics) <- maybe
                (fail ("lost located ATP failure: " <> show failure)) pure
                (Declaration.locatedVampireFailure failure)
            let failed = Verification.FailedVerification location resolution statistics []
                diagnostic = Verification.failedVerificationDiagnostic failed
                notes = unlines (show <$> Diagnostic.diagnosticNotes diagnostic)
            assertBool "the ATP result remains a logical rejection"
                (Verification.failedVerificationIsLogicalRejection failed)
            assertBool "normal diagnostic reports the exhausted work limit"
                ("automatic local-evidence preparation exhausted its work limit (0/0)"
                    `List.isInfixOf` notes)
            assertEqual "no failed proof is published" 0 (length (Commit.pendingModulePrefixBatches prefix))
        _ -> assertFailure "the exhausted preparation did not retain its failed ATP obligation"

preservesOptionalObviousFailure :: Assertion
preservesOptionalObviousFailure =
  Temp.withSystemTempDirectory "felix-obvious-failure" \root -> do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    withAcceptedFixtureVampire "felix-obvious-prelude" \baseProver -> do
      let baseResolver = Declaration.vampireResolver (Provers.runPreparedTypedProver baseProver)
      bracket
        (snd <$> (Store.openStore (root Posix.</> "store.sqlite")
            (Identity.theoryId foundation) >>= expectRight))
        Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation baseResolver)
            baseSource <- readFile (repository Posix.</> "test/phase5/exact-structure-core.tex")
            writeFile (root Posix.</> "base.tex") baseSource
            writeFile (root Posix.</> "consumer.tex") (unlines
                [ "\\import{base.tex}"
                , "\\begin{proposition}\\label{optional_obvious}"
                , "Let $X$ be a record-core pointed set. Let $Y$ be a set. Assume $X=Y$ or $Y=X$. Then $Y$ is a record-core pointed set."
                , "\\end{proposition}"
                , "\\begin{proof} Follows by \\auto{record_core_refl}. \\end{proof}"
                , "\\begin{proposition}\\label{required_obvious}"
                , "Let $X$ be a record-core pointed set. Let $Y$ be a set. Assume $X=Y$ or $Y=X$. Then $Y$ is a record-core pointed set."
                , "\\end{proposition}"
                , "\\begin{proof} Follows by \\obv{record_core_refl}. \\end{proof}"
                , "\\begin{proposition}\\label{implicit_obvious}"
                , "Let $X$ be a record-core pointed set. Let $Y$ be a set. Assume $X=Y$ or $Y=X$. Then $Y$ is a record-core pointed set."
                , "\\end{proposition}"
                , "\\begin{proof} Follows. \\end{proof}"
                , "\\begin{proposition}\\label{definition_obvious}"
                , "Let $X$ be a record-core pointed set. Let $Y$ be a set. Assume $X=Y$ or $Y=X$. Then $Y$ is a record-core pointed set."
                , "\\end{proposition}"
                , "\\begin{proof} Follows by definition. \\end{proof}"
                ])
            mounts <- exactFixtureMounts root
            baseWorkspace <- parseFinalWorkspace prelude mounts "base.tex"
            base <- sole "Obvious failure base"
                =<< compileFinalParsedWorkspaceWithResolver foundation prelude baseResolver baseWorkspace
            workspace <- parseFinalWorkspace prelude mounts "consumer.tex"
            consumer <- sole "Obvious failure consumer"
                [ parsed
                | parsed <- toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
                , moduleName (Parsed.parsedModuleAddress parsed) /= completedModuleOwner base
                ]
            let blocks = Parsed.identifiedParsedModuleBlocks (Parsed.parsedModuleIdentified consumer)
                cases =
                    [ (claim, proof)
                    | (claim@Raw.BlockClaim{}, Raw.BlockProof _ proof _) <- zip blocks (drop 1 blocks)
                    ]
            assertEqual "explicit ATP and all three Obvious source methods" 4 (length cases)
            closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
            let globalTyping = Identity.globalTypingFromClosure closure
            truth <- expectRight (Core.checkCanonicalCore globalTyping Core.CTruth)
            nonProposition <- expectRight
                (Core.checkCanonicalCore globalTyping (Core.CIntrinsic Core.Empty))
            let report budget target = Obvious.obviousProofReport budget Obvious.AnyObviousProof
                    foundation globalTyping [] [] [] (Core.embedClosedCore [] target)
                noWork = Obvious.defaultObviousBudget
                    { Obvious.obviousFocusedWorkLimit = 0
                    , Obvious.obviousRefutationWorkLimit = 0
                    }
            sourceFailure <- requireFailure (report noWork truth)
            infrastructureFailure <- requireFailure (report Obvious.defaultObviousBudget nonProposition)
            requests <- newIORef (0 :: Int)
            let resolver = Declaration.vampireResolver \prepared -> do
                    modifyIORef' requests (+ 1)
                    Provers.runPreparedTypedProver baseProver prepared
            for_ (zip [False, True, True, True] cases) \(required, (claim, proof)) ->
                for_ [sourceFailure, infrastructureFailure] \failureReport -> do
                    writeIORef requests 0
                    outcome <- expectRight =<< runModuleDriver
                        foundation (moduleName (Parsed.parsedModuleAddress consumer))
                        ([Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude), completedModuleEvidence base])
                        resolver AlwaysMissValidation do
                            prepared <- Declaration.runProspectiveLoweringDriver
                                (Proof.prepareProofWithObviousFailureFixture failureReport claim (Just proof))
                            case prepared of
                                Left failure -> pure (Left failure)
                                Right checkedProof -> do
                                    lowered <- Declaration.runProspectiveLoweringDriver
                                        (Proof.lowerPreparedProof checkedProof)
                                        >>= either Declaration.failDeclarationDriver pure
                                    _ <- Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof
                                    pure (Right ())
                    let original = Obvious.obviousFailureFinal failureReport
                        expectedDisposition = Proof.proofErrorDisposition
                            (Proof.ProofObviousInferenceFailed Nowhere original)
                        fallsBack = not required && expectedDisposition == Proof.ProofSourceRejection
                    case outcome of
                        Declaration.DriverSucceeded result _ _ -> case result of
                            Right _ -> assertBool "only an optional source rejection falls back" fallsBack
                            Left failure -> do
                                assertBool "fallback was unexpectedly rejected" (not fallsBack)
                                assertEqual "the original disposition survives preparation"
                                    expectedDisposition (Proof.proofErrorDisposition failure)
                                case failure of
                                    Proof.ProofObviousInferenceFailed _ actual -> do
                                        assertBool "required calls have an invocation sidecar" (not required)
                                        assertEqual "sidecar absence preserves the original failure" original actual
                                    Proof.ProofObviousInferenceReported{} ->
                                        assertBool "the required invocation retains its diagnostic" required
                                    _ -> assertFailure ("wrong Obvious failure: " <> show failure)
                        _ -> assertFailure "Obvious failure preparation did not finish"
                    assertEqual "the accepting resolver runs only for optional source rejection"
                        (if fallsBack then 2 else 0) =<< readIORef requests
  where
    requireFailure report = maybe
        (assertFailure "injected Obvious request unexpectedly succeeded" >> fail "missing failure")
        pure (Obvious.obviousRunFailure report)

replaysExtendedExactRules :: Assertion
replaysExtendedExactRules = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace bootstrap mounts "test/phase5/obvious-extended-rules.tex"
    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
    rootModule <- sole "extended exact-rule root" sealed
    assertEqual "explicit proof, conjunction premises and universal projections" 3
        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))

replaysExistingWitnesses :: Assertion
replaysExistingWitnesses = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace bootstrap mounts "test/phase5/obvious-existing-witnesses.tex"
    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
    rootModule <- sole "existing-witness root" sealed
    assertEqual "set/function conditionals and a supplied member" 5
        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))

rejectsUnsupportedWitnessBodies :: Assertion
rejectsUnsupportedWitnessBodies = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/obvious-existing-witnesses-missing.tex"
    Temp.withSystemTempDirectory "felix-witness-missing-evidence" \root -> do
        mounts <- exactFixtureMounts root
        for_ [0, 32, 128 :: Int] \count -> do
            let relative = "missing-witness-evidence.tex"
                names = ["b_{" <> fromString (show index) <> "}" | index <- [1 .. count]]
                binders = if null names then "" else
                    "    Let $" <> StrictText.intercalate "," names <> "$ be sets.\n"
                assumptions = binders <> StrictText.unlines
                    [ "    Suppose $" <> name <> "=" <> name <> "$." | name <- names ]
            ByteString.writeFile (root Posix.</> relative)
                (Text.encodeUtf8 (StrictText.replace "    Then" (assumptions <> "    Then") source))
            workspace <- parseWorkspace bootstrap mounts relative
            parsed <- sole "missing-witness-evidence module"
                (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
            input <- expectRightIO (typedModuleInput foundation
                (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation parsed [])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed (Module.TypedProofFailed failure@Proof.ProofObviousInferenceReported{}))
                        prefix -> do
                    assertEqual "missing evidence remains an internal source rejection"
                        Proof.ProofSourceRejection (Proof.proofErrorDisposition failure)
                    assertBool "the unsupported existential publishes no theorem"
                        (null (Commit.pendingModulePrefixBatches prefix))
                    assertBool "the actual failed request's diagnostic is forced"
                        (StrictText.length (Proof.renderProofError failure) > 0)
                Module.TypedModuleFailed failure _ -> assertFailure
                    ("unexpected witness miss with " <> show count <> " irrelevant facts: " <> show failure)
                _ -> assertFailure "an existing witness without its body evidence was not rejected"

replaysBooleanTheoremPremises :: Assertion
replaysBooleanTheoremPremises = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace bootstrap mounts "test/phase5/obvious-premise-queries.tex"
    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
    rootModule <- sole "Boolean theorem-premise root" sealed
    assertEqual "explicit control, De Morgan, excluded middle and two selected premises" 4
        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))

rejectsMissingBooleanPremises :: Assertion
rejectsMissingBooleanPremises = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/obvious-premise-queries-missing.tex"
    Temp.withSystemTempDirectory "felix-missing-Boolean-premise" \root -> do
        mounts <- exactFixtureMounts root
        for_ [0, 32, 128 :: Int] \count -> do
            let relative = "missing-Boolean-premise.tex"
                names = ["b_{" <> fromString (show index) <> "}" | index <- [1 .. count]]
                binders = if null names then "" else
                    "    Let $" <> StrictText.intercalate "," names <> "$ be sets.\n"
                assumptions = binders <> StrictText.unlines
                    [ "    Suppose $" <> name <> "=" <> name <> "$." | name <- names ]
            ByteString.writeFile (root Posix.</> relative)
                (Text.encodeUtf8 (StrictText.replace "    Then" (assumptions <> "    Then") source))
            workspace <- parseWorkspace bootstrap mounts relative
            parsed <- sole "missing-Boolean-premise module"
                (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
            input <- expectRightIO (typedModuleInput foundation
                (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation parsed [])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed (Module.TypedProofFailed failure@Proof.ProofObviousInferenceReported{}))
                        prefix -> do
                    assertEqual "the missing premise remains an internal source rejection"
                        Proof.ProofSourceRejection (Proof.proofErrorDisposition failure)
                    assertEqual "the complete diagnostic retains the missing-antecedent classification"
                        (Just Diagnostic.DiagnosticProofObviousAntecedentUnavailable)
                        (Diagnostic.diagnosticCode <$> Proof.proofErrorDiagnostic failure)
                    assertBool "a missing premise publishes no theorem"
                        (null (Commit.pendingModulePrefixBatches prefix))
                    assertBool "the failed diagnostic is forced"
                        (StrictText.length (Proof.renderProofError failure) > 0)
                Module.TypedModuleFailed failure _ -> assertFailure
                    ("unexpected premise miss with " <> show count <> " irrelevant facts: " <> show failure)
                _ -> assertFailure "a theorem with an unproved premise was accepted"

replaysUniversalInstances :: Assertion
replaysUniversalInstances = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace bootstrap mounts "test/phase5/obvious-universal-instances.tex"
    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
    rootModule <- sole "universal-instance root" sealed
    assertEqual "explicit control, disjunction, partial projection and nested binders" 4
        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))

rejectsMissingUniversalPremises :: Assertion
rejectsMissingUniversalPremises = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/obvious-universal-instances-missing.tex"
    Temp.withSystemTempDirectory "felix-missing-universal-premise" \root -> do
        mounts <- exactFixtureMounts root
        for_ [0, 32, 128 :: Int] \count -> do
            let relative = "missing-universal-premise.tex"
                names = ["b_{" <> fromString (show index) <> "}" | index <- [1 .. count]]
                binders = if null names then "" else
                    "    Let $" <> StrictText.intercalate "," names <> "$ be sets.\n"
                assumptions = binders <> StrictText.unlines
                    [ "    Suppose $" <> name <> "=" <> name <> "$." | name <- names ]
            ByteString.writeFile (root Posix.</> relative)
                (Text.encodeUtf8 (StrictText.replace "    Then" (assumptions <> "    Then") source))
            workspace <- parseWorkspace bootstrap mounts relative
            parsed <- sole "missing-universal-premise module"
                (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
            input <- expectRightIO (typedModuleInput foundation
                (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation parsed [])
            runTypedModule input >>= \case
                Module.TypedModuleFailed
                        (Module.TypedActionFailed (Module.TypedProofFailed failure@Proof.ProofObviousInferenceReported{}))
                        prefix -> do
                    assertEqual "a missing premise remains an internal rejection"
                        Proof.ProofSourceRejection (Proof.proofErrorDisposition failure)
                    assertBool "the missing premise publishes no theorem"
                        (null (Commit.pendingModulePrefixBatches prefix))
                    assertBool "the actual failed request's diagnostic is forced"
                        (StrictText.length (Proof.renderProofError failure) > 0)
                Module.TypedModuleFailed failure _ -> assertFailure
                    ("unexpected universal miss with " <> show count <> " irrelevant facts: " <> show failure)
                _ -> assertFailure "a quantified disjunction supplied its missing premise"

qualifiesUniversalHints :: Assertion
qualifiesUniversalHints = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/obvious-universal-hints.tex"
    Temp.withSystemTempDirectory "felix-universal-hints" \root -> do
        mounts <- exactFixtureMounts root
        for_ [0, 32, 64 :: Int] \count -> do
            let names = ["c_{" <> fromString (show index) <> "}" | index <- [1 .. count]]
                binders = if null names then "" else
                    "    Let $" <> StrictText.intercalate "," names <> "$ be sets.\n"
                noise = binders <> StrictText.unlines
                    [ "    Suppose $" <> name <> "=" <> name <> "$." | name <- names ]
                negative = "    Suppose $a\\notin P$.\n"
                late = StrictText.replace negative (noise <> negative) source
                early = StrictText.replace "    Then" (noise <> "    Then") source
                explicit = StrictText.replace "    Follows."
                    "    $a\\in P$ or $b\\in Q$.\n    Follows." late
                missing = StrictText.replace negative "" late
            for_ [("late", late, True), ("early", early, True),
                    ("explicit", explicit, True), ("missing", missing, False)] \(label, script, succeeds) -> do
                let relative = label <> "-" <> show count <> ".tex"
                ByteString.writeFile (root Posix.</> relative) (Text.encodeUtf8 script)
                workspace <- parseWorkspace bootstrap mounts relative
                if succeeds then do
                    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
                    rootModule <- sole relative sealed
                    assertEqual (relative <> " seals one checked theorem") 1
                        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))
                else do
                    parsed <- sole relative (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
                    input <- expectRightIO (typedModuleInput foundation
                        (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation parsed [])
                    runTypedModule input >>= \case
                        Module.TypedModuleFailed
                                (Module.TypedActionFailed (Module.TypedProofFailed failure@Proof.ProofObviousInferenceReported{}))
                                prefix -> do
                            assertEqual "hints cannot supply a missing premise"
                                Proof.ProofSourceRejection (Proof.proofErrorDisposition failure)
                            assertBool "a missing premise publishes no theorem"
                                (null (Commit.pendingModulePrefixBatches prefix))
                            assertBool "the failed diagnostic is forced"
                                (StrictText.length (Proof.renderProofError failure) > 0)
                        Module.TypedModuleFailed failure _ -> assertFailure (relative <> ": " <> show failure)
                        _ -> assertFailure (relative <> " supplied its missing premise")

qualifiesMembershipExtensionality :: Assertion
qualifiesMembershipExtensionality = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/obvious-extensionality-cover.tex"
    -- The empty bootstrap has no named prelude exports. Certify the same
    -- extensionality theorem with the existing kernel method for this harness.
    let setextSource = StrictText.unlines
            [ "\\begin{proposition}\\label{setext}"
            , "    Let $A,B$ be sets."
            , "    Suppose for all $x$ we have if $x\\in A$, then $x\\in B$."
            , "    Suppose for all $x$ we have if $x\\in B$, then $x\\in A$."
            , "    Then $A=B$."
            , "\\end{proposition}"
            , "\\begin{proof} Follows by set extensionality. \\end{proof}"
            ]
        explicit = StrictText.replace "    Follows"
            ("    For all $x$ we have if $x\\in U$, then $x\\in V$.\n"
                <> "    For all $x$ we have if $x\\in V$, then $x\\in U$.\n    Follows") source
        missing script = StrictText.replace
            "    Suppose for all $x$ we have if $x\\in B$, then $x\\in V$.\n" "" script
        missingReverse = StrictText.replace
            "    Suppose for all $x$ we have if $x\\in V$, then $x\\in U$.\n" "" source
        bothDirections = StrictText.replace
            "    Suppose for all $x$ we have if $x\\in V$, then $x\\in U$."
            ("    Suppose for all $x$ we have if $x\\in V$, then $x\\in A$ or $x\\in B$.\n"
                <> "    Suppose for all $x$ we have if $x\\in A$, then $x\\in U$.\n"
                <> "    Suppose for all $x$ we have if $x\\in B$, then $x\\in U$.") source
    Temp.withSystemTempDirectory "felix-extensionality-cover" \root -> do
        mounts <- exactFixtureMounts root
        for_ [0, 32, 128 :: Int] \count -> do
            let names = ["c_{" <> fromString (show index) <> "}" | index <- [1 .. count]]
                noise = (if null names then "" else "    Let $" <> StrictText.intercalate "," names <> "$ be sets.\n")
                    <> StrictText.concat ["    Suppose $" <> name <> "=" <> name <> "$.\n" | name <- names]
            for_ [("implicit", source, True), ("both-directions", bothDirections, True), ("explicit", explicit, True),
                  ("missing", missing source, False), ("missing-explicit", missing explicit, False),
                  ("missing-reverse", missingReverse, False)] \(label, script, succeeds) -> do
                let relative = label <> "-" <> show count <> ".tex"
                ByteString.writeFile (root Posix.</> relative)
                    (Text.encodeUtf8 (setextSource <> StrictText.replace "    Then" (noise <> "    Then") script))
                workspace <- parseWorkspace bootstrap mounts relative
                if succeeds then do
                    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
                    rootModule <- sole relative sealed
                    assertEqual "membership proof seals after the checked extensionality theorem" 2
                        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))
                else do
                    parsed <- sole relative (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
                    input <- expectRightIO (typedModuleInput foundation
                        (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation parsed [])
                    runTypedModule input >>= \case
                        Module.TypedModuleFailed
                                (Module.TypedActionFailed (Module.TypedProofFailed failure@Proof.ProofObviousInferenceReported{}))
                                prefix -> do
                            assertEqual "missing coverage remains a source rejection"
                                Proof.ProofSourceRejection (Proof.proofErrorDisposition failure)
                            assertEqual "only the checked extensionality theorem precedes the failure" 1
                                (length (Commit.pendingModulePrefixBatches prefix))
                            assertBool "the rejection diagnostic is forced"
                                (StrictText.length (Proof.renderProofError failure) > 0)
                        Module.TypedModuleFailed failure _ -> assertFailure (relative <> ": " <> show failure)
                        _ -> assertFailure "missing coverage proved the equality"

qualifiesSuppliedExistentials :: Assertion
qualifiesSuppliedExistentials = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <- expectRight =<< Module.buildBootstrapPreludeFixture foundation unusedResolver
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/obvious-existential-elimination.tex"
    let explicit = StrictText.replace "    Follows."
            "    Take a set $x$ such that $x\\in P$ and $x\\in Q$ by assumption.\n    Follows." source
        nested = StrictText.replace
            "there exists a set $x$ such that $x\\in P$ and $x\\in Q$"
            "there exist sets $x,z$ such that $x\\in P$ and $z\\in Q$" source
        missing = StrictText.replace " and $x\\in Q$" "" source
        independent = StrictText.replace "Then there exists a set $y$ such that $y\\in Q$"
            "Then $a\\in Q$" (StrictText.replace "$P,Q$" "$a,P,Q$" source)
        consequence = StrictText.replace "    Then there exists a set $y$ such that $y\\in Q$."
            "    Suppose for all $x$ we have $x\\in P\\implies a\\in Q$.\n    Then $a\\in Q$."
            (StrictText.replace "$P,Q$" "$a,P,Q$" missing)
    Temp.withSystemTempDirectory "felix-supplied-existentials" \root -> do
        mounts <- exactFixtureMounts root
        for_ [0, 32, 128 :: Int] \count -> do
            let names = ["c_{" <> fromString (show index) <> "}" | index <- [1 .. count]]
                binders = if null names then "" else
                    "    Let $" <> StrictText.intercalate "," names <> "$ be sets.\n"
                noise = binders <> StrictText.unlines
                    [ "    Suppose $" <> name <> "=" <> name <> "$." | name <- names ]
            for_ [("transfer", source, True), ("explicit", explicit, True),
                    ("nested", nested, True), ("consequence", consequence, True),
                    ("missing", missing, False), ("independent", independent, False)] \(label, script, succeeds) -> do
                let relative = label <> "-" <> show count <> ".tex"
                ByteString.writeFile (root Posix.</> relative)
                    (Text.encodeUtf8 (StrictText.replace "    Then" (noise <> "    Then") script))
                workspace <- parseWorkspace bootstrap mounts relative
                if succeeds then do
                    sealed <- compileParsedWorkspaceWithResolver foundation bootstrap unusedResolver workspace
                    rootModule <- sole relative sealed
                    assertEqual (relative <> " seals one checked theorem") 1
                        (length (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix rootModule)))
                else do
                    parsed <- sole relative (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
                    input <- expectRightIO (typedModuleInput foundation
                        (Module.bootstrapPreludeReadiness bootstrap) unusedResolver AlwaysMissValidation parsed [])
                    runTypedModule input >>= \case
                        Module.TypedModuleFailed
                                (Module.TypedActionFailed (Module.TypedProofFailed failure@Proof.ProofObviousInferenceReported{}))
                                prefix -> do
                            assertEqual "an existential cannot supply missing evidence"
                                Proof.ProofSourceRejection (Proof.proofErrorDisposition failure)
                            assertBool "a missing premise publishes no theorem"
                                (null (Commit.pendingModulePrefixBatches prefix))
                            assertBool "the failed diagnostic is forced"
                                (StrictText.length (Proof.renderProofError failure) > 0)
                        Module.TypedModuleFailed failure _ -> assertFailure (relative <> ": " <> show failure)
                        _ -> assertFailure (relative <> " supplied an unrelated witness")

replaysExactObviousDischarges :: Assertion
replaysExactObviousDischarges = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase5/exact-obvious.tex"
    sealed <-
        compileParsedWorkspaceWithResolver
            foundation bootstrap unusedResolver workspace
    rootModule <- sole "exact obvious root" sealed
    let batches =
            Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix rootModule)
    assertEqual
        "definition, root conversion, and proof-bearing declarations"
        13
        (length batches)
    definitionBatch <-
        maybe
            (assertFailure "exact obvious fixture has no definition batch")
            pure
            (listToMaybe batches)
    case Semantic.declarationDeltaDefinitionViews
            (Commit.committedBatchDelta definitionBatch) of
        [view] -> do
            assertEqual
                "ordinary constant definitions publish a pointwise view"
                Semantic.DefinitionPointwiseView
                (Semantic.semanticDefinitionViewKind view)
            assertBool
                "the canonical view targets its declaration fact"
                (Semantic.semanticDefinitionViewTarget view
                    `elem`
                        (Semantic.semanticFactFingerprint
                            <$> Semantic.declarationDeltaFacts
                                (Commit.committedBatchDelta definitionBatch)))
        views ->
            assertFailure
                ("expected one canonical definition view, got "
                    <> show views)

    invalidWorkspace <- parseWorkspace
        bootstrap mounts "test/phase5/exact-obvious-unused-definition.tex"
    invalidParsed <- sole "unused-definition module"
        (toList
            (Parsed.parsedWorkspaceImportedBeforeImporter invalidWorkspace))
    invalidInput <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            invalidParsed
            [])
    runTypedModule invalidInput >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedProofFailed
                        (Proof.ProofObviousInferenceReported
                            location
                            _diagnostic)))
                prefix -> do
            assertBool
                "an evidence-free proof by definition publishes no theorem"
                (null (Commit.pendingModulePrefixBatches prefix))
            assertBool "reported failure retains definition-evidence semantics"
                ("canonical definition evidence"
                    `StrictText.isInfixOf`
                        Proof.renderProofError
                            (Proof.ProofObviousInferenceReported
                                location _diagnostic))
            assertEqual "reported ordinary proof disposition"
                Proof.ProofSourceRejection
                (Proof.proofErrorDisposition
                    (Proof.ProofObviousInferenceReported
                        location _diagnostic))
            let ordinaryProofFailure =
                    Proof.ProofObviousInferenceFailed
                        location
                        Obvious.ObviousCanonicalDefinitionEvidenceRequired
                malformedProofFailure =
                    Proof.ProofObviousInferenceFailed
                        location
                        (Obvious.ObviousMalformedInput
                            Obvious.ObviousHypothesisMetadataMismatch)
                integrityProofFailure =
                    Proof.ProofObviousInferenceFailed
                        location
                        (Obvious.ObviousIntegrityFailure
                            (KernelProof.ProofStructuralCompositionMismatch
                                "test invariant"))
                source = Parsed.parsedModuleResolved invalidParsed
                verificationKind path =
                    Verification.verificationDriverErrorKind
                        (Verification.VerificationTypedModuleError
                            source
                            (Module.TypedActionFailed path)
                            prefix)
            assertEqual "reported ordinary verification disposition"
                Verification.VerificationSourceFailure
                (verificationKind
                    (Module.TypedProofFailed
                        (Proof.ProofObviousInferenceReported
                            location _diagnostic)))
            assertEqual "ordinary Obvious proof disposition"
                Proof.ProofSourceRejection
                (Proof.proofErrorDisposition ordinaryProofFailure)
            assertEqual "malformed Obvious proof disposition"
                Proof.ProofInfrastructureFailure
                (Proof.proofErrorDisposition malformedProofFailure)
            assertEqual "integrity Obvious proof disposition"
                Proof.ProofInfrastructureFailure
                (Proof.proofErrorDisposition integrityProofFailure)
            malformedDiagnostic <- maybe
                (assertFailure "malformed Obvious failure has no diagnostic"
                    >> fail "missing")
                pure
                (Proof.proofErrorDiagnostic malformedProofFailure)
            assertEqual "malformed Obvious diagnostic code"
                Diagnostic.DiagnosticProofObviousMalformed
                (Diagnostic.diagnosticCode malformedDiagnostic)
            assertBool "malformed Obvious diagnostics offer no proof advice"
                (null (Diagnostic.diagnosticHelp malformedDiagnostic))
            integrityDiagnostic <- maybe
                (assertFailure "integrity Obvious failure has no diagnostic"
                    >> fail "missing")
                pure
                (Proof.proofErrorDiagnostic integrityProofFailure)
            assertBool "integrity Obvious diagnostics offer no proof advice"
                (null (Diagnostic.diagnosticHelp integrityDiagnostic))
            assertEqual "direct ordinary module disposition"
                Proof.ProofSourceRejection
                (Module.typedPathErrorDisposition
                    (Module.TypedProofFailed ordinaryProofFailure))
            assertEqual "direct ordinary verification disposition"
                Verification.VerificationSourceFailure
                (verificationKind
                    (Module.TypedProofFailed ordinaryProofFailure))
            assertEqual "direct malformed verification disposition"
                Verification.VerificationInfrastructureFailure
                (verificationKind
                    (Module.TypedProofFailed malformedProofFailure))
            assertEqual "direct integrity verification disposition"
                Verification.VerificationInfrastructureFailure
                (verificationKind
                    (Module.TypedProofFailed integrityProofFailure))
            assertEqual "instance ordinary module disposition"
                Proof.ProofSourceRejection
                (Module.typedPathErrorDisposition
                    (Module.TypedInstanceFailed
                        (Instance.InstanceProofFailed ordinaryProofFailure)))
            assertEqual "instance malformed verification disposition"
                Verification.VerificationInfrastructureFailure
                (verificationKind
                    (Module.TypedInstanceFailed
                        (Instance.InstanceProofFailed malformedProofFailure)))
            assertEqual "instance integrity verification disposition"
                Verification.VerificationInfrastructureFailure
                (verificationKind
                    (Module.TypedInstanceFailed
                        (Instance.InstanceProofFailed integrityProofFailure)))
        _result ->
            assertFailure
                "evidence-free proof by definition was not rejected"

publishesCanonicalDefinitionViewKinds :: Assertion
publishesCanonicalDefinitionViewKinds = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase8/typed-definition-view.tex"
    sealed <-
        compileParsedWorkspaceWithResolver
            foundation bootstrap unusedResolver workspace
    rootModule <- sole "higher-order definition-view root" sealed
    batch <- sole
        "higher-order definition-view batch"
        (Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix rootModule))
    view <- sole
        "higher-order exact definition view"
        (Semantic.declarationDeltaDefinitionViews
            (Commit.committedBatchDelta batch))
    assertEqual
        "a definition with a higher-order argument keeps its exact equation"
        Semantic.DefinitionExactView
        (Semantic.semanticDefinitionViewKind view)

compilesOrdinaryProofs :: Assertion
compilesOrdinaryProofs =
    Temp.withSystemTempDirectory "felix-exact-proofs" \root -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace
            bootstrap mounts "test/phase5/exact-proofs.tex"
        let executable = root Posix.</> "vampire"
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-proof'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        observations <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    claim =
                        Backend.typedProblemClaim problem
                    locals =
                        Backend.typedProblemLocalPremises problem
                modifyIORef' observations
                    (<> [ ( Vector.length
                                (Backend.typedProblemGlobalPremises problem)
                           , Vector.length
                                locals
                           , [ Vector.length
                                (Backend.supportedPropositionSupport
                                    (Backend.typedLocalPremiseProposition premise))
                             | premise <- Vector.toList locals
                             ]
                           , [ Backend.supportedPropositionTerm
                                    (Backend.typedLocalPremiseProposition premise)
                                == Backend.supportedPropositionTerm claim
                             | premise <- Vector.toList locals
                             ]
                           )
                        ])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        sealed <-
            compileParsedWorkspaceWithResolver
                foundation bootstrap resolver workspace
        rootModule <- sole "proof root" (drop 1 sealed)
        let batches =
                Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix rootModule)
        assertEqual "one definition and six theorem declarations"
            7
            (length batches)
        let proofBatches = drop 1 batches
        assertEqual "only closed theorem facts are published"
            [1, 1, 1, 1, 1, 1]
            [ length
                (Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta batch))
            | batch <- proofBatches
            ]
        assertEqual "proof request aggregation follows source structure"
            [0, 0, 0, 0, 0, 1]
            [ case Commit.committedBatchProofValidations batch of
                [record] ->
                    case Authority.validationDirectAuthorization
                            (Semantic.proofValidationRecordCertificate
                                record) of
                        Authority.CheckedSourceProof requests ->
                            length
                                (Authority.externalProofUseRequests requests)
                        authorization ->
                            error
                                ("unexpected proof authority: "
                                    <> show authorization)
                records ->
                    error
                        ("unexpected proof validation count: "
                            <> show (length records))
            | batch <- proofBatches
            ]
        headerBatch <- sole "header-envelope proof batch"
            (take 1 (drop 3 proofBatches))
        headerProposition <- sole "header-envelope checked proposition"
            (Commit.committedBatchPropositions headerBatch)
        assertEqual "header-envelope closed target"
            (Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CImp
                        (member
                            (Core.CBound 0)
                            (Core.CBound 1))
                        (member
                            (Core.CBound 0)
                            (Core.CBound 1)))))
            (Core.frozenCoreTerm
                (Identity.checkedPropositionTerm headerProposition))
        headerFact <- sole "header-envelope published fact"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta headerBatch))
        assertEqual "header-envelope proof remains clean"
            Authority.cleanAuthoritySafety
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority headerFact))
        observed <- readIORef observations
        case observed of
            [(0, 0, [], [])] ->
                pure ()
            _ ->
                assertFailure
                    ("unexpected proof premise policies: "
                        <> show observed)
  where
    member element set =
        Core.CApp
            (Core.CApp
                (Core.CIntrinsic Core.Member)
                element)
            set

replaysSetExtensionalityInKernel :: Assertion
replaysSetExtensionalityInKernel = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase5/exact-set-extensionality.tex"
    sealed <-
        compileParsedWorkspaceWithResolver
            foundation bootstrap unusedResolver workspace
    rootModule <- sole "set-extensionality root" sealed
    let batches = Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix rootModule)
    assertEqual
        "direct, generic, and pointwise set theorems"
        5
        (length batches)
    traverse_ (assertDirectExtensionality "set") batches

rejectsMismatchedPointwiseSetEquivalence :: Assertion
rejectsMismatchedPointwiseSetEquivalence = do
    result <-
        withAcceptedFixtureVampire "felix-set-extensionality-mismatch"
            \prover ->
                checkFileFresh
                    prover
                    "test/phase5/exact-set-extensionality-mismatch.tex"
    case result of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                    _source
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofSetExtensionalityLeftToRightUnavailable
                                location)))
                    prefix)
            , _slowReport
            ) -> do
            assertEqual "mismatched equivalence line" 7 (locLine location)
            assertEqual "failed theorem publishes no declaration"
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Left failure ->
            assertFailure
                ("unexpected pointwise-equivalence failure: " <> show failure)
        Right{} ->
            assertFailure "mismatched pointwise equivalence was accepted"

exposesPointwiseDefinitionsForSetExtensionality :: Assertion
exposesPointwiseDefinitionsForSetExtensionality =
  Temp.withSystemTempDirectory "felix-definition-set-extensionality" \root -> do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts "test/phase5/definition-set-extensionality.tex"
    rootModule <-
        sole "definition-exposed set-extensionality root"
            =<< compileParsedWorkspaceWithValidation
                foundation bootstrap unusedResolver
                AlwaysMissValidation workspace
    let batches = Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix rootModule)
        theoremBatches = drop 3 batches
    assertEqual
        "three definitions and four extensionality theorems"
        7
        (length batches)
    assertEqual
        "four definition-exposed extensionality theorems"
        4
        (length theoremBatches)
    traverse_ (assertDirectExtensionality "definition-exposed set")
        theoremBatches

    let storePath = root Posix.</> "store.sqlite"
    bracket
        (snd <$> (Store.openStore storePath
            (Identity.theoryId foundation) >>= expectRight))
        Store.closeStore
        \store -> do
            storeCheck <- Store.newStoreCheck store
            expectRightIO
                (Store.writePendingModulePrefix storeCheck
                    (Module.completedTypedModulePrefix rootModule))
            let cachedValidation = storeValidationPolicy storeCheck
            warm <-
                sole "warm definition-exposed set-extensionality root"
                    =<< compileParsedWorkspaceWithValidation
                        foundation bootstrap unusedResolver
                        cachedValidation workspace
            assertEqual
                "definition-exposed discharges retain cached authorization"
                (proofValidationRecords rootModule)
                (proofValidationRecords warm)
  where
    proofValidationRecords sealed =
        concatMap Commit.committedBatchProofValidations
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed))

acceptsSubsetObservationsForSetExtensionality :: Assertion
acceptsSubsetObservationsForSetExtensionality =
    withAcceptedFixtureVampire "felix-subset-set-extensionality" \prover -> do
        result <-
            checkFileFresh
                prover
                "test/phase5/subset-set-extensionality.tex"
        case result of
            Left failure ->
                assertFailure
                    ("subset extensionality fixture did not run: "
                        <> show failure)
            Right (verification, _slowReport) ->
                assertTypedSuccess "subset extensionality fixture" verification

replaysRecordExtensionalityInKernel :: Assertion
replaysRecordExtensionalityInKernel =
    Temp.withSystemTempDirectory "felix-record-extensionality" \root -> do
        let executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        let resolver =
                Declaration.vampireResolver
                    (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit))
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts =<< getCurrentDirectory
            workspace <- parseFinalWorkspace
                prelude mounts
                "test/phase5/exact-record-extensionality.tex"
            modules <- compileFinalParsedWorkspaceWithResolver
                foundation prelude resolver workspace
            rootModule <- sole "record-extensionality root" (drop 1 modules)
            let batches = Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix rootModule)
            assertEqual
                "explicit, generic record, and generic set theorems"
                3
                (length batches)
            traverse_ (assertDirectExtensionality "record") batches

replaysRecordAliasNormalizationInKernel :: Assertion
replaysRecordAliasNormalizationInKernel =
    Temp.withSystemTempDirectory "felix-record-alias-normalization" \root -> do
        let executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        let resolver =
                Declaration.vampireResolver
                    (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit))
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation resolver
            mounts <- exactFixtureMounts =<< getCurrentDirectory
            workspace <- parseFinalWorkspace
                prelude mounts
                "test/phase5/exact-record-alias-normalization.tex"
            modules <- compileFinalParsedWorkspaceWithResolver
                foundation prelude resolver workspace
            rootModule <- sole
                "record-alias-normalization root" (drop 1 modules)
            batch <- sole
                "record-alias-normalization theorem"
                (Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix rootModule))
            assertDirectExtensionality "record alias normalization" batch

rejectsRecordTheoremEqualityNormalization :: Assertion
rejectsRecordTheoremEqualityNormalization =
    withAcceptedFixtureVampire "felix-record-theorem-equality" \prover -> do
        result <- checkFileFresh
            prover
            "test/phase5/exact-record-theorem-equality-no-alias.tex"
        case result of
            Right
                ( Verification.VerificationCheckingFailure _report
                    (Verification.VerificationTypedModuleError
                        _source
                        (Module.TypedActionFailed
                            (Module.TypedProofFailed
                                (Proof.ProofRecordExtensionalityLeftShapeUnavailable
                                    location)))
                        _prefix)
                , _slowReport
                ) ->
                assertEqual "ordinary equality rejection line"
                    14 (locLine location)
            Left failure ->
                assertFailure
                    ("the theorem-equality boundary fixture did not run: "
                        <> show failure)
            Right other ->
                assertFailure
                    ("ordinary theorem equality changed exact-record normalization: "
                        <> show other)

rejectsIncompleteRecordExtensionality :: Assertion
rejectsIncompleteRecordExtensionality = do
    result <-
        withAcceptedFixtureVampire "felix-record-extensionality-incomplete"
            \prover ->
                checkFileFresh
                    prover
                    "test/phase5/exact-record-extensionality-incomplete.tex"
    case result of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                    _source
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofRecordExtensionalityFieldUnavailable
                                location
                                field)))
                    prefix)
            , _slowReport
            ) -> do
            assertEqual "missing field equation line" 10 (locLine location)
            assertEqual "first missing field in canonical order"
                (Raw.StructSymbol "matrixPoint")
                field
            assertEqual "failed theorem publishes no declaration"
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Left failure ->
            assertFailure
                ("unexpected incomplete record-extensionality failure: "
                    <> show failure)
        Right{} ->
            assertFailure "incomplete record extensionality was accepted"

assertDirectExtensionality
    :: String
    -> Commit.CommittedDeclarationBatch
    -> Assertion
assertDirectExtensionality family batch = do
    validation <- sole (family <> " extensionality validation")
        (Commit.committedBatchProofValidations batch)
    case Authority.validationDirectAuthorization
            (Semantic.proofValidationRecordCertificate validation) of
        Authority.CheckedSourceProof requests ->
            assertEqual
                (family <> " extensionality submits no external proof request")
                []
                (Authority.externalProofUseRequests requests)
        authorization ->
            assertFailure
                ("unexpected " <> family <> "-extensionality authorization: "
                    <> show authorization)

restoresElaborationBinderAndWitnessProofForms :: Assertion
restoresElaborationBinderAndWitnessProofForms =
    Temp.withSystemTempDirectory "felix-exact-proof-parity" \root -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace
            bootstrap mounts "test/phase5/exact-proof-parity.tex"
        parsed <- sole "parsed proof-parity module"
            (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        let blocks =
                Parsed.identifiedParsedModuleBlocks
                    (Parsed.parsedModuleIdentified parsed)
            claims = [claim | claim@Raw.BlockClaim{} <- blocks]
            proofs =
                [ proof
                | Raw.BlockProof _location proof _end <- blocks
                ]
        omittedClaim <-
            case reverse claims of
                claim : _ -> pure claim
                [] -> assertFailure "missing omitted witness claim"
                    >> fail "unreachable"
        omittedProof <-
            case reverse proofs of
                proof : _ -> pure proof
                [] -> assertFailure "missing omitted witness proof"
                    >> fail "unreachable"
        runModuleDriver
            foundation
            preludeModuleName
            []
            unusedResolver
            AlwaysMissValidation do
                Declaration.runProspectiveLoweringDriver
                    (Proof.prepareProof
                        omittedClaim (Just omittedProof))
                    >>= either Declaration.failModuleDriver pure
            >>= \case
                Right (Declaration.DriverSucceeded
                        prepared _semantic _prefix) ->
                    case Proof.preparedProofFirstOmission prepared of
                        Just location ->
                            assertEqual "nested Take retains first omission"
                                125 (locLine location)
                        Nothing ->
                            assertFailure "nested Take lost its omission"
                Right Declaration.DriverFailed{} ->
                    assertFailure "omitted witness preparation failed"
                Right Declaration.DriverSealFailed{} ->
                    assertFailure "omitted witness preparation did not seal"
                Left failure ->
                    assertFailure
                        ("omitted witness preparation did not open: "
                            <> show failure)
        let executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-proof-parity'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        runs <- newIORef (0 :: Int)
        fresh <-
            sole "proof-parity module"
                =<< compileParsedWorkspaceWithValidation
                    foundation
                    bootstrap
                    (countingAcceptedResolver executable runs)
                    AlwaysMissValidation
                    workspace
        assertEqual "restored proof request count" 0 =<< readIORef runs
        assertEqual
            "restored proof declarations preserve discharge order"
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
            (proofRequestCounts fresh)
        lastBatch <-
            case reverse
                    (Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix fresh)) of
                batch : _ -> pure batch
                [] -> assertFailure "missing restored-proof batches"
                    >> fail "unreachable"
        lastFact <- sole "omitted witness fact"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta lastBatch))
        assertEqual "omitted continuation remains escape-backed"
            (Authority.authoritySafety
                (Authority.singletonEscapeKind Authority.Omitted))
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority lastFact))
        assertBool "proof-local witnesses publish no objects"
            (all
                (null . Commit.committedBatchObjects)
                (Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix fresh)))

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warm <-
                    sole "warm proof-parity module"
                        =<< compileParsedWorkspaceWithValidation
                            foundation
                            bootstrap
                            (countingAcceptedResolver executable warmRuns)
                            validation
                            workspace
                assertEqual "warm restored proofs skip Vampire"
                    0 =<< readIORef warmRuns
                assertEqual
                    "fresh and warm proof validation keys and authority"
                    (proofValidationRecords fresh)
                    (proofValidationRecords warm)
                assertEqual
                    "fresh and warm checked proposition identities"
                    (map Identity.checkedPropositionId
                        (concatMap Commit.committedBatchPropositions
                        (Commit.pendingModulePrefixBatches
                            (Module.completedTypedModulePrefix fresh))))
                    (map Identity.checkedPropositionId
                        (concatMap Commit.committedBatchPropositions
                        (Commit.pendingModulePrefixBatches
                            (Module.completedTypedModulePrefix warm))))

        assertProofParityFailure
            foundation bootstrap mounts
            "test/phase5/exact-proof-parity-invalid-fix.tex"
            (\case
                Proof.ProofGoalStatementMismatch location ->
                    locLine location == 6
                _ -> False)
        assertProofParityFailure
            foundation bootstrap mounts
            "test/phase5/exact-proof-parity-invalid-fix-shape.tex"
            (\case
                Proof.ProofExpectedUniversalGoal
                        location Proof.EqualityGoal ->
                    locLine location == 6
                _ -> False)
        assertProofParityFailure
            foundation bootstrap mounts
            "test/phase5/exact-proof-parity-invalid-assume.tex"
            (\case
                Proof.ProofAssumptionOpeningFailed
                        location
                        (LooseDeduction.AssumptionClassicalDisjunctionMismatch{}) ->
                    locLine location == 6
                _ -> False)
  where
    proofRequestCounts sealed =
        [ case Commit.committedBatchProofValidations batch of
            [record] ->
                case Authority.validationDirectAuthorization
                        (Semantic.proofValidationRecordCertificate record) of
                    Authority.CheckedSourceProof requests ->
                        length (Authority.externalProofUseRequests requests)
                    Authority.OmittedAuthorization -> 1
                    authorization ->
                        error ("unexpected restored-proof authority: "
                            <> show authorization)
            records ->
                error ("unexpected restored-proof validation count: "
                    <> show (length records))
        | batch <- Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed)
        ]

    proofValidationRecords sealed =
        concatMap Commit.committedBatchProofValidations
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed))

restoresLocalReasoningAndCalculations :: Assertion
restoresLocalReasoningAndCalculations =
    Temp.withSystemTempDirectory "felix-exact-local-reasoning" \root -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace
            bootstrap mounts "test/phase5/exact-proof-local-reasoning.tex"
        let executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire executable
        observations <- newIORef []
        fresh <-
            sole "exact local-reasoning module"
                =<< compileParsedWorkspaceWithValidation
                    foundation
                    bootstrap
                    (observingResolver executable observations)
                    AlwaysMissValidation
                    workspace
        observed <- readIORef observations
        assertEqual "local-reasoning request count" 2 (length observed)
        assertEqual "proof forms retain source request order"
            [0, 0, 2, 0, 0, 0, 1]
            (requestCounts fresh)
        case observed of
            [biconditionalFirst, biconditionalSecond] -> do
                assertEqual "first biconditional link remains proposition equality"
                    Core.TyProp
                    (equalityOperandType
                        (localReasoningTarget biconditionalFirst))
                assertEqual "biconditional second link keeps local-only policy"
                    0 (localReasoningGlobalCount biconditionalSecond)
            _ ->
                assertFailure
                    ("unexpected local-reasoning observations: "
                        <> show observed)
        omittedBatch <- sole "omitted Suffices batch"
            (take 1
                (reverse
                    (Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix fresh))))
        omittedFact <- sole "omitted Suffices fact"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta omittedBatch))
        assertEqual "Suffices continuation omission reaches final authority"
            (Authority.authoritySafety
                (Authority.singletonEscapeKind Authority.Omitted))
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority omittedFact))

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warm <-
                    sole "warm local-reasoning module"
                        =<< compileParsedWorkspaceWithValidation
                            foundation
                            bootstrap
                            (countingAcceptedResolver executable warmRuns)
                            validation
                            workspace
                assertEqual "warm local-reasoning validation skips Vampire"
                    0 =<< readIORef warmRuns
                assertEqual "fresh and warm local-reasoning validations"
                    (validationRecords fresh)
                    (validationRecords warm)

        assertRejectedPrefix
            "first biconditional link failure" foundation bootstrap workspace
            executable 0 2 1
        assertRejectedPrefix
            "second biconditional link failure" foundation bootstrap workspace
            executable 1 2 2
  where
    observingResolver executable observations =
        Declaration.vampireResolver \prepared -> do
            let problem = Provers.preparedTypedProverLogicalProblem prepared
                claim = Backend.typedProblemClaim problem
                locals = Backend.typedProblemLocalPremises problem
                observation =
                    LocalReasoningObservation
                        { localReasoningTarget =
                            Backend.supportedPropositionTerm claim
                        , localReasoningGlobalCount = Vector.length
                            (Backend.typedProblemGlobalPremises problem)
                        , localReasoningLocalOrdinals =
                            [ Backend.localPremiseOrdinalValue
                                (Backend.typedLocalPremiseOrdinal premise)
                            | premise <- Vector.toList locals
                            ]
                        , localReasoningLocalTerms =
                            [ Backend.supportedPropositionTerm
                                (Backend.typedLocalPremiseProposition premise)
                            | premise <- Vector.toList locals
                            ]
                        , localReasoningAuxiliaries =
                            Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                        }
            modifyIORef' observations (<> [observation])
            (Provers.runPreparedTypedProver
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared)

    requestCounts sealed =
        [ case Commit.committedBatchProofValidations batch of
            [record] ->
                case Authority.validationDirectAuthorization
                        (Semantic.proofValidationRecordCertificate record) of
                    Authority.CheckedSourceProof requests ->
                        length (Authority.externalProofUseRequests requests)
                    Authority.OmittedAuthorization -> 1
                    direct -> error
                        ("unexpected local-reasoning authority: " <> show direct)
            records -> error
                ("unexpected local-reasoning validation count: "
                    <> show (length records))
        | batch <- Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed)
        ]

    validationRecords =
        concatMap Commit.committedBatchProofValidations
            . Commit.pendingModulePrefixBatches
            . Module.completedTypedModulePrefix

    equalityOperandType = \case
        Core.CEq operandType _left _right -> operandType
        term -> error ("expected checked equality, found " <> show term)

    assertRejectedPrefix
            label foundation bootstrap workspace executable rejectedIndex
            expectedPrefix expectedRuns = do
        runs <- newIORef (0 :: Int)
        parsed <- sole (label <> " parsed module")
            (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    index <- atomicModifyIORef' runs \current ->
                        (current + 1, current)
                    if index == rejectedIndex
                        then pure
                            (counterexampleResolution prepared)
                        else
                            (Provers.runPreparedTypedProver
                                    (Provers.vampire
                                        executable
                                        Provers.defaultTimeLimit
                                        Provers.defaultMemoryLimit)
                                    prepared)
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                resolver
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed _failure prefix ->
                assertEqual
                    (label <> " publishes only the prior prefix")
                    expectedPrefix
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure (label <> " unexpectedly succeeded")
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    (label <> " did not open: " <> show failure)
        assertEqual (label <> " selects the first rejected request")
            expectedRuns =<< readIORef runs

rejectsTemporarySincePremiseLeak :: Assertion
rejectsTemporarySincePremiseLeak = do
    repository <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts repository
    assertProofParityFailure
        foundation bootstrap mounts
        "test/phase5/exact-since-scope-invalid.tex"
        (\case
            Proof.ProofAssumptionUnavailable location ->
                locLine location == 8
            _ -> False)

data LocalReasoningObservation = LocalReasoningObservation
    { localReasoningTarget :: !(Core.CanonicalTerm Identity.ObjectId)
    , localReasoningGlobalCount :: !Int
    , localReasoningLocalOrdinals :: ![Natural]
    , localReasoningLocalTerms ::
        ![Core.CanonicalTerm Identity.ObjectId]
    , localReasoningAuxiliaries :: ![Foundation.FoundationAxiomTag]
    }
    deriving (Show)

selectsCalculationLinkFailureBySourceOrder :: Assertion
selectsCalculationLinkFailureBySourceOrder = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-calculation-link-order" \root -> do
        let executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
            source = "test/phase7/calculation-link-order.tex"
            laterCompleted = root Posix.</> "later-completed"
            firstRun = root Posix.</> "first-run"
            secondRun = root Posix.</> "second-run"
            prover =
                Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
        writeAcceptedFixtureVampire executable
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \openStore -> do
            let ignored =
                    Verification.verificationRequestObserver
                        (\_position _request -> pure ())
            void
                (
                    (checkFileWithStore
                        openStore
                        Verification.WarmStoreValidation
                        ignored
                        prover
                        "test/phase3/typed-unsupported.tex")
                    >>= expectRight)
            writeFile executable
                (unlines
                    [ "#!/bin/sh"
                    , "cat >/dev/null"
                    , "if mkdir \"" <> firstRun <> "\" 2>/dev/null; then"
                    , "  printf '%s\\n' '% SZS status Theorem for calculation-link-order'"
                    , "elif mkdir \"" <> secondRun <> "\" 2>/dev/null; then"
                    , "  : > \"" <> laterCompleted <> "\""
                    , "  printf '%s\\n' '% SZS status Theorem for calculation-link-order'"
                    , "else"
                    , "  printf '%s\\n' '% SZS status CounterSatisfiable for calculation-link-order'"
                    , "fi"
                    ])
            permissions <- getPermissions executable
            setPermissions executable (setOwnerExecutable True permissions)
            jobs <-
                Provers.selectEffectiveJobs
                    (Provers.effectiveJobs 2)
                    (fail "explicit jobs unexpectedly detected processors")
            positions <- newIORef []
            middleStarted <- newEmptyTMVarIO
            laterStarted <- newEmptyTMVarIO
            releaseMiddle <- newEmptyTMVarIO
            let observer =
                    Verification.verificationRequestObserver \position _request -> do
                        let ordinal =
                                Provers.workPositionLocalRequestOrdinal position
                        modifyIORef' positions (position :)
                        case ordinal of
                            1 -> pure ()
                            2 -> do
                                atomically (putTMVar middleStarted ())
                                atomically (takeTMVar releaseMiddle)
                            3 -> atomically (putTMVar laterStarted ())
                            _ ->
                                assertFailure
                                    ("unexpected calculation request ordinal: "
                                        <> show ordinal)
            withAsync
                (
                    (checkFileWithStoreAndJobs
                        openStore
                        Verification.WarmStoreValidation
                        jobs
                        observer
                        prover
                        source)
                    >>= expectRight)
                \verification -> do
                    void
                        (awaitTmvar "middle calculation link" middleStarted)
                    void
                        (awaitTmvar "later calculation continuation" laterStarted)
                    waitForFileSignal
                        "later calculation continuation" laterCompleted
                    atomically (putTMVar releaseMiddle ())
                    (result, _slowReport) <- wait verification
                    case result of
                        Verification.VerificationFailure report failed -> do
                            assertEqual "middle link failure location"
                                (source, 11)
                                ( locFile
                                    (Verification.failedVerificationLocation failed)
                                , locLine
                                    (Verification.failedVerificationLocation failed)
                                )
                            assertEqual "failed calculation admits no source fact"
                                [] (Verification.verificationDirectEscapes report)
                        other ->
                            assertFailure
                                ("calculation link order did not reject: "
                                    <> show other)
                    observedPositions <-
                        fmap
                            (\position ->
                                ( Provers.workPositionModuleOrdinal position
                                , Provers.workPositionLocalRequestOrdinal
                                    position
                                ))
                            <$> readIORef positions
                    assertEqual "all calculation requests executed"
                        [(1, 1), (1, 2), (1, 3)]
                        (sort observedPositions)

            writeAcceptedFixtureVampire executable
            retryPositions <- newIORef []
            let retryObserver =
                    Verification.verificationRequestObserver \position _request ->
                        modifyIORef' retryPositions (position :)
            (retry, _retrySlowReport) <-
                    (checkFileWithStoreAndJobs
                        openStore
                        Verification.WarmStoreValidation
                        jobs
                        retryObserver
                        prover
                        source)
                    >>= expectRight
            case retry of
                Verification.VerificationCompleted{} -> pure ()
                other ->
                    assertFailure
                        ("calculation rollback retry failed: " <> show other)
            retryObserved <- readIORef retryPositions
            assertEqual "retry executes the complete calculation proof"
                3 (length retryObserved)
  where
    awaitTmvar label variable = do
        result <- Timeout.timeout 10000000
            (atomically (takeTMVar variable))
        maybe
            (assertFailure (label <> " was not observed")
                >> fail "unreachable")
            pure
            result

verifiesRelationCompositionThroughImports :: Assertion
verifiesRelationCompositionThroughImports = checkCompositionImports
    "test/phase7/composition-direct.tex" "test/phase7/composition-diamond-root.tex"

checkCompositionImports :: FilePath -> FilePath -> Assertion
checkCompositionImports directPath diamondPath = do
    foundation <- expectRight Foundation.checkedFoundation
    withAcceptedFixtureVampire "felix-composition-imports" \prover ->
        Temp.withSystemTempDirectory "felix-composition-imports" \directory -> do
            let storePath = directory Posix.</> "store.sqlite"
            (_startup, store) <-
                Store.openStore storePath (Identity.theoryId foundation)
                    >>= expectRight
            bracket (pure store) Store.closeStore \opened -> do
                direct <- checkFileWithStore
                    opened
                    Verification.FreshStoreValidation
                    ignoredVerificationRequests
                    prover
                    directPath
                (directResult, _) <- expectRight direct
                assertTypedSuccess
                    "direct composition import"
                    directResult
                warm <- checkFileWithStore
                    opened
                    Verification.WarmStoreValidation
                    ignoredVerificationRequests
                    prover
                    directPath
                (warmResult, _) <- expectRight warm
                assertTypedSuccess
                    "warm composition import"
                    warmResult
                diamond <- checkFileWithStore
                    opened
                    Verification.WarmStoreValidation
                    ignoredVerificationRequests
                    prover
                    diamondPath
                (diamondResult, _) <- expectRight diamond
                assertTypedSuccess
                    "diamond composition import"
                    diamondResult

checksGeneralizedCalculationForms :: Assertion
checksGeneralizedCalculationForms = do
    foundation <- expectRight Foundation.checkedFoundation
    withAcceptedFixtureVampire "felix-calculation-forms" \prover ->
        Temp.withSystemTempDirectory "felix-calculation-forms" \directory -> do
            (_,store) <- Store.openStore (directory Posix.</> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight
            bracket (pure store) Store.closeStore \opened -> do
                base <- checkFileWithStore opened Verification.FreshStoreValidation
                    ignoredVerificationRequests prover "test/phase7/composition-forms-base.tex" >>= expectRight
                assertTypedSuccess "calculation forms base" (fst base)
                let noAtp = Verification.verificationRequestObserver \_ _ ->
                        assertFailure "calculation selection, conditions, or composition invoked ATP"
                    check = checkFileWithStore opened Verification.WarmStoreValidation noAtp prover
                    reject name diagnostic failure = do
                        assertBool (show failure)
                            (diagnostic `StrictText.isInfixOf` Verification.renderVerificationDriverError failure)
                        when (name == "formation" || name == "ordinary-formation") $
                            case failure of
                                Verification.VerificationTypedModuleError _ (Module.TypedActionFailed
                                        (Module.TypedProofFailed (Proof.ProofElaborationFailed problem))) _ -> case problem of
                                    Elaboration.ElaborationFormationRequirementMissing{} -> pure ()
                                    Elaboration.ElaborationFormationSearchFailed{} -> pure ()
                                    _ -> assertFailure ("expected an ordinary formation rejection: " <> show problem)
                                _ -> assertFailure ("expected a formation rejection: " <> show failure)
                for_ ["test/phase7/composition-forms.tex", "test/phase7/composition-forms.tex",
                        "test/phase7/composition-generalized-direct.tex", "test/phase7/composition-generalized-diamond-root.tex",
                        "test/phase7/composition-conflict-left.tex", "test/phase7/composition-conflict-right.tex",
                        "test/phase7/composition-condition-base.tex", "test/phase7/composition-whole-conditions.tex",
                        "test/phase7/composition-equality-condition.tex", "test/phase7/composition-equality-condition.tex"] \path -> do
                    result <- check path >>= expectRight
                    assertTypedSuccess path (fst result)
                for_ [("missing-law", "no composition"), ("parameter-mismatch", "no composition"),
                        ("self-registration", "no composition"),
                        ("missing-condition", "condition 2"), ("missing-equality", "condition 1"), ("erased-capture", "captures an endpoint"),
                        ("undetermined", "every composition parameter"), ("overlap", "overlapping composition"),
                        ("formation", "formation"), ("ordinary-formation", "formation"),
                        ("condition-exhaustion", "524288")] \(name,diagnostic) ->
                    check ("test/phase7/composition-reject-" <> name <> ".tex") >>= \case
                        Left failure -> reject name diagnostic failure
                        Right (Verification.VerificationCheckingFailure _ failure,_) -> reject name diagnostic failure
                        Right result -> assertFailure (name <> " was accepted: " <> show (fst result))
                for_ ["union","reverse"] \order ->
                    check ("test/phase7/composition-conflict-" <> order <> ".tex") >>= \case
                        Left failure -> assertBool (show failure)
                            ("overlapping composition" `StrictText.isInfixOf` Verification.renderVerificationDriverError failure)
                        Right (Verification.VerificationCheckingFailure _ failure,_) -> assertBool (show failure)
                            ("overlapping composition" `StrictText.isInfixOf` Verification.renderVerificationDriverError failure)
                        Right result -> assertFailure ("conflicting imports were accepted: " <> show (fst result))

assertProofParityFailure
    :: Foundation.CheckedFoundation
    -> Module.BootstrapPreludeFixture
    -> SourceMounts
    -> FilePath
    -> (Proof.ProofError -> Bool)
    -> Assertion
assertProofParityFailure foundation bootstrap mounts relative matches = do
    workspace <- parseWorkspace bootstrap mounts relative
    parsed <- sole "invalid proof-parity module"
        (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
    input <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            parsed
            [])
    runTypedModule input >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedProofFailed failure))
                prefix -> do
            assertBool ("unexpected proof failure: " <> show failure)
                (matches failure)
            assertBool "failing proof publishes no declaration"
                (null (Commit.pendingModulePrefixBatches prefix))
        Module.TypedModuleSucceeded{} ->
            assertFailure "invalid proof-parity module succeeded"
        Module.TypedModuleOpenFailed failure ->
            assertFailure
                ("invalid proof-parity module did not open: " <> show failure)
        Module.TypedModuleFailed failure _prefix ->
            assertFailure
                ("unexpected proof-parity module failure: " <> show failure)

compilesSeparationComprehensions :: Assertion
compilesSeparationComprehensions =
    Temp.withSystemTempDirectory "felix-exact-separation" \root -> do
        let relative = "test/phase5/exact-separation.tex"
            executable = root Posix.</> "vampire"
            failedSource = root Posix.</> relative
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace bootstrap mounts relative
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-separation'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        observations <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    request =
                        Provers.preparedTypedProverRequest prepared
                    globals =
                        Backend.typedProblemGlobalPremises problem
                modifyIORef' observations
                    (<> [ ( Backend.typedProblemRoute problem
                           , Backend.typedBackendFactReference <$> globals
                           , all
                                (\fact ->
                                    case Backend.typedBackendFactCapability fact of
                                        Backend.FofProjectable{} -> True
                                        Backend.RequiresTh0{} -> False)
                                globals
                           , Backend.localPremiseOrdinalValue
                                . Backend.typedLocalPremiseOrdinal
                                <$> Vector.toList
                                    (Backend.typedProblemLocalPremises problem)
                           , Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                           , Provers.preparedVerificationRequestId request
                           , Provers.preparedVerificationByteCount request
                           )
                        ])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        modules <- compileParsedWorkspaceWithResolver
            foundation bootstrap resolver workspace
        sealed <- sole "exact separation module" modules
        assertSeparationModule "fresh" sealed
        definition <- batchByAlias
            (Module.completedTypedModulePrefix sealed)
            "phase5_separation_definition"
        let definitionFacts =
                Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta definition)
        extensional <- sole "searchable separation view"
            [ Semantic.semanticFactFingerprint occurrence
            | occurrence <- definitionFacts
            , Semantic.semanticFactSearchEligibility occurrence
                == Semantic.SearchEligible
            ]
        equation <- sole "internal separation equation"
            [ Semantic.semanticFactFingerprint occurrence
            | occurrence <- definitionFacts
            , Semantic.semanticFactSearchEligibility occurrence
                == Semantic.SearchIneligible
            ]
        readIORef observations >>= \case
            [ ( Backend.RouteFof
              , selectedGlobals
              , True
              , [0]
              , []
              , _requestId
              , requestBytes
              ) ] -> do
                assertBool "searchable separation view is selected"
                    (extensional `elem` selectedGlobals)
                assertBool "exact separation equation is not selected"
                    (equation `notElem` selectedGlobals)
                assertBool "separation exact request has bytes"
                    (requestBytes > 0)
            observed ->
                assertFailure
                    ("unexpected implicit separation problem: "
                        <> show observed)

        createDirectoryIfMissing True (Posix.takeDirectory failedSource)
        original <- ByteString.readFile relative
        let invalid =
                Text.encodeUtf8
                    (StrictText.replace
                        "x \\in A \\mid x = x"
                        "x \\in x \\mid x = x"
                        (Text.decodeUtf8 original))
        ByteString.writeFile failedSource invalid
        failedMounts <- exactFixtureMounts root
        failedWorkspace <-
            parseWorkspace bootstrap failedMounts relative
        let parsed = Parsed.parsedWorkspaceRootModule failedWorkspace
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed
                            (Elaboration.ElaborationFreeVariable location
                                (Raw.NamedVar "x"))))
                    prefix -> do
                assertEqual "invalid separation bound line"
                    2 (locLine location)
                assertEqual
                    "invalid separation publishes none of its declaration"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure "invalid separation was accepted"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("invalid separation module did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected invalid separation failure: "
                        <> show failure)

compilesAndReusesProofLocalSetDefinitions :: Assertion
compilesAndReusesProofLocalSetDefinitions =
    Temp.withSystemTempDirectory "felix-exact-local-definition" \root -> do
        let relative = "test/phase5/exact-local-definition.tex"
            failedRelative =
                "test/phase5/exact-local-definition-failure.tex"
            sourcePath = root Posix.</> relative
            failedSourcePath = root Posix.</> failedRelative
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        createDirectoryIfMissing True (Posix.takeDirectory sourcePath)
        ByteString.readFile relative >>= ByteString.writeFile sourcePath
        createDirectoryIfMissing True (Posix.takeDirectory failedSourcePath)
        ByteString.readFile failedRelative
            >>= ByteString.writeFile failedSourcePath
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        freshRuns <- newIORef (0 :: Int)
        observations <- newIORef []
        let freshResolver = Declaration.vampireResolver \prepared -> do
                modifyIORef' freshRuns (+ 1)
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    premises =
                        Backend.typedProblemLocalPremises problem
                    definition =
                        Vector.find
                            ((== Backend.localPremiseOrdinal 0)
                                . Backend.typedLocalPremiseOrdinal)
                            premises
                modifyIORef' observations
                    (<> [ ( Backend.typedProblemRoute problem
                           , Vector.null
                                (Backend.typedProblemGlobalPremises problem)
                           , Backend.localPremiseOrdinalValue
                                . Backend.typedLocalPremiseOrdinal
                                <$> Vector.toList premises
                           , fmap localDefinitionShape definition
                           )
                        ])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation
                bootstrap
                freshResolver
                AlwaysMissValidation
                workspace
        assertEqual "fresh local-definition discharge count"
            1 =<< readIORef freshRuns
        assertEqual "explicit local-only automation retains the definition view"
            [ ( Backend.RouteTh0
              , True
              , [0, 1, 3]
              , Just expectedLocalDefinitionShape
              )
            ]
            =<< readIORef observations
        fresh <- sole "fresh local-definition module" freshModules
        localDefinitionBatch <- batchByAlias
            (Module.completedTypedModulePrefix fresh)
            "phase5_local_definition"
        assertEqual "proof-local definition publishes no object"
            []
            (Commit.committedBatchObjects localDefinitionBatch)
        assertEqual "proof-local definition publishes only its theorem"
            1
            (length
                (Commit.committedBatchPropositions
                    localDefinitionBatch))
        localDefinitionFact <- sole
            "proof-local definition theorem"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta
                    localDefinitionBatch))
        assertEqual "proof-local definition remains clean"
            Authority.cleanAuthoritySafety
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority localDefinitionFact))

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation
                        bootstrap
                        (countingAcceptedResolver executable warmRuns)
                        validation
                        workspace
                assertEqual "warm local-definition proof skips Vampire"
                    0 =<< readIORef warmRuns
                warm <- sole "warm local-definition module" warmModules
                assertEqual "warm local-definition semantic interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm local-definition prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))

        failedWorkspace <-
            parseWorkspace bootstrap mounts failedRelative
        let failedParsed =
                Parsed.parsedWorkspaceRootModule failedWorkspace
        failedInput <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                failedParsed
                [])
        runTypedModule failedInput >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofElaborationFailed
                                (Elaboration.ElaborationFreeVariable location
                                    (Raw.NamedVar "B")))))
                    prefix -> do
                assertEqual "self-reference rejection line"
                    6 (locLine location)
                assertBool "failed local definition publishes no theorem"
                    (null
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure "self-referential local definition was accepted"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("local-definition failure fixture did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected local-definition failure: "
                        <> show failure)
  where
    localDefinitionShape premise =
        let proposition =
                Backend.typedLocalPremiseProposition premise
        in ( fmap
                snd
                (Vector.toList
                    (Backend.supportedPropositionSupport proposition))
           , Backend.supportedPropositionTerm proposition
           )

    expectedLocalDefinitionShape =
        ( [Core.TySet, Core.TySet]
        , Core.CForall Core.TySet
            (Core.CEq Core.TyProp
                (member (Core.CBound 0) (Core.CBound 1))
                (andP
                    (member (Core.CBound 0) (Core.CBound 2))
                    (Core.CEq Core.TySet
                        (Core.CBound 0)
                        (Core.CBound 0))))
        )

    member element set =
        Core.CApp
            (Core.CApp
                (Core.CIntrinsic Core.Member)
                element)
            set

    andP = Core.CAnd

compilesAndReusesProofLocalFunctionGraphs :: Assertion
compilesAndReusesProofLocalFunctionGraphs =
    Temp.withSystemTempDirectory "felix-exact-local-function" \root -> do
        let relative = "test/phase5/exact-local-function.tex"
            failedRelative =
                "test/phase5/exact-local-function-failure.tex"
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        workspace <- parseWorkspace bootstrap mounts relative
        observations <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    premises =
                        [ ( Backend.typedProblemRoute problem
                          , fmap snd
                                (Vector.toList
                                    (Backend.supportedPropositionSupport
                                        proposition))
                          , Backend.supportedPropositionTerm proposition
                          )
                        | premise <-
                            Vector.toList
                                (Backend.typedProblemLocalPremises problem)
                        , let proposition =
                                Backend.typedLocalPremiseProposition premise
                        ]
                modifyIORef' observations (<> premises)
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap resolver
                AlwaysMissValidation workspace
        allObserved <- readIORef observations
        let observed =
                [ (route, proposition)
                | (route, support, proposition) <- allObserved
                , support == [Core.TySet, Core.TySet]
                , proposition == expectedLocalFunctionCharacteristic
                ]
        assertBool
            ("the local graph characteristic reaches a discharge: "
                <> show allObserved)
            (not (null observed))
        for_ observed \(route, proposition) -> do
            assertEqual "local function characteristic stays on FOF"
                Backend.RouteFof route
            assertLocalFunctionCharacteristic proposition
        freshRoot <- sole "fresh local-function root"
            (take 1 (reverse freshModules))
        rootBatch <- sole "local function publishes only its theorem"
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix freshRoot))
        assertEqual "local function publishes no object"
            [] (Commit.committedBatchObjects rootBatch)
        assertEqual "local function publishes only its theorem"
            1
            (length
                (Commit.committedBatchPropositions rootBatch))
        assertEqual "local function publishes no semantic binding"
            []
            (Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment
                    (Commit.committedBatchDelta rootBatch)))
        rootFact <- sole "local-function theorem"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta rootBatch))
        assertEqual "local-function theorem remains clean"
            Authority.cleanAuthoritySafety
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority rootFact))

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                traverse_
                    (expectRightIO
                        . Store.writePendingModulePrefix storeCheck
                        . Module.completedTypedModulePrefix)
                    freshModules
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation bootstrap
                        (countingAcceptedResolver executable warmRuns)
                        validation workspace
                assertEqual "warm local-function graph skips Vampire"
                    0 =<< readIORef warmRuns
                warmRoot <- sole "warm local-function root"
                    (take 1 (reverse warmModules))
                assertEqual "warm local-function semantic interface"
                    (completedModuleSemantic freshRoot)
                    (completedModuleSemantic warmRoot)
                assertEqual "warm local-function prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix freshRoot))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warmRoot))

        failedWorkspace <-
            parseWorkspace bootstrap mounts failedRelative
        failedInput <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                (Parsed.parsedWorkspaceRootModule failedWorkspace)
                [])
        runTypedModule failedInput >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedProofFailed
                            (Proof.ProofElaborationFailed
                                (Elaboration.ElaborationFreeVariable location
                                    (Raw.NamedVar "f")))))
                    prefix -> do
                assertEqual "self-reference rejection line"
                    6 (locLine location)
                assertBool "failed local function publishes no theorem"
                    (null
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure "self-referential local function was accepted"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("local-function failure fixture did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected local-function failure: "
                        <> show failure)
  where
    assertLocalFunctionCharacteristic proposition =
        assertEqual "local function uses the exact replacement characteristic"
            expectedLocalFunctionCharacteristic
            proposition

    expectedLocalFunctionCharacteristic =
        Core.CForall Core.TySet
            (Core.CEq Core.TyProp
                (member (Core.CBound 0) (Core.CBound 1))
                (existsP
                    (andP
                        (member (Core.CBound 0) (Core.CBound 3))
                        (Core.CEq Core.TySet
                            (Core.CBound 1)
                            (Core.CApp
                                (Core.CApp
                                    (Core.CIntrinsic Core.OrderedPair)
                                    (Core.CBound 0))
                                (Core.CBound 0))))))

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

    andP = Core.CAnd

    existsP = Core.CExists Core.TySet

propagatesContradictionContext :: Assertion
propagatesContradictionContext =
    Temp.withSystemTempDirectory "felix-exact-contradiction" \directory -> do
        let acceptedExecutable = directory Posix.</> "accepted-vampire"
            contradictoryExecutable = directory Posix.</> "contradictory-vampire"
            storePath = directory Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire acceptedExecutable
        writeFile contradictoryExecutable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status ContradictoryAxioms for exact-contradiction'"
                ])
        permissions <- getPermissions contradictoryExecutable
        setPermissions contradictoryExecutable
            (setOwnerExecutable True permissions)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        workspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-cases-contradiction.tex"
        assertEmptyCaseAstRejected foundation bootstrap workspace
        observations <- newIORef []
        fresh <-
            sole "cases and contradiction module"
                =<< compileParsedWorkspaceWithValidation
                    foundation
                    bootstrap
                    (observingResolver
                        acceptedExecutable
                        contradictoryExecutable
                        observations)
                    AlwaysMissValidation
                    workspace
        observed <- readIORef observations
        case observed of
            [exhaustive] -> do
                assertEqual "exhaustiveness sees pre-case locals only"
                    [] (localReasoningLocalOrdinals exhaustive)
                case localReasoningTarget exhaustive of
                    Core.COr (Core.COr _first _second) _third -> pure ()
                    target ->
                        assertFailure
                            ("case exhaustiveness is not left-associated: "
                                <> show target)
            _ ->
                assertFailure
                    ("unexpected cases/contradiction observations: "
                        <> show observed)
        case Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix fresh) of
            [ caseBatch
              , byContradictionBatch
              , terminalBatch
              , caseContradictionBatch
              , omittedBatch
              ] -> do
                traverse_
                    (assertBatchSafety Authority.cleanAuthoritySafety)
                    [ caseBatch
                    , byContradictionBatch
                    , terminalBatch
                    , caseContradictionBatch
                    ]
                assertBatchSafety
                    (Authority.authoritySafety
                        (Authority.singletonEscapeKind Authority.Omitted))
                    omittedBatch
            batches ->
                assertFailure
                    ("unexpected cases/contradiction declaration count: "
                        <> show (length batches))

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warm <-
                    sole "warm cases and contradiction module"
                        =<< compileParsedWorkspaceWithValidation
                            foundation
                            bootstrap
                            (countingAcceptedResolver
                                acceptedExecutable warmRuns)
                            validation
                            workspace
                assertEqual "warm structural proofs skip Vampire"
                    0 =<< readIORef warmRuns
                assertEqual "fresh and warm structural proof validations"
                    (proofValidations fresh)
                    (proofValidations warm)

        failureWorkspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-case-failure.tex"
        assertCaseFailure
            "middle case branch"
            foundation bootstrap failureWorkspace acceptedExecutable 1 2
        assertCaseFailure
            "case exhaustiveness"
            foundation bootstrap failureWorkspace acceptedExecutable 3 4

        directWorkspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-direct-contradictory.tex"
        directParsed <- sole "direct contradictory parsed module"
            (toList
                (Parsed.parsedWorkspaceImportedBeforeImporter directWorkspace))
        directInput <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                (Declaration.vampireResolver
                    (runWith contradictoryExecutable))
                AlwaysMissValidation
                directParsed
                [])
        runTypedModule directInput >>= \case
            Module.TypedModuleFailed
                    (Module.TypedDeclarationFailed
                        (Declaration.ProofObligationFailedAt
                            _location
                            Declaration.VampireObligationFailed{}))
                    prefix ->
                assertBool
                    "direct contradictory input publishes no theorem"
                    (null (Commit.pendingModulePrefixBatches prefix))
            _result ->
                assertFailure "direct contradictory input was accepted"
  where
    observingResolver acceptedExecutable contradictoryExecutable observations =
        Declaration.vampireResolver \prepared -> do
            let problem = Provers.preparedTypedProverLogicalProblem prepared
                claim = Backend.typedProblemClaim problem
                locals = Backend.typedProblemLocalPremises problem
                target = Backend.supportedPropositionTerm claim
            modifyIORef' observations
                (<> [ LocalReasoningObservation
                        { localReasoningTarget = target
                        , localReasoningGlobalCount =
                            Vector.length
                                (Backend.typedProblemGlobalPremises problem)
                        , localReasoningLocalOrdinals =
                            [ Backend.localPremiseOrdinalValue
                                (Backend.typedLocalPremiseOrdinal premise)
                            | premise <- Vector.toList locals
                            ]
                        , localReasoningLocalTerms =
                            Backend.supportedPropositionTerm
                                . Backend.typedLocalPremiseProposition
                                <$> Vector.toList locals
                        , localReasoningAuxiliaries =
                            Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                        }
                    ])
            runWith
                (if target == Core.CFalsum
                        || any
                            (\premise ->
                                case Backend.supportedPropositionTerm
                                    (Backend.typedLocalPremiseProposition
                                        premise) of
                                    Core.CNot negatedGoal ->
                                        negatedGoal /= target
                                    _ ->
                                        False)
                            (Vector.toList locals)
                    then contradictoryExecutable
                    else acceptedExecutable)
                prepared

    runWith executable prepared =
        (Provers.runPreparedTypedProver
                (Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                prepared)

    assertEmptyCaseAstRejected foundation bootstrap workspace = do
        parsed <- sole "cases parsed module"
            (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        let blocks =
                Parsed.identifiedParsedModuleBlocks
                    (Parsed.parsedModuleIdentified parsed)
        claim <- sole "cases source claim"
            [ candidate
            | candidate@Raw.BlockClaim{} <- take 1 blocks
            ]
        location <-
            case
                [ found
                | Raw.BlockProof _ (Raw.ByCase found _cases) _ <- blocks
                ] of
                found : _ -> pure found
                [] ->
                    assertFailure "cases source proof is absent"
                        >> fail "unreachable"
        let preludeModule = Module.bootstrapPreludeCompleted bootstrap
        outcome <- runModuleDriver
            foundation
            (moduleName (Parsed.parsedModuleAddress parsed))
            [completedModuleEvidence preludeModule]
            unusedResolver
            AlwaysMissValidation do
                Declaration.runProspectiveLoweringDriver
                    (Proof.prepareProof
                        claim
                        (Just (Raw.ByCase location [])))
        case outcome of
            Right (Declaration.DriverSucceeded
                    (Left (Proof.ProofEmptyCaseSplit found))
                    _semantic prefix) -> do
                assertEqual "empty case AST failure location"
                    location found
                assertBool "empty case AST publishes no declaration"
                    (null (Commit.pendingModulePrefixBatches prefix))
            _ ->
                assertFailure "empty programmatic case split was not rejected"

    assertBatchSafety expected batch = do
        fact <- sole "structural proof fact"
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta batch))
        assertEqual "structural proof authority safety"
            expected
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority fact))

    proofValidations =
        concatMap Commit.committedBatchProofValidations
            . Commit.pendingModulePrefixBatches
            . Module.completedTypedModulePrefix

    assertCaseFailure
            label foundation bootstrap workspace executable rejectedIndex
            expectedRuns = do
        runs <- newIORef (0 :: Int)
        parsed <- sole (label <> " parsed module")
            (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    index <- atomicModifyIORef' runs \current ->
                        (current + 1, current)
                    if index == rejectedIndex
                        then pure
                            (counterexampleResolution prepared)
                        else runWith executable prepared
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                resolver
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed _failure prefix ->
                assertBool
                    (label <> " publishes no declaration")
                    (null (Commit.pendingModulePrefixBatches prefix))
            _result ->
                assertFailure (label <> " unexpectedly succeeded")
        assertEqual
            (label <> " selects failures in source order")
            expectedRuns =<< readIORef runs

dischargesHigherOrderBinaryCaseExhaustivenessStructurally :: Assertion
dischargesHigherOrderBinaryCaseExhaustivenessStructurally =
    Temp.withSystemTempDirectory "felix-typed-case-analysis" \directory -> do
        let executable = directory Posix.</> "accepted-vampire"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        workspace <- parseWorkspace bootstrap mounts
            "test/phase8/typed-by-case.tex"
        observations <- newIORef []
        sealed <-
            compileParsedWorkspaceWithValidation
                foundation
                bootstrap
                (observingResolver executable observations)
                AlwaysMissValidation
                workspace
        assertEqual "typed binary case module count"
            1 (length sealed)
        assertEqual
            "only case bodies request local ATP; exhaustiveness is structural"
            [(0, 1), (0, 1)]
            =<< readIORef observations
  where
    observingResolver executable observations =
        Declaration.vampireResolver \prepared -> do
            let problem =
                    Provers.preparedTypedProverLogicalProblem prepared
            modifyIORef' observations
                (<> [ ( Vector.length
                            (Backend.typedProblemGlobalPremises problem)
                       , Vector.length
                            (Backend.typedProblemLocalPremises problem)
                       )
                    ])
            Provers.runPreparedTypedProver
                (Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                prepared

dischargesExactLocalCaseDisjunctionStructurally :: Assertion
dischargesExactLocalCaseDisjunctionStructurally =
    Temp.withSystemTempDirectory "felix-exact-local-cases" \directory -> do
        let executable = directory Posix.</> "accepted-vampire"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        workspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-local-disjunction-cases.tex"
        observedTargets <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    target =
                        Backend.supportedPropositionTerm
                            (Backend.typedProblemClaim problem)
                    localTerms =
                        Backend.supportedPropositionTerm
                            . Backend.typedLocalPremiseProposition
                            <$> Vector.toList
                                (Backend.typedProblemLocalPremises problem)
                when (target `elem` localTerms)
                    (assertFailure
                        "exact local case exhaustiveness reached Vampire")
                modifyIORef' observedTargets (<> [target])
                Provers.runPreparedTypedProver
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared
        sealed <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap resolver AlwaysMissValidation workspace
        assertEqual "exact-local case module count" 1 (length sealed)
        targets <- readIORef observedTargets
        assertEqual "only the two case bodies require Vampire" 2 (length targets)
        assertBool
            "both remaining case obligations are equalities"
            (all isEquality targets)
  where
    isEquality = \case
        Core.CEq{} -> True
        _ -> False

compilesReplacementComprehensions :: Assertion
compilesReplacementComprehensions =
    Temp.withSystemTempDirectory "felix-exact-replacement" \root -> do
        let relative = "test/phase5/exact-replacement.tex"
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        foundation <- expectRight Foundation.checkedFoundation
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-replacement'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        let prover =
                Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
            preludeResolver =
                Declaration.vampireResolver
                    (Provers.runPreparedTypedProver prover)
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \opened -> do
            prelude <-
                expectRight
                    =<< acquireFinalPreludeSession
                        opened foundation preludeResolver
            setextDelta <- sole "set extensionality declaration"
                [delta | delta <- Semantic.semanticInterfaceDeclarations
                    (Module.sealedTypedModuleSemantic (Module.finalPreludeModule prelude)),
                    any ((== Semantic.semanticName "setext") . Semantic.semanticAliasName)
                        (Semantic.declarationDeltaAliases delta)]
            setextView <- sole "set extensionality view"
                [Semantic.semanticFactFingerprint fact | fact <- Semantic.declarationDeltaFacts setextDelta,
                    Semantic.semanticFactSearchEligibility fact == Semantic.SearchEligible]
            mounts <- exactFixtureMounts =<< getCurrentDirectory
            workspace <- parseFinalWorkspace prelude mounts relative
            observations <- newIORef []
            let resolver = Declaration.vampireResolver \prepared -> do
                    let problem =
                            Provers.preparedTypedProverLogicalProblem prepared
                        request =
                            Provers.preparedTypedProverRequest prepared
                    modifyIORef' observations
                        (<> [ ( Backend.typedProblemRoute problem
                               , Provers.preparedVerificationDialect request
                               , Backend.typedBackendFactReference
                                    <$> Vector.toList
                                        (Backend.typedProblemGlobalPremises
                                            problem)
                               , Backend.typedProblemAuxiliaryTag
                                    <$> Vector.toList
                                        (Backend.typedProblemAuxiliaries problem)
                               )
                            ])
                    (Provers.runPreparedTypedProver
                            prover
                            prepared)
            modules <- compileFinalParsedWorkspaceWithResolver
                foundation prelude resolver workspace
            sealed <- sole "exact replacement module" modules
            (replacementView, separationView) <-
                assertReplacementModule sealed
            readIORef observations >>= \case
                [ ( Backend.RouteFof
                  , Provers.VerificationFof
                  , extensionalityPremises
                  , []
                  )
                  , ( Backend.RouteFof
                    , Provers.VerificationFof
                    , definitionPremises
                    , []
                  )
                  ] -> do
                    assertEqual
                        "set extensionality step cites setext"
                        [setextView]
                        extensionalityPremises
                    assertEqual
                        "definition step cites both public extensional views"
                        (sort [replacementView, separationView])
                        (sort definitionPremises)
                observed ->
                    assertFailure
                        ("unexpected replacement proof problems: "
                            <> show observed)

assertReplacementModule
    :: Module.CompletedTypedModule
    -> IO
        ( Semantic.SemanticFactOccurrenceFingerprint
        , Semantic.SemanticFactOccurrenceFingerprint
        )
assertReplacementModule sealed =
    case Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed) of
        [replacementBatch, separationBatch, theoremBatch] -> do
            definitionObject <- sole
                "replacement definition object"
                (Commit.committedBatchObjects replacementBatch)
            case Identity.assertedObjectContent definitionObject of
                Identity.TransparentObjectContent
                        _theory coreType body -> do
                    assertEqual "replacement definition type"
                        (Core.TyArrow Core.TySet Core.TySet)
                        coreType
                    assertEqual "replacement definition body"
                        expectedBody
                        body
                    assertEqual "replacement definition foundation helpers"
                        (Set.fromList
                            [ Foundation.FamilyUnionCharacteristic
                            , Foundation.SeparationCharacteristic
                            , Foundation.ReplacementCharacteristic
                            ])
                        (Foundation.foundationAxiomDependencies body)
                content ->
                    assertFailure
                        ("unexpected replacement object " <> show content)
            let definitionDelta =
                    Commit.committedBatchDelta replacementBatch
                definitionFacts =
                    Semantic.declarationDeltaFacts definitionDelta
            assertEqual "replacement definition fact count"
                2 (length definitionFacts)
            assertEqual "replacement equation/search view eligibility"
                [Semantic.SearchIneligible, Semantic.SearchEligible]
                (Semantic.semanticFactSearchEligibility <$> definitionFacts)
            assertEqual "replacement canonical view kinds"
                [ Semantic.DefinitionPointwiseView
                , Semantic.DefinitionMembershipView
                ]
                ( Semantic.semanticDefinitionViewKind
                    <$> Semantic.declarationDeltaDefinitionViews
                        definitionDelta
                )
            assertConstructionAliasTargetsFirstOrderView
                "replacement definition" replacementBatch
            assertEqual "replacement definition proposition count"
                2
                (length
                    (Commit.committedBatchPropositions replacementBatch))
            assertEqual "replacement definition proof validations"
                []
                (Commit.committedBatchProofValidations replacementBatch)
            definitionValidation <-
                maybe
                    (assertFailure "replacement validation is absent"
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation
                        replacementBatch)
            case Authority.validationDirectAuthorization
                    <$> Semantic.declarationValidationRecordCertificates
                        definitionValidation of
                [ Authority.CheckedKernelConstruction
                        (Authority.CheckedDefinitionEquation target)
                  , Authority.CheckedKernelConstruction
                        (Authority.CheckedSetConstructionExtensionality
                            generatedTarget _descriptor)
                  ] ->
                    assertEqual "replacement construction authority object"
                        target generatedTarget
                authorizations ->
                    assertFailure
                        ("unexpected replacement definition authorities "
                            <> show authorizations)

            assertEqual "separation definition object count"
                1
                (length
                    (Commit.committedBatchObjects separationBatch))
            let separationFacts =
                    Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta separationBatch)
            assertEqual "separation equation/search view eligibility"
                [Semantic.SearchIneligible, Semantic.SearchEligible]
                (Semantic.semanticFactSearchEligibility <$> separationFacts)
            assertEqual "separation canonical view kinds"
                [ Semantic.DefinitionPointwiseView
                , Semantic.DefinitionMembershipView
                ]
                ( Semantic.semanticDefinitionViewKind
                    <$> Semantic.declarationDeltaDefinitionViews
                        (Commit.committedBatchDelta separationBatch)
                )
            assertConstructionAliasTargetsFirstOrderView
                "separation definition" separationBatch
            assertEqual "separation definition proposition count"
                2
                (length
                    (Commit.committedBatchPropositions separationBatch))
            assertEqual "separation definition proof validations"
                []
                (Commit.committedBatchProofValidations separationBatch)

            assertEqual "replacement theorem adds no object"
                []
                (Commit.committedBatchObjects theoremBatch)
            assertEqual "replacement theorem fact count"
                1
                (length
                    (Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta theoremBatch)))
            assertEqual "replacement theorem proposition count"
                1
                (length
                    (Commit.committedBatchPropositions theoremBatch))
            theoremValidation <- sole
                "replacement theorem validation"
                (Commit.committedBatchProofValidations theoremBatch)
            case Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate
                        theoremValidation) of
                Authority.CheckedSourceProof
                        (Authority.UsesExternalProof
                            (_extensionalityRequest
                                :| [_definitionRequest])) -> do
                    replacementView <- searchableFactFingerprint
                        "replacement public view" replacementBatch
                    separationView <- searchableFactFingerprint
                        "separation public view" separationBatch
                    pure (replacementView, separationView)
                authorization ->
                    assertFailure
                        ("unexpected replacement theorem authority "
                            <> show authorization)
                        >> fail "unreachable"
        batches ->
            assertFailure
                ("expected replacement, separation, and theorem, found "
                    <> show (length batches))
                >> fail "unreachable"
  where
    app1 intrinsic argument =
        Core.CApp (Core.CIntrinsic intrinsic) argument
    app2 intrinsic first second =
        Core.CApp (app1 intrinsic first) second
    expectedBody =
        Core.CLam Core.TySet $
            app1 Core.FamilyUnion $
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
                                (Core.CBound 0))

usesFirstOrderDefinitionsInImplicitObviousInference :: Assertion
usesFirstOrderDefinitionsInImplicitObviousInference =
    Temp.withSystemTempDirectory "felix-first-order-implicit" \root -> do
        let relative = "test/phase5/exact-first-order-implicit.tex"
            executable = root Posix.</> "vampire"
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        workspace <- parseWorkspace bootstrap mounts relative
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for first-order-implicit'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        observations <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    request =
                        Provers.preparedTypedProverRequest prepared
                    globals =
                        Vector.toList
                            (Backend.typedProblemGlobalPremises problem)
                modifyIORef' observations
                    (<> [ ( Backend.typedProblemRoute problem
                           , Provers.preparedVerificationDialect request
                           , Backend.typedBackendFactReference <$> globals
                           , all
                                (\fact ->
                                    case Backend.typedBackendFactCapability fact of
                                        Backend.FofProjectable{} -> True
                                        Backend.RequiresTh0{} -> False)
                                globals
                           , Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                           , Provers.preparedVerificationRequestId request
                           , Provers.preparedVerificationByteCount request
                           )
                        ])
                Provers.runPreparedTypedProver
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared
        modules <- compileParsedWorkspaceWithResolver
            foundation bootstrap resolver workspace
        sealed <- sole "first-order implicit module" modules
        case Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed) of
            [definitionBatch, theoremBatch] -> do
                definitionAlias <- sole
                    "first-order definition alias"
                    (Semantic.declarationDeltaAliases
                        (Commit.committedBatchDelta definitionBatch))
                definitionFact <- sole
                    "first-order definition fact"
                    [ fact
                    | fact <- Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta definitionBatch)
                    , Semantic.semanticFactFingerprint fact ==
                        Semantic.semanticAliasTarget definitionAlias
                    ]
                assertEqual "first-order definition remains searchable"
                    Semantic.SearchEligible
                    (Semantic.semanticFactSearchEligibility definitionFact)
                let definitionFingerprint =
                        Semantic.semanticFactFingerprint definitionFact
                assertEqual "definition alias targets its first-order fact"
                    definitionFingerprint
                    (Semantic.semanticAliasTarget definitionAlias)
                definitionProposition <- sole
                    "first-order definition proposition"
                    [ proposition
                    | proposition <- Commit.committedBatchPropositions definitionBatch
                    , Identity.checkedPropositionId proposition ==
                        Semantic.semanticFactProposition definitionFact
                    ]
                assertEqual "definition fact is FOF-projectable"
                    Foundation.FoundationFofProjectable
                    (Foundation.classifyFrozenCore
                        (Identity.checkedPropositionTerm
                            definitionProposition))

                theoremValidation <- sole
                    "implicit theorem validation"
                    (Commit.committedBatchProofValidations theoremBatch)
                assertEqual
                    "implicit obvious inference needs no ATP authority"
                    (Authority.CheckedSourceProof Authority.NoExternalProofUse)
                    (Authority.validationDirectAuthorization
                        (Semantic.proofValidationRecordCertificate
                            theoremValidation))
                assertEqual
                    "implicit obvious inference sends no Vampire request"
                    []
                    =<< readIORef observations
            batches ->
                assertFailure
                    ("expected first-order definition and theorem, found "
                        <> show (length batches))

searchableFactFingerprint
    :: String
    -> Commit.CommittedDeclarationBatch
    -> IO Semantic.SemanticFactOccurrenceFingerprint
searchableFactFingerprint label batch =
    sole label
        [ Semantic.semanticFactFingerprint occurrence
        | occurrence <- Semantic.declarationDeltaFacts
            (Commit.committedBatchDelta batch)
        , Semantic.semanticFactSearchEligibility occurrence
            == Semantic.SearchEligible
        ]

compilesAndReusesRelationalReplacement :: Assertion
compilesAndReusesRelationalReplacement =
    Temp.withSystemTempDirectory "felix-exact-relational-replacement" \root -> do
        let relative = "test/phase5/exact-relational-replacement.tex"
            failureRelative =
                "test/phase5/exact-relational-replacement-failure.tex"
            localFailureRelative =
                "test/phase5/exact-relational-replacement-local-failure.tex"
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        workspace <- parseWorkspace bootstrap mounts relative
        observed <- newIORef []
        runs <- newIORef (0 :: Int)
        let resolver = Declaration.vampireResolver \prepared -> do
                modifyIORef' runs (+ 1)
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                modifyIORef' observed
                    (<> [ ( Backend.typedProblemRoute problem
                           , Backend.localPremiseOrdinalValue
                                . Backend.typedLocalPremiseOrdinal
                                <$> Vector.toList
                                    (Backend.typedProblemLocalPremises problem)
                           , Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                           )
                        ])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap resolver
                AlwaysMissValidation workspace
        fresh <- sole "fresh relational replacement module" freshModules
        assertRelationalReplacementModule fresh
        problems <- readIORef observed
        assertEqual "relational replacement request count"
            2 (length problems)
        firstProblem <- sole "module functionality request" (take 1 problems)
        assertEqual "module functionality uses FOF"
            Backend.RouteFof
            (case firstProblem of (route, _, _) -> route)
        assertEqual "module functionality has no local premises"
            []
            (case firstProblem of (_, ordinals, _) -> ordinals)
        assertEqual
            "only local singleton functionality requests set-constructor auxiliaries"
            [ (Backend.RouteFof, [], [])
            , (Backend.RouteFof, [],
                [Foundation.EmptyCharacteristic, Foundation.PairSetCharacteristic, Foundation.FamilyUnionCharacteristic])
            ]
            problems

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation bootstrap
                        (countingAcceptedResolver executable warmRuns)
                        validation workspace
                assertEqual "warm relational replacement skips Vampire"
                    0 =<< readIORef warmRuns
                warm <- sole "warm relational replacement module" warmModules
                assertEqual "warm relational replacement interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm relational replacement prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))

        let rejectingResolver =
                Declaration.vampireResolver \prepared ->
                    pure (counterexampleResolution prepared)
            runRejected relativePath = do
                failedWorkspace <-
                    parseWorkspace bootstrap mounts relativePath
                input <- expectRightIO
                    (typedModuleInput
                        foundation
                        (Module.bootstrapPreludeReadiness bootstrap)
                        rejectingResolver
                        AlwaysMissValidation
                        (Parsed.parsedWorkspaceRootModule failedWorkspace)
                        [])
                runTypedModule input
        runRejected failureRelative >>= \case
            Module.TypedModuleFailed _failure prefix -> do
                batches <- pure
                    (Commit.pendingModulePrefixBatches prefix)
                assertEqual "failed relational definition keeps its prefix"
                    1 (length batches)
                prefixBatch <- sole "relational prefix declaration" batches
                assertEqual "failed relational definition publishes no object"
                    1 (length
                        (Commit.committedBatchObjects prefixBatch))
            _result ->
                assertFailure
                    "nonfunctional relational definition did not fail"
        runRejected localFailureRelative >>= \case
            Module.TypedModuleFailed _failure prefix ->
                assertBool
                    "failed local functionality publishes no theorem"
                    (null
                        (Commit.pendingModulePrefixBatches prefix))
            _result ->
                assertFailure
                    "nonfunctional local definition did not fail"

assertRelationalReplacementModule
    :: Module.CompletedTypedModule
    -> Assertion
assertRelationalReplacementModule sealed =
    case Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed) of
        [_axiomBatch, definitionBatch, proofBatch] -> do
            _object <- sole "relational replacement object"
                (Commit.committedBatchObjects definitionBatch)
            let definitionFacts =
                    Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta definitionBatch)
            assertEqual "relational replacement fact eligibility"
                [ Semantic.SearchIneligible
                , Semantic.SearchIneligible
                , Semantic.SearchEligible
                ]
                (Semantic.semanticFactSearchEligibility <$> definitionFacts)
            let sourceSafety =
                    Authority.authoritySafety
                        (Authority.singletonEscapeKind Authority.SourceAxiom)
            assertEqual "relational extensionality inherits functionality safety"
                [ Authority.cleanAuthoritySafety
                , sourceSafety
                , sourceSafety
                ]
                ( Authority.factAuthoritySafety
                    . Semantic.semanticFactAuthority
                    <$> definitionFacts
                )
            assertConstructionAliasTargetsFirstOrderView
                "relational replacement" definitionBatch
            validation <-
                maybe
                    (assertFailure "relational replacement validation absent"
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation
                        definitionBatch)
            case Authority.validationDirectAuthorization
                    <$> Semantic.declarationValidationRecordCertificates
                        validation of
                [ Authority.CheckedKernelConstruction
                        (Authority.CheckedDefinitionEquation equationObject)
                  , Authority.CheckedSourceProof
                        (Authority.UsesExternalProof
                            (_functionalityRequest :| []))
                  , Authority.CheckedKernelConstruction
                        (Authority.CheckedSetConstructionExtensionality
                            extensionalObject _descriptor)
                  ] ->
                    assertEqual "relational facts target one object"
                        equationObject extensionalObject
                authorizations ->
                    assertFailure
                        ("unexpected relational authorities "
                            <> show authorizations)
            assertEqual "module construction generates no proof row"
                []
                (Commit.committedBatchProofValidations definitionBatch)

            proofValidation <- sole "proof-local relational validation"
                (Commit.committedBatchProofValidations proofBatch)
            case Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate
                        proofValidation) of
                Authority.CheckedSourceProof requests ->
                    assertEqual
                        "only local functionality needs Vampire"
                        1
                        (length (Authority.externalProofUseRequests requests))
                authorization ->
                    assertFailure
                        ("unexpected proof-local relational authority "
                            <> show authorization)
            proofFact <- sole "proof-local relational theorem"
                (Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta proofBatch))
            assertEqual "local extensional premise retains discharge safety"
                sourceSafety
                (Authority.factAuthoritySafety
                    (Semantic.semanticFactAuthority proofFact))
        batches ->
            assertFailure
                ("expected relational axiom, definition, and proof, found "
                    <> show (length batches))

compilesAndReusesFiniteSets :: Assertion
compilesAndReusesFiniteSets =
    Temp.withSystemTempDirectory "felix-exact-finite-set" \root -> do
        let relative = "test/phase5/exact-finite-set.tex"
            sourcePath = root Posix.</> relative
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        createDirectoryIfMissing True (Posix.takeDirectory sourcePath)
        ByteString.readFile relative >>= ByteString.writeFile sourcePath
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-finite-set'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        observations <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                modifyIORef' observations
                    (<> [ ( Backend.typedProblemRoute problem
                           , Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                           )
                        ])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap resolver
                AlwaysMissValidation
                workspace
        fresh <- sole "fresh finite-set module" freshModules
        assertFiniteSetModule "fresh" fresh
        assertEqual
            "finite-set proof uses exactly its FOF characteristics"
            [( Backend.RouteFof
             , [ Foundation.EmptyCharacteristic
               , Foundation.PairSetCharacteristic
               , Foundation.FamilyUnionCharacteristic
               ]
             )]
            =<< readIORef observations

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation bootstrap
                        (countingAcceptedResolver executable warmRuns)
                        validation
                        workspace
                assertEqual "warm finite-set proof skips Vampire"
                    0
                    =<< readIORef warmRuns
                warm <- sole "warm finite-set module" warmModules
                assertFiniteSetModule "warm" warm
                assertEqual "warm finite-set semantic interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm finite-set final prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))

checkedInductiveTerm
    :: GlobalTyping.GlobalTyping global
    -> [TypedInductive.InductiveBinder]
    -> [Core.CoreType]
    -> Core.CanonicalTerm global
    -> IO (TypedInductive.CheckedInductiveTerm global)
checkedInductiveTerm globalType variables context term = do
    scoped <-
        expectRight
            (Core.checkScopedCanonicalCore
                globalType context term)
    expectRight
        (TypedInductive.prepareCheckedInductiveTerm
            globalType variables scoped)

checkedInductiveContext
    :: GlobalTyping.GlobalTyping global
    -> [TypedInductive.InductiveBinder]
    -> Core.CanonicalTerm global
    -> IO (TypedInductive.RecursiveCarrierContext global)
checkedInductiveContext globalType variables body = do
    scoped <-
        expectRight
            (Core.checkScopedCanonicalCore
                globalType
                (replicate (length variables + 1) Core.TySet)
                body)
    expectRight
        (TypedInductive.prepareRecursiveCarrierContext
            globalType Nowhere False variables scoped)

preparesDirectInductives :: Assertion
preparesDirectInductives = do
    foundation <- expectRight Foundation.checkedFoundation
    prepared <-
        expectRight
            =<< prepareInductiveFixture
                "test/phase5/exact-inductive.tex"
    assertEqual "exact inductive carrier type"
        (Core.TyArrow Core.TySet Core.TySet)
        (Inductive.preparedInductiveCarrierType prepared)
    assertEqual "exact inductive carrier body"
        expectedCarrier
        (Core.frozenCoreTerm
            (Inductive.preparedInductiveCarrierBody prepared))
    assertEqual "foundation guard needs no imported fact"
        []
        (Vector.toList
            (Inductive.preparedInductiveGuardTargets prepared))
    let facts =
            toList
                (Inductive.preparedInductiveFacts prepared)
    assertEqual "generated fact order"
        [ "phase5_fin_intro_1"
        , "phase5_fin_dom_subset"
        , "phase5_fin_cases"
        , "phase5_fin_induct"
        ]
        (TypedInductive.typedInductiveFactMarker <$> facts)
    assertEqual "generated guarded-rule descriptors"
        [ Set.singleton Foundation.SetLfpFixed
        , Set.singleton Foundation.SetLfpBound
        , Set.singleton Foundation.SetLfpFixed
        , Set.singleton Foundation.SetLfpInduct
        ]
        ( Set.fromList
            . toList
            . TypedInductive.typedInductiveFactRules
            <$> facts
        )
    assertBool "generated targets are closed propositions"
        (all
            (\fact ->
                let target = TypedInductive.typedInductiveFactTarget fact
                in Core.frozenCoreType target == Core.TyProp
                    && Set.null (Core.frozenCoreGlobals target))
            facts)

    let singleton =
            Core.canonicalSetInsert
                (Core.CIntrinsic Core.Empty)
                (Core.CIntrinsic Core.Empty)
    domain <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping [] [] singleton
    result <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping [] [] (Core.CIntrinsic Core.Empty)
    finite <-
        expectRight
            (TypedInductive.prepareTypedInductive
                GlobalTyping.emptyGlobalTyping
                foundation
                "finite_internal"
                (TypedInductive.DirectInductive
                    []
                    domain
                    (TypedInductive.DirectInductiveClause
                        []
                        []
                        result
                        :| [])))
    finiteGuard <-
        sole
            "finite-set inductive guard"
            (Vector.toList
                (TypedInductive.typedInductiveGuardTargets finite))
    assertEqual
        "typed inductive path uses intrinsic finite-set adjunction"
        (member
            (Core.CIntrinsic Core.Empty)
            (Core.canonicalSetInsert
                (Core.CIntrinsic Core.Empty)
                (Core.CIntrinsic Core.Empty)))
        (Core.frozenCoreTerm finiteGuard)
  where
    apply1 intrinsic argument =
        Core.CApp (Core.CIntrinsic intrinsic) argument
    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set
    expectedCarrier =
        Core.CLam Core.TySet
            (Core.CApp
                (Core.CApp
                    (Core.CIntrinsic Core.ISetLfp)
                    (apply1 Core.UnivOf (Core.CBound 0)))
                (Core.CLam Core.TySet
                    (Core.CApp
                        (Core.CApp
                            (Core.CIntrinsic Core.Sep)
                            (apply1 Core.UnivOf (Core.CBound 1)))
                        (Core.CLam Core.TySet
                            (Core.CEq Core.TySet
                                (Core.CBound 0)
                                (Core.CBound 2))))))

preparesDatatypes :: Assertion
preparesDatatypes = do
    (_foundation, _owner, prepared) <-
        expectRight
            =<< prepareDatatypeFixture
                "test/phase5/datatype.tex"
    let objects =
            toList
                (Datatype.preparedDatatypeObjects prepared)
        objectIds = fst <$> objects
        objectTypes = snd <$> objects
        expectedTypes =
            [ Core.TySet
            , Core.TySet
            , Core.TyArrow Core.TySet Core.TySet
            , Core.TyArrow Core.TySet
                (Core.TyArrow Core.TySet Core.TySet)
            ]
    assertEqual "datatype transparent object types"
        expectedTypes objectTypes
    assertBool "datatype source objects are definitions"
        (all ((== Identity.TransparentObject) . Identity.objectIdFamily) objectIds)
    (carrierId, zeroId, atomId, joinId) <-
        case objectIds of
            [carrier, zero, atom, join] ->
                pure
                    ( carrier
                    , zero
                    , atom
                    , join
                    )
            _ ->
                assertFailure "datatype object inventory is incomplete"
                    >> fail "unreachable"
    let facts =
            toList
                (Datatype.preparedDatatypeFacts prepared)
        markers =
            Datatype.preparedDatatypeFactMarker <$> facts
    assertEqual "datatype generated fact order"
        [ Raw.Marker "phase5_data_phasefivezero_intro"
        , Raw.Marker "phase5_data_phasefiveatom_intro"
        , Raw.Marker "phase5_data_phasefivejoin_intro"
        , Raw.Marker
            "phase5_data_phasefivezero_phasefiveatom_distinct"
        , Raw.Marker
            "phase5_data_phasefivezero_phasefivejoin_distinct"
        , Raw.Marker
            "phase5_data_phasefiveatom_phasefivejoin_distinct"
        , Raw.Marker "phase5_data_phasefiveatom_injective"
        , Raw.Marker "phase5_data_phasefivejoin_injective"
        , Raw.Marker "phase5_data_cases"
        , Raw.Marker "phase5_data_induct"
        , Raw.Marker "phase5_data_predicate_induct"
        ]
        markers
    assertBool "datatype generated targets are checked propositions"
        (all
            (\fact ->
                Core.frozenCoreType
                    (Datatype.preparedDatatypeFactTarget fact)
                    == Core.TyProp)
            facts)
    atomIntroduction <-
        sole "domain-bearing datatype introduction"
            [ fact
            | fact <- facts
            , Datatype.preparedDatatypeFactMarker fact
                == Raw.Marker "phase5_data_phasefiveatom_intro"
            ]
    assertEqual "domain-bearing datatype introduction target"
        (Core.CForall Core.TySet
            (Core.CImp
                (member
                    (Core.CBound 0)
                    singletonEmpty)
                (member
                    (Core.CApp
                        (Core.CGlobal atomId)
                        (Core.CBound 0))
                    (Core.CGlobal carrierId))))
        (Core.frozenCoreTerm
            (Datatype.preparedDatatypeFactTarget
                atomIntroduction))
    induction <-
        sole "datatype induction law"
            [ fact
            | fact <- facts
            , Datatype.preparedDatatypeFactMarker fact
                == Raw.Marker "phase5_data_induct"
            ]
    assertEqual "datatype induction target"
        (Core.CForall Core.TySet
            (Core.CImp
                (conjunctions
                    [ member
                        (Core.CGlobal zeroId)
                        (Core.CBound 0)
                    , Core.CForall Core.TySet
                        (Core.CImp
                            (member
                                (Core.CBound 0)
                                singletonEmpty)
                            (member
                                (Core.CApp
                                    (Core.CGlobal atomId)
                                    (Core.CBound 0))
                                (Core.CBound 1)))
                    , Core.CForall Core.TySet
                        (Core.CForall Core.TySet
                            (Core.CImp
                                (conjunction
                                    (member
                                        (Core.CBound 1)
                                        (Core.CBound 2))
                                    (member
                                        (Core.CBound 0)
                                        (Core.CBound 2)))
                                (member
                                    (Core.CApp
                                        (Core.CApp
                                            (Core.CGlobal joinId)
                                            (Core.CBound 1))
                                        (Core.CBound 0))
                                    (Core.CBound 2))))
                    ])
                (Core.CForall Core.TySet
                    (Core.CImp
                        (member
                            (Core.CBound 0)
                            (Core.CGlobal carrierId))
                        (member
                            (Core.CBound 0)
                            (Core.CBound 1))))))
        (Core.frozenCoreTerm
            (Datatype.preparedDatatypeFactTarget induction))
    predicateInduction <- sole "datatype predicate induction"
        [fact | fact <- facts, Datatype.preparedDatatypeFactMarker fact == Raw.Marker "phase5_data_predicate_induct"]
    let b = Core.CBound
        d = Core.CGlobal carrierId
        app object = foldl Core.CApp (Core.CGlobal object)
        forallSets n body = foldr (const (Core.CForall Core.TySet)) body [1 .. n :: Int]
    assertEqual "predicate induction retains carrier guards beside hypotheses"
        (Core.CForall (Core.TyArrow Core.TySet Core.TyProp)
            (Core.CImp
                (conjunctions
                    [ Core.CApp (b 0) (Core.CGlobal zeroId)
                    , forallSets 1 (Core.CImp (member (b 0) singletonEmpty)
                        (Core.CApp (b 1) (app atomId [b 0])))
                    , forallSets 2 (Core.CImp
                        (conjunctions [member (b 1) d, member (b 0) d,
                            Core.CApp (b 2) (b 1), Core.CApp (b 2) (b 0)])
                        (Core.CApp (b 2) (app joinId [b 1,b 0])))
                    ])
                (forallSets 1 (Core.CImp (member (b 0) d) (Core.CApp (b 1) (b 0))))))
        (Core.frozenCoreTerm (Datatype.preparedDatatypeFactTarget predicateInduction))
  where
    singletonEmpty =
        Core.canonicalSetInsert
            (Core.CIntrinsic Core.Empty)
            (Core.CIntrinsic Core.Empty)

    member element set =
        Core.CApp
            (Core.CApp
                (Core.CIntrinsic Core.Member)
                element)
            set

    conjunction = Core.CAnd

    conjunctions = \case
        [] -> Core.CTruth
        first : remaining -> foldl' conjunction first remaining

acceptsRichDatatypeDomains :: Assertion
acceptsRichDatatypeDomains = do
    (_foundation, _owner, prepared) <-
        expectRight
            =<< prepareDatatypeFixture
                "test/phase5/datatype-rich-domain.tex"
    (carrierId, dependentId, quantifiedId) <-
        case fst <$> toList (Datatype.preparedDatatypeObjects prepared) of
            [carrier, dependent, quantified] ->
                pure (carrier, dependent, quantified)
            objects ->
                assertFailure
                    ("unexpected rich-domain datatype objects: " <> show objects)
                    >> fail "unreachable"
    let facts = toList (Datatype.preparedDatatypeFacts prepared)
        dependentDomain =
            app1 Core.FamilyUnion
                (app2 Core.Repl singletonEmpty
                    (Core.CLam Core.TySet
                        (app2 Core.Repl (Core.CBound 0)
                            (Core.CLam Core.TySet (Core.CBound 0)))))
        quantifiedDomain =
            app2 Core.Repl
                (app2 Core.Sep singletonEmpty
                    (Core.CLam Core.TySet
                        (Core.CForall Core.TySet
                            (Core.CEq Core.TySet
                                (Core.CBound 1)
                                (Core.CBound 0)))))
                (Core.CLam Core.TySet (Core.CBound 0))
    assertIntroductionDomain
        facts carrierId dependentId
        (Raw.Marker "phase5_rich_data_phasefivedependent_intro")
        dependentDomain
    assertIntroductionDomain
        facts carrierId quantifiedId
        (Raw.Marker "phase5_rich_data_phasefivequantified_intro")
        quantifiedDomain
  where
    singletonEmpty =
        Core.canonicalSetInsert
            (Core.CIntrinsic Core.Empty)
            (Core.CIntrinsic Core.Empty)

    app1 intrinsic argument =
        Core.CApp (Core.CIntrinsic intrinsic) argument

    app2 intrinsic left right =
        Core.CApp (app1 intrinsic left) right

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

    assertIntroductionDomain
            facts carrier constructor marker domain = do
        introduction <-
            sole ("datatype introduction " <> show marker)
                [ fact
                | fact <- facts
                , Datatype.preparedDatatypeFactMarker fact == marker
                ]
        assertEqual ("datatype domain semantics " <> show marker)
            (Core.CForall Core.TySet
                (Core.CImp
                    (member (Core.CBound 0) domain)
                    (member
                        (Core.CApp
                            (Core.CGlobal constructor)
                            (Core.CBound 0))
                        (Core.CGlobal carrier))))
            (Core.frozenCoreTerm
                (Datatype.preparedDatatypeFactTarget introduction))

rejectsNestedDatatypeRecursion :: Assertion
rejectsNestedDatatypeRecursion = do
    result <-
        prepareDatatypeFixture
            "test/phase5/datatype-nested.tex"
    case result of
        Left Datatype.DatatypeInvalid{} -> pure ()
        Left failure ->
            assertFailure
                ("unexpected nested datatype failure: " <> show failure)
        Right _prepared ->
            assertFailure "nested datatype recursion was accepted"

rejectsHigherOrderDatatypePremises :: Assertion
rejectsHigherOrderDatatypePremises = do
    result <-
        prepareDatatypeFixture
            "test/phase5/datatype-higher-order.tex"
    case result of
        Left Datatype.DatatypeInvalid{} -> pure ()
        Left failure ->
            assertFailure
                ("unexpected higher-order datatype failure: " <> show failure)
        Right _prepared ->
            assertFailure "a higher-order datatype premise was accepted"

compilesAndReusesDatatypes :: Assertion
compilesAndReusesDatatypes =
    Temp.withSystemTempDirectory "felix-datatype" \directory -> do
        let relative = "test/phase5/datatype.tex"
            storePath = directory Posix.</> "store.sqlite"
        (foundation, bootstrap, workspace, freshModules) <-
            compileFixture relative
        fresh <- sole "fresh datatype module" freshModules
        assertDatatypeModule "fresh" fresh
        parsed <-
            sole "datatype parsed module"
                (toList
                    (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        let artefact sealed = do
                key <- expectRight
                    (Semantic.moduleArtefactKey
                        (moduleName (Parsed.parsedModuleAddress parsed))
                        (Parsed.parsedModuleId parsed)
                        [ Semantic.semanticInterfaceAssertedId
                            (completedModuleSemantic
                                (Module.bootstrapPreludeCompleted bootstrap))
                        ]
                        (Identity.theoryId foundation))
                pure
                    (Semantic.moduleArtefactResult
                        key
                        (Syntax.moduleSyntaxAssertedId
                            (completedModuleSyntax sealed))
                        (Semantic.semanticInterfaceAssertedId
                            (completedModuleSemantic sealed))
                        (sealedValidationCertificates sealed))
        freshArtefact <- artefact fresh
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation
                        bootstrap
                        unusedResolver
                        validation
                        workspace
                warm <- sole "warm datatype module" warmModules
                assertDatatypeModule "warm" warm
                assertEqual "warm datatype semantic interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm datatype final prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))
                assertEqual "warm datatype module artefact"
                    freshArtefact
                    =<< artefact warm

        mounts <- exactFixtureMounts =<< getCurrentDirectory
        nestedWorkspace <-
            parseWorkspace bootstrap mounts
                "test/phase5/datatype-nested.tex"
        nestedParsed <-
            sole "nested datatype module"
                (toList
                    (Parsed.parsedWorkspaceImportedBeforeImporter
                        nestedWorkspace))
        nestedInput <-
            expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    unusedResolver
                    AlwaysMissValidation
                    nestedParsed
                    [])
        runTypedModule nestedInput >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedDatatypeFailed
                            (Datatype.DatatypeInvalid
                                location _message)))
                    prefix -> do
                assertEqual "nested datatype failure line"
                    4
                    (locLine location)
                assertBool "nested datatype publishes no prefix"
                    (null
                        (Commit.pendingModulePrefixBatches prefix))
            _result ->
                assertFailure "unexpected nested datatype result"

preservesDatatypePremises :: Assertion
preservesDatatypePremises = do
    (_, _, prepared) <- expectRight =<< prepareDatatypeFixture "test/phase5/datatype-premises.tex"
    (carrier, leaf, atom, join) <- case fst <$> toList (Datatype.preparedDatatypeObjects prepared) of
        [carrier, leaf, atom, join] -> pure (carrier, leaf, atom, join)
        _ -> fail "unexpected datatype premise fixture objects"
    let domain = Core.canonicalSetInsert (Core.CGlobal leaf) (Core.CIntrinsic Core.Empty)
        d = Core.CGlobal carrier
        b = Core.CBound
        member x a = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) a
        atomAt x = Core.CApp (Core.CGlobal atom) x
        joinAt x y = Core.CApp (Core.CApp (Core.CGlobal join) x) y
        target marker = Core.frozenCoreTerm . Datatype.preparedDatatypeFactTarget <$>
            sole "datatype premise law" [fact | fact <- toList (Datatype.preparedDatatypeFacts prepared),
                Datatype.preparedDatatypeFactMarker fact == Raw.Marker marker]
        forallSets n body = foldr (const (Core.CForall Core.TySet)) body [1 .. n :: Int]
        existsSets n body = foldr (const (Core.CExists Core.TySet)) body [1 .. n :: Int]
        conjunction [x] = x
        conjunction (x:xs) = foldl Core.CAnd x xs
        conjunction [] = Core.CTruth
    assertEqual "unused empty-domain premise is retained"
        (forallSets 2 (Core.CImp
            (Core.CAnd (member (b 1) domain) (member (b 0) (Core.CIntrinsic Core.Empty)))
            (member (atomAt (b 1)) d)))
        =<< target "premise_data_premiseatom_intro"
    assertEqual "constructor arguments follow their premise slots"
        (forallSets 3 (Core.CImp
            (conjunction [member (b 2) d, member (b 1) d, member (b 0) domain])
            (member (joinAt (b 1) (b 2)) d)))
        =<< target "premise_data_premisejoin_intro"
    assertEqual "cases retain unused existential witnesses"
        (forallSets 1 (Core.CImp (member (b 0) d)
            (Core.COr
                (Core.COr (Core.CEq Core.TySet (b 0) (Core.CGlobal leaf))
                    (existsSets 2 (conjunction [member (b 1) domain,
                        member (b 0) (Core.CIntrinsic Core.Empty),
                        Core.CEq Core.TySet (b 2) (atomAt (b 1))])))
                (existsSets 3 (conjunction [member (b 2) d, member (b 1) d,
                    member (b 0) domain, Core.CEq Core.TySet (b 3) (joinAt (b 1) (b 2))])))))
        =<< target "premise_data_cases"
    assertEqual "injectivity has no membership premises"
        (forallSets 4 (Core.CImp
            (Core.CEq Core.TySet (joinAt (b 3) (b 2)) (joinAt (b 1) (b 0)))
            (Core.CAnd (Core.CEq Core.TySet (b 3) (b 1)) (Core.CEq Core.TySet (b 2) (b 0)))))
        =<< target "premise_data_premisejoin_injective"
    -- These use the real owner and a resolver that fails on any external request.
    for_ ["test/phase5/datatype-premises.tex", "test/phase5/datatype-empty.tex",
          "test/phase5/datatype-rich-domain.tex", "test/phase5/datatype-recursive-witness.tex"] \relative -> void (compileFixture relative)

checksDatatypeFamilies :: Assertion
checksDatatypeFamilies = Temp.withSystemTempDirectory "felix-datatype-family" \directory -> do
    (_, _, prepared) <- expectRight =<< prepareDatatypeFixture "test/phase5/datatype-family.tex"
    (carrier, atom, join) <- case toList (Datatype.preparedDatatypeObjects prepared) of
        [(carrier, carrierType), _, (atom, _), (join, _), _] -> do
            assertEqual "family type" (Core.TyArrow Core.TySet (Core.TyArrow Core.TySet Core.TySet)) carrierType
            pure (carrier, atom, join)
        _ -> fail "unexpected datatype family objects"
    let b = Core.CBound
        member x a = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) a
        app object = foldl Core.CApp (Core.CGlobal object)
        forallSets n body = foldr (const (Core.CForall Core.TySet)) body [1 .. n :: Int]
        target marker = Core.frozenCoreTerm . Datatype.preparedDatatypeFactTarget <$>
            sole "datatype family law" [fact | fact <- toList (Datatype.preparedDatatypeFacts prepared),
                Datatype.preparedDatatypeFactMarker fact == Raw.Marker marker]
    assertEqual "fixed domain uses the first parameter under the field binder"
        (forallSets 3 (Core.CImp (member (b 0) (b 2))
            (member (app atom [b 0]) (app carrier [b 2,b 1]))))
        =<< target "family_data_familyatom_intro"
    let d = app carrier [b 4,b 3]
    assertEqual "recursive fields and unstored witnesses keep their parameter scope"
        (forallSets 5 (Core.CImp
            (Core.CAnd (Core.CAnd (member (b 2) d) (member (b 1) d)) (member (b 0) (b 3)))
            (member (app join [b 1,b 2]) d)))
        =<< target "family_data_familyjoin_intro"
    (foundation, bootstrap, workspace, fresh) <- compileFixture "test/phase5/datatype-family.tex"
    bracket
        (snd <$> (Store.openStore (directory Posix.</> "store.sqlite") (Identity.theoryId foundation) >>= expectRight))
        Store.closeStore \store -> do
            storeCheck <- Store.newStoreCheck store
            for_ fresh \sealed -> expectRightIO (Store.writePendingModulePrefix storeCheck (Module.completedTypedModulePrefix sealed))
            warm <- compileParsedWorkspaceWithValidation foundation bootstrap unusedResolver (storeValidationPolicy storeCheck) workspace
            assertEqual "family warm interfaces" (completedModuleSemantic <$> fresh) (completedModuleSemantic <$> warm)
            assertEqual "family warm authorities" (sealedValidationCertificates <$> fresh) (sealedValidationCertificates <$> warm)
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/datatype-family.tex"
    let writeFixture name transform =
            ByteString.writeFile (directory Posix.</> name) (Text.encodeUtf8 (transform source))
        objects = concatMap Commit.committedBatchObjects
            . Commit.pendingModulePrefixBatches . Module.completedTypedModulePrefix
    writeFixture "alpha.tex" (StrictText.replace "A" "C" . StrictText.replace "B" "E")
    (_, renamed) <- compileRootAt directory "alpha.tex"
    assertEqual "parameter alpha-renaming preserves representations" (concatMap objects fresh) (objects renamed)
    writeFixture "swapped.tex"
        (StrictText.replace "\\familydata{B}{A}" "\\familydata{A}{B}"
            . StrictText.replace "Z" "B" . StrictText.replace "B" "A" . StrictText.replace "A" "Z")
    (_, swapped) <- compileRootAt directory "swapped.tex"
    assertBool "swapping parameter roles changes the carrier" (concatMap objects fresh /= objects swapped)
    mounts <- exactFixtureMounts directory
    for_ [ ("repeated.tex", StrictText.replace "\\familydata{A}{B}" "\\familydata{A}{A}")
         , ("shadow.tex", StrictText.replace "\\familyatom{x}" "\\familyatom{A}"
                . StrictText.replace "$x\\in A$" "$A\\in A$")
         , ("target.tex", StrictText.replace "\\familyatom{x}\\in\\familydata{A}{B}"
                "\\familyatom{x}\\in\\familydata{B}{A}")
         , ("recursive.tex", StrictText.replace "$x\\in\\familydata{A}{B}$" "$x\\in\\familydata{B}{A}$")
         , ("unbound.tex", StrictText.replace "$x\\in A$" "$x\\in C$")
         , ("dependent.tex", StrictText.replace "$z\\in B$" "$z\\in x$")
         , ("nested.tex", StrictText.replace "$x\\in A$" "$x\\in\\pow{\\familydata{A}{B}}$")
         ] \(name, transform) -> do
        writeFixture name transform
        invalidWorkspace <- parseWorkspace bootstrap mounts name
        parsed <- sole "invalid datatype family" (toList (Parsed.parsedWorkspaceImportedBeforeImporter invalidWorkspace))
        input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver AlwaysMissValidation parsed [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedDatatypeFailed Datatype.DatatypeInvalid{})) prefix ->
                assertBool (name <> " publishes nothing") (null (Commit.pendingModulePrefixBatches prefix))
            _ -> assertFailure (name <> " did not reject the invalid family")

rejectsForgedDatatypeDescriptions :: Assertion
rejectsForgedDatatypeDescriptions = do
    (foundation, bootstrap, _, modules) <- compileFixture "test/phase5/datatype-formation.tex"
    sealed <- sole "described datatype module" modules
    batch <- sole "described datatype declaration" (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed))
    let original = completedModuleSemantic sealed
        delta = Commit.committedBatchDelta batch
        environment = Semantic.declarationDeltaEnvironment delta
        bindings = Semantic.semanticEnvironmentBindings environment
        parents = [completedModuleEvidence parent | parent <- [Module.bootstrapPreludeCompleted bootstrap]
            , Semantic.semanticInterfaceAssertedId (completedModuleSemantic parent) `elem` Semantic.semanticInterfaceDirectInputs original]
        admit interface = admitTestModule (Identity.theoryId foundation) parents interface
            (Commit.committedBatchObjects batch) (Commit.committedBatchPropositions batch)
            (Commit.committedBatchValidationCertificates batch)
    (carrier, descriptor) <- sole "carrier description"
        [(binding, found) | binding <- bindings, Just found <- [Semantic.semanticGlobalBindingDatatype binding]]
    assertEqual "semantic case keys follow written names" ["falsity", "atom", "implication"]
        (Semantic.datatypeCaseName <$> toList (Semantic.datatypeDescriptorCases descriptor))
    void (expectRight =<< admit original)
    let changeAtom change value = case Semantic.datatypeDescriptorCases value of
            first :| [atom, implication] -> value{Semantic.datatypeDescriptorCases = first :| [change atom, implication]}
            _ -> error "unexpected formula datatype cases"
        mutations =
            [ ("missing field slot", changeAtom (\clause -> clause{Semantic.datatypeCaseFields = [2]}))
            , ("wrong recursive role", changeAtom (\clause -> clause{Semantic.datatypeCasePremises = [Semantic.DatatypeRecursivePremise]}))
            , ("unbound domain", changeAtom (\clause -> clause{Semantic.datatypeCasePremises = [Semantic.DatatypeFixedPremise (Core.CBound 1)]}))
            , ("duplicate case", changeAtom (\clause -> clause{Semantic.datatypeCaseName = "falsity"}))
            , ("wrong law", \value -> value{Semantic.datatypeDescriptorCasesFact = Semantic.datatypeDescriptorInductionFact value})
            , ("wrong introduction law", changeAtom (\clause -> clause
                {Semantic.datatypeCaseIntroductionFact = Semantic.datatypeDescriptorCasesFact descriptor}))
            , ("missing injectivity law", changeAtom (\clause -> clause{Semantic.datatypeCaseInjectivityFact = Nothing}))
            , ("wrong injectivity law", changeAtom (\clause -> clause
                {Semantic.datatypeCaseInjectivityFact = Just (Semantic.datatypeCaseIntroductionFact clause)}))
            , ("missing distinctness law", changeAtom (\clause -> clause{Semantic.datatypeCaseDistinctnessFacts = []}))
            , ("wrong distinctness law", changeAtom (\clause -> clause
                {Semantic.datatypeCaseDistinctnessFacts =
                    [(key, Semantic.datatypeCaseIntroductionFact clause) | (key, _) <- Semantic.datatypeCaseDistinctnessFacts clause]}))
            , ("wrong distinctness constructor", changeAtom (\clause -> clause
                {Semantic.datatypeCaseDistinctnessFacts =
                    [(Semantic.datatypeCaseConstructor clause, fact) | (_, fact) <- Semantic.datatypeCaseDistinctnessFacts clause]}))
            ]
    for_ mutations \(label, change) -> do
        let changedBindings = [if Semantic.semanticGlobalBindingKey binding == Semantic.semanticGlobalBindingKey carrier
                then Semantic.withSemanticDatatype (change descriptor) binding else binding | binding <- bindings]
        changedEnvironment <- expectRight (Semantic.semanticEnvironmentWithStructures changedBindings (Semantic.semanticEnvironmentStructures environment))
        changedDelta <- expectRight (Semantic.declarationInterfaceDelta (Semantic.declarationDeltaSlot delta)
            (Semantic.declarationDeltaFacts delta) (Semantic.declarationDeltaAliases delta)
            (Semantic.declarationDeltaObjects delta) (Semantic.declarationDeltaPropositions delta)
            (Semantic.declarationDeltaDefinitionViews delta) (Semantic.declarationDeltaRegistrations delta) changedEnvironment)
        changed <- expectRight (Semantic.semanticInterface (Semantic.semanticInterfaceOwner original)
            (Semantic.semanticInterfaceDirectInputs original) [changedDelta])
        assertBool (label <> " changes the semantic identity")
            (Semantic.semanticInterfaceAssertedId changed /= Semantic.semanticInterfaceAssertedId original)
        admit changed >>= \case
            Left Declaration.DatatypeInterfaceInvalid{} -> pure ()
            Left failure -> assertFailure (label <> ": " <> show failure)
            Right _ -> assertFailure (label <> " admitted the forged description")

checksDatatypeNames :: Assertion
checksDatatypeNames = Temp.withSystemTempDirectory "felix-datatype-names" \directory -> do
    (_, _, prepared) <- expectRight =<< prepareDatatypeFixture "test/phase5/datatype-formation.tex"
    let markers = Datatype.preparedDatatypeFactMarker <$> toList (Datatype.preparedDatatypeFacts prepared)
    assertBool "named clauses determine public aliases"
        (all (`elem` markers) ["formation_data_falsity_intro", "formation_data_atom_intro", "formation_data_implication_intro"])
    assertEqual "prose headings normalize once" (Just "dne_2_case") (Raw.datatypeCaseKey "  DNE_2  Case  ")
    (foundation, bootstrap, _, _) <- compileFixture "test/phase5/datatype-formation.tex"
    mounts <- exactFixtureMounts directory
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/datatype-formation.tex"
    for_ [("duplicate.tex", " Atom "), ("digit.tex", "1 Falsity"), ("punctuation.tex", "False!"), ("empty.tex", " ")]
        \(name, replacement) -> do
            ByteString.writeFile (directory Posix.</> name) (Text.encodeUtf8 (StrictText.replace "Falsity" replacement source))
            workspace <- parseWorkspace bootstrap mounts name
            input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule workspace) [])
            runTypedModule input >>= \case
                Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedDatatypeFailed Datatype.DatatypeInvalid{})) prefix ->
                    assertBool (name <> " publishes nothing") (null (Commit.pendingModulePrefixBatches prefix))
                _ -> assertFailure (name <> " did not reject its case name")
    ByteString.writeFile (directory Posix.</> "collision.tex") (Text.encodeUtf8 (StrictText.unlines
        [ "\\begin{datatype}\\label{collision}"
        , "Define $\\collision$ inductively as follows."
        , "\\begin{enumerate}"
        , "\\item[A] $\\collisiona\\in\\collision$."
        , "\\item[B C] $\\collisionb\\in\\collision$."
        , "\\item[A B] $\\collisionc\\in\\collision$."
        , "\\item[C] $\\collisiond\\in\\collision$."
        , "\\end{enumerate}\\end{datatype}"
        ]))
    collision <- parseWorkspace bootstrap mounts "collision.tex"
    input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
        unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule collision) [])
    runTypedModule input >>= \case
        Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedDatatypeFailed (Datatype.DatatypeInvalid _ reason))) prefix -> do
            assertBool "ambiguous generated distinctness aliases are rejected" ("aliases collide" `StrictText.isInfixOf` reason)
            assertBool "alias collision publishes nothing" (null (Commit.pendingModulePrefixBatches prefix))
        _ -> assertFailure "ambiguous generated datatype aliases were accepted"

checksStructuralInduction :: Assertion
checksStructuralInduction = Temp.withSystemTempDirectory "felix-structural-induction" \directory -> do
    (foundation, bootstrap, workspace, fresh) <- compileFixture "test/phase5/propositional-induction.tex"
    bracket
        (snd <$> (Store.openStore (directory Posix.</> "store.sqlite") (Identity.theoryId foundation) >>= expectRight))
        Store.closeStore \store -> do
            storeCheck <- Store.newStoreCheck store
            for_ fresh \sealed -> expectRightIO (Store.writePendingModulePrefix storeCheck (Module.completedTypedModulePrefix sealed))
            warm <- compileParsedWorkspaceWithValidation foundation bootstrap unusedResolver (storeValidationPolicy storeCheck) workspace
            assertEqual "structural induction warm interfaces" (completedModuleSemantic <$> fresh) (completedModuleSemantic <$> warm)
            assertEqual "structural induction warm authorities" (sealedValidationCertificates <$> fresh) (sealedValidationCertificates <$> warm)

    datatypeSource <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/propositional.tex"
    inductionSource <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/propositional-induction.tex"
    let definitions = datatypeSource <> snd (StrictText.breakOn "\\begin{definition}" (fst
            (StrictText.breakOn "\\begin{proposition}" inductionSource)))
        bounded = fst (StrictText.breakOn "\\begin{proposition}[Active membership]"
            (snd (StrictText.breakOn "\\begin{proposition}" inductionSource)))
        active = snd (StrictText.breakOn "\\begin{proposition}[Active membership]" inductionSource)
        atomCase = "        \\caseOf{Atom.}\n            Fix $a\\in A$.\n            Then $a\\in B$ by \\obv{subseteq}.\n            Follows by \\obv{pl_formula_atom_intro}.\n"
        negatives =
            [ ("missing", StrictText.replace atomCase "" bounded, True)
            , ("duplicate", StrictText.replace "\\caseOf{Atom.}" "\\caseOf{Falsity.}" bounded, True)
            , ("extra", StrictText.replace "\\end{byCase}" "\\caseOf{Extra.} Follows. \\end{byCase}" bounded, True)
            , ("dependent", StrictText.replace "Then $p\\in\\plform{B}$."
                "Suppose $p\\in C$. Then $p\\in\\plform{B}$." active, True)
            , ("dependent-parameter", StrictText.replace "\\plform{A}" "\\plform{p}" active, True)
            , ("dependent-definition", StrictText.replace "\\end{proof}"
                "\\end{subproof} Follows by assumption. \\end{proof}"
                (StrictText.replace "\\begin{proof}[Proof by structural induction on $p$]"
                    "\\begin{proof} Let $s=p$. Show $p\\in\\plform{B}$. \\begin{subproof}[Proof by structural induction on $p$]"
                    (fst (StrictText.breakOn "\\begin{proposition}\\label{pl_formula_implicational_motive}" active))), True)
            , ("hidden-focus", StrictText.replace "Follows by \\obv{pl_formula_falsity_intro}."
                "Then $p=p$ by assumption. Follows by \\obv{pl_formula_falsity_intro}." active, False)
            , ("separate-cases", StrictText.replace "Fix $q,r\\in\\plform{A}$."
                "Then $a\\in B$ by assumption. Fix $q,r\\in\\plform{A}$." bounded, False)
            , ("unproved", StrictText.replace "Follows by \\obv{pl_formula_falsity_intro}."
                "Then $\\propbot\\in A$ by assumption. Follows by \\obv{pl_formula_falsity_intro}." bounded, False)
            ]
    for_ ["test/phase5/datatype-witness-induction.tex", "test/phase5/datatype-family-induction.tex",
            "test/phase5/datatype-shared-induction.tex"] \fixture -> void (compileFixture fixture)
    let grouped = StrictText.replace "Suppose $A\\subseteq B$.\n    Suppose $p\\in\\plform{A}$."
            "Suppose $A\\subseteq B$ and $p\\in\\plform{A}$ and $c\\in C$."
            (StrictText.replace "\\caseOf{Falsity.}" "\\caseOf{Falsity.} Then $c\\in C$ by notion."
                (fst (StrictText.breakOn "\\begin{proposition}\\label{pl_formula_implicational_motive}" active)))
    ByteString.writeFile (directory Posix.</> "grouped.tex") (Text.encodeUtf8 (definitions <> grouped))
    void (compileRootAt directory "grouped.tex")
    ByteString.writeFile (directory Posix.</> "display.tex") (Text.encodeUtf8
        (StrictText.replace "pl_formula_falsity_intro" "pl_formula_empty_0_intro"
            (StrictText.replace "Falsity" "Empty 0" (definitions <> bounded))))
    void (compileRootAt directory "display.tex")
    mounts <- exactFixtureMounts directory
    for_ negatives \(name, body, structural) -> do
        ByteString.writeFile (directory Posix.</> name <> ".tex") (Text.encodeUtf8 (definitions <> body))
        negative <- parseWorkspace bootstrap mounts (name <> ".tex")
        input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule negative) [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedProofFailed failure)) prefix -> do
                assertEqual (name <> " publishes only its definitions") 2 (length (Commit.pendingModulePrefixBatches prefix))
                when structural $ case failure of
                    Proof.ProofStructuralInductionInvalid{} -> pure ()
                    _ -> assertFailure (name <> ": " <> show failure)
            _ -> assertFailure (name <> " did not reject invalid structural induction")

    shared <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/datatype-shared.tex"
    client <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/datatype-shared-induction.tex"
    let ambiguous = shared <> StrictText.replace "Suppose $p\\in\\sharedsecond$."
            "Suppose $p\\in\\sharedsecond$ and $p\\in\\sharedfirst$."
            (snd (StrictText.breakOn "\\begin{abbreviation}" client))
    ByteString.writeFile (directory Posix.</> "ambiguous.tex") (Text.encodeUtf8 ambiguous)
    ambiguousWorkspace <- parseWorkspace bootstrap mounts "ambiguous.tex"
    ambiguousInput <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
        unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule ambiguousWorkspace) [])
    runTypedModule ambiguousInput >>= \case
        Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedProofFailed
                (Proof.ProofStructuralInductionInvalid _ reason))) _ ->
            assertBool "source ambiguity is not resolved by shared object identity" ("several datatypes" `StrictText.isInfixOf` reason)
        _ -> assertFailure "ambiguous shared-carrier induction was not rejected"

checksDatatypeFormation :: Assertion
checksDatatypeFormation = Temp.withSystemTempDirectory "felix-datatype-formation" \directory -> do
    (foundation, bootstrap, workspace, fresh) <- compileFixture "test/phase5/datatype-formation-import.tex"
    let registrations sealed = concatMap (Semantic.declarationDeltaRegistrations . Commit.committedBatchDelta)
            (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed))
    assertEqual "all three formula introductions are registered" [3,0] (length . registrations <$> fresh)
    (_, _, _, rich) <- compileFixture "test/phase5/datatype-family.tex"
    assertEqual "unstored witnesses and rich domains remain explicit" [1] (length . registrations <$> rich)
    source <- Text.decodeUtf8 <$> ByteString.readFile "test/phase5/datatype-family.tex"
    ByteString.writeFile (directory Posix.</> "missing-witness.tex") (Text.encodeUtf8 (source <> StrictText.unlines
        [ "\\begin{proposition}\\label{missing_witness}"
        , "Then $\\familyzero\\in\\familydata{A}{B}$."
        , "\\end{proposition}"
        , "\\begin{proof} Follows by notion. \\end{proof}"
        ]))
    mounts <- exactFixtureMounts directory
    negative <- parseWorkspace bootstrap mounts "missing-witness.tex"
    input <- expectRightIO (typedModuleInput foundation (Module.bootstrapPreludeReadiness bootstrap)
        unusedResolver AlwaysMissValidation (Parsed.parsedWorkspaceRootModule negative) [])
    runTypedModule input >>= \case
        Module.TypedModuleFailed (Module.TypedActionFailed (Module.TypedProofFailed Proof.ProofNotionUnavailable{})) prefix ->
            assertEqual "missing witness publishes only the datatype" 1 (length (Commit.pendingModulePrefixBatches prefix))
        _ -> assertFailure "constructor formation inferred an unstored witness"
    bracket
        (snd <$> (Store.openStore (directory Posix.</> "store.sqlite") (Identity.theoryId foundation) >>= expectRight))
        Store.closeStore \store -> do
            storeCheck <- Store.newStoreCheck store
            for_ fresh \sealed -> expectRightIO (Store.writePendingModulePrefix storeCheck (Module.completedTypedModulePrefix sealed))
            warm <- compileParsedWorkspaceWithValidation foundation bootstrap unusedResolver (storeValidationPolicy storeCheck) workspace
            assertEqual "formation warm interfaces" (completedModuleSemantic <$> fresh) (completedModuleSemantic <$> warm)
            assertEqual "formation warm authorities" (sealedValidationCertificates <$> fresh) (sealedValidationCertificates <$> warm)

sharesDatatypeDefinitions :: Assertion
sharesDatatypeDefinitions = Temp.withSystemTempDirectory "felix-shared-datatypes" \directory -> do
    (foundation, bootstrap, workspace, fresh) <- compileFixture "test/phase5/datatype-shared-import.tex"
    case concatMap (Commit.pendingModulePrefixBatches . Module.completedTypedModulePrefix) fresh of
        [first, second, imported] -> do
            assertEqual "first datatype contributes its representation" 4 (length (Commit.committedBatchObjects first))
            descriptions <- for [first, second, imported] \batch -> do
                let delta = Commit.committedBatchDelta batch
                (binding, descriptor) <- sole "source-owned datatype descriptor"
                    [(binding, descriptor)
                    | binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)
                    , Just descriptor <- [Semantic.semanticGlobalBindingDatatype binding]]
                pure (Semantic.globalBindingRef (Semantic.declarationDeltaSlot delta) (Semantic.semanticGlobalBindingKey binding), descriptor)
            assertEqual "equal representations keep three source identities" 3 (Set.size (Set.fromList (fst <$> descriptions)))
            assertEqual "each description references its own induction fact" 3
                (Set.size (Set.fromList (Semantic.datatypeDescriptorPredicateInductionFact . snd <$> descriptions)))
            for_ [second, imported] \batch -> do
                assertEqual "shared definitions need no repeated object insertion" [] (Commit.committedBatchObjects batch)
                assertEqual "each declaration keeps its own theorem aliases" 7
                    (length (Semantic.declarationDeltaAliases (Commit.committedBatchDelta batch)))
                assertEqual "reused implementation equations expose no views" []
                    (Semantic.declarationDeltaDefinitionViews (Commit.committedBatchDelta batch))
        _ -> assertFailure "shared datatype fixture did not produce three declarations"
    bracket
        (snd <$> (Store.openStore (directory Posix.</> "store.sqlite") (Identity.theoryId foundation) >>= expectRight))
        Store.closeStore \store -> do
            storeCheck <- Store.newStoreCheck store
            for_ fresh \sealed -> expectRightIO (Store.writePendingModulePrefix storeCheck (Module.completedTypedModulePrefix sealed))
            warm <- compileParsedWorkspaceWithValidation foundation bootstrap unusedResolver (storeValidationPolicy storeCheck) workspace
            assertEqual "shared datatype warm interfaces" (completedModuleSemantic <$> fresh) (completedModuleSemantic <$> warm)
            assertEqual "shared datatype warm authorities" (sealedValidationCertificates <$> fresh) (sealedValidationCertificates <$> warm)

preparesNestedInductiveRecursion :: Assertion
preparesNestedInductiveRecursion =
    withAcceptedFixtureVampire "felix-nested-inductive" \vampire -> do
        root <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts root
        workspace <-
            parseWorkspace bootstrap mounts
                "test/phase5/exact-inductive-nested.tex"
        parsed <- sole "nested exact inductive parsed module"
            (toList
                (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        observed <- newIORef []
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    let problem =
                            Provers.preparedTypedProverLogicalProblem prepared
                    modifyIORef' observed
                        (<> [ ( Backend.typedProblemRoute problem
                             , Backend.supportedPropositionTerm
                                (Backend.typedProblemClaim problem)
                             )
                           ])
                    (Provers.runPreparedTypedProver vampire prepared)
        modules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap resolver
                AlwaysMissValidation workspace
        sealed <- sole "nested exact inductive module" modules
        observations <- readIORef observed
        assertEqual "guard proof plus nested monotonicity request count"
            2 (length observations)
        (route, target) <-
            sole "nested monotonicity request"
                [ observation
                | observation@(_route, candidate) <- observations
                , candidate == expectedPowerMonotonicity
                ]
        assertEqual "nested monotonicity target"
            expectedPowerMonotonicity
            target
        assertEqual "nested monotonicity request is first-order"
            Backend.RouteFof
            route
        case Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed) of
            [_guardBatch, _unsafeBatch, inductiveBatch] -> do
                let facts =
                        Semantic.declarationDeltaFacts
                            (Commit.committedBatchDelta inductiveBatch)
                    aliases =
                        Semantic.declarationDeltaAliases
                            (Commit.committedBatchDelta inductiveBatch)
                    sourceSafety =
                        Authority.authoritySafety
                            (Authority.singletonEscapeKind Authority.SourceAxiom)
                assertEqual "nested inductive fact eligibility"
                    ( Semantic.SearchEligible
                        : Semantic.SearchIneligible
                        : replicate 4 Semantic.SearchEligible
                    )
                    (Semantic.semanticFactSearchEligibility <$> facts)
                monotonicityFact <- case facts of
                    _definition : fact : _laws -> pure fact
                    _ -> assertFailure "nested inductive fact inventory"
                        >> fail "unreachable"
                assertEqual "nested monotonicity fact is unaliased"
                    False
                    (Semantic.semanticFactFingerprint monotonicityFact
                        `elem` (Semantic.semanticAliasTarget <$> aliases))
                assertEqual "nested authority safety reaches generated laws"
                    [ Authority.cleanAuthoritySafety
                    , sourceSafety
                    , sourceSafety
                    , Authority.cleanAuthoritySafety
                    , sourceSafety
                    , sourceSafety
                    ]
                    ( Authority.factAuthoritySafety
                        . Semantic.semanticFactAuthority
                        <$> facts
                    )
                validation <-
                    maybe
                        (assertFailure "nested inductive validation is absent"
                            >> fail "unreachable")
                        pure
                        (Commit.committedBatchDeclarationValidation
                            inductiveBatch)
                assertEqual "nested inductive candidate authority shape"
                    [ "definition"
                    , "source-proof"
                    , "kernel"
                    , "kernel"
                    , "kernel"
                    , "kernel"
                    ]
                    (authorizationKind
                        . Authority.validationDirectAuthorization
                        <$> Semantic.declarationValidationRecordCertificates
                            validation)
                requestId <- nestedRequestId inductiveBatch
                Temp.withSystemTempDirectory
                    "felix-nested-inductive-cache" \temporary -> do
                        let storePath = temporary Posix.</> "store.sqlite"
                        bracket
                            (snd <$> (Store.openStore storePath
                                (Identity.theoryId foundation) >>= expectRight))
                            Store.closeStore
                            \store -> do
                                storeCheck <- Store.newStoreCheck store
                                expectRightIO
                                    (Store.writePendingModulePrefix storeCheck
                                        (Module.completedTypedModulePrefix sealed))
                                let warmValidation = storeValidationPolicy storeCheck
                                warmModules <-
                                    compileParsedWorkspaceWithValidation
                                        foundation bootstrap unusedResolver
                                        warmValidation workspace
                                warm <- sole
                                    "warm nested exact inductive module"
                                    warmModules
                                warmBatch <- case
                                    Commit.pendingModulePrefixBatches
                                        (Module.completedTypedModulePrefix warm) of
                                    [_warmGuard, _warmUnsafe, batch] -> pure batch
                                    batches ->
                                        assertFailure
                                            ("warm nested batch count: "
                                                <> show (length batches))
                                            >> fail "unreachable"
                                assertEqual "warm nested exact request"
                                    requestId
                                    =<< nestedRequestId warmBatch
                                assertEqual "warm nested semantic interface"
                                    (completedModuleSemantic sealed)
                                    (completedModuleSemantic warm)
                                assertEqual "warm nested admitted prefix"
                                    (Commit.pendingModulePrefixCurrent
                                        (Module.completedTypedModulePrefix sealed))
                                    (Commit.pendingModulePrefixCurrent
                                        (Module.completedTypedModulePrefix warm))
                                freshArtefact <-
                                    moduleArtefact
                                        foundation bootstrap parsed sealed
                                warmArtefact <-
                                    moduleArtefact
                                        foundation bootstrap parsed warm
                                assertEqual "warm nested module artefact"
                                    freshArtefact warmArtefact
            batches ->
                assertFailure
                    ("expected guard and nested inductive batches, found "
                        <> show (length batches))

        failureWorkspace <-
            parseWorkspace bootstrap mounts
                "test/phase5/exact-inductive-nested-failure.tex"
        successfulRequests <- newIORef []
        let successfulResolver =
                Declaration.vampireResolver \prepared -> do
                    let problem =
                            Provers.preparedTypedProverLogicalProblem prepared
                    modifyIORef' successfulRequests
                        (<> [Backend.supportedPropositionTerm
                                (Backend.typedProblemClaim problem)])
                    (Provers.runPreparedTypedProver vampire prepared)
        successfulModules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap successfulResolver
                AlwaysMissValidation failureWorkspace
        successful <- sole
            "successful repeated/distinct nested inductive module"
            successfulModules
        assertEqual
            "repeated and distinct contexts use two monotonicity requests"
            [ expectedPowerMonotonicity
            , expectedDoublePowerMonotonicity
            ]
            =<< readIORef successfulRequests
        case Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix successful) of
            [_guardOne, _guardTwo, batch] -> do
                validation <- maybe
                    (assertFailure
                        "successful multi-context validation absent"
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation batch)
                assertEqual
                    "deduplicated monotonicities precede all kernel laws"
                    ( ["definition", "source-proof", "source-proof"]
                        <> replicate 6 "kernel"
                    )
                    (authorizationKind
                        . Authority.validationDirectAuthorization
                        <$> Semantic.declarationValidationRecordCertificates
                            validation)
            batches ->
                assertFailure
                    ("successful multi-context batch count: "
                        <> show (length batches))
        attempts <- newIORef (0 :: Int)
        let rejectingResolver =
                Declaration.vampireResolver \prepared -> do
                    index <- atomicModifyIORef' attempts \current ->
                        (current + 1, current)
                    if index == 0
                        then pure
                            (counterexampleResolution prepared)
                        else
                        (Provers.runPreparedTypedProver vampire prepared)
        failureInput <-
            expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    rejectingResolver
                    AlwaysMissValidation
                    (Parsed.parsedWorkspaceRootModule failureWorkspace)
                    [])
        runTypedModule failureInput >>= \case
            Module.TypedModuleFailed
                    (Module.TypedDeclarationFailed
                        (Declaration.ProofObligationFailedAt
                            location
                            Declaration.VampireObligationFailed{}))
                    prefix -> do
                assertEqual "earliest monotonicity failure location"
                    14 (locLine location)
                assertEqual
                    "later monotonicity still resolves before first rejection"
                    2 =<< readIORef attempts
                assertEqual
                    "rejected monotonicity preserves only earlier declarations"
                    2
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            _result ->
                assertFailure
                    "nested monotonicity rejection unexpectedly succeeded"
  where
    authorizationKind = \case
        Authority.CheckedKernelConstruction
                Authority.CheckedDefinitionEquation{} -> "definition"
        Authority.CheckedKernelConstruction{} -> "kernel"
        Authority.CheckedSourceProof{} -> "source-proof"
        authorization -> show authorization

    nestedRequestId batch = do
        validation <- maybe
            (assertFailure "nested declaration validation absent"
                >> fail "unreachable")
            pure
            (Commit.committedBatchDeclarationValidation batch)
        certificate <- case
                Semantic.declarationValidationRecordCertificates validation of
            _definition : monotonicity : _laws -> pure monotonicity
            certificates ->
                assertFailure
                    ("nested declaration certificate count: "
                        <> show (length certificates))
                    >> fail "unreachable"
        case Authority.validationDirectAuthorization certificate of
            Authority.CheckedSourceProof
                    (Authority.UsesExternalProof (request :| [])) ->
                pure request
            authorization ->
                assertFailure
                    ("unexpected nested proof authorization "
                        <> show authorization)
                    >> fail "unreachable"

    moduleArtefact foundation bootstrap parsed sealed = do
        key <- expectRight
            (Semantic.moduleArtefactKey
                (moduleName (Parsed.parsedModuleAddress parsed))
                (Parsed.parsedModuleId parsed)
                [ Semantic.semanticInterfaceAssertedId
                    (completedModuleSemantic
                        (Module.bootstrapPreludeCompleted bootstrap))
                ]
                (Identity.theoryId foundation))
        pure
            (Semantic.moduleArtefactResult
                key
                (Syntax.moduleSyntaxAssertedId
                    (completedModuleSyntax sealed))
                (Semantic.semanticInterfaceAssertedId
                    (completedModuleSemantic sealed))
                (sealedValidationCertificates sealed))

    expectedPowerMonotonicity =
        Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CForall Core.TySet
                        (Core.CImp
                            (subset (Core.CBound 1) (Core.CBound 0))
                            (subset
                                (power (Core.CBound 1))
                                (power (Core.CBound 0)))))))

    expectedDoublePowerMonotonicity =
        Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CForall Core.TySet
                        (Core.CImp
                            (subset (Core.CBound 1) (Core.CBound 0))
                            (subset
                                (power (power (Core.CBound 1)))
                                (power (power (Core.CBound 0))))))))

    power argument =
        Core.CApp (Core.CIntrinsic Core.PowerSet) argument

    subset left right =
        Core.CForall Core.TySet
            (Core.CImp
                (member
                    (Core.CBound 0)
                    (Core.shiftCanonical 1 0 left))
                (member
                    (Core.CBound 0)
                    (Core.shiftCanonical 1 0 right)))

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

compilesTransparentNestedInductiveWrappers :: Assertion
compilesTransparentNestedInductiveWrappers =
    withAcceptedFixtureVampire "felix-nested-wrapper" \vampire -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <-
            parseWorkspace bootstrap mounts
                "test/phase5/exact-inductive-wrapper.tex"
        observed <- newIORef []
        let resolver =
                Declaration.vampireResolver \prepared -> do
                    let problem =
                            Provers.preparedTypedProverLogicalProblem prepared
                    modifyIORef' observed
                        (<> [ ( Backend.typedProblemRoute problem
                             , Backend.supportedPropositionTerm
                                (Backend.typedProblemClaim problem)
                             )
                           ])
                    (Provers.runPreparedTypedProver vampire prepared)
        modules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap resolver
                AlwaysMissValidation workspace
        sealed <- sole "transparent-wrapper nested module" modules
        observations <- readIORef observed
        assertEqual "wrapper guard plus monotonicity request count"
            2 (length observations)
        (route, target) <- case
                [ observation
                | observation@(_route, candidate) <- observations
                , candidate == expectedPowerMonotonicity
                ] of
            [observation] -> pure observation
            matches ->
                assertFailure
                    ("normalized wrapper monotonicity matches: "
                        <> show matches
                        <> "; observed: " <> show observations)
                    >> fail "unreachable"
        assertEqual "transparent-wrapper monotonicity is FOF"
            Backend.RouteFof route
        assertEqual "transparent-wrapper monotonicity target"
            expectedPowerMonotonicity target
        case Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed) of
            [_wrapperDefinition, _guardProof, inductiveBatch] -> do
                let facts =
                        Semantic.declarationDeltaFacts
                            (Commit.committedBatchDelta inductiveBatch)
                assertEqual "transparent-wrapper inductive stays clean"
                    (replicate 6 Authority.cleanAuthoritySafety)
                    ( Authority.factAuthoritySafety
                        . Semantic.semanticFactAuthority
                        <$> facts
                    )
                validation <- maybe
                    (assertFailure
                        "transparent-wrapper declaration validation absent"
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation
                        inductiveBatch)
                assertEqual "transparent-wrapper staged authority"
                    [ "definition"
                    , "source-proof"
                    , "kernel"
                    , "kernel"
                    , "kernel"
                    , "kernel"
                    ]
                    (authorizationKind
                        . Authority.validationDirectAuthorization
                        <$> Semantic.declarationValidationRecordCertificates
                            validation)
            batches ->
                assertFailure
                    ("transparent-wrapper declaration count: "
                        <> show (length batches))
  where
    authorizationKind = \case
        Authority.CheckedKernelConstruction
                Authority.CheckedDefinitionEquation{} -> "definition"
        Authority.CheckedKernelConstruction{} -> "kernel"
        Authority.CheckedSourceProof{} -> "source-proof"
        authorization -> show authorization

    expectedPowerMonotonicity =
        Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CForall Core.TySet
                        (Core.CImp
                            (subset (Core.CBound 1) (Core.CBound 0))
                            (subset
                                (power (Core.CBound 1))
                                (power (Core.CBound 0)))))))

    power argument =
        Core.CApp (Core.CIntrinsic Core.PowerSet) argument

    subset left right =
        Core.CForall Core.TySet
            (Core.CImp
                (member
                    (Core.CBound 0)
                    (Core.shiftCanonical 1 0 left))
                (member
                    (Core.CBound 0)
                    (Core.shiftCanonical 1 0 right)))

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

normalizesNestedInductiveContexts :: Assertion
normalizesNestedInductiveContexts = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = (TypedInductive.InductiveVariable 0, Core.TySet)
        x = (TypedInductive.InductiveVariable 1, Core.TySet)
        y = (TypedInductive.InductiveVariable 2, Core.TySet)
        z = (TypedInductive.InductiveVariable 3, Core.TySet)
        variables = [a, x, y, z]
    domain <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping
                [a] [Core.TySet] (Core.CIntrinsic Core.Empty)
    xTerm <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping
                variables (Core.TySet <$ variables) (Core.CBound 2)
    yTerm <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping
                variables (Core.TySet <$ variables) (Core.CBound 1)
    zTerm <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping
                variables (Core.TySet <$ variables) (Core.CBound 0)
    result <-
        checkedInductiveTerm
            GlobalTyping.emptyGlobalTyping
                variables (Core.TySet <$ variables) (Core.CBound 3)
    powerContext <-
        checkedInductiveContext
            GlobalTyping.emptyGlobalTyping variables (power (Core.CBound 0))
    doublePowerContext <-
        checkedInductiveContext
            GlobalTyping.emptyGlobalTyping
                variables (power (power (Core.CBound 0)))
    parameterizedContext <-
        checkedInductiveContext
            GlobalTyping.emptyGlobalTyping variables
            (power (pair (Core.CBound 0) (Core.CBound 3)))
    deduplicated <-
        expectRight
            (TypedInductive.prepareTypedInductive
                GlobalTyping.emptyGlobalTyping
                foundation
                "nested_dedup"
                (TypedInductive.DirectInductive
                    [a]
                    domain
                    (TypedInductive.DirectInductiveClause
                        [x, y, z]
                        [ TypedInductive.DirectRecursiveCondition
                            xTerm powerContext
                        , TypedInductive.DirectRecursiveCondition
                            yTerm powerContext
                        , TypedInductive.DirectRecursiveCondition
                            zTerm doublePowerContext
                        , TypedInductive.DirectRecursiveCondition
                            zTerm parameterizedContext
                        ]
                        result
                        :| [])))
    assertEqual "equal contexts deduplicate in first-occurrence order"
        [ monotonicityTarget 4 power
        , monotonicityTarget 4 (power . power)
        , monotonicityTarget 4
            (\hole -> power (pair hole (Core.CBound 4)))
        ]
        ( Core.frozenCoreTerm
            . TypedInductive.typedInductiveMonotonicityTarget
            <$> Vector.toList
                (TypedInductive.typedInductiveMonotonicities deduplicated)
        )

    assertCompileFailure
        "test/phase5/exact-inductive-wrong-arguments.tex"
        4
        (\case
            Inductive.InductiveRecursiveCarrierWrongArguments{} ->
                True
            _ -> False)
    assertCompileFailure
        "test/phase5/exact-inductive-outside-membership.tex"
        4
        (\case
            Inductive.InductiveRecursiveCarrierOutsideMembership{} ->
                True
            _ -> False)
    assertCompileFailure
        "test/phase5/exact-inductive-recursive-element.tex"
        4
        (\case
            Inductive.InductiveRecursiveTermMentionsCarrier{} ->
                True
            _ -> False)
    assertCompileFailure
        "test/phase5/exact-inductive-recursive-domain.tex"
        2
        (\case
            Inductive.InductiveDomainMentionsCarrier{} -> True
            _ -> False)
    assertCompileFailure
        "test/phase5/exact-inductive-recursive-result.tex"
        4
        (\case
            Inductive.InductiveResultMentionsCarrier{} -> True
            _ -> False)
    assertCompileFailure
        "test/phase5/exact-inductive-unsupported-context.tex"
        4
        (\case
            Inductive.InductiveUnsupportedRecursiveCarrierContext{} ->
                True
            _ -> False)
  where
    assertCompileFailure relative expectedLine expected =
        prepareInductiveFixture relative >>= \case
            Left failure
                | expected failure ->
                    assertEqual
                        ("nested-context failure line for " <> relative)
                        expectedLine
                        (locLine
                            (Inductive.inductiveErrorLocation
                                failure))
                | otherwise ->
                    assertFailure
                        ("unexpected nested-context failure for "
                            <> relative <> ": " <> show failure)
            Right{} ->
                assertFailure
                    ("unsupported nested context was accepted: " <> relative)

    monotonicityTarget
        :: Int
        -> (Core.CanonicalTerm global
            -> Core.CanonicalTerm global)
        -> Core.CanonicalTerm global
    monotonicityTarget sourceBinders context =
        foldr
            (const (Core.CForall Core.TySet))
            (Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CImp
                        (subset (Core.CBound 1) (Core.CBound 0))
                        (subset
                            (context (Core.CBound 1))
                            (context (Core.CBound 0))))))
            [1 .. sourceBinders]

    power argument =
        Core.CApp (Core.CIntrinsic Core.PowerSet) argument

    pair left right =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.PairSet) left)
            right

    subset left right =
        Core.CForall Core.TySet
            (Core.CImp
                (member
                    (Core.CBound 0)
                    (Core.shiftCanonical 1 0 left))
                (member
                    (Core.CBound 0)
                    (Core.shiftCanonical 1 0 right)))

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

compilesAndReusesInductives :: Assertion
compilesAndReusesInductives =
    Temp.withSystemTempDirectory "felix-exact-inductive" \directory -> do
        let relative = "test/phase5/exact-inductive.tex"
            storePath = directory Posix.</> "store.sqlite"
        (foundation, bootstrap, workspace, freshModules) <-
            compileFixture relative
        fresh <- sole "fresh exact inductive module" freshModules
        assertInductiveModule foundation "fresh" fresh
        parsed <-
            sole "exact inductive parsed module"
                (toList
                    (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        let artefact sealed = do
                key <- expectRight
                    (Semantic.moduleArtefactKey
                        (moduleName (Parsed.parsedModuleAddress parsed))
                        (Parsed.parsedModuleId parsed)
                        [ Semantic.semanticInterfaceAssertedId
                            (completedModuleSemantic
                                (Module.bootstrapPreludeCompleted bootstrap))
                        ]
                        (Identity.theoryId foundation))
                pure
                    (Semantic.moduleArtefactResult
                        key
                        (Syntax.moduleSyntaxAssertedId
                            (completedModuleSyntax sealed))
                        (Semantic.semanticInterfaceAssertedId
                            (completedModuleSemantic sealed))
                        (sealedValidationCertificates sealed))
        freshArtefact <- artefact fresh
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation
                        bootstrap
                        unusedResolver
                        validation
                        workspace
                warm <- sole "warm exact inductive module" warmModules
                assertInductiveModule foundation "warm" warm
                assertEqual "warm exact inductive semantic interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm exact inductive final prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))
                assertEqual "warm exact inductive module artefact"
                    freshArtefact
                    =<< artefact warm

authorizesRecursiveInductives :: Assertion
authorizesRecursiveInductives =
    Temp.withSystemTempDirectory "felix-recursive-inductive" \directory -> do
        let relative = "test/phase5/exact-inductive-recursive.tex"
            storePath = directory Posix.</> "store.sqlite"
        (foundation, bootstrap, workspace, freshModules) <-
            compileFixture relative
        fresh <- sole "fresh recursive inductive module" freshModules
        assertRecursiveInductiveModule "fresh" fresh
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation
                        bootstrap
                        unusedResolver
                        validation
                        workspace
                warm <- sole "warm recursive inductive module" warmModules
                assertRecursiveInductiveModule "warm" warm
                assertEqual "warm recursive inductive semantic interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm recursive inductive final prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))

assertRecursiveInductiveModule
    :: String
    -> Module.CompletedTypedModule
    -> Assertion
assertRecursiveInductiveModule label sealed =
    case Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed) of
        [_axiomBatch, inductiveBatch] -> do
            object <-
                sole (label <> " recursive inductive carrier")
                    (Commit.committedBatchObjects inductiveBatch)
            let facts =
                    Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta inductiveBatch)
                sourceSafety =
                    Authority.authoritySafety
                        (Authority.singletonEscapeKind
                            Authority.SourceAxiom)
            assertEqual (label <> " recursive inductive safety")
                (Authority.cleanAuthoritySafety : replicate 4 sourceSafety)
                ( Authority.factAuthoritySafety
                    . Semantic.semanticFactAuthority
                    <$> facts
                )
            validation <-
                maybe
                    (assertFailure
                        (label <> ": recursive validation is absent")
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation
                        inductiveBatch)
            assertEqual (label <> " recursive inductive descriptors")
                [ Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionEquation
                        (Identity.assertedObjectId object))
                , guardedRules
                    (Foundation.SetLfpBound :| [Foundation.SetLfpFixed])
                , guardedRules (Foundation.SetLfpBound :| [])
                , guardedRules (Foundation.SetLfpFixed :| [])
                , guardedRules (Foundation.SetLfpInduct :| [])
                ]
                ( Authority.validationDirectAuthorization
                    <$> Semantic.declarationValidationRecordCertificates
                        validation
                )
        batches ->
            assertFailure
                (label <> ": expected axiom and inductive batches, found "
                    <> show (length batches))
  where
    guardedRules rules =
        Authority.CheckedKernelConstruction
            (Authority.GuardedFoundationRules
                (Authority.guardedRuleSet rules))

assertDatatypeModule
    :: String
    -> Module.CompletedTypedModule
    -> Assertion
assertDatatypeModule label sealed = do
    assertEqual (label <> " datatype semantic declaration count")
        1
        (length
            (Semantic.semanticInterfaceDeclarations
                (completedModuleSemantic sealed)))
    batch <-
        sole (label <> " datatype declaration batch")
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed))
    let objects = Commit.committedBatchObjects batch
        objectIds = Identity.assertedObjectId <$> objects
        delta = Commit.committedBatchDelta batch
        facts = Semantic.declarationDeltaFacts delta
        aliases = Semantic.declarationDeltaAliases delta
        bindings =
            Semantic.semanticEnvironmentBindings
                (Semantic.declarationDeltaEnvironment delta)
        boundIds =
            Semantic.semanticGlobalTargetObject
                . Semantic.semanticGlobalBindingTarget
                <$> bindings
    assertEqual (label <> " datatype object count") 5 (length objects)
    assertBool (label <> " datatype objects are definitions")
        (all
            ((== Identity.TransparentObject)
                . Identity.objectIdFamily
                . Identity.assertedObjectId)
            objects)
    assertEqual (label <> " datatype global binding count")
        4
        (length bindings)
    assertBool (label <> " datatype globals are references")
        (all
            (\binding ->
                case Semantic.semanticGlobalBindingTarget binding of
                    Semantic.GlobalReference{} -> True
                    Semantic.TransparentExpansion{} -> False
                    Semantic.ContextualTransparentExpansion{} -> False)
            bindings)
    assertBool (label <> " datatype source bindings refer to declared objects")
        (Set.fromList boundIds `Set.isSubsetOf` Set.fromList objectIds)
    assertEqual (label <> " no automatic representation views") []
        (Semantic.declarationDeltaDefinitionViews delta)
    assertEqual (label <> " datatype public fact count") 11
        (length (filter ((== Semantic.SearchEligible) . Semantic.semanticFactSearchEligibility) facts))
    assertEqual (label <> " datatype aliases")
        (Semantic.semanticName <$>
            [ "phase5_data_phasefivezero_intro"
            , "phase5_data_phasefiveatom_intro"
            , "phase5_data_phasefivejoin_intro"
            , "phase5_data_phasefivezero_phasefiveatom_distinct"
            , "phase5_data_phasefivezero_phasefivejoin_distinct"
            , "phase5_data_phasefiveatom_phasefivejoin_distinct"
            , "phase5_data_phasefiveatom_injective"
            , "phase5_data_phasefivejoin_injective"
            , "phase5_data_cases"
            , "phase5_data_induct"
            , "phase5_data_predicate_induct"
            ])
        (Semantic.semanticAliasName <$> aliases)
    assertBool (label <> " datatype facts are clean")
        (all
            ((== Authority.cleanAuthoritySafety)
                . Authority.factAuthoritySafety
                . Semantic.semanticFactAuthority)
            facts)
    validation <-
        maybe
            (assertFailure (label <> ": datatype validation is absent")
                >> fail "unreachable")
            pure
            (Commit.committedBatchDeclarationValidation batch)
    let authorizations = Authority.validationDirectAuthorization
            <$> Semantic.declarationValidationRecordCertificates validation
    assertEqual (label <> " every datatype fact has a certificate")
        (length facts) (length authorizations)
    assertEqual (label <> " five conservative implementation equations")
        5 (length [() | Authority.CheckedKernelConstruction
            Authority.CheckedImplementationDefinition{} <- authorizations])
    assertBool (label <> " every remaining law has a replayed derivation")
        (all (\case
            Authority.CheckedKernelConstruction Authority.CheckedImplementationDefinition{} -> True
            Authority.CheckedKernelConstruction Authority.CheckedDerivedConstruction -> True
            _ -> False) authorizations)

assertInductiveModule
    :: Foundation.CheckedFoundation
    -> String
    -> Module.CompletedTypedModule
    -> Assertion
assertInductiveModule foundation label sealed =
    case Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed) of
        [batch] -> do
            object <-
                sole (label <> " inductive carrier")
                    (Commit.committedBatchObjects batch)
            case Identity.assertedObjectContent object of
                Identity.TransparentObjectContent
                        _theory coreType body -> do
                    assertEqual (label <> " inductive carrier type")
                        (Core.TyArrow Core.TySet Core.TySet)
                        coreType
                    assertEqual (label <> " inductive carrier identity")
                        (Identity.transparentObjectId
                            (Identity.theoryId foundation)
                            coreType
                            body)
                        (Identity.assertedObjectId object)
                content ->
                    assertFailure
                        (label <> ": unexpected inductive carrier "
                            <> show content)
            let delta = Commit.committedBatchDelta batch
                facts = Semantic.declarationDeltaFacts delta
                aliases = Semantic.declarationDeltaAliases delta
            assertEqual (label <> " inductive fact count")
                5
                (length facts)
            assertEqual (label <> " inductive aliases")
                (Semantic.semanticName <$>
                    [ "phase5_fin"
                    , "phase5_fin_intro_1"
                    , "phase5_fin_dom_subset"
                    , "phase5_fin_cases"
                    , "phase5_fin_induct"
                    ])
                (Semantic.semanticAliasName <$> aliases)
            assertBool (label <> " inductive facts are clean")
                (all
                    ((== Authority.cleanAuthoritySafety)
                        . Authority.factAuthoritySafety
                        . Semantic.semanticFactAuthority)
                    facts)
            assertEqual (label <> " inductive proof validations")
                []
                (Commit.committedBatchProofValidations batch)
            validation <-
                maybe
                    (assertFailure
                        (label <> ": inductive validation is absent")
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation batch)
            assertEqual (label <> " inductive validation descriptors")
                [ Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionEquation
                        (Identity.assertedObjectId object))
                , guardedRules (Foundation.SetLfpFixed :| [])
                , guardedRules (Foundation.SetLfpBound :| [])
                , guardedRules (Foundation.SetLfpFixed :| [])
                , guardedRules (Foundation.SetLfpInduct :| [])
                ]
                ( Authority.validationDirectAuthorization
                    <$> Semantic.declarationValidationRecordCertificates
                        validation
                )
        batches ->
            assertFailure
                (label <> ": expected one inductive batch, found "
                    <> show (length batches))
  where
    guardedRules rules =
        Authority.CheckedKernelConstruction
            (Authority.GuardedFoundationRules
                (Authority.guardedRuleSet rules))

assertFiniteSetModule
    :: String
    -> Module.CompletedTypedModule
    -> Assertion
assertFiniteSetModule label sealed = do
    assertEqual (label <> " finite-set semantic declarations")
        2
        (length
            (Semantic.semanticInterfaceDeclarations
                (completedModuleSemantic sealed)))
    case Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed) of
        [definitionBatch, theoremBatch] -> do
            definitionObject <- sole
                (label <> " finite-set definition object")
                (Commit.committedBatchObjects definitionBatch)
            case Identity.assertedObjectContent definitionObject of
                Identity.TransparentObjectContent
                        _theory coreType body -> do
                    assertEqual (label <> " finite-set definition type")
                        (Core.TyArrow Core.TySet
                            (Core.TyArrow Core.TySet Core.TySet))
                        coreType
                    assertEqual (label <> " finite-set definition body")
                        expectedBody
                        body
                content ->
                    assertFailure
                        (label <> ": unexpected finite-set object "
                            <> show content)
            assertEqual (label <> " finite-set definition fact count")
                1
                (length
                    (Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta definitionBatch)))
            assertEqual (label <> " finite-set definition proof validations")
                []
                (Commit.committedBatchProofValidations definitionBatch)

            assertEqual (label <> " finite-set theorem adds no object")
                []
                (Commit.committedBatchObjects theoremBatch)
            theoremFact <- sole
                (label <> " finite-set theorem fact")
                (Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta theoremBatch))
            assertEqual (label <> " finite-set theorem safety")
                Authority.cleanAuthoritySafety
                (Authority.factAuthoritySafety
                    (Semantic.semanticFactAuthority theoremFact))
            theoremValidation <- sole
                (label <> " finite-set theorem validation")
                (Commit.committedBatchProofValidations theoremBatch)
            case Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate
                        theoremValidation) of
                Authority.CheckedSourceProof
                        (Authority.UsesExternalProof (_request :| [])) ->
                    pure ()
                authorization ->
                    assertFailure
                        (label <> ": unexpected finite-set theorem authority "
                            <> show authorization)
        batches ->
            assertFailure
                (label <> ": expected finite-set definition and theorem, found "
                    <> show (length batches))
  where
    expectedBody =
        Core.CLam Core.TySet
            (Core.CLam Core.TySet
                (Core.canonicalSetInsert
                    (Core.CBound 1)
                    (Core.canonicalSetInsert
                        (Core.CBound 0)
                        (Core.CIntrinsic Core.Empty))))


compilesSourceAxioms :: Assertion
compilesSourceAxioms =
    Temp.withSystemTempDirectory "felix-exact-source-axiom" \root -> do
        let storePath = root Posix.</> "store.sqlite"
        (foundation, bootstrap, workspace, freshModules) <-
            compileFixture
                "test/phase5/exact-source-axiom-assumptions.tex"
        fresh <- sole "fresh source-axiom module" freshModules
        assertSourceAxiom "fresh" fresh
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation bootstrap unusedResolver validation workspace
                warm <- sole "warm source-axiom module" warmModules
                assertSourceAxiom "warm" warm
                assertEqual "warm source axiom preserves semantics"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm source axiom preserves prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))
  where
    assertSourceAxiom label sealed = do
        batch <- sole (label <> " source-axiom batch")
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed))
        fact <- sole (label <> " source-axiom fact")
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta batch))
        alias <- sole (label <> " source-axiom alias")
            (Semantic.declarationDeltaAliases
                (Commit.committedBatchDelta batch))
        assertEqual (label <> " source-axiom search eligibility")
            Semantic.SearchEligible
            (Semantic.semanticFactSearchEligibility fact)
        assertEqual (label <> " source-axiom marker alias")
            (Semantic.semanticName "phase5_exact_source_axiom_assumptions")
            (Semantic.semanticAliasName alias)
        proposition <- sole (label <> " source-axiom proposition")
            (Commit.committedBatchPropositions batch)
        assertEqual (label <> " source-axiom closed target")
            (Core.CForall Core.TySet
                (Core.CForall Core.TySet
                    (Core.CImp
                        (member (Core.CBound 0) (Core.CBound 1))
                        (Core.CImp
                            (Core.CEq Core.TySet
                                (Core.CBound 0)
                                (Core.CBound 0))
                            (member
                                (Core.CBound 0)
                                (Core.CBound 1))))))
            (Core.frozenCoreTerm
                (Identity.checkedPropositionTerm proposition))
        assertEqual (label <> " source-axiom safety")
            (Authority.authoritySafety
                (Authority.singletonEscapeKind Authority.SourceAxiom))
            (Authority.factAuthoritySafety
                (Semantic.semanticFactAuthority fact))
        validation <-
            maybe
                (assertFailure (label <> " source-axiom validation is absent")
                    >> fail "unreachable")
                pure
                (Commit.committedBatchDeclarationValidation batch)
        certificate <- sole (label <> " source-axiom certificate")
            (Semantic.declarationValidationRecordCertificates validation)
        assertEqual (label <> " source-axiom direct authority")
            Authority.SourceAxiomAuthorization
            (Authority.validationDirectAuthorization certificate)
        assertEqual (label <> " source axiom has no proof validations")
            []
            (Commit.committedBatchProofValidations batch)

    member element set =
        Core.CApp
            (Core.CApp
                (Core.CIntrinsic Core.Member)
                element)
            set

rejectsProofLocalGeneralization :: Assertion
rejectsProofLocalGeneralization = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation unusedResolver
    repository <- getCurrentDirectory
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts
        "test/phase5/exact-proof-local-free.tex"
    input <- expectRightIO
        (typedModuleInput
            foundation
            (Module.bootstrapPreludeReadiness bootstrap)
            unusedResolver
            AlwaysMissValidation
            (Parsed.parsedWorkspaceRootModule workspace)
            [])
    runTypedModule input >>= \case
        Module.TypedModuleFailed
                (Module.TypedActionFailed
                    (Module.TypedProofFailed
                        (Proof.ProofElaborationFailed
                            (Elaboration.ElaborationFreeVariable location
                                (Raw.NamedVar "y")))))
                prefix -> do
            assertEqual "proof-local free variable line"
                6 (locLine location)
            assertEqual "proof-local failure commits nothing"
                0
                (length
                    (Commit.pendingModulePrefixBatches prefix))
        Module.TypedModuleSucceeded{} ->
            assertFailure "proof-local variable was generalized"
        Module.TypedModuleOpenFailed failure ->
            assertFailure
                ("proof-local generalization module did not open: "
                    <> show failure)
        Module.TypedModuleFailed failure _prefix ->
            assertFailure
                ("unexpected proof-local generalization failure: "
                    <> show failure)

doesNotTreatMarkerOnlyNounAsSet :: Assertion
doesNotTreatMarkerOnlyNounAsSet = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation unusedResolver
    repository <- getCurrentDirectory
    mounts <- exactFixtureMounts repository
    workspace <- parseWorkspace
        bootstrap mounts
        "test/phase5/exact-set-marker.tex"
    Temp.withSystemTempDirectory "felix-exact-set-marker" \root -> do
        let executable = root Posix.</> "vampire"
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for set-marker'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        observed <- newIORef []
        let resolver = Declaration.vampireResolver \prepared -> do
                let problem =
                        Provers.preparedTypedProverLogicalProblem prepared
                    claim = Backend.typedProblemClaim problem
                    locals = Backend.typedProblemLocalPremises problem
                modifyIORef' observed
                    (<> [ [ Backend.supportedPropositionTerm
                                (Backend.typedLocalPremiseProposition premise)
                            == Backend.supportedPropositionTerm claim
                           | premise <- Vector.toList locals
                           ]
                        ])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                resolver
                AlwaysMissValidation
                (Parsed.parsedWorkspaceRootModule workspace)
                [])
        runTypedModule input >>= \case
            Module.TypedModuleSucceeded{} ->
                assertEqual
                    "the source noun supplies an exact structural premise"
                    []
                    =<< readIORef observed
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("marker-only set noun module did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected marker-only set noun failure: "
                        <> show failure)

compilesOmittedProofs :: Assertion
compilesOmittedProofs =
    Temp.withSystemTempDirectory "felix-exact-omitted" \root -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace
            bootstrap mounts "test/phase5/exact-omitted.tex"
        let executable = root Posix.</> "vampire"
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-omitted'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        calls <- newIORef (0 :: Int)
        let resolver = Declaration.vampireResolver \prepared -> do
                modifyIORef' calls (+ 1)
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        modules <-
            compileParsedWorkspaceWithResolver
                foundation bootstrap resolver workspace
        sealed <- sole "exact omitted module" modules
        assertEqual "the non-omitted continuation closes structurally"
            0
            =<< readIORef calls
        let batches =
                Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix sealed)
        assertEqual "top-level and nested omitted declarations"
            2 (length batches)
        for_ (zip ["top-level", "nested"] batches) \(label, batch) -> do
            fact <- sole (label <> " omitted fact")
                (Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta batch))
            assertEqual (label <> " omitted safety")
                (Authority.authoritySafety
                    (Authority.singletonEscapeKind Authority.Omitted))
                (Authority.factAuthoritySafety
                    (Semantic.semanticFactAuthority fact))
            record <- sole (label <> " omitted validation")
                (Commit.committedBatchProofValidations batch)
            assertEqual (label <> " omitted direct authority")
                Authority.OmittedAuthorization
                (Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate record))
            assertEqual (label <> " publishes only its final theorem")
                1
                (length
                    (Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta batch)))

compilesOmittedProofWithKernelFact :: Assertion
compilesOmittedProofWithKernelFact =
    Temp.withSystemTempDirectory "felix-omitted-kernel-fact" \root -> do
        let relative = "omitted-kernel-fact.tex"
            sourcePath = root Posix.</> relative
            source = StrictText.unlines
                [ "\\begin{axiom}\\label{omitted_kernel_source_axiom}"
                , "    $\\emptyset \\in \\emptyset$."
                , "\\end{axiom}"
                , ""
                , "\\begin{proposition}\\label{omitted_kernel_dependency}"
                , "    $\\emptyset \\in \\emptyset$."
                , "\\end{proposition}"
                , "\\begin{proof}"
                , "    Show $\\emptyset = \\emptyset$."
                , "    \\begin{subproof}"
                , "        Omitted."
                , "    \\end{subproof}"
                , "    Follows by \\obv{omitted_kernel_source_axiom}."
                , "\\end{proof}"
                ]
        ByteString.writeFile sourcePath (Text.encodeUtf8 source)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        calls <- newIORef (0 :: Int)
        let resolver = Declaration.vampireResolver \_prepared -> do
                modifyIORef' calls (+ 1)
                assertFailure "omitted kernel fact proof invoked Vampire"
                    >> fail "unreachable"
        modules <-
            compileParsedWorkspaceWithResolver
                foundation bootstrap resolver workspace
        assertEqual "omitted kernel fact proof has no Vampire requests"
            0
            =<< readIORef calls
        sealed <- sole "omitted kernel fact module" modules
        batches <- pure
            (Commit.pendingModulePrefixBatches
                (Module.completedTypedModulePrefix sealed))
        case batches of
            [_sourceAxiomBatch, theoremBatch] -> do
                fact <- sole "omitted kernel fact theorem"
                    (Semantic.declarationDeltaFacts
                        (Commit.committedBatchDelta theoremBatch))
                assertEqual "omitted kernel fact safety"
                    (sort
                        [ Authority.Omitted
                        , Authority.SourceAxiom
                        ])
                    (sort
                        (Authority.escapeKindsToList
                            (Authority.authoritySafetyEscapeKinds
                                (Authority.factAuthoritySafety
                                    (Semantic.semanticFactAuthority fact)))))
                record <- sole "omitted kernel fact validation"
                    (Commit.committedBatchProofValidations theoremBatch)
                assertEqual "omitted kernel fact direct authorization"
                    Authority.OmittedAuthorization
                    (Authority.validationDirectAuthorization
                        (Semantic.proofValidationRecordCertificate record))
            other ->
                assertFailure
                    ("unexpected omitted kernel fact batch count: "
                        <> show (length other))

reusesEscapeAuthority :: Assertion
reusesEscapeAuthority =
    Temp.withSystemTempDirectory "felix-exact-escape-cache" \root -> do
        let consumerRelative = "test/phase5/exact-escape-consumer.tex"
            producerRelative = "test/phase5/exact-escape-producer.tex"
            consumerPath = root Posix.</> consumerRelative
            producerPath = root Posix.</> producerRelative
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        createDirectoryIfMissing True (Posix.takeDirectory consumerPath)
        consumerSource <- ByteString.readFile consumerRelative
        producerSource <- ByteString.readFile producerRelative
        ByteString.writeFile consumerPath consumerSource
        ByteString.writeFile producerPath producerSource
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-escape'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts root
        freshWorkspace <-
            parseWorkspace bootstrap mounts consumerRelative
        freshRuns <- newIORef (0 :: Int)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap
                (acceptedResolver executable freshRuns)
                AlwaysMissValidation
                freshWorkspace
        assertEqual "fresh escape graph Vampire requests"
            4
            =<< readIORef freshRuns
        assertEscapeGraph "fresh" freshModules
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                traverse_
                    (expectRightIO
                        . Store.writePendingModulePrefix storeCheck
                        . Module.completedTypedModulePrefix)
                    freshModules
                let validation = storeValidationPolicy storeCheck
                    compileWarm workspace = do
                        runs <- newIORef (0 :: Int)
                        modules <-
                            compileParsedWorkspaceWithValidation
                                foundation bootstrap
                                (acceptedResolver executable runs)
                                validation
                                workspace
                        runCount <- readIORef runs
                        pure (modules, runCount)
                (warmModules, warmRuns) <- compileWarm freshWorkspace
                assertEqual "exact escape warm hit skips Vampire"
                    0 warmRuns
                assertEscapeGraph "warm" warmModules
                assertEqual "warm escape graph preserves module semantics"
                    (moduleSemantics freshModules)
                    (moduleSemantics warmModules)
                assertEqual "warm escape graph preserves module prefixes"
                    (modulePrefixes freshModules)
                    (modulePrefixes warmModules)

                let formattingOnly =
                        Text.encodeUtf8
                            ("% shifted exact escape source\n"
                                <> Text.decodeUtf8 consumerSource)
                ByteString.writeFile consumerPath formattingOnly
                formattedWorkspace <-
                    parseWorkspace bootstrap mounts consumerRelative
                assertBool "formatting changes the escape parsed identity"
                    (Parsed.parsedModuleId
                        (Parsed.parsedWorkspaceRootModule freshWorkspace)
                        /= Parsed.parsedModuleId
                            (Parsed.parsedWorkspaceRootModule
                                formattedWorkspace))
                (formattedModules, formattedRuns) <-
                    compileWarm formattedWorkspace
                assertEqual "formatting-only escape edit reuses validation"
                    0 formattedRuns
                assertEqual "formatting-only escape edit preserves semantics"
                    (moduleSemantics freshModules)
                    (moduleSemantics formattedModules)

                let omittedGoalEdit =
                        Text.encodeUtf8
                            (StrictText.replace
                                "    Show $x = x$."
                                "    Show if $x = x$, then $x = x$."
                                (Text.decodeUtf8 consumerSource))
                ByteString.writeFile consumerPath omittedGoalEdit
                editedWorkspace <-
                    parseWorkspace bootstrap mounts consumerRelative
                (editedModules, editedRuns) <-
                    compileWarm editedWorkspace
                assertEqual "changed omitted goal misses its proof validation"
                    1 editedRuns
                assertEqual "changed omitted goal preserves public semantics"
                    (moduleSemantics freshModules)
                    (moduleSemantics editedModules)
  where
    acceptedResolver executable runs =
        Declaration.vampireResolver \prepared -> do
            modifyIORef' runs (+ 1)
            (Provers.runPreparedTypedProver
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared)

    moduleSemantics = fmap completedModuleSemantic
    modulePrefixes =
        fmap
            (Commit.pendingModulePrefixCurrent
                . Module.completedTypedModulePrefix)

    assertEscapeGraph label = \case
        [producer, consumer] -> do
            let producerBatches =
                    Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix producer)
                consumerBatches =
                    Commit.pendingModulePrefixBatches
                        (Module.completedTypedModulePrefix consumer)
            case producerBatches of
                [sourceAxiom, omitted] -> do
                    assertEscapeSafety
                        (label <> " source axiom")
                        [Authority.SourceAxiom]
                        sourceAxiom
                    assertDeclarationDirect
                        (label <> " source axiom")
                        Authority.SourceAxiomAuthorization
                        sourceAxiom
                    assertEscapeSafety
                        (label <> " omitted theorem")
                        [Authority.Omitted]
                        omitted
                    assertProofDirectOmitted
                        (label <> " omitted theorem")
                        omitted
                batches ->
                    assertFailure
                        (label <> " producer batch count: "
                            <> show (length batches))
            case consumerBatches of
                [fromAxiom, fromOmitted, throughLocal, ownOmission] -> do
                    assertEscapeSafety
                        (label <> " source-axiom consumer")
                        [Authority.SourceAxiom]
                        fromAxiom
                    assertProofDirectChecked
                        (label <> " source-axiom consumer") 1 fromAxiom
                    assertEscapeSafety
                        (label <> " omitted consumer")
                        [Authority.Omitted]
                        fromOmitted
                    assertProofDirectChecked
                        (label <> " omitted consumer") 1 fromOmitted
                    assertEscapeSafety
                        (label <> " local source-axiom consumer")
                        [Authority.SourceAxiom]
                        throughLocal
                    assertProofDirectChecked
                        (label <> " local source-axiom consumer")
                        1 throughLocal
                    assertEscapeSafety
                        (label <> " own omission")
                        [Authority.SourceAxiom, Authority.Omitted]
                        ownOmission
                    assertProofDirectOmitted
                        (label <> " own omission") ownOmission
                batches ->
                    assertFailure
                        (label <> " consumer batch count: "
                            <> show (length batches))
        modules ->
            assertFailure
                (label <> " escape module count: "
                    <> show (length modules))

    assertEscapeSafety label expected batch = do
        fact <- sole (label <> " fact")
            (Semantic.declarationDeltaFacts
                (Commit.committedBatchDelta batch))
        assertEqual (label <> " public escape kinds")
            expected
            (Authority.escapeKindsToList
                (Authority.authoritySafetyEscapeKinds
                    (Authority.factAuthoritySafety
                        (Semantic.semanticFactAuthority fact))))

    assertDeclarationDirect label expected batch = do
        validation <-
            maybe
                (assertFailure (label <> " declaration validation is absent")
                    >> fail "unreachable")
                pure
                (Commit.committedBatchDeclarationValidation batch)
        certificate <- sole (label <> " declaration certificate")
            (Semantic.declarationValidationRecordCertificates validation)
        assertEqual (label <> " direct authorization")
            expected
            (Authority.validationDirectAuthorization certificate)

    assertProofDirectChecked label expectedCount batch = do
        authorization <- proofDirect label batch
        case authorization of
            Authority.CheckedSourceProof requests ->
                assertEqual (label <> " accepted request count")
                    expectedCount
                    (length (Authority.externalProofUseRequests requests))
            direct ->
                assertFailure
                    (label <> " has unexpected direct authority: "
                        <> show direct)

    assertProofDirectOmitted label batch = do
        authorization <- proofDirect label batch
        assertEqual (label <> " direct authorization")
            Authority.OmittedAuthorization authorization

    proofDirect label batch = do
        record <- sole (label <> " proof validation")
            (Commit.committedBatchProofValidations batch)
        pure
            (Authority.validationDirectAuthorization
                (Semantic.proofValidationRecordCertificate record))

rejectsAfterOmittedSubclaim :: Assertion
rejectsAfterOmittedSubclaim =
    Temp.withSystemTempDirectory "felix-exact-omitted-rollback" \root -> do
        repository <- getCurrentDirectory
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts repository
        workspace <- parseWorkspace
            bootstrap mounts "test/phase5/exact-escape-consumer.tex"
        parsedModules <-
            pure
                (toList
                    (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        (producerParsed, consumerParsed) <-
            case parsedModules of
                [producer, consumer] -> pure (producer, consumer)
                modules ->
                    assertFailure
                        ("unexpected rollback graph size: "
                            <> show (length modules))
                        >> fail "unreachable"
        producerInput <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                producerParsed
                [])
        producer <- runTypedModule producerInput >>= \case
            Module.TypedModuleSucceeded sealed -> pure sealed
            _ ->
                assertFailure "escape producer did not seal"
                    >> fail "unreachable"
        let executable = root Posix.</> "vampire"
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for omitted-rollback'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        calls <- newIORef (0 :: Int)
        let resolver = Declaration.vampireResolver \prepared -> do
                runCount <- readIORef calls
                modifyIORef' calls (+ 1)
                if runCount < 3
                    then
                        (Provers.runPreparedTypedProver
                                (Provers.vampire
                                    executable
                                    Provers.defaultTimeLimit
                                    Provers.defaultMemoryLimit)
                                prepared)
                    else
                        pure
                            (counterexampleResolution prepared)
        consumerInput <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                resolver
                AlwaysMissValidation
                consumerParsed
                [producer])
        runTypedModule consumerInput >>= \case
            Module.TypedModuleFailed
                    (Module.TypedDeclarationFailed
                        (Declaration.ProofObligationFailedAt
                            location
                            Declaration.VampireObligationFailed{}))
                    prefix -> do
                assertEqual "the continuation is the fourth request"
                    4
                    =<< readIORef calls
                assertEqual "rejected continuation location"
                    37 (locLine location)
                assertEqual "omitted declaration rolls back atomically"
                    3
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure "rejected omitted continuation was accepted"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("omitted rollback module did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected omitted rollback failure: "
                        <> show failure)

rejectsFixedSemanticDeclaration :: Assertion
rejectsFixedSemanticDeclaration =
    Temp.withSystemTempDirectory "felix-fixed-semantic" \root -> do
        let relative = "entry.tex"
            path = root Posix.</> relative
            source =
                "\\begin{signature}\\label{source_unions}\n"
                    <> "    $\\unions{X}$ is a set.\n"
                    <> "\\end{signature}\n"
        ByteString.writeFile path
            (Text.encodeUtf8 (StrictText.pack source))
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        let parsed = Parsed.parsedWorkspaceRootModule workspace
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedElaborationFailed
                            (Elaboration.ElaborationFixedSemanticCollision
                                location key)))
                    prefix -> do
                assertEqual "fixed collision line" 1 (locLine location)
                assertEqual "fixed collision key"
                    (Semantic.SemanticExpressionFunction
                        (Raw.TokenCons (Raw.Command "unions")
                            (Raw.TokenCons Raw.InvisibleBraceL
                                (Raw.HoleCons
                                    (Raw.TokenCons
                                        Raw.InvisibleBraceR Raw.End)))))
                    key
                assertEqual "fixed collision commits no prefix"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure "fixed semantic declaration was accepted"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("fixed semantic module did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected fixed semantic failure: "
                        <> show failure)

rejectsFixedSemanticInductive :: Assertion
rejectsFixedSemanticInductive =
    Temp.withSystemTempDirectory "felix-fixed-inductive" \root -> do
        let relative = "entry.tex"
            path = root Posix.</> relative
            source =
                "\\begin{inductive}\\label{source_pow}\n"
                    <> "    Define $\\pow{A}\\subseteq\\cumul{A}$ inductively as follows.\n"
                    <> "    \\begin{enumerate}\n"
                    <> "        \\item $A\\in\\pow{A}$.\n"
                    <> "    \\end{enumerate}\n"
                    <> "\\end{inductive}\n"
        ByteString.writeFile path
            (Text.encodeUtf8 (StrictText.pack source))
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        let parsed = Parsed.parsedWorkspaceRootModule workspace
        input <- expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                unusedResolver
                AlwaysMissValidation
                parsed
                [])
        runTypedModule input >>= \case
            Module.TypedModuleFailed
                    (Module.TypedActionFailed
                        (Module.TypedInductiveFailed
                            (Inductive.InductiveFixedSemanticCollision
                                location key)))
                    prefix -> do
                assertEqual "fixed inductive collision line"
                    1
                    (locLine location)
                assertEqual "fixed inductive collision key"
                    (Semantic.SemanticExpressionFunction
                        (Raw.TokenCons (Raw.Command "pow")
                            (Raw.TokenCons Raw.InvisibleBraceL
                                (Raw.HoleCons
                                    (Raw.TokenCons
                                        Raw.InvisibleBraceR Raw.End)))))
                    key
                assertEqual "fixed inductive collision commits no prefix"
                    0
                    (length
                        (Commit.pendingModulePrefixBatches prefix))
            Module.TypedModuleSucceeded{} ->
                assertFailure "fixed semantic inductive was accepted"
            Module.TypedModuleOpenFailed failure ->
                assertFailure
                    ("fixed semantic inductive did not open: "
                        <> show failure)
            Module.TypedModuleFailed failure _prefix ->
                assertFailure
                    ("unexpected fixed inductive failure: "
                        <> show failure)

keepsSemanticsIndependentOfFixity :: Assertion
keepsSemanticsIndependentOfFixity =
    Temp.withSystemTempDirectory "felix-exact-fixity" \root -> do
        let relative = "test/phase5/exact-producer.tex"
            path = root Posix.</> relative
        createDirectoryIfMissing True (Posix.takeDirectory path)
        original <- ByteString.readFile relative
        let changed =
                Text.encodeUtf8
                    (StrictText.replace
                        "infixl 2"
                        "infixr 6"
                        (Text.decodeUtf8 original))
        ByteString.writeFile path original
        first <- compileRootAt root relative
        ByteString.writeFile path changed
        second <- compileRootAt root relative
        let firstParsed = Parsed.parsedWorkspaceRootModule (fst first)
            secondParsed = Parsed.parsedWorkspaceRootModule (fst second)
            firstSealed = snd first
            secondSealed = snd second
        assertBool "fixity changes syntax identity"
            (Syntax.moduleSyntaxAssertedId
                (Parsed.parsedModuleSyntaxInterface firstParsed)
                /= Syntax.moduleSyntaxAssertedId
                    (Parsed.parsedModuleSyntaxInterface secondParsed))
        assertBool "fixity changes parsed identity"
            (Parsed.parsedModuleId firstParsed
                /= Parsed.parsedModuleId secondParsed)
        assertEqual "fixity preserves semantic interface"
            (completedModuleSemantic firstSealed)
            (completedModuleSemantic secondSealed)
        assertEqual "fixity preserves semantic prefix"
            (Commit.pendingModulePrefixCurrent
                (Module.completedTypedModulePrefix firstSealed))
            (Commit.pendingModulePrefixCurrent
                (Module.completedTypedModulePrefix secondSealed))

restoresCheckedSetInduction :: Assertion
restoresCheckedSetInduction =
    Temp.withSystemTempDirectory "felix-checked-set-induction" \root -> do
        let executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        writeAcceptedFixtureVampire executable
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation unusedResolver
        mounts <- exactFixtureMounts =<< getCurrentDirectory

        initialWorkspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-induction-initial.tex"
        initialObservations <- newIORef []
        initial <-
            sole "initial set-induction module"
                =<< compileParsedWorkspaceWithValidation
                    foundation bootstrap
                    (observingResolver executable initialObservations)
                    AlwaysMissValidation
                    initialWorkspace
        [initialRequest] <-
            expectCount "initial set-induction request" 1
                =<< readIORef initialObservations
        assertEqual "initial induction retains header then hypothesis ordinals"
            [0, 1]
            (localReasoningLocalOrdinals initialRequest)
        let initialTarget =
                Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)
            initialAntecedent =
                member (Core.CBound 1) (Core.CBound 0)
            initialHypothesis =
                Core.CForall Core.TySet
                    (Core.CImp
                        (member (Core.CBound 0) (Core.CBound 2))
                        (Core.CImp
                            (member (Core.CBound 0) (Core.CBound 1))
                            (Core.CEq Core.TySet
                                (Core.CBound 0)
                                (Core.CBound 0))))
        assertEqual "initial induction child target"
            initialTarget
            (localReasoningTarget initialRequest)
        assertEqual "initial induction uses the complete guarded property"
            [initialAntecedent, initialHypothesis]
            (localReasoningLocalTerms initialRequest)

        nestedWorkspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-induction-nested.tex"
        nestedObservations <- newIORef []
        nested <-
            sole "nested set-induction module"
                =<< compileParsedWorkspaceWithValidation
                    foundation bootstrap
                    (observingResolver executable nestedObservations)
                    AlwaysMissValidation
                    nestedWorkspace
        [nestedChild] <-
            expectCount "nested set-induction requests" 1
                =<< readIORef nestedObservations
        let x = Core.CBound 0
            a = Core.CBound 1
            y = Core.CBound 0
            xUnderY = Core.CBound 1
            aUnderY = Core.CBound 2
            guardAtX =
                andP
                    (member x a)
                    (notP (Core.CEq Core.TySet x a))
            nestedHypothesis =
                Core.CForall Core.TySet
                    (Core.CImp
                        (member y xUnderY)
                        (Core.CImp
                            (member y aUnderY)
                            (Core.CImp
                                (notP (Core.CEq Core.TySet y aUnderY))
                                (Core.CEq Core.TySet y y))))
            nestedTarget = Core.CEq Core.TySet x x
        assertEqual
            "omitted leading induction retains its source binder and guard"
            ([0, 1], [nestedHypothesis, guardAtX], nestedTarget)
            ( localReasoningLocalOrdinals nestedChild
            , localReasoningLocalTerms nestedChild
            , localReasoningTarget nestedChild
            )
        formulaWorkspace <- parseWorkspace bootstrap mounts
            "test/phase5/exact-induction-formula-quantified.tex"
        formulaObservations <- newIORef []
        _formula <-
            sole "formula-quantified set-induction module"
                =<< compileParsedWorkspaceWithValidation
                    foundation bootstrap
                    (observingResolver executable formulaObservations)
                    AlwaysMissValidation
                    formulaWorkspace
        [formulaChild] <-
            expectCount "formula-quantified set-induction requests" 1
                =<< readIORef formulaObservations
        assertEqual
            "formula-quantified omitted induction retains its written binder"
            (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0))
            (localReasoningTarget formulaChild)

        anchorWorkspace <- parseWorkspace bootstrap mounts
            "test/examples/no-reflexive-set.tex"
        anchorObservations <- newIORef []
        _anchor <-
            sole "omitted-focus set-induction module"
                =<< compileParsedWorkspaceWithValidation
                    foundation bootstrap
                    (observingResolver executable anchorObservations)
                    AlwaysMissValidation
                    anchorWorkspace
        [anchorRequest] <-
            expectCount "omitted-focus set-induction request" 1
                =<< readIORef anchorObservations
        anchorLocal <-
            case localReasoningLocalTerms anchorRequest of
                [term] -> pure term
                terms ->
                    assertFailure
                        ("unexpected omitted-focus locals: " <> show terms)
                        >> fail "unreachable"
        assertEqual "omitted focus retains its source binder in the child"
            ([0], Core.CForall Core.TySet
                (Core.CImp
                    (member (Core.CBound 0) (Core.CBound 1))
                    (notP (member (Core.CBound 0) (Core.CBound 0)))))
            ( localReasoningLocalOrdinals anchorRequest
            , anchorLocal
            )

        assertProofParityFailure
            foundation bootstrap mounts
            "test/phase5/exact-induction-ambiguous.tex"
            (\case
                Proof.ProofSetInductionFocusAmbiguous
                        location names ->
                    locLine location == 5
                        && names == Raw.NamedVar "A" :| [Raw.NamedVar "B"]
                _failure -> False)
        assertProofParityFailure
            foundation bootstrap mounts
            "test/phase5/exact-induction-fixed.tex"
            (\case
                Proof.ProofSetInductionActiveBinderIneligible
                        location (Raw.NamedVar "x") ->
                    locLine location == 7
                _failure -> False)

        failedInput <-
            moduleInput
                foundation bootstrap initialWorkspace
                (Declaration.vampireResolver \prepared ->
                    pure (counterexampleResolution prepared))
                AlwaysMissValidation
        runTypedModule failedInput >>= \case
            Module.TypedModuleFailed _failure prefix ->
                assertBool "failed induction child publishes no theorem"
                    (null (Commit.pendingModulePrefixBatches prefix))
            _result ->
                assertFailure "rejected induction child unexpectedly succeeded"

        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix nested))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warm <-
                    sole "warm nested set-induction module"
                        =<< compileParsedWorkspaceWithValidation
                            foundation bootstrap
                            (countingAcceptedResolver executable warmRuns)
                            validation nestedWorkspace
                assertEqual "warm set induction skips Vampire"
                    0 =<< readIORef warmRuns
                assertEqual "fresh and warm induction proof validations"
                    (proofValidations nested)
                    (proofValidations warm)
                assertBool "initial induction publishes one theorem"
                    (not
                        (null
                            (Commit.pendingModulePrefixBatches
                                (Module.completedTypedModulePrefix initial))))
  where
    observingResolver executable observations =
        Declaration.vampireResolver \prepared -> do
            let problem = Provers.preparedTypedProverLogicalProblem prepared
                locals = Backend.typedProblemLocalPremises problem
            modifyIORef' observations
                (<> [ LocalReasoningObservation
                        { localReasoningTarget =
                            Backend.supportedPropositionTerm
                                (Backend.typedProblemClaim problem)
                        , localReasoningGlobalCount =
                            Vector.length
                                (Backend.typedProblemGlobalPremises problem)
                        , localReasoningLocalOrdinals =
                            Backend.localPremiseOrdinalValue
                                . Backend.typedLocalPremiseOrdinal
                                <$> Vector.toList locals
                        , localReasoningLocalTerms =
                            Backend.supportedPropositionTerm
                                . Backend.typedLocalPremiseProposition
                                <$> Vector.toList locals
                        , localReasoningAuxiliaries =
                            Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                        }
                    ])
            (Provers.runPreparedTypedProver
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    prepared)

    expectCount label expected values = do
        assertEqual label expected (length values)
        pure values

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set

    notP = Core.CNot

    andP = Core.CAnd

    moduleInput foundation bootstrap workspace resolver validation = do
        parsed <- sole "set-induction parsed module"
            (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
        expectRightIO
            (typedModuleInput
                foundation
                (Module.bootstrapPreludeReadiness bootstrap)
                resolver validation parsed [])

    proofValidations =
        concatMap Commit.committedBatchProofValidations
            . Commit.pendingModulePrefixBatches
            . Module.completedTypedModulePrefix

restoresCheckedTransfiniteInduction :: Assertion
restoresCheckedTransfiniteInduction =
    Temp.withSystemTempDirectory "felix-checked-transfinite-induction"
        \root -> do
            let executable = root Posix.</> "vampire"
            writeAcceptedFixtureVampire executable
            foundation <- expectRight Foundation.checkedFoundation
            bootstrap <-
                expectRight
                    =<< Module.buildBootstrapPreludeFixture
                        foundation unusedResolver
            mounts <- exactFixtureMounts =<< getCurrentDirectory
            workspace <- parseWorkspace bootstrap mounts
                "test/phase5/exact-transfinite-induction.tex"
            observations <- newIORef []
            _sealed <-
                sole "transfinite-induction module"
                    =<< compileParsedWorkspaceWithValidation
                        foundation bootstrap
                        (observingResolver executable observations)
                        AlwaysMissValidation
                        workspace
            requests <-
                expectCount "transfinite-induction requests" 2
                    =<< readIORef observations
            let (bridge, child) =
                    case requests of
                        [first, second] -> (first, second)
                        _ -> error "checked transfinite request count diverged"
            case localReasoningLocalTerms bridge of
                [rawHypothesis, guardTerm] ->
                    case guardTerm of
                        Core.CApp (Core.CGlobal predicate) (Core.CBound 0) -> do
                            let expectedRaw =
                                    Core.CForall Core.TySet
                                        (Core.CImp
                                            (member
                                                (Core.CBound 0)
                                                (Core.CBound 1))
                                            (Core.CImp
                                                (Core.CApp
                                                    (Core.CGlobal predicate)
                                                    (Core.CBound 0))
                                                (reflexiveDisjunction (Core.CBound 0))))
                                expectedSimplified =
                                    Core.CForall Core.TySet
                                        (Core.CImp
                                            (member
                                                (Core.CBound 0)
                                                (Core.CBound 1))
                                            (reflexiveDisjunction (Core.CBound 0)))
                            assertEqual
                                "transfinite bridge owns the raw set-induction hypothesis"
                                expectedRaw rawHypothesis
                            assertEqual
                                "transfinite bridge derives the user-facing hypothesis"
                                expectedSimplified
                                (localReasoningTarget bridge)
                            assertEqual
                                "transfinite bridge cites one hereditary-class theorem"
                                1
                                (localReasoningGlobalCount bridge)
                            assertEqual
                                "transfinite bridge premise order"
                                [0, 1]
                                (localReasoningLocalOrdinals bridge)
                            assertEqual
                                "transfinite child proves the instantiated goal"
                                (reflexiveDisjunction (Core.CBound 0))
                                (localReasoningTarget child)
                            assertEqual
                                "transfinite child sees the ordinal guard and simplified hypothesis"
                                [guardTerm, expectedSimplified]
                                (localReasoningLocalTerms child)
                            assertEqual
                                "the raw induction hypothesis is hidden from source steps"
                                [1, 2]
                                (localReasoningLocalOrdinals child)
                        term ->
                            assertFailure
                                ("unexpected transfinite guard: " <> show term)
                locals ->
                    assertFailure
                        ("unexpected transfinite bridge locals: "
                            <> show locals)
            writeIORef observations []
            typedWorkspace <- parseWorkspace bootstrap mounts
                "test/phase8/typed-transfinite-induction.tex"
            _typedSealed <-
                sole "typed transfinite-induction module"
                    =<< compileParsedWorkspaceWithValidation
                        foundation bootstrap
                        (observingResolver executable observations)
                        AlwaysMissValidation
                        typedWorkspace
            typedRequests <-
                expectCount "typed transfinite-induction requests" 3
                    =<< readIORef observations
            let typedBridge =
                    case typedRequests of
                        [_heredity, bridgeRequest, _childRequest] ->
                            bridgeRequest
                        _ ->
                            error
                                "typed transfinite request count diverged"
            assertEqual
                "typed transfinite bridge retains raw hypothesis and guard"
                [0, 1]
                (localReasoningLocalOrdinals typedBridge)
            case localReasoningLocalTerms typedBridge of
                [ Core.CForall Core.TySet
                    (Core.CImp _membership
                        (Core.CImp _guard
                            (Core.CForall
                                (Core.TyArrow Core.TySet Core.TyProp)
                                _body)))
                    , _guardTerm
                    ] -> pure ()
                terms ->
                    assertFailure
                        ("typed transfinite bridge dropped its higher-order raw hypothesis: "
                            <> show terms)
            let storePath = root Posix.</> "store.sqlite"
            bracket
                (snd <$> (Store.openStore storePath
                    (Identity.theoryId foundation) >>= expectRight))
                Store.closeStore
                \store -> do
                    prelude <-
                        expectRight
                            =<< acquireFinalPreludeSession
                                store foundation
                                (acceptedResolver executable)
                    actualWorkspace <-
                        parseFinalWorkspace prelude mounts
                            "test/phase5/exact-transfinite-ordinal.tex"
                    actualModules <-
                        compileFinalParsedWorkspaceWithResolver
                            foundation prelude
                            (acceptedResolver executable)
                            actualWorkspace
                    assertBool
                        "the standard ordinal predicate exposes its hereditary theorem"
                        (not (null actualModules))
  where
    observingResolver executable observations =
        Declaration.vampireResolver \prepared -> do
            let problem = Provers.preparedTypedProverLogicalProblem prepared
                locals = Backend.typedProblemLocalPremises problem
            modifyIORef' observations
                (<> [ LocalReasoningObservation
                        { localReasoningTarget =
                            Backend.supportedPropositionTerm
                                (Backend.typedProblemClaim problem)
                        , localReasoningGlobalCount =
                            Vector.length
                                (Backend.typedProblemGlobalPremises problem)
                        , localReasoningLocalOrdinals =
                            Backend.localPremiseOrdinalValue
                                . Backend.typedLocalPremiseOrdinal
                                <$> Vector.toList locals
                        , localReasoningLocalTerms =
                            Backend.supportedPropositionTerm
                                . Backend.typedLocalPremiseProposition
                                <$> Vector.toList locals
                        , localReasoningAuxiliaries =
                            Backend.typedProblemAuxiliaryTag
                                <$> Vector.toList
                                    (Backend.typedProblemAuxiliaries problem)
                        }
                    ])
            Provers.runPreparedTypedProver
                (Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                prepared

    acceptedResolver executable =
        Declaration.vampireResolver \prepared ->
            Provers.runPreparedTypedProver
                (Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                prepared

    expectCount label expected values = do
        assertEqual label expected (length values)
        pure values

    reflexiveDisjunction term =
        let equality = Core.CEq Core.TySet term term
        in Core.COr equality (Core.CNot equality)

    member element set =
        Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) element)
            set


prepareInductiveFixture
    :: FilePath
    -> IO
        (Either
            Inductive.InductiveError
            Inductive.PreparedInductive)
prepareInductiveFixture relative = do
    root <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts root
    workspace <- parseWorkspace bootstrap mounts relative
    parsed <-
        sole "exact inductive parsed module"
            (toList
                (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
    let identified = Module.identifiedPhysicalModule parsed
        owner = Module.identifiedModuleOwner identified
        parsedModule = Module.identifiedModuleParsed identified
    (blockIndex, block) <-
        sole "exact inductive block"
            [ (index, candidate)
            | (index, candidate@Raw.BlockInductive{}) <-
                zip [0..]
                    (Parsed.identifiedParsedModuleBlocks parsedModule)
            ]
    let entries =
            [ Parsed.parsedSyntaxOccurrenceEntry occurrence
            | occurrence <-
                Parsed.identifiedParsedModuleSyntaxOccurrences parsedModule
            , Parsed.parsedSyntaxOccurrenceBlockIndex occurrence == blockIndex
            ]
        action
            :: Declaration.ModuleDriver Void
                (Either
                    Inductive.InductiveError
                    Inductive.PreparedInductive)
        action =
            Declaration.runProspectiveLoweringDriver
                (Inductive.prepareInductive
                    foundation
                    block
                    entries)
    result <-
        runModuleDriver
            foundation
            owner
            []
            unusedResolver
            AlwaysMissValidation
            action
    driver <- expectRight result
    case driver of
        Declaration.DriverSucceeded prepared _semantic _prefix ->
            pure prepared
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("exact inductive preparation driver failed: "
                    <> show failure)
                >> fail "unreachable"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("exact inductive preparation driver did not seal: "
                    <> show failure)
                >> fail "unreachable"

prepareDatatypeFixture
    :: FilePath
    -> IO
        (Either
            Datatype.DatatypeError
            ( Foundation.CheckedFoundation
            , ModuleName
            , Datatype.PreparedDatatype
            ))
prepareDatatypeFixture relative = do
    root <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts root
    workspace <- parseWorkspace bootstrap mounts relative
    parsed <-
        sole "datatype parsed module"
            (toList
                (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
    let identified = Module.identifiedPhysicalModule parsed
        owner = Module.identifiedModuleOwner identified
        parsedModule = Module.identifiedModuleParsed identified
    block <-
        sole "datatype block"
            (Parsed.identifiedParsedModuleBlocks parsedModule)
    let occurrences =
            [ ( Parsed.parsedSyntaxOccurrenceLocation occurrence
              , Parsed.parsedSyntaxOccurrenceMarker occurrence
              , Parsed.parsedSyntaxOccurrenceEntry occurrence
              )
            | occurrence <-
                Parsed.identifiedParsedModuleSyntaxOccurrences parsedModule
            , Parsed.parsedSyntaxOccurrenceBlockIndex occurrence == 0
            ]
        action
            :: Declaration.ModuleDriver Void
                (Either
                    Datatype.DatatypeError
                    Datatype.PreparedDatatype)
        action =
            Declaration.runProspectiveLoweringDriver
                (Datatype.prepareDatatype block occurrences)
    result <-
        runModuleDriver
            foundation
            owner
            []
            unusedResolver
            AlwaysMissValidation
            action
    driver <- expectRight result
    case driver of
        Declaration.DriverSucceeded prepared _semantic _prefix ->
            pure
                ((\datatype -> (foundation, owner, datatype))
                    <$> prepared)
        Declaration.DriverFailed failure _prefix ->
            assertFailure
                ("datatype preparation driver failed: "
                    <> show failure)
                >> fail "unreachable"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure
                ("datatype preparation driver did not seal: "
                    <> show failure)
                >> fail "unreachable"

sealedValidationCertificates
    :: Module.CompletedTypedModule
    -> [Authority.ValidationCertificate]
sealedValidationCertificates =
    concatMap Commit.committedBatchValidationCertificates
        . Commit.pendingModulePrefixBatches
        . Module.completedTypedModulePrefix
