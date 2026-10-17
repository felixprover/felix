{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Obvious (unitTests) where

import Base hiding (Empty, empty)
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , emptyGlobalTyping
    )
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Obvious
import Felix.Checking.Semantic (DefinitionViewKind(..))
import Felix.Test.Support.GlobalTyping

import Control.Monad (when)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word)
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "Obvious inference"
        [ testCase
            "introduces and eliminates the elementary logical forms"
            provesElementaryLogic
        , testCase
            "preserves checked conjunction subgoals and bounded construction"
            preservesCheckedConjunctionGoals
        , testCase
            "applies a quantified theorem and proves its antecedent"
            appliesQuantifiedTheorem
        , testCase
            "determines theorem parameters from ordered premises"
            determinesParametersFromPremises
        , testCase
            "backtracks premise matches in stable fact order"
            backtracksPremiseMatches
        , testCase
            "replays interleaved forall and implication steps"
            replaysInterleavedTheoremSpine
        , testCase
            "replays interleaved higher-order theorem steps through beta heads"
            replaysHigherOrderInterleavedTheoremSpine
        , testCase
            "substitutes theorem slots without capturing ambient binders"
            substitutesWithoutCapture
        , testCase
            "closes only premises which omit unresolved slots"
            closesPremisesByOccurrence
        , testCase
            "rejects inconsistent repeated theorem parameters"
            rejectsInconsistentRepeatedParameters
        , testCase
            "retains entered slot arguments and reduces only required comparisons"
            retainsEnteredSlotArguments
        , testCase
            "recovers slot arguments when a beta head erases an inner binder"
            recoversErasedSlotBinder
        , testCase
            "preserves source premise order under bounded work"
            preservesPremiseSearchOrder
        , testCase
            "preserves supplied order for directly supported projected theorems"
            preservesProjectedTheoremOrder
        , testCase
            "charges large simultaneous theorem substitution"
            chargesLargeTheoremSubstitution
        , testCase
            "bounds many-binder theorem bookkeeping"
            boundsManyBinderTheoremBookkeeping
        , testCase
            "cannot scope an antecedent over a later binder"
            rejectsLaterBinderInAntecedent
        , testCase
            "reconstructs shortest directed equality paths"
            reconstructsFocusedEqualityPaths
        , testCase
            "breaks equal-length equality paths by source order"
            breaksEqualityPathTiesBySourceOrder
        , testCase
            "builds multi-argument application congruence"
            buildsTargetShapedCongruence
        , testCase
            "retains scoped operands through recursive equality and transport"
            retainsScopedEqualityOperands
        , testCase
            "shares checked children during deep application congruence"
            sharesCongruenceChildren
        , testCase
            "upgrades either retained congruence operand"
            upgradesCongruenceOperands
        , testCase
            "retains descendants while upgrading deep congruence"
            retainsCongruenceSupportRecipes
        , testCase
            "retains later canonical sources after ordinary falsity"
            retainsFalsitySupport
        , testCase
            "rejects incompatible application congruence components"
            rejectsIncompatibleCongruence
        , testCase
            "tracks canonical evidence only for focused equality demand"
            tracksCanonicalEqualityEvidence
        , testCase
            "charges deep equality-term interning exactly"
            chargesDeepEqualityInterning
        , testCase
            "introduces either disjunct in source order"
            introducesDisjunctions
        , testCase
            "continues from unsupported left disjunct to the right"
            continuesAfterUnsupportedDisjunct
        , testCase
            "propagates canonical evidence through disjunction"
            propagatesCanonicalDisjunctionEvidence
        , testCase
            "charges nested disjunction search exactly"
            chargesNestedDisjunctionSearch
        , testCase
            "replays the complete signed propositional calculus"
            replaysSignedPropositionalCalculus
        , testCase
            "keeps root priority and sibling branches isolated"
            preservesRefutationBranchSemantics
        , testCase
            "coalesces selected fact domains before searching their initial evidence"
            coalescesSelectedFactDomains
        , testCase
            "reports deterministic refutation resource boundaries"
            reportsRefutationBoundaries
        , testCase
            "agrees with a declarative propositional oracle"
            agreesWithPropositionalOracle
        , testCase
            "replays frozen-catalogue equality closure"
            replaysRefutationEqualityClosure
        , testCase
            "keeps equality closure deterministic and branch-local"
            preservesRefutationEqualityBoundaries
        , testCase
            "prioritizes completed equality closure over later work"
            prioritizesCompletedEqualityClosure
        , testCase
            "agrees with an immutable finite equality oracle"
            agreesWithEqualityOracle
        , testCase
            "replays premise-driven rule chains and generated schemas"
            replaysBoundedRuleChains
        , testCase
            "composes equivalent exact theorem presentations through case reasoning"
            composesExactRulePresentations
        , testCase
            "selects rule results after interleaved eliminations"
            selectsRuleResultsAfterEliminations
        , testCase
            "freezes recursively prepared logical children"
            freezesPreparedLogicalChildren
        , testCase
            "replays signed head conversion below existing proof hypotheses"
            replaysSignedHeadConversionUnderHypotheses
        , testCase
            "retains a whole structured conjunction for its consumer"
            retainsStructuredRuleResult
        , testCase
            "shares admitted quantified results before discovering their descendants"
            sharesQuantifiedRuleResults
        , testCase
            "reuses rule substitutions across transitive case branches"
            reusesTransitiveCaseSubstitutions
        , testCase
            "exposes and replays every selected rule proposition root"
            replaysExposedRuleRoots
        , testCase
            "connects ground-premise and zero-rule demands"
            replaysDemandDrivenRules
        , testCase
            "matches rule premises modulo branch equality"
            replaysEqualityAwareRules
        , testCase
            "streams written equality alternatives before reverse work"
            streamsWrittenEqualityAlternatives
        , testCase
            "retries retained rule states after genuine equality merges"
            retriesRulesAfterEqualityMerges
        , testCase
            "activates derived proposition applications under existing equality"
            activatesDerivedPropositionsUnderEquality
        , testCase
            "reconstructs long retained rule-witness spines exactly"
            reconstructsLongRuleWitnessSpines
        , testCase
            "keeps rule grammar, scope, and branch state exact"
            preservesRuleSemanticBoundaries
        , testCase
            "terminates recursive rules at a stable fixed point"
            terminatesRecursiveRules
        , testCase
            "charges late matcher-substitution identity atomically"
            chargesLateMatcherSubstitutionIdentity
        , testCase
            "rejects selected terms outside the frozen rule universe"
            rejectsOutsideUniverseRuleTerms
        , testCase
            "rejects a newly closed partial application outside the frozen domain"
            rejectsOutsideUniversePartialApplication
        , testCase
            "reports exact rule-instance and work boundaries"
            reportsRuleResourceBoundaries
        , testCase
            "agrees with a declarative finite rule oracle"
            agreesWithRuleOracle
        , testCase
            "reports a conclusion-only parameter boundary"
            rejectsUndeterminedParameter
        , testCase
            "reports the first unavailable theorem antecedent"
            reportsUnavailableAntecedent
        , testCase
            "transports propositions through equality"
            transportsPropositions
        , testCase
            "composes cited projection with focused equality"
            composesCitedProjectionWithFocusedEquality
        , testCase
            "preserves direct proposition-transport priority"
            preservesDirectPropositionTransportPriority
        , testCase
            "skips an empty proposition-transport equality graph"
            skipsEmptyPropositionTransportEqualityGraph
        , testCase
            "keeps failed proposition-transport probes out of the graph"
            keepsFailedPropositionTransportProbesOutOfGraph
        , testCase
            "tracks definition evidence across proposition transport"
            tracksPropositionTransportDefinitionEvidence
        , testCase
            "composes equality symmetry with negation"
            composesEqualitySymmetryWithNegation
        , testCase
            "retains only imports used by the proof"
            reportsOnlyUsedImports
        , testCase
            "exposes canonical definitions only at supported roots"
            exposesCanonicalDefinitions
        , testCase
            "uses proof-local canonical definitions lexically"
            exposesLocalDefinitions
        , testCase
            "unfolds applications of proof-local predicate definitions"
            exposesAppliedLocalPredicateDefinitions
        , testCase
            "tries canonical definitions on either equality operand"
            exposesEitherEqualityOperand
        , testCase
            "recognizes elementary logical heads modulo beta conversion"
            provesBetaConvertibleHeads
        , testCase
            "projects a beta-convertible local conjunction"
            projectsBetaConvertibleConjunction
        , testCase
            "applies a theorem with a beta-convertible outer spine"
            appliesBetaConvertibleTheorem
        , testCase
            "uses beta conversion in equality, transport, and definition roots"
            appliesConversionAwareNonIntroductionRules
        , testCase
            "continues fact-side reasoning after an inapplicable falsity rule"
            continuesFactSideDefinitionReasoning
        , testCase
            "continues after a definition construction reaches its conversion limit"
            continuesAfterDefinitionConstructionLimit
        , testCase
            "continues past an evidence-free proof when definition use is required"
            requiresCanonicalDefinitionCandidate
        , testCase
            "propagates definition evidence through unary introduction"
            propagatesDefinitionEvidenceThroughIntroduction
        , testCase
            "finds definition evidence in the right conjunct"
            findsDefinitionEvidenceInRightConjunct
        , testCase
            "finds definition evidence in a theorem antecedent"
            findsDefinitionEvidenceInTheoremAntecedent
        , testCase
            "retains the canonical origin of local membership equations"
            retainsCanonicalLocalEquationOrigin
        , testCase
            "audits canonical source use after term and proof binders"
            auditsCanonicalSourceAfterBinders
        , testCase
            "publishes an ordinary conjunction for a canonical view consumer"
            publishesOrdinaryConjunction
        , testCase
            "publishes an ordinary disjunction for a canonical view consumer"
            publishesOrdinaryDisjunction
        , testCase
            "continues canonical disjunction support after a direct ordinary branch"
            retainsCanonicalDisjunctionSupport
        , testCase
            "retains canonical support in directly composed disjunction branches"
            retainsDirectConjunctionSupport
        , testCase
            "publishes a converted direct premise before seeking its support"
            publishesConvertedDirectPremise
        , testCase
            "upgrades either selected application premise without losing the other"
            upgradesSelectedApplicationPremise
        , testCase
            "keeps an open conjunction application's selected substitution during support"
            retainsApplicationSupportSubstitution
        , testCase
            "reports an unsupported canonical dependency cycle honestly"
            blocksUnsupportedCanonicalCycle
        , testCase
            "publishes ordinary transport for a canonical view consumer"
            publishesOrdinaryTransport
        , testCase
            "upgrades the retained premise of an ordinary transport"
            upgradesTransportPremise
        , testCase
            "continues a supported equality path after ordinary proposition transport"
            upgradesComposedTransport
        , testCase
            "publishes an ordinary equality chain for a canonical view consumer"
            publishesOrdinaryEquality
        , testCase
            "publishes an ordinary application for a canonical view consumer"
            publishesOrdinaryApplication
        , testCase
            "retains later canonical evidence for either completed conjunct"
            retainsCanonicalConjunctSupport
        , testCase
            "retains a supported equality path after ordinary reflexivity"
            retainsSupportedReflexivityPath
        , testCase
            "recognizes canonical imports through their exact cited association"
            recognizesCitedCanonicalImport
        , testCase
            "prefers goal-side over fact-side canonical conversion"
            prefersGoalDefinitionConversion
        , testCase
            "finishes supplied goal evidence without a global lexical-view priority"
            prefersLocalFactDefinitionConversion
        , testCase
            "keeps ordinary predicate and membership definitions goal-first"
            prefersProofLocalFactDefinitionConversion
        , testCase
            "uses proof-local definition facts before existential search"
            prefersProofLocalDefinitionToExistentialSearch
        , testCase
            "keeps unrelated predicate definitions behind goal evidence"
            keepsUnrelatedPredicateDefinitionsBehindGoalEvidence
        , testCase
            "keeps composed transport structural through application components"
            keepsComposedTransportStructural
        , testCase
            "finds direct definition evidence after an unavailable premise"
            findsDirectDefinitionAfterUnavailablePremise
        , testCase
            "eliminates a cited predicate definition before unrelated term expansion"
            eliminatesCitedPredicateDefinition
        , testCase
            "assembles a cited rule's conjunction premise from local facts"
            assemblesCitedConjunctionPremise
        , testCase
            "joins open conjunction premises with ordered backtracking"
            joinsOpenConjunctionPremises
        , testCase
            "joins conjunction evidence before an interleaved binder"
            joinsInterleavedConjunctionPremises
        , testCase
            "retains definition authority in either joined conjunct"
            retainsJoinedConjunctionAuthority
        , testCase
            "chooses premise-supported bindings before recursive theorem search"
            choosesSupportedTheoremBinding
        , testCase
            "keeps local theorem evidence before speculative citations"
            prefersLocalTheoremBeforeSpeculativeCitation
        , testCase
            "introduces conjunctions before speculative lexical theorems"
            introducesConjunctionBeforeSpeculativeTheorem
        , testCase
            "applies a cited theorem through an alias before term expansion"
            appliesCitedTheoremThroughAliasBeforeTermExpansion
        , testCase
            "composes equality before unrelated set expansion"
            composesEqualityBeforeUnrelatedSetExpansion
        , testCase
            "reverses a cited equality in a lexical context"
            reversesCitedEqualityInLexicalContext
        , testCase
            "prefers later syntactic identity to earlier conversion work"
            prefersSyntacticExactBeforeConversion
        , testCase
            "continues to a cheap rule after exact conversion is exhausted"
            continuesAfterExactConversionExhaustion
        , testCase
            "discovers later witnessed supplied sources before recursive conversion"
            discoversWitnessedSourcesBeforeRecursion
        , testCase
            "preserves cheap direct candidate order across unrelated definitions"
            preservesDirectCandidateOrder
        , testCase
            "defers full-effort direct evidence and escalates when it is necessary"
            escalatesDirectPreparation
        , testCase "retains blocked theorem exposure, spine, and matching preparation"
            retainsTheoremPreparation
        , testCase "composes supplied equality before recursive cancellation"
            composesBeforeRecursiveCancellation
        , testCase "keeps focused work independent of ground admission limits" isolatesGroundAdmissionAllowance
        , testCase "composes universal introduction with a ground residual" provesUniversalGroundResidual
        , testCase "keeps structural residual seeds separate from query evidence" separatesStructuralResidualQueries
        , testCase "keeps theorem-premise descendants focused-only after introduction" deniesPremiseGroundIntroduction
        , testCase
            "uses supplied ground evidence before full focused conversion"
            refutesBeforeFullFocusedConversion
        , testCase
            "uses a cited theorem recursively on a projected literal fact"
            usesCitedTheoremOnProjectedLiteralFact
        , testCase
            "uses a local theorem recursively on a projected literal fact"
            usesLocalTheoremOnProjectedLiteralFact
        , testCase
            "uses a proof-local goal definition before conversion work"
            prefersLocalGoalDefinitionBeforeConversion
        , testCase
            "uses a proof-local fact definition before conversion work"
            prefersLocalFactDefinitionBeforeConversion
        , testCase
            "charges conversion work to one aggregate pool"
            exhaustsBoundedConversion
        , testCase
            "terminates on search-budget exhaustion and repeated states"
            terminatesDeterministically
        , testCase
            "shares consumable allowances across completed searches"
            sharesCompletedAllowances
        , testCase
            "reports stable detailed outcomes and coarse work"
            reportsDetailedOutcomes
        , testGroup "candidate diagnostics scaling fixture"
            [ testCase "1 available fact" (candidateScalingFixture 1)
            , testCase "8 available facts" (candidateScalingFixture 8)
            , testCase "64 available facts" (candidateScalingFixture 64)
            ]
        , testCase
            "attributes fact-side and goal-side definition candidates"
            reportsDefinitionCandidateParticipation
        , testCase
            "returns nested definition exhaustion to the enclosing theorem"
            returnsNestedDefinitionExhaustion
        , testCase
            "continues nested fact definitions after a conversion limit"
            continuesNestedFactDefinitionsAfterConversionLimit
        , testCase
            "eliminates facts after nested goal expansion exhausts an operation"
            eliminatesFactsAfterGoalExhaustion
        , testCase
            "keeps exhausted goal-to-fact continuation nonrecursive"
            keepsExhaustedFactContinuationDirect
        , testCase
            "reuses checked expansions of projected facts"
            reusesCheckedFactExpansions
        , testCase
            "separates fact-expansion caches across proof contexts"
            separatesFactExpansionContexts
        , testCase
            "rejects malformed requests before search"
            rejectsMalformedRequests
        , testCase
            "preserves exact import associations when admitting definition views"
            preservesDefinitionImportAssociations
        , testCase
            "admits entered goals and sources before unused syntax disappears"
            admitsEnteredSyntaxBeforeErasure
        ]

sharesCompletedAllowances :: Assertion
sharesCompletedAllowances = do
    foundation <- expectRight Foundation.checkedFoundation
    atom <- checkedScoped [TyProp] (CBound 0)
    goal <- checkedScoped [TyProp] (COr (CBound 0) CFalsum)
    witness <- checkedScoped [] (CExists TySet (CEq TySet (CBound 0) empty))
    truth <- checkedScoped [] CTruth
    let run allowance hypotheses target = obviousProofReportWithin allowance
            AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] target
        initial allowance hypotheses target = obviousInitialProofReportWithin allowance
            AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] target
        balances before report following = do
            let prior = obviousRemainingBudget before
                remaining = obviousRemainingBudget following
                statistics = obviousRunStatistics report
            assertEqual "focused work is debited, including failed attempts"
                (obviousFocusedWorkLimit prior - obviousFocusedWorkConsumed statistics)
                (obviousFocusedWorkLimit remaining)
            assertEqual "refutation work is debited"
                (obviousRefutationWorkLimit prior - obviousRefutationWorkConsumed statistics)
                (obviousRefutationWorkLimit remaining)
            assertEqual "conversion work is debited"
                (Conversion.conversionPoolAmount (obviousConversionPool prior) - obviousConversionWorkConsumed statistics)
                (Conversion.conversionPoolAmount (obviousConversionPool remaining))
        breadth = fmap quota . obviousBreadthObservations . obviousRunStatistics
        quota = \case
            ObviousFactDomainBreadth cap used _ -> (cap,used)
            ObviousWitnessBreadth _prefix cap used _ -> (cap,used)
            ObviousPremiseQueryBreadth cap used _ -> (cap,used)
            ObviousUniversalBreadth cap used _ -> (cap,used)
            ObviousUniversalHintEffort cap used -> (cap,used)
            ObviousExistentialBreadth cap used _ -> (cap,used)
            ObviousExtensionalityBreadth cap used _ -> (cap,used)
            ObviousEndpointBreadth cap used _ -> (cap,used)
        full = obviousAllowance defaultObviousBudget
        (ordinary, _) = run full [atom] goal
    for_ [(defaultObviousBudget, [atom], goal),
          (defaultObviousBudget {obviousFocusedWorkLimit = 4}, [atom], goal),
          (defaultObviousBudget, [], witness)] \(budget,hypotheses,target) -> do
        let allowance = obviousAllowance budget
        (first, remaining) <- maybe (assertFailure "initial attempt was skipped" >> fail "unreachable") pure
            (initial allowance hypotheses target)
        balances allowance first remaining
        assertEqual "initial work is a quarter, rounded down"
            (obviousFocusedWorkLimit budget `div` 4)
            (obviousFocusedWorkLimit (obviousEffectiveBudget (obviousRunStatistics first)))
        assertEqual "all request quotas use the same quarter rule, including zero"
            ((`div` 4) . fst <$> breadth ordinary) (fst <$> breadth first)
        let (second, following) = run remaining hypotheses target
        balances remaining second following
        assertEqual "unused initial credit and reserve remain available"
            (zipWith (\(cap,_) (_,spent) -> cap - spent) (breadth ordinary) (breadth first))
            (fst <$> breadth second)
        when (budget == defaultObviousBudget) do
            proof <- expectRight (obviousRunResult second)
            assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target proof
        let (third, final) = run following [] truth
        balances following third final
        assertEqual "a later sibling cannot reset private quotas"
            ((\(cap,spent) -> cap - spent) <$> breadth second) (fst <$> breadth third)
    for_ [0,1,2,3] \work ->
        assertBool "a zero focused slice skips the initial search"
            (isNothing (initial (obviousAllowance defaultObviousBudget {obviousFocusedWorkLimit = work}) [atom] goal))

admitsEnteredSyntaxBeforeErasure :: Assertion
admitsEnteredSyntaxBeforeErasure = do
    foundation <- expectRight Foundation.checkedFoundation
    let missing = fixtureGlobalTyping (globalTypingFixture [])
        unused = CGlobal namedSetObject
        erased = CApp (CLam TySet CTruth) unused
    target <- checkedGlobalScoped [] erased
    projected <- checkedGlobalScoped [] membership
    source <- checkedGlobalScoped []
        (CAnd membership (CEq TySet unused unused))
    joinedTarget <- checkedGlobalScoped [] (CAnd membership erased)
    let run hypotheses goal = obviousProofDetailed
            defaultObviousBudget AnyObviousProof foundation missing
            hypotheses [] [] goal
        expected = ObviousIntegrityFailure
            (KernelProof.ProofTermIllTyped UnknownCoreGlobal)
        (rootStatistics, rootResult) = run [] target
        (_sourceStatistics, sourceResult) = run [source] projected
        (_joinedStatistics, joinedResult) = run [projected] joinedTarget
    assertFailureKind "root admission precedes beta erasure" expected rootResult
    assertEqual "rejected root admission spends no conversion credit"
        0 (obviousConversionWorkConsumed rootStatistics)
    assertFailureKind "selected conjunction admits its discarded branch"
        expected sourceResult
    assertFailureKind "conjunction subgoals cannot discard an unadmitted beta argument"
        expected joinedResult

preservesCheckedConjunctionGoals :: Assertion
preservesCheckedConjunctionGoals = do
    foundation <- expectRight Foundation.checkedFoundation
    atom <- checkedScoped [TyProp] (CBound 0)
    for_ [1, 8, 32] \depth -> do
        let term = foldl' (\left _ -> CAnd left (CBound 0)) (CBound 0) [1 .. depth :: Int]
        target <- checkedScoped [TyProp] term
        let run limit = obviousProofDetailed
                defaultObviousBudget
                    { obviousFocusedWorkLimit = limit
                    , obviousRefutationWorkLimit = 0
                    }
                AnyObviousProof foundation emptyGlobalTyping [atom] [] [] target
            (statistics, result) = run (obviousFocusedWorkLimit defaultObviousBudget)
            work = obviousFocusedWorkConsumed statistics
        proof <- expectRight result
        let built = obviousBuiltProof proof
        replayed <- expectRight (replayScopedKernelDerivation
            foundation defaultKernelReplayLimits emptyGlobalTyping Vector.empty
            (Vector.singleton atom) target (KernelProof.builtProofDerivation built))
        assertEqual "each introduction retains the same original hypothesis"
            (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual "independent replay sees every exact conjunction node"
            (fromIntegral (2 * depth + 1)) (replayedScopedKernelNodeCount replayed)
        _ <- expectRight (snd (run work))
        assertFailureKind "one less focused work cannot finish construction"
            (ObviousResourceExhausted ObviousFocusedWorkLimit) (snd (run (work - 1)))

provesElementaryLogic :: Assertion
provesElementaryLogic = do
    proposition <- checkedScoped [] membership
    negation <- checkedScoped [] (CNot membership)
    conjunction <- checkedScoped [] (CAnd membership membership)
    implication <- checkedScoped [] (CImp membership membership)
    universal <- checkedScoped []
        (CForall TySet
            (CImp
                (member (CBound 0) empty)
                (member (CBound 0) empty)))
    falsum <- checkedScoped [] CFalsum
    assertObvious [proposition] [] conjunction
    assertObvious [] [] implication
    assertObvious [] [] universal
    assertObvious [proposition, negation] [] falsum

appliesQuantifiedTheorem :: Assertion
appliesQuantifiedTheorem = do
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (CEq TySet (CBound 0) empty)
                (member (CBound 0) empty)))
    target <- checkedScoped [] membership
    proof <- expectRight =<< runObvious
        [] [obviousImport (importIx 0) theorem] target
    assertEqual
        "the cited theorem is the only authority leaf"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

determinesParametersFromPremises :: Assertion
determinesParametersFromPremises = do
    let one = pair empty empty
        targetTerm = member one one
        firstPremise = membership
        secondPremise = member empty one
    seededTheorem <- checkedClosed
        (CForall TySet
            (CImp
                (member (CBound 0) empty)
                targetTerm))
    first <- checkedScoped [] firstPremise
    target <- checkedScoped [] targetTerm
    seededProof <- expectRight =<< runObvious
        [first]
        [obviousImport (importIx 0) seededTheorem]
        target
    assertEqual
        "the premise alone determines the absent result parameter"
        (Set.singleton (importIx 0))
        (obviousUsedImports seededProof)

    orderedTheorem <- checkedClosed
        (CForall TySet
            (CImp
                (member (CBound 0) empty)
                (CImp
                    (member (CBound 0) one)
                    targetTerm)))
    second <- checkedScoped [] secondPremise
    proof <- expectRight =<< runObvious
        [first, second]
        [obviousImport (importIx 1) orderedTheorem]
        target
    assertEqual
        "the premise-seeded application retains its theorem authority"
        (Set.singleton (importIx 1))
        (obviousUsedImports proof)

backtracksPremiseMatches :: Assertion
backtracksPremiseMatches = do
    let one = pair empty empty
        two = pair one empty
        firstForEmpty = member empty empty
        firstForOne = member one empty
        secondForOne = member one one
        targetTerm = member two two
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (member (CBound 0) empty)
                (CImp
                    (member (CBound 0) one)
                    targetTerm)))
    hypotheses <- traverse (checkedScoped [])
        [firstForEmpty, firstForOne, secondForOne]
    target <- checkedScoped [] targetTerm
    _proof <- expectRight =<< runObvious
        hypotheses
        [obviousImport (importIx 0) theorem]
        target
    pure ()

replaysInterleavedTheoremSpine :: Assertion
replaysInterleavedTheoremSpine = do
    let one = pair empty empty
        premiseTerm = member empty one
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (member (CBound 0) one)
                (CForall TySet
                    (CImp
                        (CEq TySet (CBound 1) (CBound 0))
                        (member (CBound 1) (CBound 0))))))
    premise <- checkedScoped [] premiseTerm
    target <- checkedScoped [] membership
    _proof <- expectRight =<< runObvious
        [premise]
        [obviousImport (importIx 0) theorem]
        target
    pure ()

replaysHigherOrderInterleavedTheoremSpine :: Assertion
replaysHigherOrderInterleavedTheoremSpine = do
    foundation <- expectRight Foundation.checkedFoundation
    let beta proposition = CApp (CLam TyProp (CBound 0)) proposition
        functionType = TyArrow TySet TySet
        context = [TySet]
        applied = CApp (CIntrinsic FamilyUnion) (CBound 0)
        premiseTerm = member applied empty
        targetTerm = member applied applied
        theoremTerm = beta
            (CForall functionType
                (beta (CImp
                    (beta (member (CApp (CBound 0) (CBound 1)) empty))
                    (beta (CForall TySet
                        (beta (CImp
                            (beta (CEq TySet
                                (CApp (CBound 1) (CBound 0))
                                (CApp (CBound 1) (CBound 2))))
                            (beta (member
                                (CApp (CBound 1) (CBound 0))
                                (CApp (CBound 1) (CBound 0)))))))))))
    hypotheses <- traverse (checkedScoped context)
        [theoremTerm, premiseTerm, CTruth]
    target <- checkedScoped context targetTerm
    let (statistics, result) = obviousProofDetailed
            defaultObviousBudget
                { obviousFocusedWorkLimit = 1000000
                , obviousRefutationWorkLimit = 0
                }
            AnyObviousProof foundation emptyGlobalTyping
            hypotheses [] [] target
    proof <- expectRight result
    assertEqual "the focused compiler retains heterogeneous interleaved binders"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    replayed <- expectRight
        (replayScopedKernelDerivation
            foundation defaultKernelReplayLimits emptyGlobalTyping
            Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
    assertEqual "the open theorem and first premise are the exact local authority"
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "the interleaved proof preserves the requested open conclusion"
        target (KernelProof.builtProofStatement (obviousBuiltProof proof))

substitutesWithoutCapture :: Assertion
substitutesWithoutCapture = do
    let ambient = CBound 0
        premiseTerm = member ambient ambient
        targetTerm = member ambient empty
        theoremTerm =
            CForall TySet
                (CForall TySet
                    (CImp
                        (member (CBound 1) (CBound 2))
                        (member (CBound 1) (CBound 0))))
    premise <- checkedScoped [TySet] premiseTerm
    theorem <- checkedScoped [TySet] theoremTerm
    target <- checkedScoped [TySet] targetTerm
    assertObvious [premise, theorem] [] target

closesPremisesByOccurrence :: Assertion
closesPremisesByOccurrence = do
    let one = pair empty empty
        targetTerm = member one one
        laterPremise = member empty one
        theoremTerm =
            CImp membership
                (CForall TySet
                    (CImp
                        (member (CBound 0) one)
                        targetTerm))
    first <- checkedScoped [] membership
    later <- checkedScoped [] laterPremise
    theorem <- checkedClosed theoremTerm
    target <- checkedScoped [] targetTerm
    _proof <- expectRight =<< runObvious
        [first, later]
        [obviousImport (importIx 0) theorem]
        target
    pure ()

rejectsInconsistentRepeatedParameters :: Assertion
rejectsInconsistentRepeatedParameters = do
    let one = pair empty empty
        two = pair one empty
        repeatedPattern =
            member (pair (CBound 0) (CBound 0)) empty
        inconsistentFact = member (pair empty one) empty
        targetTerm = member two two
    theorem <- checkedClosed
        (CForall TySet
            (CImp repeatedPattern targetTerm))
    fact <- checkedScoped [] inconsistentFact
    target <- checkedScoped [] targetTerm
    result <- runObvious
        [fact]
        [obviousImport (importIx 0) theorem]
        target
    case result of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure
                "an inconsistent repeated slot unexpectedly matched"

retainsEnteredSlotArguments :: Assertion
retainsEnteredSlotArguments = do
    foundation <- expectRight Foundation.checkedFoundation
    let delayed = foldr (\_ term -> CApp
            (CLam TySet (pair (CBound 0) (CBound 0))) term) empty [1..12 :: Int]
        betaEmpty = CApp (CLam TySet (CBound 0)) empty
        theoremTerm = CForall TySet (member (pair (CBound 0) (CBound 0)) empty)
        budget pool = defaultObviousBudget
            { obviousRefutationWorkLimit = 0
            , obviousConversionPool = Conversion.conversionPool pool
            }
    theorem <- checkedScoped [] theoremTerm
    forM_ [(delayed, delayed, 0), (betaEmpty, empty, 1000000)] \(left, right, pool) -> do
        target <- checkedScoped [] (member (pair left right) empty)
        let (statistics, result) = obviousProofDetailed (budget pool) AnyObviousProof
                foundation emptyGlobalTyping [theorem] [] [] target
        proof <- expectRight result
        assertEqual "the selected theorem succeeds in focused search"
            ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
        when (pool == 0) (assertEqual "retained syntax needs no conversion"
            0 (obviousConversionWorkConsumed statistics))
        assertCandidateReplays foundation emptyGlobalTyping [theorem] [] target proof

recoversErasedSlotBinder :: Assertion
recoversErasedSlotBinder = do
    foundation <- expectRight Foundation.checkedFoundation
    let functionType = TyArrow TySet TySet
        context = [TyArrow functionType TyProp]
        theoremTerm = CForall TySet
            (CApp (CBound 1) (CLam TySet (CBound 1)))
        targetTerm = CApp (CBound 0)
            (CLam TySet (CApp (CLam TySet empty) (CBound 0)))
    theorem <- checkedScoped context theoremTerm
    target <- checkedScoped context targetTerm
    let (statistics, result) = obviousProofDetailed
            defaultObviousBudget {obviousRefutationWorkLimit = 0} AnyObviousProof
            foundation emptyGlobalTyping [theorem] [] [] target
    proof <- expectRight result
    assertEqual "required head recovery preserves first-order slot support"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertCandidateReplays foundation emptyGlobalTyping [theorem] [] target proof

preservesPremiseSearchOrder :: Assertion
preservesPremiseSearchOrder = do
    foundation <- expectRight Foundation.checkedFoundation
    let one = pair empty empty
        two = pair one empty
        firstForEmpty = member empty empty
        firstForOne = member one empty
        secondForOne = member one one
        targetTerm = member two two
        runWith focused hypotheses theorem target =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof
                foundation emptyGlobalTyping hypotheses
                [obviousImport (importIx 0) theorem]
                [] target
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (member (CBound 0) empty)
                (CImp
                    (member (CBound 0) one)
                    targetTerm)))
    badOrder <- traverse (checkedScoped [])
        [firstForEmpty, firstForOne, secondForOne]
    goodOrder <- traverse (checkedScoped [])
        [firstForOne, firstForEmpty, secondForOne]
    target <- checkedScoped [] targetTerm
    let (badStatistics, badResult) =
            runWith 1000000 badOrder theorem target
        (goodStatistics, goodResult) =
            runWith 1000000 goodOrder theorem target
        badWork = obviousFocusedWorkConsumed badStatistics
        goodWork = obviousFocusedWorkConsumed goodStatistics
    badProof <- expectRight badResult
    goodProof <- expectRight goodResult
    assertCandidateReplays foundation emptyGlobalTyping badOrder
        [obviousImport (importIx 0) theorem] target badProof
    assertCandidateReplays foundation emptyGlobalTyping goodOrder
        [obviousImport (importIx 0) theorem] target goodProof
    assertBool
        "the failed first match is visible in focused work"
        (badWork > goodWork)
    let (fallbackStatistics, fallbackResult) =
            runWith goodWork badOrder theorem target
    fallbackProof <- expectRight fallbackResult
    assertCandidateReplays foundation emptyGlobalTyping badOrder
        [obviousImport (importIx 0) theorem] target fallbackProof
    assertBool "ground completion cancels or outlasts the incomplete focused route"
        (obviousFocusedTierOutcome fallbackStatistics /= ObviousTierCandidateBuilt)
    let focusedOnly = obviousProofDetailed
            ((focusedBudget goodWork) {obviousRefutationWorkLimit = 0}) AnyObviousProof
            foundation emptyGlobalTyping badOrder [obviousImport (importIx 0) theorem] [] target
    assertFailureKind "focused search does not reorder the poorly ordered premise search"
        (ObviousResourceExhausted ObviousFocusedWorkLimit) (snd focusedOnly)
    assertEqual
        "bounded rule saturation completes with the smaller focused allowance"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome fallbackStatistics)
    assertBool "the fallback retains one rule instance"
        (obviousRuleInstancesAdmitted fallbackStatistics >= 1)

preservesProjectedTheoremOrder :: Assertion
preservesProjectedTheoremOrder = do
    let one = pair empty empty
        firstPremise = membership
        secondPremise = member one empty
        cheaperPremise = member empty one
        targetTerm = member one one
        packagedTheorems =
            CAnd
                (CImp firstPremise (CImp secondPremise targetTerm))
                (CImp cheaperPremise targetTerm)
    theorem <- checkedScoped [] packagedTheorems
    first <- checkedClosed firstPremise
    second <- checkedClosed secondPremise
    cheaper <- checkedClosed cheaperPremise
    target <- checkedScoped [] targetTerm
    foundation <- expectRight Foundation.checkedFoundation
    let imports =
            [ obviousImport (importIx 0) first
            , obviousImport (importIx 1) second
            , obviousImport (importIx 2) cheaper
            ]
    proof <- expectRight
        (obviousProof
            defaultObviousBudget foundation emptyGlobalTyping
            [theorem] imports [] target)
    assertCandidateReplays
        foundation emptyGlobalTyping [theorem] imports target proof
    assertEqual "the first completely supported sibling is selected"
        (Set.fromList [importIx 0, importIx 1])
        (obviousUsedImports proof)

chargesLargeTheoremSubstitution :: Assertion
chargesLargeTheoremSubstitution = do
    foundation <- expectRight Foundation.checkedFoundation
    let targetTerm = otherMembership
        largePattern = nestedNegation 80 (member (CBound 0) empty)
        largeFactTerm = nestedNegation 80 membership
        runWith focused fact theorem target =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof
                foundation emptyGlobalTyping [fact]
                [obviousImport (importIx 0) theorem]
                [] target
    theorem <- checkedClosed
        (CForall TySet (CImp largePattern targetTerm))
    fact <- checkedScoped [] largeFactTerm
    target <- checkedScoped [] targetTerm
    let (statistics, result) =
            runWith 1000000 fact theorem target
        work = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping [fact]
        [obviousImport (importIx 0) theorem] target proof
    _boundaryProof <- expectRight
        (snd (runWith work fact theorem target))
    let (shortStatistics, shortResult) = runWith (work - 1) fact theorem target
    assertEqual "large substitution stops before publishing a focused candidate"
        (ObviousTierResourceExhausted ObviousFocusedWorkLimit)
        (obviousFocusedTierOutcome shortStatistics)
    assertEqual "the failed focused builder retains its real expenditure"
        (work - 1) (obviousFocusedWorkConsumed shortStatistics)
    -- Generic instantiation can supply an independent ground proof after the
    -- focused builder stops. Its success does not replenish that builder.
    case shortResult of
        Right groundProof -> do
            assertEqual "an alternative success comes from the ground tier"
                ObviousTierCandidateBuilt (obviousRefutationTierOutcome shortStatistics)
            assertCandidateReplays foundation emptyGlobalTyping [fact]
                [obviousImport (importIx 0) theorem] target groundProof
        Left failure -> assertEqual "without another proof the focused limit remains visible"
            (ObviousResourceExhausted ObviousFocusedWorkLimit) failure

boundsManyBinderTheoremBookkeeping :: Assertion
boundsManyBinderTheoremBookkeeping = do
    foundation <- expectRight Foundation.checkedFoundation
    let binderCount = 32 :: Int
        positions = [0 .. binderCount - 1]
        boundAt position =
            CBound (fromIntegral (binderCount - position - 1))
        boundTuple =
            foldr pair empty (map boundAt positions)
        concreteTuple =
            foldr pair empty
                [ COpaqueInteger (fromIntegral (500 + position))
                | position <- positions
                ]
        theoremBody =
            member boundTuple (CBound (fromIntegral binderCount))
        theoremTerm =
            foldr (\_ body -> CForall TySet body) theoremBody positions
        targetTerm = member concreteTuple (CBound 0)
        run focused theorem target =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof foundation emptyGlobalTyping [theorem] [] [] target
    theorem <- checkedScoped [TySet] theoremTerm
    target <- checkedScoped [TySet] targetTerm
    let (ampleStatistics, ampleResult) = run 1000000 theorem target
        focusedWork = obviousFocusedWorkConsumed ampleStatistics
    proof <- expectRight ampleResult
    assertCandidateReplays foundation emptyGlobalTyping [theorem] [] target proof
    assertEqual "the many-binder theorem is solved in the focused tier"
        ObviousTierCandidateBuilt
        (obviousFocusedTierOutcome ampleStatistics)
    exactProof <- expectRight (snd (run focusedWork theorem target))
    assertCandidateReplays foundation emptyGlobalTyping [theorem] [] target exactProof
    let (shortStatistics, _shortResult) =
            run (focusedWork - 1) theorem target
    assertEqual
        "one-short many-binder bookkeeping publishes no focused candidate"
        (ObviousTierResourceExhausted ObviousFocusedWorkLimit)
        (obviousFocusedTierOutcome shortStatistics)

rejectsLaterBinderInAntecedent :: Assertion
rejectsLaterBinderInAntecedent =
    case checkCanonicalCore emptyGlobalTyping
            (CImp
                (member (CBound 0) empty)
                (CForall TySet CTruth)) of
        Left (UnboundCoreIndex 0) -> pure ()
        Left failure ->
            assertFailure
                ("unexpected checked-scoping failure: " <> show failure)
        Right _checked ->
            assertFailure
                "an antecedent unexpectedly saw a later theorem binder"

reconstructsFocusedEqualityPaths :: Assertion
reconstructsFocusedEqualityPaths = do
    let one = pair empty empty
        two = pair one empty
    first <- checkedScoped [] (CEq TySet empty one)
    second <- checkedScoped [] (CEq TySet two one)
    cycleEdge <- checkedScoped [] (CEq TySet one empty)
    target <- checkedScoped [] (CEq TySet empty two)
    assertObvious [first, cycleEdge, second] [] target

breaksEqualityPathTiesBySourceOrder :: Assertion
breaksEqualityPathTiesBySourceOrder = do
    let one = pair empty empty
        two = pair one empty
        destination = pair two empty
    firstLeft <- checkedClosed (CEq TySet empty one)
    firstRight <- checkedClosed (CEq TySet one destination)
    secondLeft <- checkedClosed (CEq TySet empty two)
    secondRight <- checkedClosed (CEq TySet two destination)
    target <- checkedScoped [] (CEq TySet empty destination)
    let imports =
            [ obviousImport (importIx 0) firstLeft
            , obviousImport (importIx 1) firstRight
            , obviousImport (importIx 2) secondLeft
            , obviousImport (importIx 3) secondRight
            ]
    proof <- expectRight =<< runObvious [] imports target
    assertEqual
        "the first admitted shortest path is retained"
        (Set.fromList [importIx 0, importIx 1])
        (obviousUsedImports proof)

buildsTargetShapedCongruence :: Assertion
buildsTargetShapedCongruence = do
    let one = pair empty empty
        two = pair one empty
        three = pair two empty
    first <- checkedScoped [] (CEq TySet empty two)
    second <- checkedScoped [] (CEq TySet one three)
    target <- checkedScoped []
        (CEq TySet
            (pair empty one)
            (pair two three))
    assertObvious [first, second] [] target

-- Failed whole-term graph probes descend through applications with the same
-- checked operands. The equality and proposition-transport entry points must
-- both preserve their ambient scope and exact selected evidence.
retainsScopedEqualityOperands :: Assertion
retainsScopedEqualityOperands = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TyArrow TySet TySet, TySet, TySet, TySet]
        function = CBound 0
        left = CApp function (nestedPair 12 (CBound 1))
        right = CApp function (nestedPair 12 (CBound 3))
        edges = [CEq TySet (CBound 1) (CBound 2), CEq TySet (CBound 2) (CBound 3)]
        cases =
            [ ("equality", edges, CEq TySet left right, [0, 1])
            , ("proposition transport", edges <> [member left empty],
                member right empty, [0, 1, 2])
            ]
    forM_ cases $ \(label, terms, goal, usedHypotheses) -> do
        hypotheses <- traverse (checkedScoped context) terms
        target <- checkedScoped context goal
        let budget = (focusedBudget 100000) {obviousRefutationWorkLimit = 0}
            run allowance = obviousProofDetailed allowance AnyObviousProof
                foundation emptyGlobalTyping hypotheses [] [] target
            (statistics, result) = run budget
        proof <- expectRight result
        assertEqual (label <> " closes in focused inference")
            ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
        replayed <- expectRight
            (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
                (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual (label <> " retains exact hypothesis origins")
            (Set.fromList (map hypothesisIx usedHypotheses))
            (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual (label <> " adds no imported authority")
            Set.empty (replayedScopedKernelImportUses replayed)
        assertConversionPoolBoundary label run budget statistics proof

sharesCongruenceChildren :: Assertion
sharesCongruenceChildren = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TySet, TySet, TyArrow TySet TySet]
        chain size term = foldl' (\current _ -> CApp (CBound 2) current) term [1 .. size]
        run hypotheses target allowance = obviousProofDetailed
            ((focusedBudget allowance) {obviousRefutationWorkLimit = 0}) AnyObviousProof
            foundation emptyGlobalTyping hypotheses [] [] target
    equality <- checkedScoped context (CEq TySet (CBound 0) (CBound 1))
    forM_ [4, 16 :: Int] $ \size -> do
        target <- checkedScoped context
            (CEq TySet (chain size (CBound 0)) (chain size (CBound 1)))
        let (statistics, result) = run [equality] target 100000
            cost = obviousFocusedWorkConsumed statistics
        proof <- expectRight result
        assertCandidateReplays foundation emptyGlobalTyping [equality] [] target proof
        exact <- expectRight (snd (run [equality] target cost))
        assertCandidateReplays foundation emptyGlobalTyping [equality] [] target exact
        assertEqual "analysis and descent debit their actual focused work"
            (ObviousTierResourceExhausted ObviousFocusedWorkLimit)
            (obviousFocusedTierOutcome (fst (run [equality] target (cost - 1))))
        when (size == 16) $ do
            -- The merged baseline uses 244 units for this direct proof. A
            -- retained tree must not be built before the direct attempt wins.
            let (directStatistics, directResult) = run [target] target 244
            direct <- expectRight directResult
            assertCandidateReplays foundation emptyGlobalTyping [target] [] target direct
            assertEqual "direct evidence needs no conversion"
                0 (obviousConversionWorkConsumed directStatistics)

upgradesCongruenceOperands :: Assertion
upgradesCongruenceOperands = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TyArrow TySet TySet, TyArrow TySet TySet, TySet, TySet]
    function <- checkedScoped context (CEq (TyArrow TySet TySet) (CBound 0) (CBound 1))
    argument <- checkedScoped context (CEq TySet (CBound 2) (CBound 3))
    target <- checkedScoped context
        (CEq TySet (CApp (CBound 0) (CBound 2)) (CApp (CBound 1) (CBound 3)))
    forM_ [(function, [1, 2]), (argument, [0, 2])] $ \(canonical, used) -> do
        let hypotheses = [function, argument, canonical]
        proof <- expectRight (obviousProofWithRequirement
            (defaultObviousBudget {obviousRefutationWorkLimit = 0})
            MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses []
            [obviousLocalDefinitionView 2 DefinitionExactView] target)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual "the upgraded operand replaces its ordinary duplicate"
            (Set.fromList (map hypothesisIx used))
            (replayedScopedKernelExternalHypothesisUses replayed)

retainsCongruenceSupportRecipes :: Assertion
retainsCongruenceSupportRecipes = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TySet, TySet, TyArrow TySet TySet]
        chain size term = foldl' (\current _ -> CApp (CBound 2) current) term [1 .. size]
    equality <- checkedScoped context (CEq TySet (CBound 0) (CBound 1))
    forM_ [4, 16 :: Int] $ \size -> do
        target <- checkedScoped context
            (CEq TySet (chain size (CBound 0)) (chain size (CBound 1)))
        let hypotheses = [equality, equality]
            budget = (focusedBudget 1000000) {obviousRefutationWorkLimit = 0}
            run allowance = obviousProofDetailed allowance MustUseCanonicalDefinition
                foundation emptyGlobalTyping hypotheses []
                [obviousLocalDefinitionView 1 DefinitionExactView] target
            (statistics, result) = run budget
            cost = obviousFocusedWorkConsumed statistics
        proof <- expectRight result
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual "the deepest supported edge is actually consumed"
            (Set.singleton (hypothesisIx 1))
            (replayedScopedKernelExternalHypothesisUses replayed)
        exact <- expectRight (snd (run budget {obviousFocusedWorkLimit = cost}))
        assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target exact
        assertFailureKind "support reconstruction stops one structural unit short"
            (ObviousResourceExhausted ObviousFocusedWorkLimit)
            (snd (run budget {obviousFocusedWorkLimit = cost - 1}))
        when (size == 16) $ do
            -- Re-proving completed descendants at each upgrade used 70,174
            -- structural and 139,439 conversion units in the diagnostic draft.
            assertBool ("support descent reuses its completed ordinary children: "
                <> show (cost, obviousConversionWorkConsumed statistics))
                (cost < 30000 && obviousConversionWorkConsumed statistics < 50000)

retainsFalsitySupport :: Assertion
retainsFalsitySupport = do
    foundation <- expectRight Foundation.checkedFoundation
    let equation = CEq TySet empty (pair empty empty)
        reversed = CEq TySet (pair empty empty) empty
    target <- checkedScoped [] CFalsum
    forM_
        [ ("later matching fact", [equation, CNot equation, equation], 2, [1, 2])
        , ("later reversed equality", [equation, CNot equation, reversed], 2, [1, 2])
        , ("ordinary root closure", [CFalsum, equation, CNot equation, equation], 3, [2, 3])
        ] $ \(label, terms, canonical, used) -> do
            hypotheses <- traverse (checkedScoped []) terms
            let budget = (focusedBudget 100000) {obviousRefutationWorkLimit = 0}
                run allowance = obviousProofDetailed allowance MustUseCanonicalDefinition
                    foundation emptyGlobalTyping hypotheses []
                    [obviousLocalDefinitionView canonical DefinitionExactView] target
                (statistics, result) = run budget
            proof <- expectRight result
            replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
                (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
            assertEqual (label <> " consumes the later source")
                (Set.fromList (map hypothesisIx used))
                (replayedScopedKernelExternalHypothesisUses replayed)
            let cost = obviousFocusedWorkConsumed statistics
            exact <- expectRight (snd (run budget {obviousFocusedWorkLimit = cost}))
            assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target exact
            assertFailureKind (label <> " charges selected construction exactly")
                (ObviousResourceExhausted ObviousFocusedWorkLimit)
                (snd (run budget {obviousFocusedWorkLimit = cost - 1}))

rejectsIncompatibleCongruence :: Assertion
rejectsIncompatibleCongruence = do
    let left = CApp (CIntrinsic FamilyUnion) empty
        right =
            CApp
                (CLogicalSelect TySet)
                (CLam TySet CTruth)
    target <- checkedScoped [] (CEq TySet left right)
    result <- runObvious [] [] target
    case result of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure
                "type-incompatible congruence components unexpectedly matched"

tracksCanonicalEqualityEvidence :: Assertion
tracksCanonicalEqualityEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let one = pair empty empty
        two = pair one empty
    ordinary <- checkedScoped [] (CEq TySet empty two)
    canonical <- checkedScoped [] (CEq TySet empty one)
    tailEdge <- checkedScoped [] (CEq TySet one two)
    target <- checkedScoped [] (CEq TySet empty two)
    let hypotheses = [ordinary, canonical, tailEdge]
        result =
            obviousProofWithRequirement
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation emptyGlobalTyping hypotheses []
                [obviousLocalDefinitionView 1 DefinitionExactView]
                target
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target proof

chargesDeepEqualityInterning :: Assertion
chargesDeepEqualityInterning = do
    foundation <- expectRight Foundation.checkedFoundation
    let deep = nestedPair 70 empty
        one = pair empty empty
        two = pair one empty
        runWith focused hypotheses target =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof
                foundation emptyGlobalTyping hypotheses [] [] target
    first <- checkedScoped [] (CEq TySet deep one)
    second <- checkedScoped [] (CEq TySet one two)
    target <- checkedScoped [] (CEq TySet deep two)
    let hypotheses = [first, second]
        runFocusedOnly focused = obviousProofDetailed
            ((focusedBudget focused) {obviousRefutationWorkLimit = 0}) AnyObviousProof
            foundation emptyGlobalTyping hypotheses [] [] target
        (statistics, result) = runFocusedOnly 1000000
        work = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target proof
    _boundary <- expectRight
        (snd (runFocusedOnly work))
    assertFailureKind "the isolated focused owner stops one unit short"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        (snd (runFocusedOnly (work - 1)))
    let (fallbackStatistics, fallbackResult) =
            runWith (work - 1) hypotheses target
    fallbackProof <- expectRight fallbackResult
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target fallbackProof
    assertBool "the interrupted focused route publishes no candidate"
        (obviousFocusedTierOutcome fallbackStatistics /= ObviousTierCandidateBuilt)
    assertEqual "refutation reconstructs the transitive equality path"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome fallbackStatistics)
    assertBool "refutation processes equality events"
        (obviousEqualityEventsProcessed fallbackStatistics > 0)

introducesDisjunctions :: Assertion
introducesDisjunctions = do
    left <- checkedScoped [] membership
    right <- checkedScoped [] otherMembership
    target <- checkedScoped [] (COr membership otherMembership)
    assertObvious [left] [] target
    assertObvious [right] [] target

    leftImport <- checkedClosed membership
    rightImport <- checkedClosed otherMembership
    proof <- expectRight =<< runObvious []
        [ obviousImport (importIx 0) leftImport
        , obviousImport (importIx 1) rightImport
        ]
        target
    assertEqual
        "the left source-order disjunct wins when both are available"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

continuesAfterUnsupportedDisjunct :: Assertion
continuesAfterUnsupportedDisjunct = do
    let left =
            CNot
                (CForall TySet
                    (CEq TySet (CBound 0) empty))
        higherOrderSource =
            CForall TySet
                (CNot
                    (CForall TySet
                        (CEq TySet (CBound 1) empty)))
    theorem <- checkedClosed higherOrderSource
    right <- checkedScoped [] otherMembership
    target <- checkedScoped [] (COr left otherMembership)
    _proof <- expectRight =<< runObvious
        [right]
        [obviousImport (importIx 0) theorem]
        target
    pure ()

propagatesCanonicalDisjunctionEvidence :: Assertion
propagatesCanonicalDisjunctionEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let one = pair empty empty
        rightTerm = CEq TySet empty one
    ordinary <- checkedScoped [] membership
    canonical <- checkedScoped [] rightTerm
    target <- checkedScoped [] (COr membership rightTerm)
    let hypotheses = [ordinary, canonical]
        result =
            obviousProofWithRequirement
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation emptyGlobalTyping hypotheses []
                [obviousLocalDefinitionView 1 DefinitionExactView]
                target
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target proof

chargesNestedDisjunctionSearch :: Assertion
chargesNestedDisjunctionSearch = do
    foundation <- expectRight Foundation.checkedFoundation
    let targetTerm = nestedDisjunction 40 membership CTruth
        runWith budget target =
            obviousProofDetailed
                budget
                AnyObviousProof
                foundation emptyGlobalTyping [] [] [] target
    target <- checkedScoped [] targetTerm
    let focusedOnly allowance = (focusedBudget allowance) {obviousRefutationWorkLimit = 0}
        (statistics, result) = runWith (focusedOnly 1000000) target
        work = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping [] [] target proof
    _boundary <- expectRight (snd (runWith (focusedOnly work) target))
    assertFailureKind "one-short focused introduction cannot construct its proof"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        (snd (runWith (focusedOnly (work - 1)) target))
    let (fallbackStatistics, fallbackResult) =
            runWith (focusedBudget (work - 1)) target
    fallbackProof <- expectRight fallbackResult
    assertCandidateReplays foundation emptyGlobalTyping [] [] target fallbackProof
    assertBool "ground completion cancels or outlasts the incomplete focused route"
        (obviousFocusedTierOutcome fallbackStatistics /= ObviousTierCandidateBuilt)
    assertEqual "refutation can complete the bounded disjunction"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome fallbackStatistics)

replaysSignedPropositionalCalculus :: Assertion
replaysSignedPropositionalCalculus = do
    let propositionA = membership
        propositionB = otherMembership
        unrelated = member (pair empty empty) empty
        cases =
            [ ("false truth", [], CTruth)
            , ("true falsum", [CFalsum], unrelated)
            , ("true negation", [CNot propositionA, propositionA], unrelated)
            , ("false negation", [], COr propositionA (CNot propositionA))
            , ( "exposed true negation"
              , [betaWrap (CNot propositionA), propositionA]
              , unrelated
              )
            , ( "exposed false root"
              , []
              , betaWrap (COr propositionA (CNot propositionA))
              )
            , ( "true conjunction"
              , [CAnd propositionA propositionB, CNot propositionA]
              , unrelated
              )
            , ( "false conjunction"
              , [propositionA, propositionB]
              , CAnd propositionA propositionB
              )
            , ( "nested branch reason DAG"
              , []
              , CAnd
                    (COr propositionA (CNot propositionA))
                    (COr propositionB (CNot propositionB))
              )
            , ( "true disjunction"
              , [ COr propositionA propositionB
                , CNot propositionA
                , CNot propositionB
                ]
              , unrelated
              )
            , ("false disjunction", [propositionA],
                COr propositionA propositionB)
            , ( "true implication"
              , [ CImp propositionA propositionB
                , propositionA
                , CNot propositionB
                ]
              , unrelated
              )
            , ("false implication premise", [CNot propositionA],
                CImp propositionA propositionB)
            , ("false implication conclusion", [propositionB],
                CImp propositionA propositionB)
            ]
    traverse_
        (\(label, facts, target) ->
            assertRefutationCase label facts target)
        cases

assertRefutationCase
    :: String
    -> [CanonicalTerm Void]
    -> CanonicalTerm Void
    -> Assertion
assertRefutationCase label factTerms targetTerm = do
    foundation <- expectRight Foundation.checkedFoundation
    facts <- traverse (checkedScoped []) factTerms
    target <- checkedScoped [] targetTerm
    let (statistics, result) =
            obviousProofDetailed
                refutationBudget
                AnyObviousProof
                foundation emptyGlobalTyping facts [] [] target
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping facts [] target proof
    assertEqual (label <> " starts after focused exhaustion")
        (ObviousTierResourceExhausted ObviousFocusedWorkLimit)
        (obviousFocusedTierOutcome statistics)
    assertEqual (label <> " is reconstructed by refutation")
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome statistics)

preservesRefutationBranchSemantics :: Assertion
preservesRefutationBranchSemantics = do
    foundation <- expectRight Foundation.checkedFoundation
    let propositionA = membership
        propositionB = otherMembership
        unrelated = member (pair empty empty) empty
        importsBudget = refutationBudget
    conjunction <- checkedClosed (CAnd propositionA propositionB)
    direct <- checkedClosed propositionA
    negation <- checkedClosed (CNot propositionA)
    target <- checkedScoped [] unrelated
    let imports =
            [ obviousImport (importIx 0) conjunction
            , obviousImport (importIx 1) direct
            , obviousImport (importIx 2) negation
            ]
        (rootStatistics, rootResult) =
            obviousProofDetailed
                importsBudget AnyObviousProof foundation emptyGlobalTyping
                [] imports [] target
    rootProof <- expectRight rootResult
    assertCandidateReplays foundation emptyGlobalTyping [] imports target rootProof
    assertEqual "root barrier retains the direct contradictory facts"
        (Set.fromList [importIx 1, importIx 2])
        (obviousUsedImports rootProof)
    assertEqual "root contradiction is reconstructed by refutation"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome rootStatistics)
    let (repeatedStatistics, repeatedResult) =
            obviousProofDetailed
                importsBudget AnyObviousProof foundation emptyGlobalTyping
                [] imports [] target
    repeatedProof <- expectRight repeatedResult
    assertEqual "repeated search selects the same root authority"
        (obviousUsedImports rootProof)
        (obviousUsedImports repeatedProof)
    assertEqual "repeated search has stable coarse work"
        ( obviousRefutationWorkConsumed rootStatistics
        , obviousBranchNodesCreated rootStatistics
        , obviousSignedFormulasAdmitted rootStatistics
        )
        ( obviousRefutationWorkConsumed repeatedStatistics
        , obviousBranchNodesCreated repeatedStatistics
        , obviousSignedFormulasAdmitted repeatedStatistics
        )

    disjunction <- checkedScoped [] (COr propositionA propositionB)
    propositionTarget <- checkedScoped [] propositionA
    let (siblingStatistics, siblingResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [disjunction] [] [] propositionTarget
    assertFailureKind "an open sibling cannot borrow the first child's fact"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        siblingResult
    assertEqual "the second sibling saturates independently"
        ObviousTierNoProof
        (obviousRefutationTierOutcome siblingStatistics)
    assertEqual "the query negation simplifies the disjunction in the root"
        1
        (obviousBranchNodesCreated siblingStatistics)

    let (canonicalStatistics, canonicalResult) =
            obviousProofDetailed
                refutationBudget MustUseCanonicalDefinition
                foundation emptyGlobalTyping [] [] [] propositionTarget
    assertFailureKind "canonical mode preserves the first failed focused boundary"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        canonicalResult
    assertEqual "canonical mode also completes its owned ground search"
        ObviousTierNoProof
        (obviousRefutationTierOutcome canonicalStatistics)

reportsRefutationBoundaries :: Assertion
reportsRefutationBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    atom <- checkedScoped [] membership
    other <- checkedScoped [] otherMembership
    disjunction <- checkedScoped [] (COr membership otherMembership)
    target <- checkedScoped [] (COr otherMembership membership)
    let run budget hypotheses goal =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                hypotheses [] [] goal
        zeroWork = refutationBudget
            { obviousRefutationWorkLimit = 0 }
        (zeroWorkStatistics, zeroWorkResult) = run zeroWork [] atom
    assertFailureKind "focused exhaustion remains the combined zero-work result"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        zeroWorkResult
    assertEqual "zero refutation work is independently visible"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome zeroWorkStatistics)

    let zeroTerms = refutationBudget {obviousGroundTermLimit = 0}
        (zeroTermStatistics, zeroTermResult) = run zeroTerms [] atom
    assertFailureKind "focused exhaustion keeps combined-result precedence"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        zeroTermResult
    assertEqual "zero ground-term failure is structured"
        (ObviousTierResourceExhausted ObviousGroundTermLimit)
        (obviousRefutationTierOutcome zeroTermStatistics)
    assertEqual "failed catalogue publication admits no terms"
        0
        (obviousTermsAdmitted zeroTermStatistics)

    let zeroBranches = refutationBudget {obviousBranchNodeLimit = 0}
        (zeroBranchStatistics, zeroBranchResult) =
            run zeroBranches [] atom
    assertFailureKind "focused exhaustion precedes zero branch capacity"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        zeroBranchResult
    assertEqual "failed root publication creates no branch"
        0
        (obviousBranchNodesCreated zeroBranchStatistics)
    -- This includes selected-root admission, negated-goal, syntax-first view
    -- and catalogue work; exposed heads spend no conversion credit.
    -- Equality-state initialization begins only after the zero branch cap.
    let rootPreparationWork = 76
    assertEqual "the root cap precedes proof-context extension"
        rootPreparationWork
        (obviousRefutationWorkConsumed zeroBranchStatistics)
    let exactZeroBranches =
            zeroBranches
                { obviousRefutationWorkLimit = rootPreparationWork
                }
        shortZeroBranches =
            zeroBranches
                { obviousRefutationWorkLimit = rootPreparationWork - 1
                }
        (exactZeroStatistics, exactZeroResult) =
            run exactZeroBranches [] atom
        (shortZeroStatistics, shortZeroResult) =
            run shortZeroBranches [] atom
    assertFailureKind
        "the exact root-preparation boundary still reports its cap"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        exactZeroResult
    assertEqual "the root cap wins before context construction"
        (ObviousTierResourceExhausted ObviousBranchNodeLimit)
        (obviousRefutationTierOutcome exactZeroStatistics)
    assertFailureKind "one-short root preparation publishes no candidate"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        shortZeroResult
    assertEqual "one-short root preparation exhausts counted work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortZeroStatistics)
    assertEqual "neither root-cap boundary publishes a branch"
        (0, 0)
        ( obviousBranchNodesCreated exactZeroStatistics
        , obviousBranchNodesCreated shortZeroStatistics
        )

    let (ampleStatistics, ampleResult) =
            run refutationBudget [disjunction] target
        usedWork = obviousRefutationWorkConsumed ampleStatistics
        usedTerms = obviousTermsAdmitted ampleStatistics
        exactWorkBudget = refutationBudget
            { obviousRefutationWorkLimit = usedWork }
        exactTermBudget = refutationBudget
            { obviousGroundTermLimit = usedTerms }
    ampleProof <- expectRight ampleResult
    assertCandidateReplays
        foundation emptyGlobalTyping [disjunction] [] target ampleProof
    _exactWork <- expectRight (snd (run exactWorkBudget [disjunction] target))
    _exactTerms <- expectRight (snd (run exactTermBudget [disjunction] target))
    let (shortWorkStatistics, shortWorkResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork - 1 }
                [disjunction]
                target
    case shortWorkResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "refutation published a proof past its work boundary"
    assertEqual "one-short reconstruction exhausts refutation work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortWorkStatistics)
    let (shortTermStatistics, shortTermResult) =
            run
                refutationBudget
                    { obviousGroundTermLimit = usedTerms - 1 }
                [disjunction]
                target
    assertFailureKind "one-short catalogue publishes no fallback candidate"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        shortTermResult
    assertEqual "one-short catalogue reports its hard cap"
        (ObviousTierResourceExhausted ObviousGroundTermLimit)
        (obviousRefutationTierOutcome shortTermStatistics)

    let usedBranches = obviousBranchNodesCreated ampleStatistics
        exactBranches = refutationBudget {obviousBranchNodeLimit = usedBranches}
        shortBranches = refutationBudget {obviousBranchNodeLimit = usedBranches - 1}
    _exactBranchProof <-
        expectRight (snd (run exactBranches [disjunction] target))
    let (shortBranchStatistics, shortBranchResult) =
            run shortBranches [disjunction] target
    assertFailureKind "one-short branch allowance publishes no candidate"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        shortBranchResult
    assertEqual "one-short branch allowance reports its cap"
        (ObviousTierResourceExhausted ObviousBranchNodeLimit)
        (obviousRefutationTierOutcome shortBranchStatistics)

    -- The preceding commutativity proof now propagates without a split. Keep a
    -- separate case whose first split has neither disjunct decided at pop time.
    caseTarget <- checkedScoped [] (member (pair empty empty) empty)
    caseRules <- traverse (checkedScoped [])
        [ CImp membership (scopedCoreTerm caseTarget)
        , CImp otherMembership (scopedCoreTerm caseTarget) ]
    let caseFacts = disjunction : caseRules
        (caseStatistics, caseResult) = run refutationBudget caseFacts caseTarget
        caseBranches = obviousBranchNodesCreated caseStatistics
    caseProof <- expectRight caseResult
    assertCandidateReplays foundation emptyGlobalTyping caseFacts [] caseTarget caseProof
    assertBool "the separate case still exercises child-branch admission" (caseBranches > 1)
    _ <- expectRight (snd (run refutationBudget {obviousBranchNodeLimit = caseBranches} caseFacts caseTarget))
    let (shortCaseStatistics, shortCaseResult) =
            run refutationBudget {obviousBranchNodeLimit = caseBranches - 1} caseFacts caseTarget
    assertFailureKind "one-short child admission publishes no candidate"
        (ObviousResourceExhausted ObviousFocusedWorkLimit) shortCaseResult
    assertEqual "the child admission retains its hard branch boundary"
        (ObviousTierResourceExhausted ObviousBranchNodeLimit)
        (obviousRefutationTierOutcome shortCaseStatistics)

    let duplicateRun = run refutationBudget [atom, atom] other
        (duplicateStatistics, duplicateResult) = duplicateRun
    assertFailureKind "duplicate atom request remains open"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        duplicateResult
    assertEqual "duplicate signed admission is idempotent"
        2
        (obviousSignedFormulasAdmitted duplicateStatistics)

    let atomicTerms =
            [ CEq TySet empty (pair empty empty)
            , CForall TySet (member (CBound 0) empty)
            , CExists TySet (member (CBound 0) empty)
            ]
    traverse_
        (\atomicTerm -> do
            atomicTarget <- checkedScoped [] atomicTerm
            let (atomicStatistics, atomicResult) =
                    run refutationBudget [] atomicTarget
            assertFailureKind "deferred logical shape remains open"
                (ObviousResourceExhausted ObviousFocusedWorkLimit)
                atomicResult
            assertEqual "deferred logical shape is atomic in Stage 4"
                ObviousTierNoProof
                (obviousRefutationTierOutcome atomicStatistics))
        atomicTerms

    ambientTarget <- checkedScoped [TySet] (member (CBound 0) empty)
    ambientUniversal <- checkedScoped [TySet]
        (CForall TySet (CEq TySet (CBound 1) (CBound 0)))
    let collectAmbient hypotheses =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                hypotheses [] [] ambientTarget
        (baseCatalogueStatistics, _baseResult) = collectAmbient []
        (binderCatalogueStatistics, _binderResult) =
            collectAmbient [ambientUniversal]
    assertEqual
        "a binder adds only its closed root; its ambient occurrence reuses a term and its open occurrence is skipped"
        (obviousTermsAdmitted baseCatalogueStatistics + 1)
        (obviousTermsAdmitted binderCatalogueStatistics)

data OracleProposition
    = OracleAtom !Int
    | OracleTruth
    | OracleFalsum
    | OracleNot !OracleProposition
    | OracleAnd !OracleProposition !OracleProposition
    | OracleOr !OracleProposition !OracleProposition
    | OracleImp !OracleProposition !OracleProposition
    deriving stock (Show, Eq, Ord)

oraclePropositionValue
    :: Map.Map Int Bool
    -> OracleProposition
    -> Bool
oraclePropositionValue valuation = \case
    OracleAtom atom -> Map.findWithDefault False atom valuation
    OracleTruth -> True
    OracleFalsum -> False
    OracleNot proposition -> not (oraclePropositionValue valuation proposition)
    OracleAnd left right ->
        oraclePropositionValue valuation left
            && oraclePropositionValue valuation right
    OracleOr left right ->
        oraclePropositionValue valuation left
            || oraclePropositionValue valuation right
    OracleImp premise conclusion ->
        not (oraclePropositionValue valuation premise)
            || oraclePropositionValue valuation conclusion

oraclePropositionEntails
    :: [OracleProposition]
    -> OracleProposition
    -> Bool
oraclePropositionEntails hypotheses target =
    all validates oracleValuations
  where
    validates valuation =
        not (all (oraclePropositionValue valuation) hypotheses)
            || oraclePropositionValue valuation target

    oracleValuations =
        [ Map.fromList [(0, first), (1, second), (2, third)]
        | first <- [False, True]
        , second <- [False, True]
        , third <- [False, True]
        ]

oraclePropositionTerm
    :: OracleProposition
    -> CanonicalTerm Void
oraclePropositionTerm = \case
    OracleAtom 0 -> membership
    OracleAtom 1 -> otherMembership
    OracleAtom _ -> member (pair empty empty) empty
    OracleTruth -> CTruth
    OracleFalsum -> CFalsum
    OracleNot proposition -> CNot (oraclePropositionTerm proposition)
    OracleAnd left right ->
        CAnd
            (oraclePropositionTerm left)
            (oraclePropositionTerm right)
    OracleOr left right ->
        COr
            (oraclePropositionTerm left)
            (oraclePropositionTerm right)
    OracleImp premise conclusion ->
        CImp
            (oraclePropositionTerm premise)
            (oraclePropositionTerm conclusion)

agreesWithPropositionalOracle :: Assertion
agreesWithPropositionalOracle = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = OracleAtom 0
        b = OracleAtom 1
        c = OracleAtom 2
        cases =
            [ ([], OracleOr a (OracleNot a))
            , ([a, OracleNot a], OracleFalsum)
            , ([OracleAnd a b], a)
            , ([OracleAnd a b], b)
            , ([OracleOr a b, OracleNot a], b)
            , ([OracleImp a b, a], b)
            , ([OracleImp a b, OracleImp b c, a], c)
            , ([OracleNot (OracleNot a)], a)
            , ([OracleNot (OracleAnd a b), a], OracleNot b)
            , ([OracleTruth], OracleTruth)
            , ([a], b)
            , ([OracleOr a b], a)
            , ([OracleImp a b], b)
            , ([OracleNot a], a)
            , ([], OracleFalsum)
            ]
    traverse_ (checkCase foundation) (zip [0 :: Int ..] cases)
  where
    checkCase foundation (caseIndex, (oracleFacts, oracleTarget)) = do
        hypotheses <-
            traverse
                (checkedScoped [] . oraclePropositionTerm)
                oracleFacts
        target <- checkedScoped [] (oraclePropositionTerm oracleTarget)
        let expected =
                oraclePropositionEntails oracleFacts oracleTarget
            (statistics, result) =
                obviousProofDetailed
                    refutationBudget AnyObviousProof foundation emptyGlobalTyping
                    hypotheses [] [] target
            label = "propositional oracle case " <> show caseIndex
        if expected
            then do
                proof <- expectRight result
                assertCandidateReplays
                    foundation emptyGlobalTyping hypotheses [] target proof
                assertEqual (label <> " builds a refutation candidate")
                    ObviousTierCandidateBuilt
                    (obviousRefutationTierOutcome statistics)
            else do
                case result of
                    Left _failure -> pure ()
                    Right _proof ->
                        assertFailure
                            (label <> " proved a false consequence")
                assertEqual (label <> " saturates in the supported fragment")
                    ObviousTierNoProof
                    (obviousRefutationTierOutcome statistics)

coalescesSelectedFactDomains :: Assertion
coalescesSelectedFactDomains = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyArrow TySet TyProp, TyArrow TySet TyProp, TyProp, TySet]
        pairWithEmpty argument = pair argument empty
        firstPredicate argument = member argument empty
        secondPredicate depth argument = member argument (CBound depth)
        firstView = CForall TySet (CEq TyProp (CApp (CBound 1) (CBound 0))
            (COr (firstPredicate (pairWithEmpty (CBound 0))) (CBound 3)))
        secondView = CForall TySet (CEq TyProp (CApp (CBound 2) (CBound 0))
            (COr (secondPredicate 4 (pairWithEmpty (CBound 0))) (CBound 3)))
        contradiction two = if two then CForall TySet (CForall TySet
            (CImp (firstPredicate (pairWithEmpty (CBound 1)))
                (CImp (secondPredicate 5 (pairWithEmpty (CBound 0))) CFalsum)))
            else CForall TySet (CImp (firstPredicate (pairWithEmpty (CBound 0))) CFalsum)
    target <- checkedScoped types (CBound 2)
    forM_ [False, True] $ \two -> do
        hypotheses <- traverse (checkedScoped types)
            [CApp (CBound 0) empty, CApp (CBound 1) (CBound 3), firstView, secondView, contradiction two]
        let views = [obviousLocalDefinitionView index DefinitionPointwiseView | index <- if two then [2, 3] else [2]]
            run selected = obviousProofDetailed defaultObviousBudget MustUseCanonicalDefinition
                foundation emptyGlobalTyping hypotheses [] selected target
            (statistics, result) = run views
        proof <- expectRight result
        assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target proof
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual "only consumed selected sources justify the proof"
            (Set.fromList (map hypothesisIx (if two then [0, 1, 2, 3, 4] else [0, 2, 4])))
            (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual "one viable base query and one combined package, without selected-prefix searches"
            2 (obviousBranchNodesCreated statistics)
        assertEqual "the supplied opportunity starts one combined fact domain"
            1 (obviousFactDomainsStarted statistics)
        assertBool "the default covers the required selected-fact composition"
            (not (obviousFactDomainsDeferred statistics))
        for_ [1, 8] $ \breadth -> do
            let (allowedStatistics, allowedResult) = obviousProofDetailed
                    defaultObviousBudget {obviousFactDomainLimit = breadth} MustUseCanonicalDefinition
                    foundation emptyGlobalTyping hypotheses [] views target
            allowed <- expectRight allowedResult
            assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target allowed
            assertEqual "additional breadth neither repeats a selected snapshot nor changes its work"
                (obviousRefutationWorkConsumed statistics) (obviousRefutationWorkConsumed allowedStatistics)
            assertEqual "completed demand starts no further domains" 1 (obviousFactDomainsStarted allowedStatistics)
        let (deferredStatistics, deferredResult) = obviousProofDetailed
                defaultObviousBudget {obviousFactDomainLimit = 0} MustUseCanonicalDefinition
                foundation emptyGlobalTyping hypotheses [] views target
        case deferredResult of
            Right _ -> assertFailure "a necessary outside-domain selection ignored the breadth policy"
            Left ObviousResourceExhausted{} -> assertFailure "policy deferral became real resource exhaustion"
            Left failure | obviousFailureClass failure == ObviousIntegrityClass -> assertFailure (show failure)
            Left _ -> pure ()
        assertEqual "a prevented start is not an activation" 0 (obviousFactDomainsStarted deferredStatistics)
        assertBool "a genuinely eligible prevented activation is reported"
            (obviousFactDomainsDeferred deferredStatistics)
        let spent = obviousRefutationWorkConsumed statistics
            bounded amount = obviousProofDetailed defaultObviousBudget {obviousRefutationWorkLimit = amount}
                MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses [] views target
        (exactStatistics, exactProof) <- case bounded spent of
            (measured, Right candidate) -> pure (measured, candidate)
            (_, Left failure) -> assertFailure (show failure) >> fail "exact ground allowance"
        assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target exactProof
        assertEqual "exact activation debit includes probes, preparation and construction"
            spent (obviousRefutationWorkConsumed exactStatistics)
        let (shortStatistics, shortResult) = bounded (spent - 1)
        assertFailureKind "one-short activation cannot restart with renewed credit"
            (ObviousResourceExhausted ObviousRefutationWorkLimit) shortResult
        assertEqual "failed activation preserves the full one-short debit"
            (spent - 1) (obviousRefutationWorkConsumed shortStatistics)
        conjunction <- checkedScoped types (CAnd (CBound 2) (CBound 2))
        let (upgradeStatistics, upgradeResult) = obviousProofDetailed defaultObviousBudget MustUseCanonicalDefinition
                foundation emptyGlobalTyping (hypotheses <> [target]) [] views conjunction
        upgraded <- expectRight upgradeResult
        assertEqual "the conjunction and its child retain their distinct exact targets"
            2 (obviousFactDomainsStarted upgradeStatistics)
        upgradedReplay <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList (hypotheses <> [target])) conjunction
            (KernelProof.builtProofDerivation (obviousBuiltProof upgraded)))
        assertBool "a later canonical consumer retains the selected-domain route beside ordinary reuse"
            (not (Set.disjoint (Set.fromList (map hypothesisIx (if two then [2, 3] else [2])))
                (replayedScopedKernelExternalHypothesisUses upgradedReplay)))
        let (sharedStatistics, sharedResult) = obviousProofDetailed defaultObviousBudget MustUseCanonicalDefinition
                foundation emptyGlobalTyping (hypotheses <> [target]) [] views target
        shared <- expectRight sharedResult
        assertCandidateReplays foundation emptyGlobalTyping (hypotheses <> [target]) [] target shared
        assertEqual "ordinary reuse does not create a new activation identity for canonical demand"
            1 (obviousFactDomainsStarted sharedStatistics)
        forM_ (if two then [take 1 views, drop 1 views] else [[]]) $ \missing ->
            case snd (run missing) of
                Left ObviousResourceExhausted{} -> assertFailure "a missing view exhausted production work"
                Left failure | obviousFailureClass failure == ObviousIntegrityClass -> assertFailure (show failure)
                Left _ -> pure ()
                Right _ -> assertFailure "unselected syntax supplied proof evidence"
        when two $ for_ [4, 8] $ \irrelevantCount -> do
            irrelevant <- traverse (checkedScoped types)
                [CImp (foldr (const (CAnd CTruth)) CTruth [1 .. depth :: Int]) CTruth
                | depth <- [1 .. irrelevantCount]]
            let (scaledStatistics, scaledResult) = obviousProofDetailed defaultObviousBudget MustUseCanonicalDefinition
                    foundation emptyGlobalTyping (hypotheses <> irrelevant) [] views target
            scaled <- expectRight scaledResult
            assertCandidateReplays foundation emptyGlobalTyping (hypotheses <> irrelevant) [] target scaled
            assertEqual "irrelevant supplied sources do not multiply selected-domain starts"
                1 (obviousFactDomainsStarted scaledStatistics)
    -- Sibling implication scopes need separate certified inputs. Their first
    -- domains still spend one request-wide policy allowance.
    siblingTarget <- checkedScoped types (CAnd
        (CImp (CApp (CBound 0) empty) (CBound 2))
        (CImp (CApp (CBound 1) (CBound 3)) (CBound 2)))
    siblingFacts <- traverse (checkedScoped types)
        [firstView, secondView, contradiction False,
         CForall TySet (CImp (secondPredicate 4 (pairWithEmpty (CBound 0))) CFalsum)]
    let siblingViews = [obviousLocalDefinitionView index DefinitionPointwiseView | index <- [0, 1]]
        siblings breadth = obviousProofDetailed defaultObviousBudget {obviousFactDomainLimit = breadth}
            MustUseCanonicalDefinition foundation emptyGlobalTyping siblingFacts [] siblingViews siblingTarget
    for_ [2, 8] $ \breadth -> do
        let (statistics, result) = siblings breadth
        proof <- expectRight result
        assertCandidateReplays foundation emptyGlobalTyping siblingFacts [] siblingTarget proof
        assertEqual "distinct sibling queries share one request-wide activation count"
            2 (obviousFactDomainsStarted statistics)
        assertBool "two starts cover both live sibling demands" (not (obviousFactDomainsDeferred statistics))
    let (limitedStatistics, limitedResult) = siblings 1
    case limitedResult of
        Right _ -> assertFailure "a sibling acquired its own fresh breadth allowance"
        Left ObviousResourceExhausted{} -> assertFailure "sibling policy deferral exhausted a real resource"
        Left failure | obviousFailureClass failure == ObviousIntegrityClass -> assertFailure (show failure)
        Left _ -> pure ()
    assertEqual "the spent start is not refunded" 1 (obviousFactDomainsStarted limitedStatistics)
    assertBool "the unmet sibling demand is reported as deferred" (obviousFactDomainsDeferred limitedStatistics)

refutationBudget :: ObviousBudget
refutationBudget =
    defaultObviousBudget
        { obviousFocusedWorkLimit = 0
        , obviousRefutationWorkLimit = 1000000
        , obviousGroundTermLimit = 10000
        , obviousBranchNodeLimit = 1000
        }

-- Record-shape consumers need whole quantified/existential components, not
-- arbitrary ground instances of their bodies. Publish the admitted bundle once.
retainsStructuredRuleResult :: Assertion
retainsStructuredRuleResult = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 20
        p x = member x (COpaqueInteger 21)
        targetTerm = member a (COpaqueInteger 22)
        bundle subject = CAnd
            (CForall TySet (member (CBound 0) subject))
            (CExists TySet (member (CBound 0) subject))
        source = CForall TySet (CImp (p (CBound 0)) (bundle (CBound 1)))
    sources <- traverse checkedClosed [source, CImp (bundle a) targetTerm]
    hypotheses <- traverse (checkedScoped []) [p a]
    target <- checkedScoped [] targetTerm
    let imports = zipWith (obviousImport . importIx) [0..] sources
        (statistics, result) = obviousProofDetailed refutationBudget AnyObviousProof
            foundation emptyGlobalTyping hypotheses imports [] target
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping hypotheses imports target proof
    assertEqual "the complete structured result is instantiated once" 1
        (obviousRuleInstancesAdmitted statistics)
    assertEqual "producer and consumer retain their exact cited authority"
        (Set.fromList [importIx 0, importIx 1]) (obviousUsedImports proof)

-- Once P(a) discharges a prefix, its quantified result owns the remaining
-- discovery. Inline descendants of the original source would repeat all
-- combinations of a,b,c even though their intermediate formulas coincide.
sharesQuantifiedRuleResults :: Assertion
sharesQuantifiedRuleResults = do
    foundation <- expectRight Foundation.checkedFoundation
    let p x = member x (COpaqueInteger 10)
        q x = member x (COpaqueInteger 11)
        values = COpaqueInteger <$> [20,21,22]
        source = foldr (\_ body -> CForall TySet (CImp (p (CBound 0)) body))
            (q (CBound 0)) [1..3 :: Int]
    theorem <- checkedClosed source
    hypotheses <- traverse (checkedScoped []) (p <$> values)
    missing <- checkedScoped [] (q (COpaqueInteger 23))
    present <- checkedScoped [] (q (COpaqueInteger 22))
    let imports = [obviousImport (importIx 0) theorem]
        run target = obviousProofDetailed refutationBudget AnyObviousProof
            foundation emptyGlobalTyping hypotheses imports [] target
        (statistics, result) = run missing
    case result of
        Left _ -> pure ()
        Right _ -> assertFailure "the rule invented a missing guard"
    assertEqual "ordinary finite saturation completes"
        ObviousTierNoProof (obviousRefutationTierOutcome statistics)
    assertBool "three three-way prefixes do not become a Cartesian product"
        (obviousRuleInstancesAdmitted statistics <= 9)
    proof <- expectRight (snd (run present))
    assertCandidateReplays foundation emptyGlobalTyping hypotheses imports present proof
    assertEqual "shared intermediate reasoning retains the exact source"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)

-- A small version of the club proof: selected conjunction results supply the
-- ordinal guards, then transitivity closes both sides of a membership/equality
-- case. Repeated partial matches and equality retries must not scan all earlier
-- substitutions. The unused powers deliberately lie outside the frozen domain.
reusesTransitiveCaseSubstitutions :: Assertion
reusesTransitiveCaseSubstitutions = do
    foundation <- expectRight Foundation.checkedFoundation
    let value = COpaqueInteger
        ordinal x = member x (value 99)
        seed x = member x (value 98)
        transitivity = CForall TySet (CForall TySet (CForall TySet
            (CImp (ordinal (CBound 2))
                (CImp (CAnd (member (CBound 1) (CBound 0)) (member (CBound 0) (CBound 2)))
                    (member (CBound 1) (CBound 2))))))
        classification = CForall TySet (CImp (seed (CBound 0))
            (CAnd (ordinal (CBound 0))
                (member (CApp (CIntrinsic PowerSet) (CBound 0)) (value 97))))
        budget = refutationBudget {obviousRefutationWorkLimit = 600000}
    sources <- traverse checkedClosed [transitivity, classification]
    let imports = zipWith (obviousImport . importIx) [0..] sources
    forM_ [([], value 100), ([TySet], CBound 0)] \(ambient, a) -> do
        hypotheses <- traverse (checkedScoped ambient)
            ([seed (value i) | i <- [0..5]]
                <> [member (value i) (value (i + 1)) | i <- [0..4]]
                <> [COr (member a (value 0)) (CEq TySet a (value 0))])
        target <- checkedScoped ambient (member a (value 5))
        let (statistics, result) = obviousProofDetailed budget AnyObviousProof
                foundation emptyGlobalTyping hypotheses imports [] target
        proof <- expectRight result
        assertCandidateReplays foundation emptyGlobalTyping hypotheses imports target proof
        assertEqual "both selected classification and transitivity are replayed"
            (Set.fromList [importIx 0, importIx 1]) (obviousUsedImports proof)
        assertEqual "both case branches close within the fixed allowance"
            ObviousTierCandidateBuilt (obviousRefutationTierOutcome statistics)
        assertBool "the proof actually splits the disjunction"
            (obviousBranchNodesCreated statistics >= 3)

selectsRuleResultsAfterEliminations :: Assertion
selectsRuleResultsAfterEliminations = do
    foundation <- expectRight Foundation.checkedFoundation
    forM_ [([], COpaqueInteger 71), ([TySet], CBound 0)] \(ambient, a) -> do
        let b = COpaqueInteger 72
            p term = member term (COpaqueInteger 73)
            q term = member term (COpaqueInteger 74)
            h term = member term (COpaqueInteger 75)
            g term = CApp (CIntrinsic PowerSet) term
            x = CBound 0
            simple = CForall TySet (CImp (h x) (CAnd (p x) (q (g x))))
            interleaved = CForall TySet (CImp (h x)
                (CAnd CTruth (CForall TySet
                    (CImp (CAnd (h (CBound 1)) (q x))
                        (CAnd (q (g (CBound 1))) (p (CBound 1)))))))
        target <- checkedScoped ambient (p a)
        forM_ [simple, interleaved] \sourceTerm -> do
            source <- checkedClosed sourceTerm
            facts <- traverse (checkedScoped ambient) [h a, q b]
            let imports = [obviousImport (importIx 0) source]
                run budget selectedFacts selectedImports = obviousProofDetailed budget
                    AnyObviousProof foundation emptyGlobalTyping selectedFacts selectedImports [] target
                (statistics, result) = run refutationBudget facts imports
            proof <- expectRight result
            assertCandidateReplays foundation emptyGlobalTyping facts imports target proof
            assertEqual "the selected source is replayed from its exact import"
                (Set.singleton (importIx 0)) (obviousUsedImports proof)
            assertEqual "the refutation route succeeds without focused search"
                ObviousTierCandidateBuilt (obviousRefutationTierOutcome statistics)
            let focusedOnly = defaultObviousBudget {obviousRefutationWorkLimit = 0}
                (focusedStatistics, focusedResult) = run focusedOnly facts imports
            focusedProof <- expectRight focusedResult
            assertCandidateReplays foundation emptyGlobalTyping facts imports target focusedProof
            assertEqual "selected-result application also succeeds in focused search alone"
                ObviousTierCandidateBuilt (obviousFocusedTierOutcome focusedStatistics)
            let spent = obviousFocusedWorkConsumed focusedStatistics
                bounded allowance = run focusedOnly {obviousFocusedWorkLimit = allowance} facts imports
            _exact <- expectRight (snd (bounded spent))
            assertFailureKind "one-short focused selection cannot finish replay"
                (ObviousResourceExhausted ObviousFocusedWorkLimit) (snd (bounded (spent - 1)))
            forM_ [run budget missingFacts missingImports
                  | budget <- [refutationBudget, focusedOnly]
                  , (missingFacts, missingImports) <- [([], imports), (facts, [])]] \(_, missing) -> case missing of
                Right _ -> assertFailure "projection invented its premise or source"
                Left failure | obviousFailureClass failure == ObviousIntegrityClass ->
                    assertFailure (show failure)
                Left _ -> pure ()

composesExactRulePresentations :: Assertion
composesExactRulePresentations = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 0
        x = CBound 0
        predicate name argument = CApp (CApp (CIntrinsic Member) argument) (COpaqueInteger name)
        p = predicate 1
        q = predicate 2
        sideCondition = predicate 3
        conclusion = predicate 4
        curried premise = CImp (premise x) (CImp (sideCondition x) (conclusion x))
        conjoined premise = CImp (CAnd (premise x) (sideCondition x)) (conclusion x)
        reassociated premise = CImp (CAnd CTruth (CAnd (premise x) (sideCondition x))) (conclusion x)
        presentations =
            [ [CForall TySet (curried p), CForall TySet (curried q)]
            , [CForall TySet (conjoined p), CForall TySet (conjoined q)]
            , [CForall TySet (reassociated p), CForall TySet (reassociated q)]
            , [CForall TySet (CAnd (conjoined p) (conjoined q))]
            ]
        premises = [COr (p a) (q a), sideCondition a]
    target <- checkedScoped [] (conclusion a)
    forM_ presentations \rules -> do
        forM_ [rules <> premises, reverse (rules <> premises)] \terms -> do
            hypotheses <- traverse (checkedScoped []) terms
            let (statistics, result) = obviousProofDetailed defaultObviousBudget AnyObviousProof
                    foundation emptyGlobalTyping hypotheses [] [] target
            proof <- expectRight result
            assertCandidateReplays foundation emptyGlobalTyping hypotheses [] target proof
            assertBool "the complete default driver uses a checked ground rule instance"
                (obviousRuleInstancesAdmitted statistics > 0)
        hypotheses <- traverse (checkedScoped []) (rules <> [COr (p a) (q a)])
        case obviousProofDetailed defaultObviousBudget AnyObviousProof
                foundation emptyGlobalTyping hypotheses [] [] target of
            (_, Left _) -> pure ()
            (_, Right _) -> assertFailure "case reasoning invented the missing side condition"

replaysRefutationEqualityClosure :: Assertion
replaysRefutationEqualityClosure = do
    let a = COpaqueInteger 0
        b = COpaqueInteger 1
        c = COpaqueInteger 2
        d = COpaqueInteger 3
        familyUnion term = CApp (CIntrinsic FamilyUnion) term
    assertRefutationCase
        "transitive equality"
        [CEq TySet a b, CEq TySet b c]
        (CEq TySet a c)
    assertRefutationCase
        "application congruence"
        [CEq TySet a b]
        (CEq TySet (familyUnion a) (familyUnion b))
    assertRefutationCase
        "curried application congruence"
        [CEq TySet a b, CEq TySet c d]
        (CEq TySet (pair a c) (pair b d))
    assertRefutationCase
        "proposition equality transport"
        [member a c, CEq TySet a b]
        (member b c)
    assertRefutationCase
        "cycles and duplicate edges"
        [ CEq TySet a b
        , CEq TySet b a
        , CEq TySet a b
        , CEq TySet b c
        ]
        (CEq TySet a c)

preservesRefutationEqualityBoundaries :: Assertion
preservesRefutationEqualityBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 10
        b = COpaqueInteger 11
        c = COpaqueInteger 12
        d = COpaqueInteger 13
        run hypotheses imports target =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                hypotheses imports [] target
    firstLeft <- checkedClosed (CEq TySet a b)
    firstRight <- checkedClosed (CEq TySet b d)
    secondLeft <- checkedClosed (CEq TySet a c)
    secondRight <- checkedClosed (CEq TySet c d)
    target <- checkedScoped [] (CEq TySet a d)
    let imports =
            [ obviousImport (importIx 0) firstLeft
            , obviousImport (importIx 1) firstRight
            , obviousImport (importIx 2) secondLeft
            , obviousImport (importIx 3) secondRight
            ]
        (tieStatistics, tieResult) = run [] imports target
    tieProof <- expectRight tieResult
    assertCandidateReplays foundation emptyGlobalTyping [] imports target tieProof
    assertEqual "equality BFS retains the first source-ordered path"
        (Set.fromList [importIx 0, importIx 1])
        (obviousUsedImports tieProof)
    assertBool "transitive closure records equality events"
        (obviousEqualityEventsProcessed tieStatistics >= 2)

    equality <- checkedScoped [] (CEq TySet a b)
    unrelated <- checkedScoped [] otherMembership
    disjunction <- checkedScoped [] (COr (CEq TySet a b) otherMembership)
    let (siblingStatistics, siblingResult) =
            run [disjunction] [] equality
    assertFailureKind
        "an equality established in one child does not leak to its sibling"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        siblingResult
    assertEqual "the equality sibling remains open"
        ObviousTierNoProof
        (obviousRefutationTierOutcome siblingStatistics)
    assertEqual "the disequality target simplifies the disjunction in the root"
        1
        (obviousBranchNodesCreated siblingStatistics)

    -- Here the first child closes by transitivity, while the second must not
    -- inherit its middle equality. Neither root alternative is a unit.
    genuineCases <- checkedScoped [] (COr
        (CAnd (CEq TySet a b) (CEq TySet b c))
        (CAnd (CEq TySet a b) otherMembership))
    genuineTarget <- checkedScoped [] (CEq TySet a c)
    let (genuineStatistics, genuineResult) = run [genuineCases] [] genuineTarget
    assertFailureKind "the second case cannot use the first case's transitive path"
        (ObviousResourceExhausted ObviousFocusedWorkLimit) genuineResult
    assertEqual "the independent equality case remains open" ObviousTierNoProof
        (obviousRefutationTierOutcome genuineStatistics)
    assertBool "both actual child scopes were visited"
        (obviousBranchNodesCreated genuineStatistics >= 3)

    left <- checkedScoped [] (CEq TySet a b)
    right <- checkedScoped [] (CEq TySet b c)
    transitiveTarget <- checkedScoped [] (CEq TySet a c)
    let (ampleStatistics, ampleResult) =
            run [left, right] [] transitiveTarget
        usedWork = obviousRefutationWorkConsumed ampleStatistics
        exactBudget = refutationBudget
            { obviousRefutationWorkLimit = usedWork }
        shortBudget = refutationBudget
            { obviousRefutationWorkLimit = usedWork - 1 }
        exactRun budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                [left, right] [] [] transitiveTarget
    ampleProof <- expectRight ampleResult
    assertCandidateReplays
        foundation emptyGlobalTyping [left, right] [] transitiveTarget ampleProof
    _exactProof <- expectRight (snd (exactRun exactBudget))
    let (shortStatistics, shortResult) = exactRun shortBudget
    case shortResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure
                "equality reconstruction crossed its refutation-work boundary"
    assertEqual "one-short equality reconstruction exhausts work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

    -- Keep these values demanded so this reduction also checks that unrelated
    -- proposition terms do not become equality authority.
    assertBool "unrelated atom is distinct from the equality target"
        (unrelated /= equality)

prioritizesCompletedEqualityClosure :: Assertion
prioritizesCompletedEqualityClosure = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 14
        b = COpaqueInteger 15
        c = COpaqueInteger 16
        predicate term = member term empty
        activeRule =
            CForall TySet
                (CImp
                    (predicate (CBound 0))
                    (member (CBound 0) (pair empty empty)))
    rule <- checkedClosed activeRule
    left <- checkedClosed (CEq TySet a b)
    right <- checkedClosed (CEq TySet b c)
    target <- checkedScoped [] (CEq TySet a c)
    let imports =
            [ obviousImport (importIx 0) rule
            , obviousImport (importIx 1) left
            , obviousImport (importIx 2) right
            ]
        run budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                [] imports [] target
        (ampleStatistics, ampleResult) = run refutationBudget
        -- Includes adjacency work and the two positive/one negative hint events.
        -- Ordered compilation removes two redundant phase-entry charges.
        closureWork = 844
    proof <- expectRight ampleResult
    assertCandidateReplays foundation emptyGlobalTyping [] imports target proof
    assertEqual "the unused active rule is not proof authority"
        (Set.fromList [importIx 1, importIx 2])
        (obviousUsedImports proof)
    assertEqual
        "equality closure stops at the completed reason boundary"
        closureWork
        (obviousRefutationWorkConsumed ampleStatistics)
    _exact <- expectRight
        (snd
            (run
                refutationBudget
                    { obviousRefutationWorkLimit = closureWork
                    }))
    let (shortStatistics, shortResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = closureWork - 1
                    }
    case shortResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure
                "one-short equality closure unexpectedly produced a proof"
    assertEqual "one-short closure reconstruction exhausts work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

data OracleGroundTerm
    = OracleConstant !Int
    | OracleUnion !OracleGroundTerm
    | OraclePair !OracleGroundTerm !OracleGroundTerm
    deriving stock (Show, Eq, Ord)

oracleGroundTerm :: OracleGroundTerm -> CanonicalTerm Void
oracleGroundTerm = \case
    OracleConstant value -> COpaqueInteger (fromIntegral value)
    OracleUnion term ->
        CApp (CIntrinsic FamilyUnion) (oracleGroundTerm term)
    OraclePair left right ->
        pair (oracleGroundTerm left) (oracleGroundTerm right)

oracleGroundSubterms :: OracleGroundTerm -> Set.Set OracleGroundTerm
oracleGroundSubterms term =
    Set.insert term
        (case term of
            OracleConstant{} -> Set.empty
            OracleUnion argument -> oracleGroundSubterms argument
            OraclePair left right ->
                oracleGroundSubterms left
                    `Set.union` oracleGroundSubterms right)

oracleGroundPair
    :: OracleGroundTerm
    -> OracleGroundTerm
    -> (OracleGroundTerm, OracleGroundTerm)
oracleGroundPair left right
    | left <= right = (left, right)
    | otherwise = (right, left)

oracleCongruenceClosure
    :: Set.Set OracleGroundTerm
    -> [(OracleGroundTerm, OracleGroundTerm)]
    -> Set.Set (OracleGroundTerm, OracleGroundTerm)
oracleCongruenceClosure universe equalities = fixedPoint initial
  where
    terms = Set.toAscList universe
    initial =
        Set.fromList
            ([oracleGroundPair term term | term <- terms]
                <> [oracleGroundPair left right | (left, right) <- equalities])

    fixedPoint relation =
        let updated = closeOnce relation
        in if updated == relation
            then relation
            else fixedPoint updated

    closeOnce relation =
        relation
            `Set.union` Set.fromList
                [ oracleGroundPair left right
                | left <- terms
                , right <- terms
                , relatedByTransitivity relation left right
                    || congruent relation left right
                ]

    related relation left right =
        oracleGroundPair left right `Set.member` relation

    relatedByTransitivity relation left right =
        any
            (\middle ->
                related relation left middle
                    && related relation middle right)
            terms

    congruent relation left right =
        case (left, right) of
            (OracleUnion leftArgument, OracleUnion rightArgument) ->
                related relation leftArgument rightArgument
            (OraclePair leftFirst leftSecond,
                    OraclePair rightFirst rightSecond) ->
                related relation leftFirst rightFirst
                    && related relation leftSecond rightSecond
            _ -> False

agreesWithEqualityOracle :: Assertion
agreesWithEqualityOracle = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = OracleConstant 80
        b = OracleConstant 81
        c = OracleConstant 82
        unionA = OracleUnion a
        unionB = OracleUnion b
        unionC = OracleUnion c
        pairAC = OraclePair a c
        pairBC = OraclePair b c
        pairCC = OraclePair c c
        equalities = [(a, b)]
        queries =
            [ (a, a)
            , (a, b)
            , (a, c)
            , (unionA, unionB)
            , (unionA, unionC)
            , (pairAC, pairBC)
            , (pairAC, pairCC)
            ]
        universe =
            Set.unions
                [ oracleGroundSubterms term
                | (left, right) <- equalities <> queries
                , term <- [left, right]
                ]
        closure = oracleCongruenceClosure universe equalities
    hypotheses <-
        traverse
            (\(left, right) ->
                checkedScoped []
                    (CEq TySet
                        (oracleGroundTerm left)
                        (oracleGroundTerm right)))
            equalities
    traverse_
        (checkQuery foundation hypotheses closure)
        (zip [0 :: Int ..] queries)

    equality <-
        checkedScoped []
            (CEq TySet (oracleGroundTerm a) (oracleGroundTerm b))
    disequality <-
        checkedScoped []
            (CNot
                (CEq TySet
                    (oracleGroundTerm a)
                    (oracleGroundTerm b)))
    unrelated <- checkedScoped [] membership
    let (clashStatistics, clashResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [equality, disequality] [] [] unrelated
    clashProof <- expectRight clashResult
    assertCandidateReplays
        foundation emptyGlobalTyping [equality, disequality] [] unrelated clashProof
    assertEqual "the equality oracle's inconsistent theory closes"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome clashStatistics)
  where
    checkQuery foundation hypotheses closure
            (queryIndex, (left, right)) = do
        target <-
            checkedScoped []
                (CEq TySet
                    (oracleGroundTerm left)
                    (oracleGroundTerm right))
        let expected =
                oracleGroundPair left right `Set.member` closure
            (statistics, result) =
                obviousProofDetailed
                    refutationBudget AnyObviousProof foundation emptyGlobalTyping
                    hypotheses [] [] target
            label = "equality oracle query " <> show queryIndex
        if expected
            then do
                proof <- expectRight result
                assertCandidateReplays
                    foundation emptyGlobalTyping hypotheses [] target proof
                assertEqual (label <> " builds a candidate")
                    ObviousTierCandidateBuilt
                    (obviousRefutationTierOutcome statistics)
            else do
                case result of
                    Left _failure -> pure ()
                    Right _proof ->
                        assertFailure (label <> " proved a non-consequence")
                assertEqual (label <> " saturates")
                    ObviousTierNoProof
                    (obviousRefutationTierOutcome statistics)

replaysBoundedRuleChains :: Assertion
replaysBoundedRuleChains = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 20
        b = COpaqueInteger 21
        one = pair empty empty
        two = pair one empty
        three = pair two empty
        predicate set term = member term set
        u = predicate empty
        v = predicate one
        w = predicate two
        z = predicate three
        firstRule =
            CForall TySet
                (CImp
                    (u (CBound 0))
                    (CImp
                        (v (CBound 0))
                        (w (CBound 0))))
        secondRule =
            CForall TySet
                (CImp (w (CBound 0)) (z (CBound 0)))
        generatedRule =
            CForall TySet
                (CImp
                    (u (CBound 0))
                    (CForall TySet
                        (CImp
                            (v (CBound 0))
                            (w (CBound 1)))))
        run terms targetTerm = do
            hypotheses <- traverse (checkedScoped []) terms
            target <- checkedScoped [] targetTerm
            let (statistics, result) =
                    obviousProofDetailed
                        refutationBudget AnyObviousProof foundation emptyGlobalTyping
                        hypotheses [] [] target
            proof <- expectRight result
            assertCandidateReplays
                foundation emptyGlobalTyping hypotheses [] target proof
            pure statistics
    first <- run
        [u a, v a, firstRule, secondRule]
        (z a)
    second <- run
        [firstRule, secondRule, u a, v a]
        (z a)
    assertEqual "fact-before-rule and rule-before-fact reach the same tier"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome first)
    assertEqual "rule activation order reaches the same fixed point"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome second)
    assertBool "the two-step rule chain retains both instances"
        (obviousRuleInstancesAdmitted first >= 2)

    generated <- run
        [u a, v b, generatedRule]
        (w a)
    assertBool "a generated universal conclusion activates as a second rule"
        (obviousRuleInstancesAdmitted generated >= 2)
    _quantified <- run [u a, generatedRule]
        (CForall TySet (CImp (v (CBound 0)) (w a)))
    pure ()

replaysExposedRuleRoots :: Assertion
replaysExposedRuleRoots = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 22
        b = COpaqueInteger 23
        one = pair empty empty
        p term = member term empty
        q term = member term one
        betaProposition proposition =
            CApp (CLam TyProp (CBound 0)) proposition
        ruleTerm =
            CForall TySet
                (betaProposition
                    (CImp
                        (betaProposition
                            (CEq TySet (CBound 0) a))
                        (betaProposition
                            (CImp
                                (betaProposition (p (CBound 0)))
                                (q (CBound 0))))))
    rule <- checkedClosed ruleTerm
    equality <- checkedClosed (CEq TySet b a)
    fact <- checkedClosed (p b)
    target <- checkedScoped [] (q b)
    let imports =
            [ obviousImport (importIx 0) rule
            , obviousImport (importIx 1) equality
            , obviousImport (importIx 2) fact
            ]
        run budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                [] imports [] target
        exactBudget =
            refutationBudget
        (statistics, result) = run exactBudget
    proof <- expectRuleProof "four-root rule" statistics result
    assertCandidateReplays foundation emptyGlobalTyping [] imports target proof
    assertEqual "all and only the rule-chain imports are authority"
        (Set.fromList [importIx 0, importIx 1, importIx 2])
        (obviousUsedImports proof)
    assertConversionPoolBoundary "exposed rule chain" run exactBudget statistics proof
    assertEqual "the beta-aware rule chain is reconstructed in refutation"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome statistics)
    let scopedRuleTerm =
            CForall TySet
                (CForall TySet
                    (CImp
                        (betaProposition
                            (member (CBound 2) (CBound 1)))
                        (CImp
                            (betaProposition
                                (CEq TySet (CBound 1) (CBound 0)))
                            (q (CBound 1)))))
    scopedRule <- checkedScoped [TySet] scopedRuleTerm
    scopedFact <- checkedScoped [TySet] (member (CBound 0) a)
    scopedEquality <- checkedScoped [TySet] (CEq TySet a b)
    scopedTarget <- checkedScoped [TySet] (q a)
    let scopedHypotheses = [scopedRule, scopedFact, scopedEquality]
        (scopedStatistics, scopedResult) =
            obviousProofDetailed
                refutationBudget
                AnyObviousProof foundation emptyGlobalTyping
                scopedHypotheses [] [] scopedTarget
    scopedProof <-
        expectRuleProof "scoped residualized rule"
            scopedStatistics scopedResult
    assertCandidateReplays
        foundation emptyGlobalTyping scopedHypotheses [] scopedTarget scopedProof
    assertConversionPoolBoundary "scoped rule with repeated slots"
        (\budget -> obviousProofDetailed budget AnyObviousProof foundation emptyGlobalTyping
            scopedHypotheses [] [] scopedTarget)
        refutationBudget scopedStatistics scopedProof

    zeroRule <- checkedClosed
        (CForall TySet (betaProposition (p (CBound 0))))
    zeroTarget <- checkedScoped [] (p b)
    let zeroImports = [obviousImport (importIx 6) zeroRule]
        zeroBudget =
            refutationBudget
        (zeroStatistics, zeroResult) =
            obviousProofDetailed
                zeroBudget AnyObviousProof foundation emptyGlobalTyping
                [] zeroImports [] zeroTarget
    zeroProof <-
        expectRuleProof "zero-premise exposed demand"
            zeroStatistics zeroResult
    assertCandidateReplays
        foundation emptyGlobalTyping [] zeroImports zeroTarget zeroProof
    assertConversionPoolBoundary "zero-premise universal demand"
        (\budget -> obviousProofDetailed budget AnyObviousProof foundation emptyGlobalTyping
            [] zeroImports [] zeroTarget)
        zeroBudget zeroStatistics zeroProof
  where
    expectRuleProof label statistics = \case
        Right proof -> pure proof
        Left failure ->
            assertFailure
                ( label <> " failed with " <> show failure
                    <> "; refutation tier: "
                    <> show (obviousRefutationTierOutcome statistics)
                )
                >> fail "missing rule proof"

replaysSignedHeadConversionUnderHypotheses :: Assertion
replaysSignedHeadConversionUnderHypotheses = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TySet, TyProp]
        proposition = member (CBound 0) empty
        betaProposition = CApp (CLam TyProp (CBound 0)) proposition
        cases =
            [ ("true reason", betaProposition, CNot proposition)
            , ("false reason", proposition, CNot betaProposition)
            ]
    forM_ cases $ \(label, positive, negative) -> do
        hypotheses <- traverse (checkedScoped context)
            [CBound 1, positive, negative]
        target <- checkedScoped context otherMembership
        let (statistics, result) =
                obviousProofDetailed
                    refutationBudget AnyObviousProof
                    foundation emptyGlobalTyping hypotheses [] [] target
        proof <- expectRight result
        assertEqual (label <> " is reconstructed by signed refutation")
            ObviousTierCandidateBuilt
            (obviousRefutationTierOutcome statistics)
        assertEqual (label <> " preserves the requested statement and context")
            target
            (KernelProof.builtProofStatement (obviousBuiltProof proof))
        replayed <- expectRight
            (replayScopedKernelDerivation
                foundation defaultKernelReplayLimits emptyGlobalTyping
                Vector.empty (Vector.fromList hypotheses) target
                (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual (label <> " uses exactly the contradictory hypotheses")
            (Set.fromList [hypothesisIx 1, hypothesisIx 2])
            (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual (label <> " needs no imported authority")
            Set.empty (replayedScopedKernelImportUses replayed)

freezesPreparedLogicalChildren :: Assertion
freezesPreparedLogicalChildren = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 70
        function term = CApp (CGlobal functionObject) term
        p term = CApp (CGlobal predicateObject) term
        r term = CApp (CGlobal factPredicateObject) term
        q = otherMembership
        goal = member a (CGlobal namedSetObject)
        exposedChild =
            CApp
                (CLam TySet (p (function (CBound 0))))
                a
        disjunction = COr exposedChild q
        rule =
            CForall TySet
                (CImp (p (CBound 0)) goal)
    hypotheses <- traverse (checkedGlobalScoped [])
        [disjunction, CNot q]
    importedRule <- checkedGlobalClosed rule
    target <- checkedGlobalScoped [] goal
    let imports = [obviousImport (importIx 0) importedRule]
        budget =
            refutationBudget
        (statistics, result) =
            obviousProofDetailed
                budget AnyObviousProof foundation globalType
                hypotheses imports [] target
    proof <- expectRight result
    assertCandidateReplays
        foundation globalType hypotheses imports target proof
    assertConversionPoolBoundary "recursive child preparation"
        (\selectedBudget -> obviousProofDetailed selectedBudget AnyObviousProof
            foundation globalType hypotheses imports [] target)
        budget statistics proof
    let (zeroPoolStatistics, zeroPoolResult) =
            obviousProofDetailed
                budget {obviousConversionPool = Conversion.conversionPool 0}
                AnyObviousProof foundation globalType
                hypotheses imports [] target
    case zeroPoolResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "zero conversion pool unexpectedly completed the child view"
    assertEqual "recursive preparation reports the empty conversion pool"
        (ObviousTierResourceExhausted ObviousConversionPoolLimit)
        (obviousRefutationTierOutcome zeroPoolStatistics)
    assertEqual "failed recursive preparation publishes no search objects"
        (0, 0, 0)
        ( obviousTermsAdmitted zeroPoolStatistics
        , obviousSignedFormulasAdmitted zeroPoolStatistics
        , obviousBranchNodesCreated zeroPoolStatistics
        )

    let binary left right =
            CApp (CApp (CGlobal binaryPredicateObject) left) right
        ambientRule =
            CForall TySet
                (CImp
                    (CApp
                        (CLam TyProp (CBound 0))
                        (binary (function a) (CBound 0)))
                    (member (CBound 0) (CGlobal namedSetObject)))
        producerRule =
            CForall TySet
                (CImp
                    (p (CBound 0))
                    (binary (function (CBound 0)) (CBound 0)))
    ambientFact <- checkedGlobalScoped [] (p a)
    ambientRules <-
        traverse checkedGlobalClosed [producerRule, ambientRule]
    let ambientImports =
            zipWith
                (\position checked ->
                    obviousImport (importIx position) checked)
                [3, 4]
                ambientRules
        ambientHypotheses = [ambientFact]
        (ambientStatistics, ambientResult) =
            obviousProofDetailed
                budget AnyObviousProof foundation globalType
                ambientHypotheses ambientImports [] target
    ambientProof <- expectRight ambientResult
    assertCandidateReplays
        foundation globalType ambientHypotheses ambientImports target
        ambientProof
    assertConversionPoolBoundary "ambient child under a rule binder"
        (\selectedBudget -> obviousProofDetailed selectedBudget AnyObviousProof
            foundation globalType ambientHypotheses ambientImports [] target)
        budget ambientStatistics ambientProof
    assertBool
        "the open f(x) producer and ambient-ground consumer both instantiate"
        (obviousRuleInstancesAdmitted ambientStatistics >= 2)

    let discardedChild =
            CApp
                (CLam TySet CTruth)
                (function a)
        discardedCarrier = CAnd discardedChild CTruth
        firstRule =
            CForall TySet
                (CImp
                    (p (CBound 0))
                    (r (function (CBound 0))))
        secondRule =
            CForall TySet
                (CImp (r (CBound 0)) goal)
    discardedHypotheses <- traverse (checkedGlobalScoped [])
        [discardedCarrier, p a]
    discardedRules <- traverse checkedGlobalClosed [firstRule, secondRule]
    let discardedImports =
            zipWith
                (\position checked ->
                    obviousImport (importIx position) checked)
                [1, 2]
                discardedRules
        (discardedStatistics, discardedResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation globalType
                discardedHypotheses discardedImports [] target
    assertFailureKind
        "a discarded beta argument is not frozen as a usable term"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        discardedResult
    assertEqual
        "the generated f(a) conclusion remains outside the semantic universe"
        ObviousTierUnsupported
        (obviousRefutationTierOutcome discardedStatistics)
    assertEqual
        "the rejected generated conclusion publishes no rule instance"
        0
        (obviousRuleInstancesAdmitted discardedStatistics)

replaysDemandDrivenRules :: Assertion
replaysDemandDrivenRules = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 30
        one = pair empty empty
        p term = member term empty
        q = member a one
        consumer = CImp (p a) q
        universal = CForall TySet (p (CBound 0))
        run terms = do
            hypotheses <- traverse (checkedScoped []) terms
            target <- checkedScoped [] q
            let (statistics, result) =
                    obviousProofDetailed
                        refutationBudget AnyObviousProof foundation emptyGlobalTyping
                        hypotheses [] [] target
            proof <- expectRight result
            assertCandidateReplays
                foundation emptyGlobalTyping hypotheses [] target proof
            pure statistics
    demandBeforeRule <- run [consumer, universal]
    ruleBeforeDemand <- run [universal, consumer]
    assertBool "the ground premise demand triggers the universal rule"
        (obviousRuleInstancesAdmitted demandBeforeRule >= 2)
    assertEqual "demand and zero-rule admission orders agree"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome ruleBeforeDemand)

replaysEqualityAwareRules :: Assertion
replaysEqualityAwareRules = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 40
        b = COpaqueInteger 41
        c = COpaqueInteger 42
        one = pair empty empty
        two = pair one empty
        p term = member term empty
        u term = member term one
        v term = member term two
        goal = member a (pair two empty)
        run terms targetTerm = do
            hypotheses <- traverse (checkedScoped []) terms
            target <- checkedScoped [] targetTerm
            let (statistics, result) =
                    obviousProofDetailed
                        refutationBudget AnyObviousProof foundation emptyGlobalTyping
                        hypotheses [] [] target
            proof <- expectRight result
            assertCandidateReplays
                foundation emptyGlobalTyping hypotheses [] target proof
            pure statistics
    _closed <- run
        [ CEq TySet a c
        , CEq TySet c b
        , CImp (CEq TySet a b) goal
        ]
        goal
    _reversed <- run
        [ CEq TySet a b
        , CForall TySet
            (CImp
                (CEq TySet (CBound 0) a)
                (p (CBound 0)))
        ]
        (p b)
    orientation <- run
        [ CEq TySet a b
        , p b
        , CForall TySet
            (CForall TySet
                (CImp
                    (CEq TySet (CBound 1) (CBound 0))
                    (CImp
                        (p (CBound 1))
                        (u (CBound 0)))))
        ]
        (u a)
    assertBool
        "a failed written orientation backtracks to the reversed equality"
        (obviousRuleInstancesAdmitted orientation >= 1)
    component <- run
        [ CEq TySet a b
        , v a
        , u b
        , CForall TySet
            (CImp
                (v (CBound 0))
                (CImp (u (CBound 0)) goal))
        ]
        goal
    assertBool
        "a closed atomic premise is rebuilt componentwise without P(a) admission"
        (obviousRuleInstancesAdmitted component >= 1)

streamsWrittenEqualityAlternatives :: Assertion
streamsWrittenEqualityAlternatives = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 45
        b = COpaqueInteger 46
        ruleTerm =
            CForall TySet
                (CForall TySet
                    (CEq TySet (CBound 1) (CBound 0)))
    rule <- checkedClosed ruleTerm
    target <- checkedScoped [] (CEq TySet a b)
    let imports = [obviousImport (importIx 0) rule]
        run budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                [] imports [] target
        (statistics, result) = run refutationBudget
        usedWork = obviousRefutationWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping [] imports target proof
    -- This boundary ends with the written candidate's proof-producing
    -- admission, including both signed hint events; constructing the reverse
    -- orientation would move it.
    assertEqual "written-orientation success includes owned publication"
        472
        usedWork
    assertEqual "the written zero-premise orientation admits one instance"
        1
        (obviousRuleInstancesAdmitted statistics)
    _exact <- expectRight
        (snd
            (run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork
                    }))
    let (shortStatistics, shortResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork - 1
                    }
    case shortResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure
                "one-short written-orientation proof unexpectedly succeeded"
    assertEqual "one-short written orientation exhausts before publication"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

    undeterminedRule <- checkedClosed
        (CForall TySet
            (CForall TySet
                (CForall TySet
                    (CEq TySet (CBound 2) (CBound 1)))))
    let undeterminedImports =
            [obviousImport (importIx 1) undeterminedRule]
        (undeterminedStatistics, undeterminedResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [] undeterminedImports [] target
    assertFailureKind
        "an equality orientation with an unused binder produces no proof"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        undeterminedResult
    assertEqual "the refuter records the undetermined candidate as no-proof"
        ObviousTierNoProof
        (obviousRefutationTierOutcome undeterminedStatistics)
    assertEqual
        "undetermined written orientation stops before reverse construction"
        255 -- Includes retention of the negative target hint event.
        (obviousRefutationWorkConsumed undeterminedStatistics)

retriesRulesAfterEqualityMerges :: Assertion
retriesRulesAfterEqualityMerges = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 43
        b = COpaqueInteger 44
        one = pair empty empty
        two = pair one empty
        p term = member term empty
        q = member a one
        r = member b two
        consumer = CImp (p a) q
        equalityProducer = CImp r (CEq TySet a b)
        terms = [consumer, equalityProducer, p b, r]
    hypotheses <- traverse (checkedScoped []) terms
    target <- checkedScoped [] q
    let run budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                hypotheses [] [] target
        (statistics, result) = run refutationBudget
        usedWork = obviousRefutationWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target proof
    assertBool "the producer and retried consumer both instantiate"
        (obviousRuleInstancesAdmitted statistics >= 2)
    repeatedProof <- expectRight (snd (run refutationBudget))
    assertEqual "merge retry retains a deterministic proof authority"
        (obviousUsedImports proof)
        (obviousUsedImports repeatedProof)
    _exact <-
        expectRight
            (snd
                (run
                    refutationBudget
                        { obviousRefutationWorkLimit = usedWork }))
    let (shortStatistics, shortResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork - 1 }
    case shortResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "one-short equality retry unexpectedly succeeded"
    assertEqual "one-short equality retry exhausts refutation work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

activatesDerivedPropositionsUnderEquality :: Assertion
activatesDerivedPropositionsUnderEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 45
        b = COpaqueInteger 46
        one = pair empty empty
        u term = member term empty
        p term = member term one
        rule =
            CForall TySet
                (CImp (u (CBound 0)) (p (CBound 0)))
        terms = [CEq TySet a b, u a, rule]
    hypotheses <- traverse (checkedScoped []) terms
    target <- checkedScoped [] (p b)
    let (statistics, result) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                hypotheses [] [] target
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target proof
    assertEqual "the cross-stage seam needs one rule instance"
        1
        (obviousRuleInstancesAdmitted statistics)
    assertBool "the derived proposition participates in equality closure"
        (obviousEqualityEventsProcessed statistics >= 2)

reconstructsLongRuleWitnessSpines :: Assertion
reconstructsLongRuleWitnessSpines = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 47
        one = pair empty empty
        p term = member term empty
        q term = member term one
        premiseCount = 24
        rule =
            CForall TySet
                (foldr CImp (q (CBound 0))
                    (replicate premiseCount (p (CBound 0))))
    fact <- checkedScoped [] (p a)
    source <- checkedScoped [] rule
    target <- checkedScoped [] (q a)
    let hypotheses = [fact, source]
        run budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                hypotheses [] [] target
        (statistics, result) = run refutationBudget
        usedWork = obviousRefutationWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target proof
    assertEqual "one completed long-chain instance is retained"
        1
        (obviousRuleInstancesAdmitted statistics)
    _exact <-
        expectRight
            (snd
                (run
                    refutationBudget
                        { obviousRefutationWorkLimit = usedWork }))
    let (shortStatistics, shortResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork - 1 }
    case shortResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "one-short long witness reconstruction succeeded"
    assertEqual "long witness reconstruction stops at its work boundary"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

preservesRuleSemanticBoundaries :: Assertion
preservesRuleSemanticBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 50
        b = COpaqueInteger 51
        p term = member term empty
        q term = member empty term
        scopedRule =
            CForall TySet
                (CImp
                    (member (CBound 1) (CBound 0))
                    (member (CBound 0) (CBound 1)))
    scopedFact <- checkedScoped [TySet] (member (CBound 0) a)
    scopedSource <- checkedScoped [TySet] scopedRule
    scopedTarget <- checkedScoped [TySet] (member a (CBound 0))
    let (scopedStatistics, scopedResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [scopedFact, scopedSource] [] [] scopedTarget
    scopedProof <- expectRight scopedResult
    assertCandidateReplays foundation emptyGlobalTyping
        [scopedFact, scopedSource] [] scopedTarget scopedProof
    assertBool "ambient set parameters remain rigid"
        (obviousRuleInstancesAdmitted scopedStatistics >= 1)

    predicateFact <-
        checkedScoped [TyArrow TySet TyProp]
            (CApp (CBound 0) a)
    predicateRule <-
        checkedScoped [TyArrow TySet TyProp]
            (CForall TySet
                (CImp
                    (CApp (CBound 1) (CBound 0))
                    (p (CBound 0))))
    predicateTarget <-
        checkedScoped [TyArrow TySet TyProp] (p a)
    let (_predicateStatistics, predicateResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [predicateFact, predicateRule] [] [] predicateTarget
    predicateProof <- expectRight predicateResult
    assertCandidateReplays foundation emptyGlobalTyping
        [predicateFact, predicateRule] [] predicateTarget predicateProof

    unrelated <- checkedScoped [] (q b)
    compound <- checkedScoped [] (CImp (COr (p a) (q a)) (p b))
    let (grammarStatistics, grammarResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [compound] [] [] unrelated
    assertFailureKind
        "a compound premise remains inert rather than unsupported"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        grammarResult
    assertEqual "NotARule saturation is an ordinary no-proof result"
        ObviousTierNoProof
        (obviousRefutationTierOutcome grammarStatistics)
    assertEqual "an inert schema creates no instance"
        0
        (obviousRuleInstancesAdmitted grammarStatistics)

    undeterminedTarget <- checkedScoped [] (p a)
    undeterminedRule <-
        checkedScoped []
            (CForall TySet
                (CForall TySet (p (CBound 1))))
    let undeterminedResult =
            snd
                (obviousProofDetailed
                    defaultObviousBudget AnyObviousProof foundation emptyGlobalTyping
                    [undeterminedRule] [] [] undeterminedTarget)
    assertFailureKind
        "a selected zero-rule demand reports its first unused binder"
        (ObviousUndeterminedParameter 1)
        undeterminedResult

    disjunction <-
        checkedScoped [] (COr (p a) (q b))
    branchRule <-
        checkedScoped [] (CImp (p a) (p b))
    branchTarget <- checkedScoped [] (p b)
    let (branchStatistics, branchResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [disjunction, branchRule] [] [] branchTarget
    assertFailureKind
        "a rule conclusion derived in one child does not leak to its sibling"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        branchResult
    assertEqual "the sibling rule search remains open"
        ObviousTierNoProof
        (obviousRefutationTierOutcome branchStatistics)
    assertEqual
        "both disjunction siblings remain isolated without an extra implication branch"
        3
        (obviousBranchNodesCreated branchStatistics)

    existential <- checkedScoped []
        (CExists TySet (p (CBound 0)))
    propositionBinder <- checkedScoped []
        (CForall TyProp
            (CImp (CBound 0) (p a)))
    compoundConclusion <- checkedScoped []
        (CForall TySet
            (COr (p (CBound 0)) (q (CBound 0))))
    interiorBeta <- checkedScoped []
        (CForall TySet
            (CImp
                (p
                    (CApp
                        (CLam TySet (CBound 0))
                        (CBound 0)))
                (q (CBound 0))))
    betaFact <- checkedScoped [] (p a)
    let (inertStatistics, inertResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [ existential
                , propositionBinder
                , compoundConclusion
                , interiorBeta
                , betaFact
                ]
                [] [] unrelated
    assertFailureKind
        "true existentials and non-rule schemas remain inert"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        inertResult
    assertEqual "inert schemas admit no instances"
        0
        (obviousRuleInstancesAdmitted inertStatistics)

    falseUniversal <- checkedScoped []
        (CForall TySet (p (CBound 0)))
    falseExistential <- checkedScoped []
        (CExists TySet (p (CBound 0)))
    let assertAtomicTarget label atomicTarget = do
            let (statistics, result) =
                    obviousProofDetailed
                        refutationBudget AnyObviousProof foundation emptyGlobalTyping
                        [] [] [] atomicTarget
            assertFailureKind label
                (ObviousResourceExhausted ObviousFocusedWorkLimit)
                result
            assertEqual (label <> " is atomic in the refuter")
                ObviousTierNoProof
                (obviousRefutationTierOutcome statistics)
    assertAtomicTarget "a false universal remains atomic" falseUniversal
    assertAtomicTarget "a false existential remains atomic" falseExistential

    universalFact <- checkedScoped []
        (CForall TySet (p (CBound 0)))
    positiveAtom <- checkedScoped [] (p a)
    let (demandStatistics, demandResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                [positiveAtom, universalFact] [] [] unrelated
    assertFailureKind
        "a true atom creates no complementary demand"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        demandResult
    assertEqual "the unrelated zero rule remains demand-inert"
        0
        (obviousRuleInstancesAdmitted demandStatistics)

terminatesRecursiveRules :: Assertion
terminatesRecursiveRules = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 55
        one = pair empty empty
        two = pair one empty
        p term = member term empty
        q term = member term one
        r term = member term two
        selfRule =
            CForall TySet
                (CImp (p (CBound 0)) (p (CBound 0)))
        forwardRule =
            CForall TySet
                (CImp (p (CBound 0)) (q (CBound 0)))
        backwardRule =
            CForall TySet
                (CImp (q (CBound 0)) (p (CBound 0)))
        run terms = do
            hypotheses <- traverse (checkedScoped []) terms
            target <- checkedScoped [] (r a)
            let (statistics, result) =
                    obviousProofDetailed
                        refutationBudget AnyObviousProof foundation emptyGlobalTyping
                        hypotheses [] [] target
            assertFailureKind
                "recursive rules reach quiescence"
                (ObviousResourceExhausted ObviousFocusedWorkLimit)
                result
            assertEqual "recursive saturation has no proof"
                ObviousTierNoProof
                (obviousRefutationTierOutcome statistics)
            pure statistics
    self <- run [p a, selfRule]
    assertEqual "a self-rule retains one duplicate instance"
        1
        (obviousRuleInstancesAdmitted self)
    mutual <- run [p a, forwardRule, backwardRule]
    assertEqual "a mutual cycle retains each directed instance once"
        2
        (obviousRuleInstancesAdmitted mutual)

chargesLateMatcherSubstitutionIdentity :: Assertion
chargesLateMatcherSubstitutionIdentity = do
    foundation <- expectRight Foundation.checkedFoundation
    let binderCount = 12 :: Int
        positions = [0 .. binderCount - 1]
        values =
            [ COpaqueInteger (fromIntegral (200 + position))
            | position <- positions
            ]
        carriers =
            [ nestedPair (fromIntegral position) empty
            | position <- positions
            ]
        alternative = COpaqueInteger 212
        boundAt position =
            CBound (fromIntegral (binderCount - position - 1))
        premises =
            [ member (boundAt position) carrier
            | (position, carrier) <- zip positions carriers
            ]
        conclusionCarrier = pair empty (pair empty empty)
        conclusion = member (CBound 0) conclusionCarrier
        rule =
            foldr
                (\_ body -> CForall TySet body)
                (foldr CImp conclusion premises)
                positions
        fixedFacts =
            [ member value carrier
            | (value, carrier) <-
                take (binderCount - 1) (zip values carriers)
            ]
        lastValue = COpaqueInteger 211
        lastCarrier = nestedPair 11 empty
        finalFacts =
            [ member lastValue lastCarrier
            , member alternative lastCarrier
            ]
        targetTerm =
            member (COpaqueInteger 999) (pair conclusionCarrier empty)
    hypotheses <-
        traverse (checkedScoped []) (fixedFacts <> finalFacts <> [rule])
    target <- checkedScoped [] targetTerm
    let run limit =
            obviousProofDetailed
                refutationBudget
                    { obviousRefutationWorkLimit = limit }
                AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] target
        (ampleStatistics, ampleResult) =
            obviousProofDetailed
                refutationBudget AnyObviousProof foundation emptyGlobalTyping
                hypotheses [] [] target
        usedWork = obviousRefutationWorkConsumed ampleStatistics
        hasBothInstances limit =
            obviousRuleInstancesAdmitted (fst (run limit)) >= 2
        firstBoundary lower upper
            | lower >= upper = lower
            | hasBothInstances middle = firstBoundary lower middle
            | otherwise = firstBoundary (middle + 1) upper
          where
            middle = lower + (upper - lower) `div` 2
        boundary = firstBoundary 0 usedWork
        (boundaryStatistics, _boundaryResult) = run boundary
        (shortStatistics, _shortResult) = run (boundary - 1)
    assertFailureKind
        "the many-binder fixed point remains an intentional no-proof case"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        ampleResult
    assertEqual "late alternatives retain exactly two instances"
        2
        (obviousRuleInstancesAdmitted ampleStatistics)
    assertEqual "the second long substitution publishes at its boundary"
        2
        (obviousRuleInstancesAdmitted boundaryStatistics)
    assertBool
        "one-short long-substitution work publishes no second instance"
        (obviousRuleInstancesAdmitted shortStatistics < 2)
    assertEqual "one-short long-substitution work is exhausted"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

rejectsOutsideUniverseRuleTerms :: Assertion
rejectsOutsideUniverseRuleTerms = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 60
        b = COpaqueInteger 61
        c = COpaqueInteger 62
        unary headObject term = CApp (CGlobal headObject) term
        binary headObject left right =
            CApp (CApp (CGlobal headObject) left) right
        function term = unary functionObject term
        u = unary predicateObject
        r = binary binaryPredicateObject
        goal = unary factPredicateObject a
        rule =
            CForall TySet
                (CForall TySet
                    (CImp
                        (u (CBound 1))
                        (CImp
                            (r (function (CBound 1)) (CBound 0))
                            goal)))
    hypotheses <-
        traverse (checkedGlobalScoped [])
            [ CEq TySet a b
            , u a
            , r (function b) c
            , rule
            ]
    target <- checkedGlobalScoped [] goal
    let run budget selectedHypotheses =
            obviousProofDetailed
                budget AnyObviousProof foundation globalType
                selectedHypotheses [] [] target
        (statistics, result) = run refutationBudget hypotheses
    assertFailureKind
        "the coordinator retains focused exhaustion precedence"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        result
    assertEqual "the detailed rule outcome records selected unsupported work"
        ObviousTierUnsupported
        (obviousRefutationTierOutcome statistics)
    assertEqual "an outside-universe candidate admits no instance"
        0
        (obviousRuleInstancesAdmitted statistics)

    successfulHypotheses <-
        traverse (checkedGlobalScoped [])
            [ CEq TySet a b
            , u a
            , r (function b) c
            , rule
            , u b
            ]
    let (successStatistics, successResult) =
            run refutationBudget successfulHypotheses
    successProof <- expectRight successResult
    assertCandidateReplays
        foundation globalType successfulHypotheses [] target successProof
    assertEqual
        "a later supported substitution wins after a terminal rejection"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome successStatistics)
    assertEqual "only the supported substitution becomes an instance"
        1
        (obviousRuleInstancesAdmitted successStatistics)

    let d = COpaqueInteger 63
        trigger = unary factPredicateObject d
        equalityProducer = CImp trigger (CEq TySet c d)
    retryHypotheses <-
        traverse (checkedGlobalScoped [])
            [ CEq TySet a b
            , u a
            , r (function b) c
            , rule
            , equalityProducer
            , trigger
            ]
    let (retryStatistics, retryResult) =
            run refutationBudget retryHypotheses
        usedWork = obviousRefutationWorkConsumed retryStatistics
    assertFailureKind
        "a later equality merge does not erase the terminal unsupported result"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        retryResult
    assertEqual "quiescence retains the selected unsupported result"
        ObviousTierUnsupported
        (obviousRefutationTierOutcome retryStatistics)
    assertEqual "only the equality producer is admitted as an instance"
        1
        (obviousRuleInstancesAdmitted retryStatistics)
    assertBool "the later produced equality is processed"
        (obviousEqualityEventsProcessed retryStatistics >= 2)
    let (repeatedStatistics, repeatedResult) =
            run refutationBudget retryHypotheses
    assertEqual "terminal retry accounting is deterministic"
        retryStatistics repeatedStatistics
    assertFailureKind "terminal retry outcome is deterministic"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        repeatedResult

    let (shortStatistics, shortResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork - 1 }
                retryHypotheses
    case shortResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "one-short terminal saturation succeeded"
    assertEqual
        "later exhaustion outranks a sticky unsupported operation"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

rejectsOutsideUniversePartialApplication :: Assertion
rejectsOutsideUniversePartialApplication = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TyArrow TySet (TyArrow TySet TySet)]
        a = COpaqueInteger 64
        b = COpaqueInteger 65
        p term = member term empty
        applied depth argument = CApp (CApp (CBound depth) argument) b
        rule = CForall TySet
            (CImp (p (CBound 0)) (p (applied 1 (CBound 0))))
    hypotheses <- traverse (checkedScoped context) [p a, rule]
    target <- checkedScoped context CFalsum
    let (statistics, result) = obviousProofDetailed
            refutationBudget AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] target
    assertEqual "a newly closed partial application is outside the frozen domain"
        ObviousTierUnsupported (obviousRefutationTierOutcome statistics)
    assertFailureKind "an unsupported search retains the coordinator's source-rejection precedence"
        (ObviousResourceExhausted ObviousFocusedWorkLimit) result
    assertEqual "the rejected derived term publishes no rule instance"
        0 (obviousRuleInstancesAdmitted statistics)

    seededTarget <- checkedScoped context (p (applied 0 a))
    let (seededStatistics, seededResult) = obviousProofDetailed
            refutationBudget AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] seededTarget
    proof <- expectRight seededResult
    assertCandidateReplays foundation emptyGlobalTyping hypotheses [] seededTarget proof
    assertEqual "the same checked rule succeeds when its closed applications are seeded"
        ObviousTierCandidateBuilt (obviousRefutationTierOutcome seededStatistics)
    assertEqual "the seeded rule publishes one instance"
        1 (obviousRuleInstancesAdmitted seededStatistics)

reportsRuleResourceBoundaries :: Assertion
reportsRuleResourceBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 70
        one = pair empty empty
        p term = member term empty
        q term = member term one
        rule = CForall TySet
            (CImp (p (CBound 0)) (q (CBound 0)))
    fact <- checkedScoped [] (p a)
    source <- checkedScoped [] rule
    target <- checkedScoped [] (q a)
    let run budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                [fact, source] [] [] target
        (ampleStatistics, ampleResult) = run refutationBudget
        usedWork = obviousRefutationWorkConsumed ampleStatistics
    ampleProof <- expectRight ampleResult
    assertCandidateReplays foundation emptyGlobalTyping
        [fact, source] [] target ampleProof
    assertEqual "one rule produces one retained instance"
        1
        (obviousRuleInstancesAdmitted ampleStatistics)

    let zeroInstanceBudget =
            refutationBudget {obviousRuleInstanceLimit = 0}
        (zeroStatistics, zeroResult) = run zeroInstanceBudget
    case zeroResult of
        Left _failure -> pure ()
        Right _proof -> assertFailure "zero rule-instance capacity succeeded"
    assertEqual "zero instance capacity is a named refutation boundary"
        (ObviousTierResourceExhausted ObviousRuleInstanceLimit)
        (obviousRefutationTierOutcome zeroStatistics)
    assertEqual "the cap preflight publishes no instance"
        0
        (obviousRuleInstancesAdmitted zeroStatistics)

    zeroPremiseRule <- checkedScoped []
        (CForall TySet
            (p (nestedPair 12 (CBound 0))))
    zeroPremiseTarget <- checkedScoped []
        (p (nestedPair 12 a))
    let runZeroPremise budget =
            obviousProofDetailed
                budget AnyObviousProof foundation emptyGlobalTyping
                [zeroPremiseRule] [] [] zeroPremiseTarget
        zeroPremiseCapBudget =
            refutationBudget {obviousRuleInstanceLimit = 0}
        (zeroPremiseStatistics, zeroPremiseResult) =
            runZeroPremise zeroPremiseCapBudget
        zeroPremiseCapWork =
            obviousRefutationWorkConsumed zeroPremiseStatistics
    -- The boundary owns matching, substitution identity and the negative target
    -- hint event, but no conclusion closure or derived-universe census.
    assertEqual "zero-premise instance preflight includes owned query admission"
        3416
        zeroPremiseCapWork
    case zeroPremiseResult of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "zero-premise rule crossed its zero instance cap"
    assertEqual
        "zero-premise matching reaches the named cap before conclusion closure"
        (ObviousTierResourceExhausted ObviousRuleInstanceLimit)
        (obviousRefutationTierOutcome zeroPremiseStatistics)
    let (zeroPremiseExactStatistics, _zeroPremiseExactResult) =
            runZeroPremise
                zeroPremiseCapBudget
                    { obviousRefutationWorkLimit = zeroPremiseCapWork
                    }
        (zeroPremiseShortStatistics, _zeroPremiseShortResult) =
            runZeroPremise
                zeroPremiseCapBudget
                    { obviousRefutationWorkLimit = zeroPremiseCapWork - 1
                    }
    assertEqual "the exact zero-premise preflight reports its named cap"
        (ObviousTierResourceExhausted ObviousRuleInstanceLimit)
        (obviousRefutationTierOutcome zeroPremiseExactStatistics)
    assertEqual "one-short zero-premise matching exhausts semantic work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome zeroPremiseShortStatistics)
    assertEqual "neither zero-premise boundary publishes an instance"
        (0, 0)
        ( obviousRuleInstancesAdmitted zeroPremiseExactStatistics
        , obviousRuleInstancesAdmitted zeroPremiseShortStatistics
        )

    _exactProof <-
        expectRight
            (snd
                (run
                    refutationBudget
                        { obviousRefutationWorkLimit = usedWork }))
    let (shortStatistics, shortResult) =
            run
                refutationBudget
                    { obviousRefutationWorkLimit = usedWork - 1 }
    case shortResult of
        Left _failure -> pure ()
        Right _proof -> assertFailure "one-short rule work succeeded"
    assertEqual "one-short rule replay exhausts refutation work"
        (ObviousTierResourceExhausted ObviousRefutationWorkLimit)
        (obviousRefutationTierOutcome shortStatistics)

newtype OraclePredicate = OraclePredicate Int
    deriving stock (Show, Eq, Ord)

newtype OracleIndividual = OracleIndividual Int
    deriving stock (Show, Eq, Ord)

data OracleRule = OracleRule
    ![OraclePredicate]
    !OraclePredicate
    deriving stock (Show, Eq, Ord)

oracleIndividualPair
    :: OracleIndividual
    -> OracleIndividual
    -> (OracleIndividual, OracleIndividual)
oracleIndividualPair left right
    | left <= right = (left, right)
    | otherwise = (right, left)

oracleIndividualClosure
    :: [OracleIndividual]
    -> [(OracleIndividual, OracleIndividual)]
    -> Set.Set (OracleIndividual, OracleIndividual)
oracleIndividualClosure individuals equalities = fixedPoint initial
  where
    initial =
        Set.fromList
            ([oracleIndividualPair individual individual
             | individual <- individuals]
                <> [oracleIndividualPair left right
                   | (left, right) <- equalities])

    fixedPoint relation =
        let updated =
                relation
                    `Set.union` Set.fromList
                        [ oracleIndividualPair left right
                        | left <- individuals
                        , right <- individuals
                        , any
                            (\middle ->
                                related relation left middle
                                    && related relation middle right)
                            individuals
                        ]
        in if updated == relation
            then relation
            else fixedPoint updated

    related relation left right =
        oracleIndividualPair left right `Set.member` relation

oracleRuleClosure
    :: [OracleIndividual]
    -> Set.Set (OracleIndividual, OracleIndividual)
    -> Set.Set (OraclePredicate, OracleIndividual)
    -> [OracleRule]
    -> Set.Set (OraclePredicate, OracleIndividual)
oracleRuleClosure individuals equality initialFacts rules =
    fixedPoint initialFacts
  where
    fixedPoint facts =
        let derived =
                Set.fromList
                    [ (conclusion, individual)
                    | OracleRule premises conclusion <- rules
                    , individual <- individuals
                    , all
                        (\premise -> holds facts premise individual)
                        premises
                    ]
            updated = facts `Set.union` derived
        in if updated == facts
            then facts
            else fixedPoint updated

    holds facts predicate individual =
        any
            (\(foundPredicate, foundIndividual) ->
                foundPredicate == predicate
                    && oracleIndividualPair foundIndividual individual
                        `Set.member` equality)
            (Set.toAscList facts)

oraclePredicateCarrier :: OraclePredicate -> CanonicalTerm Void
oraclePredicateCarrier (OraclePredicate predicate) =
    go predicate empty
  where
    go remaining term
        | remaining <= 0 = term
        | otherwise = go (remaining - 1) (pair term empty)

oracleIndividualTerm :: OracleIndividual -> CanonicalTerm Void
oracleIndividualTerm (OracleIndividual individual) =
    COpaqueInteger (fromIntegral individual)

oracleAtomTerm
    :: OraclePredicate
    -> CanonicalTerm Void
    -> CanonicalTerm Void
oracleAtomTerm predicate individual =
    member individual (oraclePredicateCarrier predicate)

oracleGroundAtomTerm
    :: (OraclePredicate, OracleIndividual)
    -> CanonicalTerm Void
oracleGroundAtomTerm (predicate, individual) =
    oracleAtomTerm predicate (oracleIndividualTerm individual)

oracleRuleTerm :: OracleRule -> CanonicalTerm Void
oracleRuleTerm (OracleRule premises conclusion) =
    CForall TySet
        (foldr CImp
            (oracleAtomTerm conclusion (CBound 0))
            [ oracleAtomTerm premise (CBound 0)
            | premise <- premises
            ])

agreesWithRuleOracle :: Assertion
agreesWithRuleOracle = do
    foundation <- expectRight Foundation.checkedFoundation
    let first = OracleIndividual 90
        second = OracleIndividual 91
        individuals = [first, second]
        equalities = [(first, second)]
        p = OraclePredicate 0
        q = OraclePredicate 1
        r = OraclePredicate 2
        s = OraclePredicate 3
        universal = OraclePredicate 4
        absent = OraclePredicate 5
        facts = Set.fromList [(p, first), (q, first)]
        rules =
            [ OracleRule [p, q] r
            , OracleRule [r] s
            , OracleRule [] universal
            ]
        equalityClosure =
            oracleIndividualClosure individuals equalities
        closure =
            oracleRuleClosure
                individuals equalityClosure facts rules
        queries =
            [ (r, first)
            , (r, second)
            , (s, first)
            , (s, second)
            , (universal, first)
            , (universal, second)
            , (q, second)
            , (absent, first)
            ]
    equalityHypotheses <-
        traverse
            (\(left, right) ->
                checkedScoped []
                    (CEq TySet
                        (oracleIndividualTerm left)
                        (oracleIndividualTerm right)))
            equalities
    factHypotheses <-
        traverse
            (checkedScoped [] . oracleGroundAtomTerm)
            (Set.toAscList facts)
    ruleHypotheses <-
        traverse
            (checkedScoped [] . oracleRuleTerm)
            rules
    let hypotheses =
            equalityHypotheses <> factHypotheses <> ruleHypotheses
    traverse_
        (checkQuery foundation hypotheses equalityClosure closure)
        (zip [0 :: Int ..] queries)
  where
    checkQuery foundation hypotheses equality closure
            (queryIndex, query@(predicate, individual)) = do
        target <- checkedScoped [] (oracleGroundAtomTerm query)
        let expected =
                any
                    (\(foundPredicate, foundIndividual) ->
                        foundPredicate == predicate
                            && oracleIndividualPair
                                foundIndividual individual
                                `Set.member` equality)
                    (Set.toAscList closure)
            (statistics, result) =
                obviousProofDetailed
                    refutationBudget AnyObviousProof foundation emptyGlobalTyping
                    hypotheses [] [] target
            label = "rule oracle query " <> show queryIndex
        if expected
            then do
                proof <- expectRight result
                assertCandidateReplays
                    foundation emptyGlobalTyping hypotheses [] target proof
                assertEqual (label <> " builds a candidate")
                    ObviousTierCandidateBuilt
                    (obviousRefutationTierOutcome statistics)
            else do
                case result of
                    Left _failure -> pure ()
                    Right _proof ->
                        assertFailure (label <> " proved a non-consequence")
                assertEqual (label <> " reaches a rule fixed point")
                    ObviousTierNoProof
                    (obviousRefutationTierOutcome statistics)

rejectsUndeterminedParameter :: Assertion
rejectsUndeterminedParameter = do
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (member (CBound 0) empty)
                membership))
    target <- checkedScoped [] membership
    foundation <- expectRight Foundation.checkedFoundation
    let report =
            obviousProofReport defaultObviousBudget AnyObviousProof
                foundation emptyGlobalTyping []
                [obviousImport (importIx 0) theorem] [] target
        result = obviousRunResult report
    case result of
        Left (ObviousUndeterminedParameter 0) -> pure ()
        Left failure ->
            assertFailure
                ("expected an undetermined parameter, got " <> show failure)
        Right _proof ->
            assertFailure "expected theorem application to fail"
    assertSingleCandidateOutcome
        (CandidateImport (importIx 0))
        (CandidatePreparedTheoremView 0)
        (ProofIncomplete ParameterUndetermined)
        report

reportsUnavailableAntecedent :: Assertion
reportsUnavailableAntecedent = do
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (member empty (pair (CBound 0) (CBound 0)))
                (member (CBound 0) empty)))
    target <- checkedScoped [] membership
    foundation <- expectRight Foundation.checkedFoundation
    let report =
            obviousProofReport defaultObviousBudget AnyObviousProof
                foundation emptyGlobalTyping []
                [obviousImport (importIx 0) theorem] [] target
        result = obviousRunResult report
    case result of
        Left ObviousAntecedentUnavailable{} -> pure ()
        Left failure ->
            assertFailure
                ("expected an unavailable antecedent, got " <> show failure)
        Right _proof ->
            assertFailure "expected theorem application to fail"
    assertSingleCandidateOutcome
        (CandidateImport (importIx 0))
        (CandidatePreparedTheoremView 0)
        (ProofIncomplete AntecedentUnavailable)
        report

transportsPropositions :: Assertion
transportsPropositions = do
    left <- checkedScoped [] membership
    right <- checkedScoped [] otherMembership
    equivalence <- checkedScoped []
        (CEq TyProp membership otherMembership)
    assertObvious [left, equivalence] [] right
    foundation <- expectRight Foundation.checkedFoundation
    let incompleteReport =
            obviousProofReport defaultObviousBudget AnyObviousProof
                foundation emptyGlobalTyping [equivalence] [] [] right
    assertSingleCandidateOutcome
        (CandidateHypothesis 0)
        (CandidateEqualityTransportView 0)
        (ProofIncomplete TransportPremiseUnavailable)
        incompleteReport

composesCitedProjectionWithFocusedEquality :: Assertion
composesCitedProjectionWithFocusedEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let right = pair empty empty
        targetTerm = member right empty
        projectedTerm = CAnd CTruth (CAnd membership CTruth)
    projected <- checkedClosed projectedTerm
    equality <- checkedClosed (CEq TySet empty right)
    target <- checkedScoped [] targetTerm
    let imports =
            [ obviousImport (importIx 0) projected
            , obviousImport (importIx 1) equality
            ]
        (statistics, result) =
            obviousProofDetailed
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                imports
                []
                target
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping [] imports target proof
    assertEqual "projection and equality are the exact cited authority"
        (Set.fromList [importIx 0, importIx 1])
        (obviousUsedImports proof)
    assertEqual "ground composition can complete while focused equality is still pending"
        (ObviousTierNotCompleted, ObviousTierCandidateBuilt)
        (obviousFocusedTierOutcome statistics, obviousRefutationTierOutcome statistics)
    suppliedFocusedProof <- expectRight (obviousProof
        defaultObviousBudget {obviousRefutationWorkLimit = 0}
        foundation emptyGlobalTyping [] imports [] target)
    assertCandidateReplays foundation emptyGlobalTyping [] imports target suppliedFocusedProof

    let uncited =
            obviousProof
                defaultObviousBudget
                foundation
                emptyGlobalTyping
                []
                [obviousImport (importIx 0) projected]
                []
                target
    case uncited of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure "an uncited equality participated in transport"

    -- Isolate the focused boundary; refutation may independently prove this goal.
    -- Graph probes retain checked operands and recursive congruence shares
    -- their checked children, so repeated child recovery is absent too.
    -- choice-forest-v1 includes one ownership registration per admitted choice.
    -- E8b charges one schema check for each of the two prepared source views.
    -- adjacency-v2 charges each supported adjacency lookup explicitly, even
    -- when a tiny graph's old global scan was cheaper in structural units.
    -- Obligation lookup validates its nominal context once before payload comparison.
    for_
        [ ("root", 363, membership)
        , ("two-level projection", 574, projectedTerm)
        ] \(label, expectedWork, sourceTerm) -> do
            source <- checkedScoped [] sourceTerm
            equalityHypothesis <- checkedScoped [] (CEq TySet empty right)
            let hypotheses = [source, equalityHypothesis]
                run focused =
                    obviousProofDetailed
                        (focusedBudget focused) {obviousRefutationWorkLimit = 0}
                        AnyObviousProof
                        foundation
                        emptyGlobalTyping
                        hypotheses
                        []
                        []
                        target
                (ampleStatistics, ampleResult) = run 1000000
                consumed = obviousFocusedWorkConsumed ampleStatistics
            focusedProof <- expectRight ampleResult
            assertCandidateReplays
                foundation emptyGlobalTyping hypotheses [] target focusedProof
            assertEqual (label <> " focused-work threshold")
                expectedWork consumed
            _exactProof <- expectRight (snd (run consumed))
            assertFailureKind
                (label <> " one-short traversal budget")
                (ObviousResourceExhausted ObviousFocusedWorkLimit)
                (snd (run (consumed - 1)))

preservesDirectPropositionTransportPriority :: Assertion
preservesDirectPropositionTransportPriority = do
    foundation <- expectRight Foundation.checkedFoundation
    premise <- checkedScoped [] membership
    equivalence <- checkedScoped []
        (CEq TyProp membership otherMembership)
    irrelevant <- traverse
        (checkedScoped [] . (\index ->
            member (COpaqueInteger index) empty))
        [1 .. 16]
    target <- checkedScoped [] otherMembership
    let hypotheses = equivalence : premise : irrelevant
        run focused =
            obviousProofDetailed
                defaultObviousBudget
                    { obviousFocusedWorkLimit = focused }
                AnyObviousProof
                foundation
                emptyGlobalTyping
                hypotheses
                []
                []
                target
        (statistics, result) = run 1000000
        consumed = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays
        foundation emptyGlobalTyping hypotheses [] target proof
    assertEqual "early direct transport threshold with nominal scope admission" 565 consumed
    _exactProof <- expectRight (snd (run consumed))
    pure ()

skipsEmptyPropositionTransportEqualityGraph :: Assertion
skipsEmptyPropositionTransportEqualityGraph = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checkedGlobalScoped [] membership
    target <- checkedGlobalScoped []
        (CApp (CGlobal predicateObject) empty)
    definition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                (member (CBound 0) empty)))
    let definitionImport = obviousImport (importIx 0) definition
        definitionView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView definitionImport
        run focused =
            obviousProofDetailed
                defaultObviousBudget
                    { obviousFocusedWorkLimit = focused }
                MustUseCanonicalDefinition
                foundation
                globalType
                [source]
                []
                [definitionView]
                target
        (statistics, result) = run 1000000
        consumed = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    assertEqual "the next rule supplies the canonical definition"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)
    assertEqual "empty-graph skip, selected-view family and source publication threshold" 331 consumed
    _exactProof <- expectRight (snd (run consumed))
    assertFailureKind
        "an unnecessary empty-graph pass consumes the next rule's last step"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        (snd (run (consumed - 1)))

keepsFailedPropositionTransportProbesOutOfGraph :: Assertion
keepsFailedPropositionTransportProbesOutOfGraph = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checkedGlobalScoped [] membership
    equality <- checkedGlobalScoped []
        (CEq TySet empty (pair empty empty))
    irrelevant <- traverse
        (checkedGlobalScoped [] . (\index ->
            member (COpaqueInteger index) (pair empty empty)))
        [1 .. 32]
    target <- checkedGlobalScoped []
        (CApp (CGlobal predicateObject) empty)
    definition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                (member (CBound 0) empty)))
    let definitionImport = obviousImport (importIx 0) definition
        definitionView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView definitionImport
        hypotheses = source : equality : irrelevant
        run focused =
            obviousProofDetailed
                defaultObviousBudget
                    { obviousFocusedWorkLimit = focused }
                MustUseCanonicalDefinition
                foundation
                globalType
                hypotheses
                []
                [definitionView]
                target
        (statistics, result) = run 1000000
        consumed = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    assertCandidateReplays
        foundation globalType hypotheses [definitionImport] target proof
    assertEqual "the later definition remains the exact authority"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)
    assertEqual "failed transport probes retain the graph and charge the selected-view family"
        601 consumed
    _exactProof <- expectRight (snd (run consumed))
    assertFailureKind
        "one-short no-pollution budget"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        (snd (run (consumed - 1)))

tracksPropositionTransportDefinitionEvidence :: Assertion
tracksPropositionTransportDefinitionEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let right = pair empty empty
        targetTerm = member right empty
        defined = CApp (CGlobal factPredicateObject) empty
        sourceDefinitionTerm =
            CForall TySet
                (CEq TyProp
                    (CApp (CGlobal factPredicateObject) (CBound 0))
                    (member (CBound 0) empty))
        equalityDefinitionTerm =
            CForall TySet
                (CEq TyProp
                    (CApp (CGlobal factPredicateObject) (CBound 0))
                    (CEq TySet empty right))
    target <- checkedGlobalScoped [] targetTerm
    source <- checkedGlobalClosed membership
    equality <- checkedGlobalClosed (CEq TySet empty right)
    definedFact <- checkedGlobalClosed defined
    sourceDefinition <- checkedGlobalClosed sourceDefinitionTerm
    equalityDefinition <- checkedGlobalClosed equalityDefinitionTerm
    let sourceView =
            obviousImportedDefinitionView
                factPredicateObject
                DefinitionPointwiseView
                (obviousImport (importIx 1) sourceDefinition)
        equalityView =
            obviousImportedDefinitionView
                factPredicateObject
                DefinitionPointwiseView
                (obviousImport (importIx 2) equalityDefinition)
        prove imports views =
            obviousProofWithRequirement
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation
                globalType
                []
                imports
                views
                target

    sourceDefined <- expectRight
        (prove
            [ obviousImport (importIx 0) definedFact
            , obviousImport (importIx 2) equality
            ]
            [sourceView])
    assertEqual "the source supplies definition evidence"
        (Set.fromList [importIx 0, importIx 1, importIx 2])
        (obviousUsedImports sourceDefined)

    pathDefined <- expectRight
        (prove
            [ obviousImport (importIx 0) source
            , obviousImport (importIx 1) definedFact
            ]
            [equalityView])
    assertEqual "the equality path supplies definition evidence"
        (Set.fromList [importIx 0, importIx 1, importIx 2])
        (obviousUsedImports pathDefined)

    let ordinaryImports =
            [ obviousImport (importIx 0) source
            , obviousImport (importIx 1) equality
            ]
    case prove ordinaryImports [] of
        Left _failure -> pure ()
        Right _proof ->
            assertFailure
                "ordinary transport bypassed definition-requirement enforcement"

composesEqualitySymmetryWithNegation :: Assertion
composesEqualitySymmetryWithNegation = do
    let other = pair empty empty
    equality <- checkedScoped [] (CEq TySet empty other)
    reverseEquality <- checkedScoped [] (CEq TySet other empty)
    reverseDisequality <- checkedScoped [] (CNot (CEq TySet other empty))
    disequality <- checkedScoped [] (CNot (CEq TySet empty other))
    assertObvious [equality] [] reverseEquality
    assertObvious [reverseDisequality] [] disequality

reportsOnlyUsedImports :: Assertion
reportsOnlyUsedImports = do
    irrelevant <- checkedClosed otherMembership
    theorem <- checkedClosed
        (CForall TySet
            (CImp
                (CEq TySet (CBound 0) empty)
                (member (CBound 0) empty)))
    target <- checkedScoped [] membership
    proof <- expectRight =<< runObvious
        []
        [ obviousImport (importIx 0) irrelevant
        , obviousImport (importIx 1) theorem
        ]
        target
    assertEqual
        "unused explicit citations are not proof authority"
        (Set.singleton (importIx 1))
        (obviousUsedImports proof)

    membershipFact <- checkedClosed membership
    otherFact <- checkedClosed otherMembership
    let wideTerm =
            foldr1 CAnd
                (take 12 (cycle [membership, otherMembership]))
        wideImports =
            [ obviousImport (importIx 10) membershipFact
            , obviousImport (importIx 11) otherFact
            ]
        wideRun foundation focused wideTarget =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                wideImports
                []
                wideTarget
    wideTarget <- checkedScoped [] wideTerm
    foundation <- expectRight Foundation.checkedFoundation
    let (wideStatistics, wideResult) =
            wideRun foundation 1000000 wideTarget
        wideWork = obviousFocusedWorkConsumed wideStatistics
    wideProof <- expectRight wideResult
    assertEqual "wide proof retains distinct leaves once"
        (Set.fromList [importIx 10, importIx 11])
        (obviousUsedImports wideProof)
    assertCandidateReplays
        foundation emptyGlobalTyping [] wideImports wideTarget wideProof
    exactWideProof <-
        expectRight
            (snd (wideRun foundation wideWork wideTarget))
    assertEqual "wide exact-boundary authority"
        (Set.fromList [importIx 10, importIx 11])
        (obviousUsedImports exactWideProof)
    let (wideFallbackStatistics, wideFallbackResult) =
            wideRun foundation (wideWork - 1) wideTarget
    wideFallbackProof <- expectRight wideFallbackResult
    assertCandidateReplays
        foundation emptyGlobalTyping [] wideImports wideTarget wideFallbackProof
    assertEqual "focused dependency fold stops at its boundary"
        (ObviousTierResourceExhausted ObviousFocusedWorkLimit)
        (obviousFocusedTierOutcome wideFallbackStatistics)
    assertEqual "refutation reconstructs the wide consequence"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome wideFallbackStatistics)

exposesCanonicalDefinitions :: Assertion
exposesCanonicalDefinitions = do
    predicateDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                (CEq TySet (CBound 0) (CBound 0))))
    functionDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TySet
                (CApp (CGlobal functionObject) (CBound 0))
                (CBound 0)))
    factPredicateDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal factPredicateObject) (CBound 0))
                (member (CBound 0) empty)))
    membershipDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (member (CBound 0) (CGlobal namedSetObject))
                (CEq TySet (CBound 0) (CBound 0))))
    predicateGoal <- checkedGlobalScoped []
        (CApp (CGlobal predicateObject) empty)
    functionGoal <- checkedGlobalScoped []
        (CEq TySet (CApp (CGlobal functionObject) empty) empty)
    bodyMembership <- checkedGlobalScoped [] membership
    membershipGoal <- checkedGlobalScoped []
        (member empty (CApp (CGlobal functionObject) empty))
    predicateFact <- checkedGlobalClosed
        (CApp (CGlobal factPredicateObject) empty)
    exposedFactGoal <- checkedGlobalScoped []
        membership
    directMembershipGoal <- checkedGlobalScoped []
        (member empty (CGlobal namedSetObject))
    foundation <- expectRight Foundation.checkedFoundation
    let predicateImport = obviousImport (importIx 0) predicateDefinition
        functionImport = obviousImport (importIx 1) functionDefinition
        factPredicateImport =
            obviousImport (importIx 2) factPredicateDefinition
        membershipImport =
            obviousImport (importIx 4) membershipDefinition
        predicateView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView predicateImport
        functionView =
            obviousImportedDefinitionView
                functionObject DefinitionPointwiseView functionImport
        factPredicateView =
            obviousImportedDefinitionView
                factPredicateObject DefinitionPointwiseView
                factPredicateImport
        membershipView =
            obviousImportedDefinitionView
                namedSetObject DefinitionMembershipView membershipImport
        prove hypotheses ordinary definitions goal =
            expectRight
                (obviousProof
                    defaultObviousBudget foundation globalType
                    hypotheses ordinary definitions goal)
    predicateProof <- prove [] [] [predicateView] predicateGoal
    functionProof <- prove [] [] [functionView] functionGoal
    membershipProof <- prove
        [bodyMembership] [] [functionView] membershipGoal
    exposedProof <- prove
        [] [obviousImport (importIx 3) predicateFact]
        [factPredicateView] exposedFactGoal
    directMembershipProof <- prove
        [] [] [membershipView] directMembershipGoal
    assertEqual "predicate definition import"
        (Set.singleton (importIx 0))
        (obviousUsedImports predicateProof)
    assertEqual "function definition import"
        (Set.singleton (importIx 1))
        (obviousUsedImports functionProof)
    assertEqual "membership fallback import"
        (Set.singleton (importIx 1))
        (obviousUsedImports membershipProof)
    assertEqual "fact-side definition imports"
        (Set.fromList [importIx 2, importIx 3])
        (obviousUsedImports exposedProof)
    assertEqual "generated membership view import"
        (Set.singleton (importIx 4))
        (obviousUsedImports directMembershipProof)

exposesLocalDefinitions :: Assertion
exposesLocalDefinitions = do
    definition <- checkedScoped [TySet]
        (CEq TySet (CBound 0) empty)
    body <- checkedScoped [TySet] membership
    target <- checkedScoped [TySet]
        (member empty (CBound 0))
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            defaultObviousBudget foundation emptyGlobalTyping
            [body, definition]
            []
            [obviousLocalDefinitionView 1 DefinitionExactView]
            target)
    assertEqual
        "the local view does not acquire global authority"
        Set.empty
        (obviousUsedImports proof)

exposesAppliedLocalPredicateDefinitions :: Assertion
exposesAppliedLocalPredicateDefinitions = do
    let context = [TySet, TyArrow TySet TyProp]
        predicate = CBound 1
        argument = CBound 0
        antecedent = member argument empty
        conclusion = member empty argument
        body = CImp antecedent conclusion
    definition <- checkedScoped context
        (CEq (TyArrow TySet TyProp)
            predicate
            (CLam TySet body))
    application <- checkedScoped context
        (CApp predicate argument)
    premise <- checkedScoped context antecedent
    target <- checkedScoped context conclusion
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            defaultObviousBudget foundation emptyGlobalTyping
            [application, premise, definition]
            []
            [obviousLocalDefinitionView 2 DefinitionExactView]
            target)
    applicationTarget <- checkedScoped context
        (CApp predicate argument)
    bodyFact <- checkedScoped context body
    goalProof <- expectRight
        (obviousProof
            defaultObviousBudget foundation emptyGlobalTyping
            [bodyFact, definition]
            []
            [obviousLocalDefinitionView 1 DefinitionExactView]
            applicationTarget)
    assertEqual
        "the local predicate view does not acquire global authority"
        Set.empty
        (obviousUsedImports proof)
    assertEqual
        "the local predicate goal does not acquire global authority"
        Set.empty
        (obviousUsedImports goalProof)

exposesEitherEqualityOperand :: Assertion
exposesEitherEqualityOperand = do
    let definedLeft = CApp (CGlobal functionObject) empty
    definition <- checkedGlobalScoped [TySet]
        (CEq TySet (CBound 0) empty)
    unfolded <- checkedGlobalScoped [TySet]
        (CEq TySet definedLeft empty)
    target <- checkedGlobalScoped [TySet]
        (CEq TySet definedLeft (CBound 0))
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            defaultObviousBudget foundation globalType
            [unfolded, definition]
            []
            [obviousLocalDefinitionView 1 DefinitionExactView]
            target)
    assertEqual
        "the right-side local view does not acquire global authority"
        Set.empty
        (obviousUsedImports proof)

provesBetaConvertibleHeads :: Assertion
provesBetaConvertibleHeads = do
    proposition <- checkedScoped [] membership
    truth <- checkedScoped [] (betaWrap CTruth)
    falsum <- checkedScoped [] (betaWrap CFalsum)
    conjunction <- checkedScoped []
        (betaWrap (CAnd membership membership))
    implication <- checkedScoped []
        (betaWrap (CImp membership membership))
    negation <- checkedScoped []
        (betaWrap (CNot CFalsum))
    universal <- checkedScoped []
        (betaWrap
            (CForall TySet
                (CImp
                    (member (CBound 0) empty)
                    (member (CBound 0) empty))))
    equality <- checkedScoped []
        (betaWrap (CEq TySet empty empty))
    negative <- checkedScoped [] (CNot membership)
    assertObvious [] [] truth
    assertObvious [proposition, negative] [] falsum
    assertObvious [proposition] [] conjunction
    assertObvious [] [] implication
    assertObvious [] [] negation
    assertObvious [] [] universal
    assertObvious [] [] equality

projectsBetaConvertibleConjunction :: Assertion
projectsBetaConvertibleConjunction = do
    conjunction <- checkedScoped []
        (betaWrap (CAnd membership otherMembership))
    target <- checkedScoped [] membership
    assertObvious [conjunction] [] target

appliesBetaConvertibleTheorem :: Assertion
appliesBetaConvertibleTheorem = do
    theorem <- checkedClosed
        (betaWrap
            (CForall TySet
                (CImp
                    (CEq TySet (CBound 0) empty)
                    (member
                        (CApp
                            (CLam TySet (CBound 0))
                            (CBound 0))
                        empty))))
    target <- checkedScoped [] membership
    assertObvious
        [] [obviousImport (importIx 0) theorem] target

appliesConversionAwareNonIntroductionRules :: Assertion
appliesConversionAwareNonIntroductionRules = do
    let other = pair empty empty
    forwardEquality <- checkedScoped []
        (betaWrap (CEq TySet empty other))
    reverseEquality <- checkedScoped []
        (betaWrap (CEq TySet other empty))
    left <- checkedScoped [] (betaWrap membership)
    equivalence <- checkedScoped []
        (betaWrap (CEq TyProp membership otherMembership))
    right <- checkedScoped [] (betaWrap otherMembership)
    assertObvious [forwardEquality] [] reverseEquality
    assertObvious [left, equivalence] [] right

    definition <- checkedGlobalClosed
        (CForall TySet
            (CEq TySet
                (CApp (CGlobal functionObject) (CBound 0))
                (CBound 0)))
    goal <- checkedGlobalScoped []
        (CEq TySet
            (CApp
                (CLam TySet (CBound 0))
                (CApp (CGlobal functionObject) empty))
            empty)
    foundation <- expectRight Foundation.checkedFoundation
    let definitionImport =
            obviousImport (importIx 0) definition
        definitionView =
            obviousImportedDefinitionView
                functionObject DefinitionPointwiseView definitionImport
    proof <- expectRight
        (obviousProof
            defaultObviousBudget foundation globalType
            [] [] [definitionView] goal)
    assertEqual
        "the converted definition root retains its canonical authority"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

continuesFactSideDefinitionReasoning :: Assertion
continuesFactSideDefinitionReasoning = do
    premise <- checkedGlobalScoped [] membership
    falsum <- checkedGlobalScoped [] CFalsum
    let definedFact = CApp (CGlobal factPredicateObject) empty
        definition body =
            CForall TySet
                (CEq TyProp
                    (CApp (CGlobal factPredicateObject) (CBound 0))
                    body)
    fact <- checkedGlobalClosed definedFact
    implicationDefinition <- checkedGlobalClosed
        (definition (CImp membership CFalsum))
    negationDefinition <- checkedGlobalClosed
        (definition (CNot membership))
    foundation <- expectRight Foundation.checkedFoundation
    let factImport = obviousImport (importIx 0) fact
        proveWith definitionStatement = do
            let definitionImport =
                    obviousImport (importIx 1) definitionStatement
                definitionView =
                    obviousImportedDefinitionView
                        factPredicateObject
                        DefinitionPointwiseView
                        definitionImport
            proof <- expectRight
                (obviousProof
                    defaultObviousBudget
                    foundation
                    globalType
                    [premise]
                    [factImport]
                    [definitionView]
                    falsum)
            assertEqual
                "the exposed fact and its defining equation are both used"
                (Set.fromList [importIx 0, importIx 1])
                (obviousUsedImports proof)
    proveWith implicationDefinition
    proveWith negationDefinition

continuesAfterDefinitionConstructionLimit :: Assertion
continuesAfterDefinitionConstructionLimit = do
    let definedFact = CApp (CGlobal factPredicateObject) empty
        definition body =
            CForall TySet
                (CEq TyProp
                    (CApp (CGlobal factPredicateObject) (CBound 0))
                    body)
    fact <- checkedGlobalClosed definedFact
    target <- checkedGlobalScoped [] membership
    exhaustingDefinition <- checkedGlobalClosed
        (definition (expensiveProposition otherMembership))
    exactDefinition <- checkedGlobalClosed
        (definition membership)
    foundation <- expectRight Foundation.checkedFoundation
    let factImport = obviousImport (importIx 0) fact
        exhaustingView =
            obviousImportedDefinitionView
                factPredicateObject DefinitionPointwiseView
                (obviousImport (importIx 1) exhaustingDefinition)
        exactView =
            obviousImportedDefinitionView
                factPredicateObject DefinitionPointwiseView
                (obviousImport (importIx 2) exactDefinition)
    let (statistics, result) = obviousProofDetailed
            (focusedBudget 100000) AnyObviousProof
            foundation globalType [] [factImport] [exhaustingView, exactView] target
    proof <- expectRight result
    assertBool "the failed construction's conversion work remains charged"
        (obviousConversionWorkConsumed statistics >= 2000000)
    assertEqual "the later checked view supplies exactly the used definition"
        (Set.fromList [importIx 0, importIx 2]) (obviousUsedImports proof)
    assertEqual "the selected focused proof cancels the unneeded ground input probe"
        (ObviousTierCandidateBuilt, ObviousTierNoProof)
        (obviousFocusedTierOutcome statistics, obviousRefutationTierOutcome statistics)
    assertCandidateReplays foundation globalType []
        [factImport, obviousImport (importIx 1) exhaustingDefinition,
            obviousImport (importIx 2) exactDefinition] target proof
    -- With no alternate construction, both converter ceilings are ordinary
    -- resource rejections. The canonical request isolates focused ownership.
    for_
        [ (ObviousConversionOperationLimit, obviousConversionPool defaultObviousBudget)
        , (ObviousConversionPoolLimit, Conversion.conversionPool 50000)
        ] \(limit, pool) -> do
            let (limitedStatistics, limitedResult) = obviousProofDetailed
                    (focusedBudget 100000) {obviousConversionPool = pool}
                    MustUseCanonicalDefinition foundation globalType
                    [] [factImport] [exhaustingView] target
            assertFailureKind "construction reports the actual converter owner"
                (ObviousResourceExhausted limit) limitedResult
            assertBool "the unsuccessful request retains its spent conversion work"
                (obviousConversionWorkConsumed limitedStatistics > 0)
            assertBool "a construction cannot overspend its request pool"
                (obviousConversionWorkConsumed limitedStatistics
                    <= Conversion.conversionPoolAmount pool)

requiresCanonicalDefinitionCandidate :: Assertion
requiresCanonicalDefinitionCandidate = do
    let targetTerm = CApp (CGlobal predicateObject) empty
    target <- checkedGlobalScoped [] targetTerm
    definition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                (CEq TySet (CBound 0) (CBound 0))))
    foundation <- expectRight Foundation.checkedFoundation
    let definitionImport = obviousImport (importIx 0) definition
        definitionView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView definitionImport
        prove definitions =
            obviousProofWithRequirement
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation
                globalType
                [target]
                []
                definitions
                target
    proof <- expectRight (prove [definitionView])
    assertEqual
        "the later definition-bearing proof wins over exact local reuse"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)
    assertFailureKind
        "an exact ordinary local is not definition evidence"
        ObviousCanonicalDefinitionEvidenceRequired
        (prove [])
    let rejectedReport =
            obviousProofReport defaultObviousBudget
                MustUseCanonicalDefinition foundation globalType
                [target] [] [] target
    assertSingleCandidateOutcome
        (CandidateHypothesis 0)
        CandidateDirectView
        ProofRejectedByRequirement
        rejectedReport

    factTarget <- checkedGlobalScoped [] membership
    let definedFact = CApp (CGlobal factPredicateObject) empty
    fact <- checkedGlobalClosed definedFact
    factDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal factPredicateObject) (CBound 0))
                membership))
    let factImport = obviousImport (importIx 1) fact
        factDefinitionImport = obviousImport (importIx 2) factDefinition
        factView =
            obviousImportedDefinitionView
                factPredicateObject DefinitionPointwiseView
                factDefinitionImport
    factProof <- expectRight
        (obviousProofWithRequirement
            defaultObviousBudget
            MustUseCanonicalDefinition
            foundation
            globalType
            [factTarget]
            [factImport]
            [factView]
            factTarget)
    assertEqual
        "fact-side conversion also continues past the exact local"
        (Set.fromList [importIx 1, importIx 2])
        (obviousUsedImports factProof)

propagatesDefinitionEvidenceThroughIntroduction :: Assertion
propagatesDefinitionEvidenceThroughIntroduction = do
    let defined = CApp (CGlobal predicateObject) empty
    ordinary <- checkedGlobalScoped [] defined
    target <- checkedGlobalScoped [] (CImp membership defined)
    (foundation, definitionView) <- canonicalPredicateView
    proof <- expectRight
        (obviousProofWithRequirement
            defaultObviousBudget
            MustUseCanonicalDefinition
            foundation
            globalType
            [ordinary]
            []
            [definitionView]
            target)
    assertEqual
        "the implication body uses the canonical definition"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

findsDefinitionEvidenceInRightConjunct :: Assertion
findsDefinitionEvidenceInRightConjunct = do
    let defined = CApp (CGlobal predicateObject) empty
    left <- checkedGlobalScoped [] membership
    right <- checkedGlobalScoped [] defined
    target <- checkedGlobalScoped [] (CAnd membership defined)
    (foundation, definitionView) <- canonicalPredicateView
    proof <- expectRight
        (obviousProofWithRequirement
            defaultObviousBudget
            MustUseCanonicalDefinition
            foundation
            globalType
            [left, right]
            []
            [definitionView]
            target)
    assertEqual
        "the second conjunction branch uses the canonical definition"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

findsDefinitionEvidenceInTheoremAntecedent :: Assertion
findsDefinitionEvidenceInTheoremAntecedent = do
    let defined = CApp (CGlobal predicateObject) empty
    premise <- checkedGlobalScoped [] defined
    theorem <- checkedGlobalScoped [] (CImp defined otherMembership)
    target <- checkedGlobalScoped [] otherMembership
    (foundation, definitionView) <- canonicalPredicateView
    proof <- expectRight
        (obviousProofWithRequirement
            defaultObviousBudget
            MustUseCanonicalDefinition
            foundation
            globalType
            [premise, theorem]
            []
            [definitionView]
            target)
    assertEqual
        "the ordinary theorem delegates the definition requirement"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

retainsCanonicalLocalEquationOrigin :: Assertion
retainsCanonicalLocalEquationOrigin = do
    let definitionTerm =
            CForall TySet
                (CEq TyProp
                    (member (CBound 0) (CBound 1))
                    (CEq TySet (CBound 0) (CBound 0)))
        targetTerm =
            CEq TyProp
                (member empty (CBound 0))
                (CEq TySet empty empty)
    definition <- checkedScoped [TySet] definitionTerm
    target <- checkedScoped [TySet] targetTerm
    foundation <- expectRight Foundation.checkedFoundation
    let prove views =
            obviousProofWithRequirement
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation
                emptyGlobalTyping
                [definition]
                []
                views
                target
    _proof <- expectRight
        (prove [obviousLocalDefinitionView 0 DefinitionMembershipView])
    assertFailureKind
        "an unmarked local equation is only an ordinary hypothesis"
        ObviousCanonicalDefinitionEvidenceRequired
        (prove [])

auditsCanonicalSourceAfterBinders :: Assertion
auditsCanonicalSourceAfterBinders = do
    foundation <- expectRight Foundation.checkedFoundation
    ordinary <- checkedScoped [TySet] CTruth
    equation <- checkedScoped [TySet] (CEq TySet (CBound 0) empty)
    target <- checkedScoped [TySet]
        (CForall TySet (CImp membership (CEq TySet (CBound 1) empty)))
    let hypotheses = [ordinary, equation]
        views = [obviousLocalDefinitionView 1 DefinitionExactView]
        run work = obviousProofDetailed
            defaultObviousBudget {obviousFocusedWorkLimit = work, obviousRefutationWorkLimit = 0}
            MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses [] views target
        (statistics, result) = run (obviousFocusedWorkLimit defaultObviousBudget)
        used = obviousFocusedWorkConsumed statistics
    proof <- expectRight result
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
        (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
    assertEqual "the witness remains the original external equation, not the introduced assumption"
        (Set.singleton (hypothesisIx 1)) (replayedScopedKernelExternalHypothesisUses replayed)
    _ <- expectRight (snd (run used))
    assertFailureKind "one-short publication cannot skip the selected-source audit"
        (ObviousResourceExhausted ObviousFocusedWorkLimit) (snd (run (used - 1)))
    assertFailureKind "an unused registered source cannot bless an ordinary proof"
        ObviousCanonicalDefinitionEvidenceRequired
        (obviousProofWithRequirement defaultObviousBudget MustUseCanonicalDefinition
            foundation emptyGlobalTyping hypotheses [] views ordinary)

recognizesCitedCanonicalImport :: Assertion
recognizesCitedCanonicalImport = do
    foundation <- expectRight Foundation.checkedFoundation
    let written = CEq TySet (CGlobal namedSetObject) empty
    equation <- checkedGlobalClosed written
    target <- checkedGlobalScoped [] written
    conflicting <- checkedGlobalClosed CTruth
    let source = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView namedSetObject DefinitionExactView source
        conflict = obviousImportedDefinitionView namedSetObject DefinitionExactView
            (obviousImport (importIx 0) conflicting)
        run requirement views = obviousProofWithRequirement defaultObviousBudget
            requirement foundation globalType [] [source] views target
    proof <- expectRight (run MustUseCanonicalDefinition [view])
    assertEqual "direct canonical reuse retains the cited import"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType [] [source] target proof
    assertFailureKind "an index cannot substitute a different canonical statement"
        (ObviousMalformedInput (ObviousConflictingImportStatement (importIx 0)))
        (run MustUseCanonicalDefinition [conflict])
    -- An ordinary invocation does not enter an unused definition sidecar.
    ordinary <- expectRight (run AnyObviousProof [conflict])
    assertCandidateReplays foundation globalType [] [source] target ordinary
    assertFailureKind "citation alone does not register a canonical source"
        ObviousCanonicalDefinitionEvidenceRequired (run MustUseCanonicalDefinition [])

retainsSupportedReflexivityPath :: Assertion
retainsSupportedReflexivityPath = do
    foundation <- expectRight Foundation.checkedFoundation
    equation <- checkedScoped [TySet] (CEq TySet (CBound 0) empty)
    target <- checkedScoped [TySet] (CEq TySet (CBound 0) (CBound 0))
    let views = [obviousLocalDefinitionView 0 DefinitionExactView]
        run registered = obviousProofWithRequirement defaultObviousBudget
            MustUseCanonicalDefinition foundation emptyGlobalTyping [equation] [] registered target
    proof <- expectRight (run views)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.singleton equation) target
        (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
    assertEqual "the supported loop consumes the equality rather than blessing reflexivity"
        (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
    assertFailureKind "an ordinary equality path supplies no canonical witness"
        ObviousCanonicalDefinitionEvidenceRequired (run [])

retainsCanonicalConjunctSupport :: Assertion
retainsCanonicalConjunctSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    equation <- checkedScoped [] (CEq TySet empty empty)
    forM_ [0, 1] \canonicalIndex -> do
        let hypotheses = [equation, equation]
            views = [obviousLocalDefinitionView canonicalIndex DefinitionExactView]
        forM_ [CEq TySet empty empty, CAnd (CEq TySet empty empty) CTruth,
                CAnd CTruth (CEq TySet empty empty)] \term -> do
            target <- checkedScoped [] term
            proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
                MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses [] views target)
            replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
                (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
            assertEqual "support consumes the registered source in either arrival order"
                (Set.singleton (hypothesisIx canonicalIndex))
                (replayedScopedKernelExternalHypothesisUses replayed)

publishesOrdinaryDisjunction :: Assertion
publishesOrdinaryDisjunction = do
    foundation <- expectRight Foundation.checkedFoundation
    premise <- checkedGlobalScoped [] membership
    target <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0))
            (COr membership otherMembership)))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType [premise] [] [view] target)
    assertCandidateReplays foundation globalType [premise] [imported] target proof

retainsCanonicalDisjunctionSupport :: Assertion
retainsCanonicalDisjunctionSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    ordinary <- checkedGlobalScoped [] membership
    defined <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    target <- checkedGlobalScoped [] (COr membership otherMembership)
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0)) membership))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
        hypotheses = [ordinary, defined]
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType hypotheses [] [view] target)
    assertEqual "the later branch proof consumes the canonical equation"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    importedJudgement <- expectRight (derivationImportJudgement equation)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        globalType (Vector.singleton importedJudgement) (Vector.fromList hypotheses) target
        (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
    assertEqual "the canonical branch consumes the defined fact"
        (Set.singleton (hypothesisIx 1)) (replayedScopedKernelExternalHypothesisUses replayed)

retainsDirectConjunctionSupport :: Assertion
retainsDirectConjunctionSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    equation <- checkedScoped [] (CEq TySet empty empty)
    let hypotheses = [equation, equation]
        views = [obviousLocalDefinitionView 1 DefinitionExactView]
    forM_ [CAnd (CEq TySet empty empty) CTruth,
            CAnd CTruth (CEq TySet empty empty)] \branch -> do
        target <- checkedScoped [] (COr branch membership)
        proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
            MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses [] views target)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual "the direct conjunction upgrades either consumed child"
            (Set.singleton (hypothesisIx 1)) (replayedScopedKernelExternalHypothesisUses replayed)

publishesConvertedDirectPremise :: Assertion
publishesConvertedDirectPremise = do
    foundation <- expectRight Foundation.checkedFoundation
    ordinary <- checkedScoped [] membership
    equation <- checkedScoped [] (CEq TySet empty empty)
    target <- checkedScoped [] otherMembership
    theorem <- checkedClosed (CImp (CApp (CLam TySet membership) empty)
        (CImp (CEq TySet empty empty) otherMembership))
    let imported = obviousImport (importIx 0) theorem
        hypotheses = [ordinary, equation]
        views = [obviousLocalDefinitionView 1 DefinitionExactView]
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses [imported] views target)
    assertCandidateReplays foundation emptyGlobalTyping hypotheses [imported] target proof

upgradesSelectedApplicationPremise :: Assertion
upgradesSelectedApplicationPremise = do
    foundation <- expectRight Foundation.checkedFoundation
    let equality value = CEq TySet (COpaqueInteger value) (COpaqueInteger value)
    left <- checkedScoped [] (equality 17)
    right <- checkedScoped [] (equality 18)
    target <- checkedScoped [] membership
    theorem <- checkedClosed (CImp (equality 17) (CImp (equality 18) membership))
    let imported = obviousImport (importIx 0) theorem
    forM_ [(left, 1), (right, 0)] \(canonical, retainedIndex) -> do
        let hypotheses = [left, right, canonical]
            views = [obviousLocalDefinitionView 2 DefinitionExactView]
        proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
            MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses [imported] views target)
        importedJudgement <- expectRight (derivationImportJudgement theorem)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping (Vector.singleton importedJudgement) (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual "the selected application consumes the upgraded and retained premises"
            (Set.fromList [hypothesisIx retainedIndex, hypothesisIx 2])
            (replayedScopedKernelExternalHypothesisUses replayed)

retainsApplicationSupportSubstitution :: Assertion
retainsApplicationSupportSubstitution = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 17
        b = COpaqueInteger 18
        equality term = CEq TySet term term
    ordinary <- checkedScoped [] (equality a)
    premise <- checkedScoped [] (member a empty)
    canonical <- checkedScoped [] (equality a)
    unrelated <- checkedScoped [] (equality b)
    target <- checkedScoped [] otherMembership
    theorem <- checkedClosed (CForall TySet
        (CImp (CAnd (equality (CBound 0)) (member (CBound 0) empty)) otherMembership))
    let imported = obviousImport (importIx 0) theorem
        run support = obviousProofWithRequirement defaultObviousBudget
            MustUseCanonicalDefinition foundation emptyGlobalTyping [ordinary, premise, support]
            [imported] [obviousLocalDefinitionView 2 DefinitionExactView] target
    proof <- expectRight (run canonical)
    assertCandidateReplays foundation emptyGlobalTyping [ordinary, premise, canonical] [imported] target proof
    assertFailureKind "support cannot change the selected binding without proving its membership premise"
        ObviousCanonicalDefinitionEvidenceRequired (run unrelated)

    laterPremise <- checkedScoped [] (member b empty)
    cycleRule <- checkedScoped [] (CImp otherMembership (equality a))
    let laterHypotheses = [ordinary, premise, unrelated, laterPremise, cycleRule]
    later <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation emptyGlobalTyping laterHypotheses [imported]
        [obviousLocalDefinitionView 2 DefinitionExactView] target)
    importedJudgement <- expectRight (derivationImportJudgement theorem)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping (Vector.singleton importedJudgement) (Vector.fromList laterHypotheses) target
        (KernelProof.builtProofDerivation (obviousBuiltProof later)))
    assertBool "a later supplied witness remains discoverable while the earlier support recipe waits"
        (Set.fromList [hypothesisIx 2, hypothesisIx 3] `Set.isSubsetOf`
            replayedScopedKernelExternalHypothesisUses replayed)

blocksUnsupportedCanonicalCycle :: Assertion
blocksUnsupportedCanonicalCycle = do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checkedScoped [])
        [membership, CImp membership otherMembership, CImp otherMembership membership,
            CEq TySet (COpaqueInteger 17) (COpaqueInteger 17)]
    target <- checkedScoped [] membership
    let run offeredWork = obviousProofDetailed
            defaultObviousBudget {obviousFocusedWorkLimit = offeredWork}
            MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses []
            [obviousLocalDefinitionView 3 DefinitionExactView] target
        (statistics, result) = run (obviousFocusedWorkLimit defaultObviousBudget)
        work = obviousFocusedWorkConsumed statistics
    assertFailureKind "circular ordinary evidence cannot manufacture canonical support"
        ObviousCanonicalDefinitionEvidenceRequired result
    assertFailureKind "the charged support-cycle check finishes at its exact boundary"
        ObviousCanonicalDefinitionEvidenceRequired (snd (run work))
    let (shortStatistics, shortResult) = run (work - 1)
    assertFailureKind "one-short cycle analysis is a real request limit"
        (ObviousResourceExhausted ObviousFocusedWorkLimit) shortResult
    assertEqual "failed cycle analysis remains debited" (work - 1)
        (obviousFocusedWorkConsumed shortStatistics)

publishesOrdinaryTransport :: Assertion
publishesOrdinaryTransport = do
    foundation <- expectRight Foundation.checkedFoundation
    premise <- checkedGlobalScoped [] membership
    transport <- checkedGlobalScoped [] (CEq TyProp membership otherMembership)
    target <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0)) otherMembership))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType [transport, premise] [] [view] target)
    assertCandidateReplays foundation globalType [transport, premise] [imported] target proof

upgradesTransportPremise :: Assertion
upgradesTransportPremise = do
    foundation <- expectRight Foundation.checkedFoundation
    transport <- checkedGlobalScoped [] (CEq TyProp membership otherMembership)
    ordinary <- checkedGlobalScoped [] membership
    defined <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    target <- checkedGlobalScoped [] otherMembership
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0)) membership))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
        hypotheses = [transport, ordinary, defined]
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType hypotheses [] [view] target)
    importedJudgement <- expectRight (derivationImportJudgement equation)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        globalType (Vector.singleton importedJudgement) (Vector.fromList hypotheses) target
        (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
    assertEqual "transport consumes the upgraded premise's supplied evidence"
        (Set.fromList [hypothesisIx 0, hypothesisIx 2])
        (replayedScopedKernelExternalHypothesisUses replayed)

upgradesComposedTransport :: Assertion
upgradesComposedTransport = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 17
        b = COpaqueInteger 18
    premise <- checkedScoped [] (member a empty)
    equality <- checkedScoped [] (CEq TySet a b)
    target <- checkedScoped [] (member b empty)
    let hypotheses = [premise, equality, equality]
    for_ [(defaultObviousBudget {obviousRefutationWorkLimit = 0}, [0, 2]),
          (defaultObviousBudget, [0, 1, 2])] $ \(budget, used) -> do
        proof <- expectRight (obviousProofWithRequirement budget
            MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses []
            [obviousLocalDefinitionView 2 DefinitionExactView] target)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual "each worker consumes its selected canonical edge and original proposition"
            (Set.fromList (map hypothesisIx used))
            (replayedScopedKernelExternalHypothesisUses replayed)

publishesOrdinaryApplication :: Assertion
publishesOrdinaryApplication = do
    foundation <- expectRight Foundation.checkedFoundation
    rule <- checkedGlobalScoped [] (CImp membership otherMembership)
    premise <- checkedGlobalScoped [] membership
    target <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0)) otherMembership))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType [rule, premise] [] [view] target)
    assertCandidateReplays foundation globalType [rule, premise] [imported] target proof

publishesOrdinaryEquality :: Assertion
publishesOrdinaryEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let middle = pair empty empty
        right = pair middle empty
    first <- checkedGlobalScoped [] (CEq TySet empty middle)
    second <- checkedGlobalScoped [] (CEq TySet middle right)
    target <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0)) (CEq TySet empty right)))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType [first, second] [] [view] target)
    assertCandidateReplays foundation globalType [first, second] [imported] target proof

publishesOrdinaryConjunction :: Assertion
publishesOrdinaryConjunction = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checkedGlobalScoped [] (CApp (CGlobal predicateObject) empty)
    equation <- checkedGlobalClosed (CForall TySet
        (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0)) (CAnd CTruth CTruth)))
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView predicateObject DefinitionPointwiseView imported
    proof <- expectRight (obviousProofWithRequirement defaultObviousBudget
        MustUseCanonicalDefinition foundation globalType [] [] [view] target)
    assertEqual "the completed view consumes its canonical equation"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType [] [imported] target proof

canonicalPredicateView
    :: IO
        ( Foundation.CheckedFoundation
        , ObviousDefinitionView ObjectId
        )
canonicalPredicateView = do
    definition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                (CEq TySet (CBound 0) (CBound 0))))
    foundation <- expectRight Foundation.checkedFoundation
    let definitionImport = obviousImport (importIx 0) definition
    pure
        ( foundation
        , obviousImportedDefinitionView
            predicateObject DefinitionPointwiseView definitionImport
        )

prefersGoalDefinitionConversion :: Assertion
prefersGoalDefinitionConversion = do
    let targetTerm = CApp (CGlobal predicateObject) empty
        factTerm = CApp (CGlobal factPredicateObject) empty
    target <- checkedGlobalScoped [] targetTerm
    premise <- checkedGlobalScoped [] membership
    fact <- checkedGlobalClosed factTerm
    targetDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                membership))
    factDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal factPredicateObject) (CBound 0))
                targetTerm))
    foundation <- expectRight Foundation.checkedFoundation
    let targetDefinitionImport =
            obviousImport (importIx 0) targetDefinition
        factDefinitionImport =
            obviousImport (importIx 1) factDefinition
        factImport = obviousImport (importIx 2) fact
        targetView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView
                targetDefinitionImport
        factView =
            obviousImportedDefinitionView
                factPredicateObject DefinitionPointwiseView
                factDefinitionImport
    proof <- expectRight
        (obviousProof
            defaultObviousBudget
            foundation
            globalType
            [premise]
            [factImport]
            [factView, targetView]
            target)
    assertEqual
        "the documented goal-side conversion wins"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

prefersLocalFactDefinitionConversion :: Assertion
prefersLocalFactDefinitionConversion = do
    let targetTerm = CApp (CGlobal predicateObject) empty
        factTerm = CApp (CGlobal factPredicateObject) empty
    target <- checkedGlobalScoped [] targetTerm
    fact <- checkedGlobalScoped [] factTerm
    premise <- checkedGlobalScoped [] membership
    localDefinition <- checkedGlobalScoped []
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal factPredicateObject) (CBound 0))
                (CApp (CGlobal predicateObject) (CBound 0))))
    targetDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                membership))
    foundation <- expectRight Foundation.checkedFoundation
    let targetDefinitionImport =
            obviousImport (importIx 0) targetDefinition
        targetView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView
                targetDefinitionImport
        localView =
            obviousLocalDefinitionView 0 DefinitionPointwiseView
    proof <- expectRight
        (obviousProof
            defaultObviousBudget
            foundation
            globalType
            [localDefinition, fact, premise]
            []
            [targetView, localView]
            target)
    assertEqual
        "completed goal evidence precedes the unfinished lexical view"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)
    assertCandidateReplays foundation globalType [localDefinition, fact, premise]
        [targetDefinitionImport] target proof

prefersProofLocalFactDefinitionConversion :: Assertion
prefersProofLocalFactDefinitionConversion =
  forM_
    [ ("predicate", CApp (CGlobal factPredicateObject), factPredicateObject,
        DefinitionPointwiseView, importIx 0)
    , ("membership", \term -> member term (CGlobal namedSetObject), namedSetObject,
        DefinitionMembershipView, importIx 0)
    ] \(name, factApplication, subject, kind, expectedImport) -> do
    let targetTerm = CApp (CGlobal predicateObject) empty
        factTerm = factApplication empty
    target <- checkedGlobalScoped [] targetTerm
    fact <- checkedGlobalScoped [] (CAnd factTerm otherMembership)
    premise <- checkedGlobalScoped [] membership
    targetDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                membership))
    factDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (factApplication (CBound 0))
                targetTerm))
    foundation <- expectRight Foundation.checkedFoundation
    let targetDefinitionImport =
            obviousImport (importIx 0) targetDefinition
        factDefinitionImport =
            obviousImport (importIx 1) factDefinition
        targetView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView
                targetDefinitionImport
        factView =
            obviousImportedDefinitionView
                subject kind factDefinitionImport
    proof <- expectRight
        (obviousProof
            defaultObviousBudget
            foundation
            globalType
            [fact, premise]
            []
            [factView, targetView]
            target)
    assertEqual
        (name <> " definition priority")
        (Set.singleton expectedImport)
        (obviousUsedImports proof)

prefersProofLocalDefinitionToExistentialSearch :: Assertion
prefersProofLocalDefinitionToExistentialSearch = do
    let factTerm = CApp (CGlobal factPredicateObject) empty
        targetTerm =
            CExists TySet
                (member (CBound 0) (CGlobal namedSetObject))
    fact <- checkedGlobalScoped [] factTerm
    target <- checkedGlobalScoped [] targetTerm
    definition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal factPredicateObject) (CBound 0))
                targetTerm))
    foundation <- expectRight Foundation.checkedFoundation
    let definitionImport = obviousImport (importIx 0) definition
        definitionView =
            obviousImportedDefinitionView
                factPredicateObject DefinitionPointwiseView
                definitionImport
    proof <- expectRight
        (obviousProof
            defaultObviousBudget
            foundation
            globalType
            [fact]
            []
            [definitionView]
            target)
    assertEqual
        "existential proof retains the defining equation"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

-- The subring proof uses a cited subset definition and a conjunction of
-- memberships. Uncited definitions of the ambient carrier must not preempt
-- that direct elimination with speculative term expansion.
eliminatesCitedPredicateDefinition :: Assertion
eliminatesCitedPredicateDefinition = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = replicate 3 TySet
        subset a b = CApp (CApp (CGlobal binaryPredicateObject) a) b
        members set = CAnd (member (CBound 2) set)
            (CAnd (member (CBound 1) set) (member (CBound 0) set))
        ambient = CGlobal namedSetObject
    hypotheses <- traverse (checkedGlobalScoped context)
        [subset empty ambient, members empty]
    target <- checkedGlobalScoped context (members ambient)
    definition <- checkedGlobalClosed
        (CForall TySet (CForall TySet
            (CEq TyProp (subset (CBound 1) (CBound 0))
                (CForall TySet
                    (CImp (member (CBound 0) (CBound 2))
                        (member (CBound 0) (CBound 1)))))))
    carrierDefinition <- checkedGlobalClosed
        (CEq TySet ambient (expensiveSet empty))
    let imported = obviousImport (importIx 0) definition
        carrierImport = obviousImport (importIx 1) carrierDefinition
        views =
            [ obviousImportedDefinitionView binaryPredicateObject
                DefinitionPointwiseView imported
            , obviousImportedDefinitionView namedSetObject
                DefinitionExactView carrierImport
            ]
        (statistics, result) = obviousProofDetailed
            (focusedBudget 100000) AnyObviousProof foundation globalType
            hypotheses [imported] views target
    proof <- expectRight result
    assertEqual "cited subset elimination stays in focused inference"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "the carrier definition is not proof authority"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        [imported, carrierImport] target proof

-- Reaching the conversion limit while constructing a definition view blocks
-- that candidate. Other checked views can still supply the conjuncts.
continuesNestedFactDefinitionsAfterConversionLimit :: Assertion
continuesNestedFactDefinitionsAfterConversionLimit = do
    foundation <- expectRight Foundation.checkedFoundation
    let first = CApp (CGlobal predicateObject) empty
        second = CApp (CGlobal factPredicateObject) empty
        third = CApp (CApp (CGlobal binaryPredicateObject) empty) empty
    hypotheses <- traverse (checkedGlobalScoped []) [first, second, third]
    target <- checkedGlobalScoped [] (CAnd membership otherMembership)
    definitions <- traverse checkedGlobalClosed
        [ CForall TySet (CEq TyProp
            (CApp (CGlobal predicateObject) (CBound 0))
            (expensiveProposition CFalsum))
        , CForall TySet (CEq TyProp
            (CApp (CGlobal factPredicateObject) (CBound 0)) membership)
        , CForall TySet (CForall TySet (CEq TyProp
            (CApp (CApp (CGlobal binaryPredicateObject) (CBound 1)) (CBound 0))
            otherMembership))
        ]
    let imports = zipWith obviousImport
            [importIx 0, importIx 1, importIx 2] definitions
        views = zipWith (\object imported ->
            obviousImportedDefinitionView object DefinitionPointwiseView imported)
            [predicateObject, factPredicateObject, binaryPredicateObject] imports
        (statistics, result) = obviousProofDetailed
            (focusedBudget 100000) AnyObviousProof foundation globalType
            hypotheses [] views target
    proof <- expectRight result
    assertBool "the failed construction's conversion work remains charged"
        (obviousConversionWorkConsumed statistics >= 2000000)
    assertEqual "only the successful fact definitions are proof authority"
        (Set.fromList [importIx 1, importIx 2]) (obviousUsedImports proof)
    assertEqual "the selected conjunct proofs cancel unfinished ground preparation"
        (ObviousTierCandidateBuilt, ObviousTierNotCompleted)
        (obviousFocusedTierOutcome statistics, obviousRefutationTierOutcome statistics)
    assertCandidateReplays foundation globalType hypotheses imports target proof

-- The free-module typing proof still needs fact elimination after recursive
-- goal expansion has exhausted an operation. Only that next, established rule gets
-- the continuation; recursive goal alternatives have already stopped.
eliminatesFactsAfterGoalExhaustion :: Assertion
eliminatesFactsAfterGoalExhaustion = do
    foundation <- expectRight Foundation.checkedFoundation
    let goal = CApp (CGlobal predicateObject) empty
        first = CApp (CGlobal factPredicateObject) empty
        second = CApp (CApp (CGlobal binaryPredicateObject) empty) empty
    hypotheses <- traverse (checkedGlobalScoped []) [first, second]
    target <- checkedGlobalScoped [] (CAnd goal otherMembership)
    definitions <- traverse checkedGlobalClosed
        [ CForall TySet (CEq TyProp
            (CApp (CGlobal predicateObject) (CBound 0))
            (expensiveProposition CFalsum))
        , CForall TySet (CEq TyProp
            (CApp (CGlobal factPredicateObject) (CBound 0)) goal)
        , CForall TySet (CForall TySet (CEq TyProp
            (CApp (CApp (CGlobal binaryPredicateObject) (CBound 1)) (CBound 0))
            otherMembership))
        ]
    let imports = zipWith obviousImport
            [importIx 0, importIx 1, importIx 2] definitions
        views = zipWith (\object imported ->
            obviousImportedDefinitionView object DefinitionPointwiseView imported)
            [predicateObject, factPredicateObject, binaryPredicateObject] imports
        (statistics, result) = obviousProofDetailed
            ((focusedBudget 100000) {obviousRefutationWorkLimit = 0}) AnyObviousProof foundation globalType
            hypotheses [] views target
    proof <- expectRight result
    assertEqual "fact elimination closes both conjunction components"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "exhausted goal definition contributes no authority"
        (Set.fromList [importIx 1, importIx 2]) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses imports target proof

-- Continuing into ordinary recursive fact search revives the product-ring
-- starvation: an exposed implication can start another large, unavailable
-- antecedent. The exhausted continuation must only reuse existing premises.
keepsExhaustedFactContinuationDirect :: Assertion
keepsExhaustedFactContinuationDirect = do
    foundation <- expectRight Foundation.checkedFoundation
    let goal term = CApp (CGlobal predicateObject) term
        fact term = CApp (CGlobal factPredicateObject) term
        missing term = CApp (CApp (CGlobal binaryPredicateObject) term) term
        conclusion term = CAnd (goal term) (member term term)
        large = foldr CAnd CFalsum (replicate 64 CTruth)
    hypotheses <- traverse (checkedGlobalScoped []) [membership, fact empty]
    target <- checkedGlobalScoped [] (conclusion empty)
    theorem <- checkedGlobalClosed
        (CForall TySet (CImp (member (CBound 0) empty)
            (conclusion (CBound 0))))
    definitions <- traverse checkedGlobalClosed
        [ CForall TySet (CEq TyProp (goal (CBound 0)) (expensiveProposition CFalsum))
        , CForall TySet (CEq TyProp (fact (CBound 0))
            (CImp (missing (CBound 0)) (goal (CBound 0))))
        , CForall TySet (CForall TySet (CEq TyProp
            (CApp (CApp (CGlobal binaryPredicateObject) (CBound 1)) (CBound 0))
            large))
        ]
    let imported = obviousImport (importIx 0) theorem
        definitionImports = zipWith obviousImport
            [importIx 1, importIx 2, importIx 3] definitions
        views = zipWith (\object equation ->
            obviousImportedDefinitionView object DefinitionPointwiseView equation)
            [predicateObject, factPredicateObject, binaryPredicateObject]
            definitionImports
        (statistics, result) = obviousProofDetailed
            (focusedBudget 20000) AnyObviousProof foundation globalType
            hypotheses [imported] views target
    proof <- expectRight result
    assertEqual "the enclosing theorem is reached without recursive fact search"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "only the cited theorem is needed"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        (imported : definitionImports) target proof

-- The second demand reuses the checked expansion of the same projected source
-- proof; all later semantic comparisons still consume the current pool.
reusesCheckedFactExpansions :: Assertion
reusesCheckedFactExpansions = do
    foundation <- expectRight Foundation.checkedFoundation
    let named = CGlobal namedSetObject
    fact <- checkedGlobalScoped [] (CAnd (member empty named) otherMembership)
    target <- checkedGlobalScoped [] (CAnd membership membership)
    equation <- checkedGlobalClosed (CEq TySet named empty)
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView namedSetObject DefinitionExactView imported
    forM_ [AnyObviousProof, MustUseCanonicalDefinition] \requirement -> do
        let (statistics, result) = obviousProofDetailed
                (focusedBudget 100000) requirement foundation globalType
                [fact] [] [view] target
        proof <- expectRight result
        let run budget = obviousProofDetailed budget requirement foundation globalType
                [fact] [] [view] target
            necessaryBudget = (focusedBudget 100000)
                {obviousConversionPool = Conversion.conversionPool 629}
            (_necessaryStatistics, necessaryResult) = run necessaryBudget
        -- A parallel exact probe can spend another 97 units after the checked
        -- expansion is available. Its failure remains charged, but neither it
        -- nor its complete allowance is needed by the retained conjunction.
        assertEqual "the ample run charges the unsuccessful exact probe"
            726 (obviousConversionWorkConsumed statistics)
        necessary <- expectRight necessaryResult
        assertCandidateReplays foundation globalType [fact] [imported] target necessary
        let focusedRun allowance = run allowance {obviousRefutationWorkLimit = 0}
            (focusedStatistics, focusedResult) = focusedRun necessaryBudget
        focusedProof <- expectRight focusedResult
        assertConversionPoolBoundary "necessary focused fact expansion work"
            focusedRun necessaryBudget focusedStatistics focusedProof
        let (groundStatistics, groundResult) = run ((focusedBudget 100000)
                {obviousConversionPool = Conversion.conversionPool 550})
        groundProof <- expectRight groundResult
        assertEqual "the smaller pool permits completion from the published fact"
            ObviousTierCandidateBuilt (obviousRefutationTierOutcome groundStatistics)
        assertCandidateReplays foundation globalType [fact] [imported] target groundProof
        let oneLess = (focusedBudget 100000)
                {obviousConversionPool = Conversion.conversionPool 725}
            (cappedStatistics, cappedResult) = run oneLess
        capped <- expectRight cappedResult
        assertEqual "the truncated failed probe is still debited" 725
            (obviousConversionWorkConsumed cappedStatistics)
        assertCandidateReplays foundation globalType [fact] [imported] target capped
        assertEqual "reuse retains the defining equation's authority"
            (Set.singleton (importIx 0)) (obviousUsedImports proof)
        assertCandidateReplays foundation globalType [fact] [imported] target proof

-- Similar hypotheses in sibling implication contexts own different source
-- keys. Reusing the first branch's checked proof would cross a proof boundary.
separatesFactExpansionContexts :: Assertion
separatesFactExpansionContexts = do
    foundation <- expectRight Foundation.checkedFoundation
    let named = CGlobal namedSetObject
        one = pair empty empty
        implication element = CImp (member element named) (member element empty)
    target <- checkedGlobalScoped [] (CAnd (implication empty) (implication one))
    equation <- checkedGlobalClosed (CEq TySet named empty)
    let imported = obviousImport (importIx 0) equation
        view = obviousImportedDefinitionView namedSetObject DefinitionExactView imported
        run budget = obviousProofDetailed budget
            AnyObviousProof foundation globalType [] [] [view] target
        (statistics, result) = run (focusedBudget 100000)
    proof <- expectRight result
    assertConversionPoolBoundary "distinct sibling proof contexts"
        run (focusedBudget 100000) statistics proof
    assertCandidateReplays foundation globalType [] [imported] target proof

assemblesCitedConjunctionPremise :: Assertion
assemblesCitedConjunctionPremise = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = replicate 4 TySet
        property x y = CApp (CApp (CGlobal binaryPredicateObject) x) y
        comparison x y = CApp (CGlobal predicateObject) (pair x y)
    hypotheses <- traverse (checkedGlobalScoped context)
        [ property (CBound 3) (CBound 2)
        , member (CBound 1) (CBound 3)
        , member (CBound 0) (CBound 2)
        ]
    target <- checkedGlobalScoped context (comparison (CBound 1) (CBound 0))
    definition <- checkedGlobalClosed
        (CForall TySet (CForall TySet
            (CEq TyProp (property (CBound 1) (CBound 0))
                (nestedBeta 1 (CForall TySet (CForall TySet
                    (CImp (CAnd (member (CBound 1) (CBound 3))
                            (member (CBound 0) (CBound 2)))
                        (comparison (CBound 1) (CBound 0)))))))))
    comparisonDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp (CApp (CGlobal predicateObject) (CBound 0))
                (expensiveProposition CFalsum)))
    let imported = obviousImport (importIx 0) definition
        comparisonImport = obviousImport (importIx 1) comparisonDefinition
        views =
            [ obviousImportedDefinitionView binaryPredicateObject
                DefinitionPointwiseView imported
            , obviousImportedDefinitionView predicateObject
                DefinitionPointwiseView comparisonImport
            ]
        (statistics, result) = obviousProofDetailed
            (focusedBudget 100000) AnyObviousProof foundation globalType
            hypotheses [imported] views target
    proof <- expectRight result
    assertBool "the retained direct conjunction finishes before full goal-view preparation"
        (obviousConversionWorkConsumed statistics < 10000)
    assertEqual "conjunction assembly stays in the direct focused path"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "the comparison definition is not needed"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        [imported, comparisonImport] target proof

-- The order-type inference x in A, A subset B |- x in B leaves A
-- undetermined by the cited conclusion. Matching one whole conjunction misses
-- the instance even when each component has direct checked evidence.
joinsOpenConjunctionPremises :: Assertion
joinsOpenConjunctionPremises = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = replicate 3 TySet
        subset smaller larger = CApp (CApp (CGlobal binaryPredicateObject) smaller) larger
        x = CBound 2
        a = CBound 1
        b = CBound 0
        joined = CAnd (member x a) (subset a b)
        cases =
            [ ("separate facts", [member x a, subset a b], [0, 1])
            , ("backtracking through a projected fact",
                [member x empty, CAnd (member x a) CTruth, subset a b], [1, 2])
            , ("whole fact retains priority",
                [member x a, subset a b, joined], [2])
            ]
    theorem <- checkedGlobalClosed
        (CForall TySet (CForall TySet (CForall TySet
            (CImp (CAnd (member (CBound 2) (CBound 1))
                    (subset (CBound 1) (CBound 0)))
                (member (CBound 2) (CBound 0))))))
    target <- checkedGlobalScoped context (member x b)
    let imported = obviousImport (importIx 0) theorem
    replayImport <- expectRight (derivationImportJudgement theorem)
    forM_ cases $ \(label, terms, usedHypotheses) -> do
        hypotheses <- traverse (checkedGlobalScoped context) terms
        let budget = (focusedBudget 10000) {obviousRefutationWorkLimit = 0}
            run allowance = obviousProofDetailed allowance AnyObviousProof
                foundation globalType hypotheses [imported] [] target
            (statistics, result) = run budget
        proof <- expectRight result
        assertEqual (label <> " closes in focused inference")
            ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
        replayed <- expectRight
            (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                globalType (Vector.singleton replayImport)
                (Vector.fromList hypotheses) target
                (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
        assertEqual (label <> " keeps exact hypothesis origins")
            (Set.fromList (map hypothesisIx usedHypotheses))
            (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual (label <> " uses only the cited theorem")
            (Set.singleton (importIx 0)) (replayedScopedKernelImportUses replayed)
        assertConversionPoolBoundary label run budget statistics proof

joinsInterleavedConjunctionPremises :: Assertion
joinsInterleavedConjunctionPremises = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = replicate 3 TySet
        predicate term = CApp (CGlobal predicateObject) term
        subset smaller larger = CApp (CApp (CGlobal binaryPredicateObject) smaller) larger
        x = CBound 2
        a = CBound 1
        b = CBound 0
    -- The first conjunction has only the x,A prefix; the B slot is introduced
    -- afterwards. Both early A choices satisfy it, but only the second choice
    -- satisfies the later premise. Its failure must backtrack the whole join.
    hypotheses <- traverse (checkedGlobalScoped context)
        [ member x empty, predicate empty, member x a, predicate a, subset a b ]
    theorem <- checkedGlobalClosed
        (CForall TySet (CForall TySet
            (CImp (CAnd (member (CBound 1) (CBound 0)) (predicate (CBound 0)))
                (CForall TySet
                    (CImp (subset (CBound 1) (CBound 0))
                        (member (CBound 2) (CBound 0)))))))
    target <- checkedGlobalScoped context (member x b)
    let imported = obviousImport (importIx 0) theorem
        (statistics, result) = obviousProofDetailed
            ((focusedBudget 10000) {obviousRefutationWorkLimit = 0})
            AnyObviousProof foundation globalType hypotheses [imported] [] target
    proof <- expectRight result
    assertEqual "interleaved joining closes in focused inference"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    replayImport <- expectRight (derivationImportJudgement theorem)
    replayed <- expectRight
        (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            globalType (Vector.singleton replayImport) (Vector.fromList hypotheses)
            target (KernelProof.builtProofDerivation (obviousBuiltProof proof)))
    assertEqual "backtracking discards the earlier conjunction's dependencies"
        (Set.fromList [hypothesisIx 2, hypothesisIx 3, hypothesisIx 4])
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "interleaved joining keeps the cited authority"
        (Set.singleton (importIx 0)) (replayedScopedKernelImportUses replayed)

retainsJoinedConjunctionAuthority :: Assertion
retainsJoinedConjunctionAuthority = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TySet, TySet]
        predicate term = CApp (CGlobal predicateObject) term
        result term = CApp (CGlobal factPredicateObject) term
    hypotheses <- traverse (checkedGlobalScoped context)
        [predicate (CBound 1), CEq TySet (CBound 1) empty]
    target <- checkedGlobalScoped context (result (CBound 0))
    forM_ [CAnd, flip CAnd] $ \conjoin -> do
        theorem <- checkedGlobalClosed
            (CForall TySet (CForall TySet
                (CImp (conjoin (predicate (CBound 1)) (CEq TySet (CBound 1) empty))
                    (result (CBound 0)))))
        let imported = obviousImport (importIx 0) theorem
            run views = obviousProofDetailed
                ((focusedBudget 10000) {obviousRefutationWorkLimit = 0})
                MustUseCanonicalDefinition foundation globalType
                hypotheses [imported] views target
            (statistics, found) = run [obviousLocalDefinitionView 1 DefinitionExactView]
        proof <- expectRight found
        assertEqual "either conjunct can supply the required definition origin"
            ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
        assertCandidateReplays foundation globalType hypotheses [imported] target proof
        -- The unrestricted join determines the parameters, but its completed
        -- proof cannot supply a canonical certificate without the view.
        assertFailureKind "ordinary conjunction evidence cannot mint definition authority"
            ObviousCanonicalDefinitionEvidenceRequired (snd (run []))

-- Product-ring reindexing cites a theorem for the whole conjunction. If
-- splitting it exhausts an operation, nested definition alternatives must return to
-- that enclosing application before consuming the remaining focused work.
returnsNestedDefinitionExhaustion :: Assertion
returnsNestedDefinitionExhaustion = do
    foundation <- expectRight Foundation.checkedFoundation
    let predicate term = CApp (CGlobal predicateObject) term
        conclusion term = CAnd (predicate term) (member term term)
        large = foldr CAnd CFalsum (replicate 64 CTruth)
    premise <- checkedGlobalScoped [] membership
    target <- checkedGlobalScoped [] (conclusion empty)
    theorem <- checkedGlobalClosed
        (CForall TySet (CImp (member (CBound 0) empty)
            (conclusion (CBound 0))))
    definitions <- traverse checkedGlobalClosed
        [ CForall TySet (CEq TyProp (predicate (CBound 0)) body)
        | body <- [expensiveProposition CFalsum, large]
        ]
    let imported = obviousImport (importIx 0) theorem
        definitionImports = zipWith obviousImport
            [importIx 1, importIx 2] definitions
        views = map (obviousImportedDefinitionView predicateObject
            DefinitionPointwiseView) definitionImports
        (statistics, result) = obviousProofDetailed
            (focusedBudget 12000) AnyObviousProof foundation globalType
            [premise] [imported] views target
    proof <- expectRight result
    assertEqual "the enclosing conjunction theorem remains reachable"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "failed definition alternatives are not authority"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType [premise]
        (imported : definitionImports) target proof

-- In the EDM proof, the conclusion determines z but leaves A open in
-- Ordinal(A) -> z in A -> Ordinal(z). An earlier ordinal must not trigger
-- speculative membership proof search before the witnessed later one is tried.
choosesSupportedTheoremBinding :: Assertion
choosesSupportedTheoremBinding = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = replicate 3 TySet
        predicate term = CApp (CGlobal predicateObject) term
        relation x y = CApp (CApp (CGlobal binaryPredicateObject) x) y
        a = CBound 2
        b = CBound 1
        z = CBound 0
    hypotheses <- traverse (checkedGlobalScoped context)
        [predicate a, predicate b, relation z b]
    target <- checkedGlobalScoped context (predicate z)
    theorem <- checkedGlobalClosed
        (CForall TySet (CForall TySet
            (CImp (predicate (CBound 1))
                (CImp (relation (CBound 0) (CBound 1))
                    (predicate (CBound 0))))))
    definition <- checkedGlobalClosed
        (CForall TySet (CForall TySet
            (CEq TyProp (relation (CBound 1) (CBound 0))
                (expensiveProposition CFalsum))))
    let imported = obviousImport (importIx 0) theorem
        definitionImport = obviousImport (importIx 1) definition
        view = obviousImportedDefinitionView binaryPredicateObject
            DefinitionPointwiseView definitionImport
        (statistics, result) = obviousProofDetailed
            (focusedBudget 100000) AnyObviousProof foundation globalType
            hypotheses [imported] [view] target
    proof <- expectRight result
    assertEqual "the witnessed instance closes in focused inference"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "only the stated theorem supports the conclusion"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertBool "the later witness precedes irrelevant conversion"
        (obviousConversionWorkConsumed statistics < 10000)
    assertCandidateReplays foundation globalType hypotheses
        [imported, definitionImport] target proof

prefersLocalTheoremBeforeSpeculativeCitation :: Assertion
prefersLocalTheoremBeforeSpeculativeCitation = do
    foundation <- expectRight Foundation.checkedFoundation
    let predicate object term = CApp (CGlobal object) term
        context = [TySet, TySet]
    hypotheses <- traverse (checkedGlobalScoped context)
        [ CForall TySet (predicate predicateObject (CBound 0))
        , CEq TySet (CBound 1) empty
        ]
    target <- checkedGlobalScoped context (predicate predicateObject (CBound 0))
    theorem <- checkedGlobalClosed
        (CForall TySet (CImp (predicate factPredicateObject (CBound 0))
            (predicate predicateObject (CBound 0))))
    definition <- checkedGlobalClosed
        (CForall TySet (CEq TyProp (predicate factPredicateObject (CBound 0))
            (member (expensiveSet empty) empty)))
    let theoremImport = obviousImport (importIx 0) theorem
        definitionImport = obviousImport (importIx 1) definition
        views =
            [ obviousLocalDefinitionView 1 DefinitionExactView
            , obviousImportedDefinitionView factPredicateObject
                DefinitionPointwiseView definitionImport
            ]
    proof <- expectRight
        (obviousProof (focusedBudget 1000000) foundation globalType
            hypotheses [theoremImport] views target)
    assertEqual "direct local theorem precedes speculative cited premises"
        Set.empty (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        [theoremImport, definitionImport] target proof

introducesConjunctionBeforeSpeculativeTheorem :: Assertion
introducesConjunctionBeforeSpeculativeTheorem = do
    foundation <- expectRight Foundation.checkedFoundation
    let predicate object term = CApp (CGlobal object) term
        conjunction term = CAnd (predicate predicateObject term) (member term empty)
        context = [TySet]
    hypotheses <- traverse (checkedGlobalScoped context)
        [ CForall TySet (CImp (predicate factPredicateObject (CBound 0))
            (conjunction (CBound 0)))
        , predicate predicateObject empty
        , membership
        , CEq TySet (CBound 0) empty
        ]
    target <- checkedGlobalScoped context (conjunction empty)
    definition <- checkedGlobalClosed
        (CForall TySet (CEq TyProp (predicate factPredicateObject (CBound 0))
            (member (expensiveSet empty) empty)))
    let definitionImport = obviousImport (importIx 0) definition
        views =
            [ obviousLocalDefinitionView 3 DefinitionExactView
            , obviousImportedDefinitionView factPredicateObject
                DefinitionPointwiseView definitionImport
            ]
        (_statistics, result) = obviousProofDetailed
            (focusedBudget 1000000) AnyObviousProof foundation globalType
            hypotheses [] views target
    proof <- expectRight result
    assertEqual "the speculative predicate definition is unused"
        Set.empty (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        [definitionImport] target proof

findsDirectDefinitionAfterUnavailablePremise :: Assertion
findsDirectDefinitionAfterUnavailablePremise = do
    foundation <- expectRight Foundation.checkedFoundation
    let fixture = globalTypingFixture (replicate 4 (TyArrow TySet TyProp))
        typing = fixtureGlobalTyping fixture
    case fixtureObjectIds fixture of
        [p, q, r, s] -> do
            let predicate object term = CApp (CGlobal object) term
                checked = expectRight . checkCanonicalCore typing
                scoped = expectRight . checkScopedCanonicalCore typing []
                definition object body =
                    CForall TySet (CEq TyProp (predicate object (CBound 0)) body)
            forM_ [CExists TySet (predicate p (CBound 0)), membership] \targetTerm -> do
                hypotheses <- traverse scoped [predicate q empty, predicate s empty]
                target <- scoped targetTerm
                conditional <- checked (definition q
                    (CImp (predicate r (CBound 0)) targetTerm))
                direct <- checked (definition s targetTerm)
                unavailable <- checked (definition r
                    (expensiveProposition CFalsum))
                let imports = zipWith obviousImport (map importIx [0, 1, 2])
                        [conditional, direct, unavailable]
                    views = zipWith
                        (\object -> obviousImportedDefinitionView object DefinitionPointwiseView)
                        [q, s, r] imports
                proof <- expectRight
                    (obviousProof (focusedBudget 1000000) foundation typing
                        hypotheses [] views target)
                assertEqual "direct definition evidence survives an unavailable premise"
                    (Set.singleton (importIx 1)) (obviousUsedImports proof)
                assertCandidateReplays foundation typing hypotheses imports target proof
        _ -> assertFailure "the predicate fixture changed arity"

keepsUnrelatedPredicateDefinitionsBehindGoalEvidence :: Assertion
keepsUnrelatedPredicateDefinitionsBehindGoalEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let predicate object term = CApp (CGlobal object) term
        targetTerm = predicate predicateObject empty
    fact <- checkedGlobalScoped [] (predicate factPredicateObject empty)
    premise <- checkedGlobalScoped [] membership
    target <- checkedGlobalScoped [] targetTerm
    factDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp (predicate factPredicateObject (CBound 0))
                (CAnd
                    (predicate predicateObject
                        (expensiveSet (pair empty empty)))
                    CTruth)))
    goalDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp (predicate predicateObject (CBound 0)) membership))
    let factImport = obviousImport (importIx 0) factDefinition
        goalImport = obviousImport (importIx 1) goalDefinition
        hypotheses = [fact, premise]
        views =
            [ obviousImportedDefinitionView factPredicateObject
                DefinitionPointwiseView factImport
            , obviousImportedDefinitionView predicateObject
                DefinitionPointwiseView goalImport
            ]
    proof <- expectRight
        (obviousProof (focusedBudget 1000000) foundation globalType
            hypotheses [] views target)
    assertEqual "an unrelated projected fact cannot starve goal evidence"
        (Set.singleton (importIx 1)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        [factImport, goalImport] target proof

-- The reciprocal regression arose from speculative conversion inside G's
-- application congruence. A lexical membership law keeps exact conversion
-- deferred, while an unrelated argument under the same predicate head must
-- not consume the contraction needed by the goal-definition proof.
keepsComposedTransportStructural :: Assertion
keepsComposedTransportStructural = do
    foundation <- expectRight Foundation.checkedFoundation
    let fixture = globalTypingFixture
            [TyArrow TySet (TyArrow TySet TyProp), TySet]
        typing = fixtureGlobalTyping fixture
    case fixtureObjectIds fixture of
        [p, named] -> do
            let predicate object x y = CApp (CApp (CGlobal object) x) y
                scoped = expectRight . checkScopedCanonicalCore typing [TySet]
            hypotheses <- traverse scoped
                [ predicate p (expensiveSet (pair empty empty)) empty
                , otherMembership
                , CForall TySet
                    (CEq TyProp (member (CBound 0) (CBound 1)) CTruth)
                , CEq TySet (CGlobal named) empty
                ]
            target <- scoped (predicate p empty empty)
            definition <- expectRight (checkCanonicalCore typing
                (CForall TySet (CForall TySet
                    (CEq TyProp (predicate p (CBound 1) (CBound 0))
                        (nestedBeta 1 otherMembership)))))
            let imported = obviousImport (importIx 0) definition
                view = obviousImportedDefinitionView p DefinitionPointwiseView imported
                (statistics, result) = obviousProofDetailed
                    (focusedBudget 1000000) AnyObviousProof foundation typing
                    hypotheses []
                    [view, obviousLocalDefinitionView 2 DefinitionMembershipView]
                    target
            proof <- expectRight result
            assertBool "the intended transport finishes before a full-effort irrelevant operation"
                (obviousConversionWorkConsumed statistics < 10000)
            assertEqual "goal evidence remains available to focused inference"
                ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
            assertEqual "transport speculation leaves goal evidence available"
                (Set.singleton (importIx 0)) (obviousUsedImports proof)
            assertCandidateReplays foundation typing hypotheses [imported] target proof
        _ -> assertFailure "the binary predicate fixture changed arity"

-- The group-library regressions appeared when term definitions in local
-- equalities/memberships were promoted ahead of goal definition evidence.
-- Keep the unrelated term expansion costly, without changing the search limits.
appliesCitedTheoremThroughAliasBeforeTermExpansion :: Assertion
appliesCitedTheoremThroughAliasBeforeTermExpansion = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TySet]
        predicate object term = CApp (CGlobal object) term
        alias = CBound 0
    hypotheses <- traverse (checkedGlobalScoped context)
        [ CEq TySet (CGlobal namedSetObject) empty
        , membership
        , CEq TySet alias empty
        ]
    theorem <- checkedGlobalClosed
        (CForall TySet
            (CImp (predicate factPredicateObject (CBound 0))
                (predicate predicateObject (CBound 0))))
    premiseDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp (predicate factPredicateObject (CBound 0))
                (member (CBound 0) empty)))
    termDefinition <- checkedGlobalClosed
        (CEq TySet (CGlobal namedSetObject) (expensiveSet empty))
    target <- checkedGlobalScoped context (predicate predicateObject alias)
    let imports = [obviousImport (importIx 0) theorem]
        premiseImport = obviousImport (importIx 1) premiseDefinition
        termImport = obviousImport (importIx 2) termDefinition
        views =
            [ obviousImportedDefinitionView factPredicateObject
                DefinitionPointwiseView premiseImport
            , obviousImportedDefinitionView namedSetObject
                DefinitionExactView termImport
            , obviousLocalDefinitionView 2 DefinitionExactView
            ]
    let (_statistics, result) = obviousProofDetailed
            (focusedBudget 1000000) AnyObviousProof foundation globalType
            hypotheses imports views target
    proof <- expectRight result
    assertEqual "only the cited rule and its premise definition are used"
        (Set.fromList [importIx 0, importIx 1]) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        (imports <> [premiseImport, termImport]) target proof

composesEqualityBeforeUnrelatedSetExpansion :: Assertion
composesEqualityBeforeUnrelatedSetExpansion = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = [TySet, TySet, TySet]
        a = CBound 2
        b = CBound 1
        c = CBound 0
    hypotheses <- traverse (checkedGlobalScoped context)
        [ member empty (CGlobal namedSetObject)
        , CEq TySet a b
        , CEq TySet b c
        ]
    functionDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TySet (CApp (CGlobal functionObject) (CBound 0))
                (pair (CBound 0) empty)))
    setDefinition <- checkedGlobalClosed
        (CEq TySet (CGlobal namedSetObject) (expensiveSet empty))
    target <- checkedGlobalScoped context
        (CEq TySet (CApp (CGlobal functionObject) a) (pair c empty))
    let functionImport = obviousImport (importIx 0) functionDefinition
        setImport = obviousImport (importIx 1) setDefinition
        views =
            [ obviousImportedDefinitionView functionObject
                DefinitionPointwiseView functionImport
            , obviousImportedDefinitionView namedSetObject
                DefinitionExactView setImport
            ]
    let (_statistics, result) = obviousProofDetailed
            (focusedBudget 1000000) AnyObviousProof foundation globalType
            hypotheses [] views target
    proof <- expectRight result
    assertEqual "congruence uses the goal's definition only"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        [functionImport, setImport] target proof

reversesCitedEqualityInLexicalContext :: Assertion
reversesCitedEqualityInLexicalContext = do
    foundation <- expectRight Foundation.checkedFoundation
    let context = replicate 4 TySet
        a = CBound 3
        b = CBound 2
        c = CBound 1
    hypotheses <- traverse (checkedGlobalScoped context)
        [ CEq TySet (CGlobal namedSetObject) empty
        , CEq TySet (CBound 0) empty
        ]
    theorem <- checkedGlobalClosed
        (CForall TySet (CForall TySet (CForall TySet
            (CEq TySet (pair (pair (CBound 2) (CBound 1)) (CBound 0))
                (pair (CBound 2) (pair (CBound 1) (CBound 0)))))))
    termDefinition <- checkedGlobalClosed
        (CEq TySet (CGlobal namedSetObject) (nestedSetBeta 2 empty))
    target <- checkedGlobalScoped context
        (CEq TySet (pair a (pair b c)) (pair (pair a b) c))
    let imports = [obviousImport (importIx 0) theorem]
        termImport = obviousImport (importIx 1) termDefinition
        views =
            [ obviousImportedDefinitionView namedSetObject
                DefinitionExactView termImport
            , obviousLocalDefinitionView 1 DefinitionExactView
            ]
        (statistics, result) = obviousProofDetailed
            (focusedBudget 1000000) AnyObviousProof foundation globalType
            hypotheses imports views target
    proof <- expectRight result
    assertEqual "symmetry retains exactly the cited equality theorem"
        (Set.singleton (importIx 0)) (obviousUsedImports proof)
    assertCandidateReplays foundation globalType hypotheses
        (imports <> [termImport]) target proof
    assertConversionPoolBoundary "reversed cited equality"
        (\budget -> obviousProofDetailed budget AnyObviousProof foundation globalType
            hypotheses imports views target)
        (focusedBudget 1000000) statistics proof

prefersSyntacticExactBeforeConversion :: Assertion
prefersSyntacticExactBeforeConversion = do
    let targetTerm = CApp (CGlobal predicateObject) empty
        conversionTrap =
            CApp
                (CGlobal predicateObject)
                (nestedSetBeta 2 (pair empty empty))
    target <- checkedGlobalScoped [] targetTerm
    trap <- checkedGlobalScoped [] conversionTrap
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            (focusedBudget 100000)
            foundation globalType [trap, target] [] [] target)
    assertEqual
        "the exact later fact is reused without spending conversion budget"
        target
        (KernelProof.builtProofStatement (obviousBuiltProof proof))

-- Recursive use of the first source would consume the conversion pool. The
-- later witnessed source gets a direct opportunity in every association of
-- the same written leaves, and replay must select its real authority.
discoversWitnessedSourcesBeforeRecursion :: Assertion
discoversWitnessedSourcesBeforeRecursion = do
    foundation <- expectRight Foundation.checkedFoundation
    let p = CApp (CGlobal predicateObject) empty
        q = CApp (CGlobal factPredicateObject) empty
        bad = CImp (expensiveProposition CFalsum) p
        middle = CImp p otherMembership
        good = CImp q p
        budget = (focusedBudget 100000)
            { obviousRefutationWorkLimit = 0
            , obviousConversionPool = Conversion.conversionPool 50000 }
    target <- checkedGlobalScoped [] p
    for_ [ ([bad, middle, good, q], [2, 3])
         , ([CAnd bad (CAnd middle good), q], [0, 1])
         , ([CAnd (CAnd bad middle) good, q], [0, 1])
         ] \(terms, expected) -> do
        checked <- traverse checkedGlobalClosed terms
        let imports = zipWith obviousImport (importIx <$> [0 ..]) checked
            run = obviousProofDetailed budget AnyObviousProof
                foundation globalType [] imports [] target
            (statistics, result) = run
        proof <- expectRight result
        assertEqual "only the witnessed source and premise are selected"
            (Set.fromList (importIx <$> expected)) (obviousUsedImports proof)
        assertBool "the ready application finishes before the recursive conversion consumes the pool"
            (obviousConversionWorkConsumed statistics < 50000)
        assertCandidateReplays foundation globalType [] imports target proof

preservesDirectCandidateOrder :: Assertion
preservesDirectCandidateOrder = do
    foundation <- expectRight Foundation.checkedFoundation
    let p = CApp (CGlobal predicateObject)
    target <- checkedGlobalScoped [] (p empty)
    earlier <- checkedGlobalClosed (p (nestedSetBeta 1 empty))
    literal <- checkedGlobalClosed (p empty)
    unrelated <- checkedGlobalScoped [] (CEq TySet (CGlobal namedSetObject) empty)
    let imports = [obviousImport (importIx 0) earlier, obviousImport (importIx 1) literal]
    for_ [[], [obviousLocalDefinitionView 0 DefinitionExactView]] \views -> do
        proof <- expectRight (obviousProof (focusedBudget 100000)
            foundation globalType [unrelated] imports views target)
        assertEqual "the earlier convertible candidate remains first"
            (Set.singleton (importIx 0)) (obviousUsedImports proof)
        assertCandidateReplays foundation globalType [unrelated] imports target proof

escalatesDirectPreparation :: Assertion
escalatesDirectPreparation = do
    foundation <- expectRight Foundation.checkedFoundation
    let p = CApp (CGlobal predicateObject)
        earlierTerm = p (nestedSetBeta 128 empty)
    target <- checkedGlobalScoped [] (p empty)
    earlierScoped <- checkedGlobalScoped [] earlierTerm
    earlier <- checkedGlobalClosed earlierTerm
    literal <- checkedGlobalClosed (p empty)
    let firstSource = obviousImport (importIx 0) earlier
        literalSource = obviousImport (importIx 1) literal
        fullCost = Conversion.conversionCostAmount (Conversion.conversionCost
            (Conversion.convertibleChecked globalType (Conversion.conversionLimit 2000000) earlierScoped target))
        run imports = obviousProofDetailed (focusedBudget 100000) AnyObviousProof
            foundation globalType [] imports [] target
    assertBool "the unchanged converter needs more than the initial 512-unit policy slice" (fullCost > 512)
    let (cheapStatistics, cheapResult) = run [firstSource, literalSource]
    cheap <- expectRight cheapResult
    assertEqual "later literal evidence precedes the deferred full-effort candidate"
        (Set.singleton (importIx 1)) (obviousUsedImports cheap)
    assertEqual "the failed preparatory probe remains charged" 512
        (obviousConversionWorkConsumed cheapStatistics)
    assertCandidateReplays foundation globalType [] [firstSource, literalSource] target cheap
    let (fullStatistics, fullResult) = run [firstSource]
    full <- expectRight fullResult
    assertEqual "the original candidate remains reachable after escalation"
        (Set.singleton (importIx 0)) (obviousUsedImports full)
    assertEqual "the successful retry pays both executions" (512 + fullCost)
        (obviousConversionWorkConsumed fullStatistics)
    assertCandidateReplays foundation globalType [] [firstSource] target full
    let runPool amount = obviousProofDetailed
            ((focusedBudget 100000) {obviousRefutationWorkLimit = 0, obviousConversionPool = Conversion.conversionPool amount})
            AnyObviousProof foundation globalType [] [firstSource] [] target
    for_ [1023, 1024] \amount -> do
        let (statistics, result) = runPool amount
        assertFailureKind "a retry must receive strictly more than the earlier effective allowance"
            (ObviousResourceExhausted ObviousConversionPoolLimit) result
        assertEqual "a refused same/smaller retry performs no conversion" 512
            (obviousConversionWorkConsumed statistics)
    let (exactStatistics, exactResult) = runPool (512 + fullCost)
        (shortStatistics, shortResult) = runPool (512 + fullCost - 1)
    exact <- expectRight exactResult
    assertCandidateReplays foundation globalType [] [firstSource] target exact
    assertEqual "the full retry can finish at exact pool equality" (512 + fullCost)
        (obviousConversionWorkConsumed exactStatistics)
    assertFailureKind "one short is real pool exhaustion, not another policy retry"
        (ObviousResourceExhausted ObviousConversionPoolLimit) shortResult
    assertEqual "the failed larger retry remains charged" (512 + fullCost - 1)
        (obviousConversionWorkConsumed shortStatistics)

retainsTheoremPreparation :: Assertion
retainsTheoremPreparation = do
    foundation <- expectRight Foundation.checkedFoundation
    let p = CApp (CGlobal predicateObject)
        targetTerm = p empty
        nestedProposition = foldr (\_ body -> CApp (CLam TyProp (CBound 0)) body)
            (CImp membership targetTerm) [1 .. 128 :: Int]
        nestedTail = foldr (\_ body -> CApp (CLam TyProp (CBound 0)) body)
            targetTerm [1 .. 128 :: Int]
        cases =
            [ ("exposure", nestedProposition)
            , ("spine", CImp membership nestedTail)
            , ("matching", CImp membership (p (nestedSetBeta 128 empty)))
            ]
    fact <- checkedGlobalScoped [] membership
    target <- checkedGlobalScoped [] targetTerm
    later <- checkedGlobalClosed (CImp membership targetTerm)
    for_ cases \(label, entered) -> do
        first <- checkedGlobalClosed entered
        let earlier = obviousImport (importIx 0) first
            witness = obviousImport (importIx 1) later
            run imports = obviousProofDetailed
                ((focusedBudget 100000) {obviousRefutationWorkLimit = 0})
                AnyObviousProof foundation globalType [fact] imports [] target
            (cheapStatistics, cheapResult) = run [earlier, witness]
        cheap <- expectRight cheapResult
        assertEqual (label <> ": the later supplied witness precedes the full retry")
            (Set.singleton (importIx 1)) (obviousUsedImports cheap)
        assertBool (label <> ": preparation is bounded before the witness")
            (obviousConversionWorkConsumed cheapStatistics < 10000)
        assertCandidateReplays foundation globalType [fact] [earlier, witness] target cheap
        let (fullStatistics, fullResult) = run [earlier]
        full <- expectRight fullResult
        assertBool (label <> ": completion requires escalation")
            (obviousConversionWorkConsumed fullStatistics > 512)
        assertEqual (label <> ": the retained source supplies the proof")
            (Set.singleton (importIx 0)) (obviousUsedImports full)
        assertCandidateReplays foundation globalType [fact] [earlier] target full

-- Finite interleaving cancels two successors after composing a supplied
-- equality chain. Its local induction class is also available, but expanding
-- that class must not start a new recursive tree before the chain is used.
composesBeforeRecursiveCancellation :: Assertion
composesBeforeRecursiveCancellation = do
    foundation <- expectRight Foundation.checkedFoundation
    let fixture = globalTypingFixture [TyArrow TySet (TyArrow TySet TySet), TyArrow TySet TySet, TySet]
        typing = fixtureGlobalTyping fixture
    (additionObject, successorObject, naturalsObject) <- case fixtureObjectIds fixture of
        [addition, successor, naturals] -> pure (addition, successor, naturals)
        _ -> assertFailure "cancellation fixture globals changed arity"
    let add x y = CApp (CApp (CGlobal additionObject) x) y
        double x = add x x
        successor x = CApp (CGlobal successorObject) x
        twice = successor . successor
        natural x = member x (CGlobal naturalsObject)
        context = replicate 4 TySet
        inductionClass = CBound 3
        k = CBound 2
        l = CBound 1
        q = CBound 0
        inductionBody = CForall TySet (CImp (natural (CBound 0))
            (CImp (CEq TySet (double (CBound 1)) (double (CBound 0)))
                (CEq TySet (CBound 1) (CBound 0))))
        terms =
            [ CForall TySet (CEq TyProp (member (CBound 0) (CBound 4))
                (CAnd (natural (CBound 0)) inductionBody))
            , CEq TySet inductionClass (CApp (CApp (CIntrinsic Sep) (CGlobal naturalsObject))
                (CLam TySet inductionBody))
            , member empty inductionClass
            , member k inductionClass
            , natural k
            , natural (successor k)
            , natural l
            , CEq TySet (double (successor k)) (double l)
            , CAnd (natural q) (CEq TySet l (successor q))
            , CAnd (CEq TySet (double (successor k)) (twice (double k)))
                (CEq TySet (double l) (twice (double q)))
            ]
    facts <- traverse (expectRight . checkScopedCanonicalCore typing context) terms
    injective <- expectRight (checkCanonicalCore typing (CForall TySet (CForall TySet
        (CImp (CEq TySet (successor (CBound 1)) (successor (CBound 0)))
            (CEq TySet (CBound 1) (CBound 0))))))
    target <- expectRight (checkScopedCanonicalCore typing context (CEq TySet (double k) (double q)))
    let imported = obviousImport (importIx 0) injective
        views = [obviousLocalDefinitionView 0 DefinitionMembershipView, obviousLocalDefinitionView 1 DefinitionExactView]
        (statistics, result) = obviousProofDetailed
            defaultObviousBudget {obviousRefutationWorkLimit = 0}
            AnyObviousProof foundation typing facts [imported] views target
    proof <- expectRight result
    assertCandidateReplays foundation typing facts [imported] target proof
    assertBool "the supplied chain precedes induction-class expansion and deeper recursion"
        (obviousFocusedWorkConsumed statistics < 100000)
    -- The preceding Take step in set/finite-interleave.tex needs the original
    -- ground query's disjunction, not a larger domain for the induction class.
    predecessorCases <- expectRight (checkCanonicalCore typing (CForall TySet
        (CImp (natural (CBound 0)) (COr (CEq TySet (CBound 0) empty)
            (CExists TySet (CAnd (natural (CBound 0)) (CEq TySet (CBound 1) (successor (CBound 0)))))))))
    nonzero <- expectRight (checkScopedCanonicalCore typing context (CNot (CEq TySet l empty)))
    predecessor <- expectRight (checkScopedCanonicalCore typing context
        (CExists TySet (CAnd (natural (CBound 0)) (CEq TySet (CBound 2) (successor (CBound 0))))))
    let predecessorImport = obviousImport (importIx 0) predecessorCases
        predecessorFacts = take 8 facts <> [nonzero]
        (groundStatistics, groundResult) = obviousProofDetailed defaultObviousBudget AnyObviousProof
            foundation typing predecessorFacts [predecessorImport] views predecessor
    groundProof <- expectRight groundResult
    assertCandidateReplays foundation typing predecessorFacts [predecessorImport] predecessor groundProof
    -- Existing-witness search may spend work on a read-only body query as well.
    -- Its work belongs to the same pool; it must not authorize another selected
    -- induction-class domain. Check that boundary directly, not via total work.
    assertBool "speculative witnesses do not add induction-class domain starts"
        (obviousFactDomainsStarted groundStatistics <= 1)

isolatesGroundAdmissionAllowance :: Assertion
isolatesGroundAdmissionAllowance = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checkedScoped [] CTruth
    for_ [0, 1, 2] \work -> do
        let (statistics, result) = obviousProofDetailed
                defaultObviousBudget {obviousRefutationWorkLimit = work}
                AnyObviousProof foundation emptyGlobalTyping [] [] [] target
        proof <- expectRight result
        assertCandidateReplays foundation emptyGlobalTyping [] [] target proof
        assertEqual "an unavailable ground channel cannot stop focused construction"
            ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
        assertEqual "failed task admission is charged without borrowing focused work"
            work (obviousRefutationWorkConsumed statistics)
        assertEqual "partial scheduling cannot publish a query branch" 0
            (obviousBranchNodesCreated statistics)
    -- An exact comparison can exhaust conversion without making the already
    -- exposed logical problem unavailable to the ground structural owner.
    atom <- checkedScoped [] membership
    trap <- checkedScoped [] (member (nestedSetBeta 128 (pair empty empty)) empty)
    positive <- checkedScoped [] otherMembership
    negative <- checkedScoped [] (CNot otherMembership)
    let hypotheses = [trap, positive, negative]
        (statistics, result) = obviousProofDetailed
            defaultObviousBudget {obviousConversionPool = Conversion.conversionPool 16}
            AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] atom
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping hypotheses [] atom proof
    assertEqual "the failed exact comparison spends the true conversion pool" 16
        (obviousConversionWorkConsumed statistics)
    assertEqual "logical closure remains available with zero conversion remainder"
        ObviousTierCandidateBuilt (obviousRefutationTierOutcome statistics)

provesUniversalGroundResidual :: Assertion
provesUniversalGroundResidual = do
    foundation <- expectRight Foundation.checkedFoundation
    let body = member (pair (CBound 0) empty) empty
    target <- checkedScoped [] (CForall TySet (COr body (CNot body)))
    let (statistics, result) = obviousProofDetailed defaultObviousBudget AnyObviousProof
            foundation emptyGlobalTyping [] [] [] target
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping [] [] target proof
    assertEqual "the universal is reconstructed by focused introduction"
        ObviousTierCandidateBuilt (obviousFocusedTierOutcome statistics)
    assertEqual "its body closes through the owned ground service"
        ObviousTierCandidateBuilt (obviousRefutationTierOutcome statistics)
    assertBool "the extended family admits the eigenvariable application"
        (obviousTermsAdmitted statistics > 0)

separatesStructuralResidualQueries :: Assertion
separatesStructuralResidualQueries = do
    foundation <- expectRight Foundation.checkedFoundation
    for_ [CAnd (COr membership (CNot membership)) membership
         , CAnd (CImp membership membership) (CImp membership otherMembership)] \term -> do
        target <- checkedScoped [] term
        let (_statistics, result) = obviousProofDetailed defaultObviousBudget AnyObviousProof
                foundation emptyGlobalTyping [] [] [] target
        case result of
            Right _ -> assertFailure "a structural sibling inherited seed assertions or another query's assumptions"
            Left ObviousResourceExhausted{} -> assertFailure "the finite negative control must finish within its allowance"
            Left failure | obviousFailureClass failure == ObviousIntegrityClass ->
                assertFailure ("residual query integrity failure: " <> show failure)
            Left _ -> pure ()

deniesPremiseGroundIntroduction :: Assertion
deniesPremiseGroundIntroduction = do
    foundation <- expectRight Foundation.checkedFoundation
    let body = member (pair (CBound 0) empty) empty
        premise = CForall TySet (COr body (CNot body))
    theorem <- checkedClosed (CImp premise otherMembership)
    target <- checkedScoped [] otherMembership
    let imported = obviousImport (importIx 0) theorem
        (_statistics, result) = obviousProofDetailed defaultObviousBudget AnyObviousProof
            foundation emptyGlobalTyping [] [imported] [] target
    case result of
        Right _ -> assertFailure "universal introduction restored fresh seed rights to a theorem premise"
        Left ObviousResourceExhausted{} -> assertFailure "the denied premise should block without exhausting its owner"
        Left failure | obviousFailureClass failure == ObviousIntegrityClass ->
            assertFailure ("premise eligibility integrity failure: " <> show failure)
        Left _ -> pure ()

continuesAfterExactConversionExhaustion :: Assertion
continuesAfterExactConversionExhaustion = do
    let targetTerm = CApp (CGlobal predicateObject) empty
        conversionTrap =
            CApp
                (CGlobal predicateObject)
                (nestedSetBeta 2 (pair empty empty))
    target <- checkedGlobalScoped [] targetTerm
    trap <- checkedGlobalScoped [] conversionTrap
    premise <- checkedGlobalScoped [] membership
    theorem <- checkedGlobalClosed (CImp membership targetTerm)
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            (focusedBudget 100000)
            foundation globalType [trap, premise]
            [obviousImport (importIx 0) theorem]
            [] target)
    assertEqual
        "the theorem rule remains available after an irrelevant conversion"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

refutesBeforeFullFocusedConversion :: Assertion
refutesBeforeFullFocusedConversion = do
    let targetTerm = CApp (CGlobal predicateObject) empty
    target <- checkedGlobalScoped [] targetTerm
    alternatives <- checkedGlobalScoped [] (COr membership targetTerm)
    negatedPremise <- checkedGlobalScoped [] (CNot membership)
    goalDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                (expensiveProposition membership)))
    foundation <- expectRight Foundation.checkedFoundation
    let definitionImport = obviousImport (importIx 0) goalDefinition
        definitionView =
            obviousImportedDefinitionView
                predicateObject DefinitionPointwiseView definitionImport
        budget = (focusedBudget 100000)
            { obviousRefutationWorkLimit = 1000000 }
        hypotheses = [alternatives, negatedPremise]
        (statistics, result) =
            obviousProofDetailed
                budget AnyObviousProof foundation globalType
                hypotheses [] [definitionView] target
    proof <- expectRight result
    assertCandidateReplays
        foundation globalType hypotheses [] target proof
    assertEqual "supplied evidence cancels the speculative focused conversion"
        ObviousTierNotCompleted
        (obviousFocusedTierOutcome statistics)
    assertEqual "refutation uses the remaining pool to complete the proof"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome statistics)
    let (focusedStatistics, focusedResult) = obviousProofDetailed
            (budget {obviousRefutationWorkLimit = 0}) AnyObviousProof foundation globalType
            hypotheses [] [definitionView] target
    assertFailureKind "the focused-only control still reaches the real operation cap"
        (ObviousResourceExhausted ObviousConversionOperationLimit) focusedResult
    assertBool "the failed full conversion is actually charged"
        (obviousConversionWorkConsumed focusedStatistics >= 2000000)
    -- Ground Boolean reconstruction can also finish at the actual pool boundary.
    -- No canceled speculative operation is run just to produce a failure.
    let used = obviousConversionWorkConsumed statistics
        run available = obviousProofDetailed
            (budget {obviousConversionPool = Conversion.conversionPool available})
            AnyObviousProof foundation globalType hypotheses [] [definitionView] target
        (handoffStatistics, handoffResult) = run (used + 1)
        (stoppedStatistics, stoppedResult) = run used
    handoffProof <- expectRight handoffResult
    assertCandidateReplays foundation globalType hypotheses [] target handoffProof
    assertEqual "the handoff neither resets nor fabricates conversion credit"
        used (obviousConversionWorkConsumed handoffStatistics)
    assertEqual "logical Refutation completes with its one unused pool unit"
        ObviousTierCandidateBuilt (obviousRefutationTierOutcome handoffStatistics)
    stoppedProof <- expectRight stoppedResult
    assertCandidateReplays foundation globalType hypotheses [] target stoppedProof
    assertEqual "logical refutation can finish with no conversion credit"
        ObviousTierCandidateBuilt (obviousRefutationTierOutcome stoppedStatistics)
    assertEqual "aggregate exhaustion does not spend beyond its pool"
        used (obviousConversionWorkConsumed stoppedStatistics)

usesCitedTheoremOnProjectedLiteralFact :: Assertion
usesCitedTheoremOnProjectedLiteralFact = do
    let context = [TySet]
        one = pair empty empty
        application term = CApp (CGlobal functionObject) term
        twice term = application (application term)
        premise = CEq TySet (twice empty) (twice one)
        projectedPremise = CAnd premise CTruth
        targetTerm = CEq TySet empty one
        cancellation =
            CForall TySet
                (CForall TySet
                    (CImp
                        (CEq TySet
                            (application (CBound 1))
                            (application (CBound 0)))
                        (CEq TySet (CBound 1) (CBound 0))))
    fact <- checkedGlobalScoped context projectedPremise
    definition <- checkedGlobalScoped context
        (CEq TySet (CBound 0) empty)
    target <- checkedGlobalScoped context targetTerm
    theorem <- checkedGlobalClosed cancellation
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            (focusedBudget 1000000)
            foundation globalType [fact, definition]
            [obviousImport (importIx 0) theorem]
            [obviousLocalDefinitionView 1 DefinitionExactView]
            target)
    assertEqual
        "recursive cancellation retains only the cited theorem"
        (Set.singleton (importIx 0))
        (obviousUsedImports proof)

usesLocalTheoremOnProjectedLiteralFact :: Assertion
usesLocalTheoremOnProjectedLiteralFact = do
    let context = [TySet]
        one = pair empty empty
        application term = CApp (CGlobal functionObject) term
        twice term = application (application term)
        premise = CEq TySet (twice empty) (twice one)
        projectedPremise = CAnd premise CTruth
        targetTerm = CEq TySet empty one
        cancellation =
            CForall TySet
                (CForall TySet
                    (CImp
                        (CEq TySet
                            (application (CBound 1))
                            (application (CBound 0)))
                        (CEq TySet (CBound 1) (CBound 0))))
    fact <- checkedGlobalScoped context projectedPremise
    theorem <- checkedGlobalScoped context cancellation
    definition <- checkedGlobalScoped context
        (CEq TySet (CBound 0) empty)
    target <- checkedGlobalScoped context targetTerm
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            (focusedBudget 1000000)
            foundation globalType [fact, theorem, definition]
            []
            [obviousLocalDefinitionView 2 DefinitionExactView]
            target)
    assertEqual
        "recursive cancellation uses only local proof authority"
        Set.empty
        (obviousUsedImports proof)

prefersLocalGoalDefinitionBeforeConversion :: Assertion
prefersLocalGoalDefinitionBeforeConversion = do
    let context = [TySet]
        conversionTrap =
            member
                (expensiveSet (pair empty empty))
                (CBound 0)
        unfolded = member empty empty
        goal = member empty (CBound 0)
    trap <- checkedScoped context conversionTrap
    body <- checkedScoped context unfolded
    definition <- checkedScoped context
        (CEq TySet (CBound 0) empty)
    target <- checkedScoped context goal
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            (focusedBudget 100000)
            foundation emptyGlobalTyping
            [trap, body, definition]
            []
            [obviousLocalDefinitionView 2 DefinitionExactView]
            target)
    assertEqual
        "the local definition reconstructs the original goal"
        target
        (KernelProof.builtProofStatement (obviousBuiltProof proof))

prefersLocalFactDefinitionBeforeConversion :: Assertion
prefersLocalFactDefinitionBeforeConversion = do
    let context = [TySet]
        conversionTrap =
            member
                (expensiveSet (pair empty empty))
                empty
        folded = member empty (CBound 0)
        goal = member empty empty
    trap <- checkedScoped context conversionTrap
    body <- checkedScoped context folded
    definition <- checkedScoped context
        (CEq TySet (CBound 0) empty)
    target <- checkedScoped context goal
    foundation <- expectRight Foundation.checkedFoundation
    proof <- expectRight
        (obviousProof
            (focusedBudget 100000)
            foundation emptyGlobalTyping
            [trap, body, definition]
            []
            [obviousLocalDefinitionView 2 DefinitionExactView]
            target)
    assertEqual
        "the local definition exposes the folded fact"
        target
        (KernelProof.builtProofStatement (obviousBuiltProof proof))

exhaustsBoundedConversion :: Assertion
exhaustsBoundedConversion = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checkedScoped []
        (nestedBeta 5 CTruth)
    let run selectedBudget = obviousProofDetailed selectedBudget AnyObviousProof foundation
            emptyGlobalTyping [] [] [] target
        budget = focusedBudget 100000
        (statistics, result) = run budget
    proof <- expectRight result
    assertCandidateReplays foundation emptyGlobalTyping [] [] target proof
    assertConversionPoolBoundary "beta-written truth" run budget statistics proof
    irrelevant <- checkedScoped [] otherMembership
    unresolved <- checkedScoped [] membership
    assertFailureKind
        "the coordinated search retains its first no-matching-conclusion observation"
        (ObviousNoMatchingConclusion unresolved)
        (obviousProof
            (focusedBudget 100000)
            foundation emptyGlobalTyping [irrelevant] [] [] unresolved)

betaWrap
    :: CanonicalTerm global
    -> CanonicalTerm global
betaWrap proposition =
    CApp (CLam TyProp (CBound 0)) proposition

nestedBeta
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
nestedBeta 0 proposition = proposition
nestedBeta amount proposition =
    betaWrap (nestedBeta (amount - 1) proposition)

nestedSetBeta
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
nestedSetBeta 0 term = term
nestedSetBeta amount term =
    CApp (CLam TySet (CBound 0)) (nestedSetBeta (amount - 1) term)

nestedNegation
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
nestedNegation 0 proposition = proposition
nestedNegation amount proposition =
    CNot (nestedNegation (amount - 1) proposition)

nestedPair
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
nestedPair 0 term = term
nestedPair amount term =
    pair (nestedPair (amount - 1) term) empty

nestedDisjunction
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
nestedDisjunction 0 _unavailable result = result
nestedDisjunction amount unavailable result =
    COr unavailable
        (nestedDisjunction (amount - 1) unavailable result)

terminatesDeterministically :: Assertion
terminatesDeterministically = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checkedScoped [] membership
    assertFailureKind
        "zero search budget"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        (obviousProof
            (focusedBudget 0)
            foundation emptyGlobalTyping [] [] [] target)
    loop <- checkedClosed (CImp membership membership)
    case obviousProof
            defaultObviousBudget
            foundation
            emptyGlobalTyping
            []
            [obviousImport (importIx 0) loop]
            []
            target of
        Left ObviousRepeatedState{} -> pure ()
        Left failure ->
            assertFailure
                ("expected a repeated state, got " <> show failure)
        Right _proof ->
            assertFailure "expected the cyclic theorem application to fail"

    let deepProposition = nestedNegation 80 CTruth
    deepFact <- checkedScoped [] deepProposition
    deepTarget <- checkedScoped [] deepProposition
    let deepRun focused =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof
                foundation
                emptyGlobalTyping
                [deepFact]
                []
                []
                deepTarget
        (deepStatistics, deepResult) = deepRun 1000000
        deepWork = obviousFocusedWorkConsumed deepStatistics
    deepProof <- expectRight deepResult
    assertCandidateReplays
        foundation emptyGlobalTyping [deepFact] [] deepTarget deepProof
    assertBool "deep exact search performs counted structural work"
        (deepWork > 80)
    _exactDeepProof <- expectRight (snd (deepRun deepWork))
    let (deepFallbackStatistics, deepFallbackResult) =
            deepRun (deepWork - 1)
    deepFallbackProof <- expectRight deepFallbackResult
    assertCandidateReplays
        foundation emptyGlobalTyping [deepFact] [] deepTarget deepFallbackProof
    assertEqual "deep focused equality stops at its boundary"
        (ObviousTierResourceExhausted ObviousFocusedWorkLimit)
        (obviousFocusedTierOutcome deepFallbackStatistics)
    assertEqual "refutation reuses the exact deep root"
        ObviousTierCandidateBuilt
        (obviousRefutationTierOutcome deepFallbackStatistics)

    let irrelevantProposition = nestedNegation 24 CTruth
    irrelevant <- checkedScoped [] irrelevantProposition
    cyclicTarget <- checkedScoped [] membership
    cyclicTheorem <- checkedClosed (CImp membership membership)
    let longHypotheses = replicate 8 irrelevant
        cyclicImports =
            [obviousImport (importIx 1) cyclicTheorem]
        cyclicRun focused =
            obviousProofDetailed
                (focusedBudget focused)
                AnyObviousProof
                foundation
                emptyGlobalTyping
                longHypotheses
                cyclicImports
                []
                cyclicTarget
        (cyclicStatistics, cyclicResult) = cyclicRun 1000000
        cyclicWork = obviousFocusedWorkConsumed cyclicStatistics
    case cyclicResult of
        Left ObviousRepeatedState{} -> pure ()
        Left failure ->
            assertFailure
                ("expected an interned repeated obligation, got "
                    <> show failure)
        Right _proof ->
            assertFailure
                "expected the interned cyclic obligation to fail"
    assertBool "obligation identity traverses the hypothesis sequence"
        (cyclicWork > 8 * 24)
    case snd (cyclicRun cyclicWork) of
        Left ObviousRepeatedState{} -> pure ()
        Left failure ->
            assertFailure
                ("exact obligation boundary changed the result: "
                    <> show failure)
        Right _proof ->
            assertFailure
                "the cyclic obligation unexpectedly succeeded at its boundary"
    assertFailureKind
        "obligation identity exhaustion does not publish a partial match"
        (ObviousResourceExhausted ObviousFocusedWorkLimit)
        (snd (cyclicRun (cyclicWork - 1)))

reportsDetailedOutcomes :: Assertion
reportsDetailedOutcomes = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checkedScoped [] CTruth
    let successfulBudget = focusedBudget 100
        successfulReport =
            obviousProofReport
                successfulBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                target
        (successfulStatistics, successfulResult) =
            obviousProofDetailed
                successfulBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                target
    assertEqual "report and detailed statistics agree"
        successfulStatistics
        (obviousRunStatistics successfulReport)
    assertEqual "a successful report has no failure details"
        Nothing
        (obviousRunFailure successfulReport)
    proof <- expectRight successfulResult
    reportProof <- expectRight (obviousRunResult successfulReport)
    assertEqual "report erasure preserves the checked conclusion"
        (KernelProof.builtProofStatement (obviousBuiltProof proof))
        (KernelProof.builtProofStatement (obviousBuiltProof reportProof))
    assertEqual "report erasure preserves selected imports"
        (obviousUsedImports proof)
        (obviousUsedImports reportProof)
    assertCandidateReplays foundation emptyGlobalTyping [] [] target proof
    assertEqual "effective budget"
        successfulBudget
        (obviousEffectiveBudget successfulStatistics)
    assertEqual "focused success outcome"
        ObviousTierCandidateBuilt
        (obviousFocusedTierOutcome successfulStatistics)
    assertEqual "refutation has not started"
        ObviousTierNotStarted
        (obviousRefutationTierOutcome successfulStatistics)
    assertBool "focused work includes structural traversal"
        (obviousFocusedWorkConsumed successfulStatistics > 1)
    assertEqual "exposed logical heads spend structural work only"
        0
        (obviousConversionWorkConsumed successfulStatistics)
    assertEqual "ground task admission is charged without allocating a query or catalogue"
        (4, 0, 0, 0, 0, 0)
        ( obviousRefutationWorkConsumed successfulStatistics
        , obviousBranchNodesCreated successfulStatistics
        , obviousTermsAdmitted successfulStatistics
        , obviousSignedFormulasAdmitted successfulStatistics
        , obviousEqualityEventsProcessed successfulStatistics
        , obviousRuleInstancesAdmitted successfulStatistics
        )

    betaTarget <- checkedScoped [] (nestedBeta 1 CTruth)
    let exhaustedBudget = successfulBudget
            {obviousConversionPool = Conversion.conversionPool 0}
        (exhaustedStatistics, exhaustedResult) =
            obviousProofDetailed
                exhaustedBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                betaTarget
    assertFailureKind
        "zero conversion pool"
        (ObviousResourceExhausted ObviousConversionPoolLimit)
        exhaustedResult
    assertEqual "focused pool exhaustion outcome"
        (ObviousTierResourceExhausted ObviousConversionPoolLimit)
        (obviousFocusedTierOutcome exhaustedStatistics)
    assertEqual "failed preparation consumes no unavailable conversion work"
        0
        (obviousConversionWorkConsumed exhaustedStatistics)

    let exhaustedReport =
            obviousProofReport
                exhaustedBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                betaTarget
    exhaustedFailure <- maybe
        (assertFailure "a failed report omitted its details" >> fail "missing")
        pure
        (obviousRunFailure exhaustedReport)
    assertEqual "head preparation owns the focused lifecycle failure"
        (ObviousFocusedExposureFailed
            (ObviousResourceExhaustedClass ObviousConversionPoolLimit))
        (obviousFailureFocusedGoalView exhaustedFailure)
    assertEqual "terminal focus suppresses refutation explicitly"
        (ObviousFocusedOnlyFailure
            ObviousRefutationQueryNotStarted)
        (obviousFailurePath exhaustedFailure)
    assertEqual "exposure failure does not claim candidate observation"
        CandidateObservationNotStarted
        (obviousFailureCandidateCoverage exhaustedFailure)

    noMatchTarget <- checkedScoped [] membership
    let noMatchReport =
            obviousProofReport
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                noMatchTarget
    noMatchFailure <- maybe
        (assertFailure "no-match report omitted its details" >> fail "missing")
        pure
        (obviousRunFailure noMatchReport)
    assertFailureKind "report retains the first completed no-match observation"
        (ObviousNoMatchingConclusion noMatchTarget)
        (obviousRunResult noMatchReport)
    assertEqual "focused no-match remains the primary diagnostic"
        ObviousNoMatchClass
        (obviousFailurePrimaryClass noMatchFailure)
    assertEqual "ordinary no-match finishes candidate observation"
        CandidateObservationFinished
        (obviousFailureCandidateCoverage noMatchFailure)
    case obviousFailurePath noMatchFailure of
        ObviousCoordinatedFailure -> pure ()
        path ->
            assertFailure
                ("unexpected no-match tier path: " <> show path)

    let definitionReport =
            obviousProofReport
                successfulBudget
                MustUseCanonicalDefinition
                foundation
                emptyGlobalTyping
                []
                []
                []
                target
    definitionFailure <- maybe
        (assertFailure "definition report omitted its details" >> fail "missing")
        pure
        (obviousRunFailure definitionReport)
    assertEqual "canonical-definition mode records its owned ground search"
        ObviousCoordinatedFailure
        (obviousFailurePath definitionFailure)
    assertEqual "unattributed root completion does not fabricate a candidate"
        ([], [CandidateOriginalGoalView])
        ( obviousFailureCandidates definitionFailure
        , obviousFailureRootRequirementRejections definitionFailure
        )

    changedTarget <- checkedScoped [] (nestedBeta 1 membership)
    let changedReport =
            obviousProofReport
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                changedTarget
    changedFailure <- maybe
        (assertFailure "changed-view report omitted its details" >> fail "missing")
        pure
        (obviousRunFailure changedReport)
    case obviousFailureFocusedGoalView changedFailure of
        ObviousFocusedViewChanged _summary -> pure ()
        lifecycle ->
            assertFailure
                ("expected a changed focused view, got " <> show lifecycle)

preservesDefinitionImportAssociations :: Assertion
preservesDefinitionImportAssociations = do
    foundation <- expectRight Foundation.checkedFoundation
    let named = CGlobal namedSetObject
        one = pair empty empty
    fact <- checkedGlobalScoped [] (member empty named)
    target <- checkedGlobalScoped [] membership
    otherTarget <- checkedGlobalScoped [] (member empty one)
    truth <- checkedGlobalClosed CTruth
    equation <- checkedGlobalClosed (CEq TySet named empty)
    otherEquation <- checkedGlobalClosed (CEq TySet named one)
    let index = importIx 7
        imported = obviousImport index equation
        view source = obviousImportedDefinitionView namedSetObject DefinitionExactView source
        run requirement hypotheses imports views goal = obviousProofDetailed
            defaultObviousBudget requirement foundation globalType hypotheses imports views goal
        conflicting = ObviousMalformedInput (ObviousConflictingImportStatement index)
    forM_ [AnyObviousProof, MustUseCanonicalDefinition] \requirement -> do
        let (statistics, result) = run requirement [fact]
                [obviousImport index truth] [view imported] target
        assertFailureKind "a used view cannot replace an ordinary import statement" conflicting result
        assertEqual "late association failure reports actual focused work"
            ObviousTierIntegrityFailure (obviousFocusedTierOutcome statistics)
        assertBool "checking the association consumes focused work"
            (obviousFocusedWorkConsumed statistics > 0)
        assertBool "a ground alternative cannot hide the encountered association failure"
            (obviousRefutationTierOutcome statistics /= ObviousTierCandidateBuilt)
        assertFailureKind "different definition views cannot share an authority index" conflicting
            (snd (run requirement [fact] []
                [view imported, view (obviousImport index otherEquation)] otherTarget))
        proof <- expectRight (snd (run requirement [fact] [imported]
            [view imported, view imported] target))
        assertCandidateReplays foundation globalType [fact] [imported] target proof
    -- An unused view need not be traversed to return an already checked fact.
    proof <- expectRight (snd (run AnyObviousProof [target] [obviousImport index truth]
        [view imported] target))
    assertEqual "literal reuse does not consume unused definition evidence"
        Set.empty (obviousUsedImports proof)
    assertCandidateReplays foundation globalType [target] [] target proof


rejectsMalformedRequests :: Assertion
rejectsMalformedRequests = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checkedScoped [] CTruth
    let boundaryBudget =
            (focusedBudget 100) {obviousConversionPool = Conversion.conversionPool maxBound}
        (_boundaryStatistics, boundaryResult) =
            obviousProofDetailed
                boundaryBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                target
    _proof <- expectRight boundaryResult

    let excessiveCapacity = fromIntegral (maxBound :: Int) + 1
        malformedBudget = (focusedBudget 100)
            {obviousGroundTermLimit = excessiveCapacity}
        (malformedStatistics, malformedResult) =
            obviousProofDetailed
                malformedBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                target
    assertFailureKind
        "a structural limit above implementation capacity"
        (ObviousMalformedInput
            (ObviousLimitExceedsImplementationCapacity
                ObviousGroundTermLimit excessiveCapacity))
        malformedResult
    assertEqual "malformed request does not start search"
        (ObviousTierNotStarted, ObviousTierNotStarted, 0, 0)
        ( obviousFocusedTierOutcome malformedStatistics
        , obviousRefutationTierOutcome malformedStatistics
        , obviousFocusedWorkConsumed malformedStatistics
        , obviousConversionWorkConsumed malformedStatistics
        )
    let malformedReport =
            obviousProofReport
                malformedBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                target
    malformedFailure <- maybe
        (assertFailure "malformed report omitted its details" >> fail "missing")
        pure
        (obviousRunFailure malformedReport)
    assertEqual "validation failure has an exact tier path"
        ObviousValidationFailure
        (obviousFailurePath malformedFailure)
    assertEqual "validation does not manufacture a focused view"
        ObviousFocusedViewUnavailable
        (obviousFailureFocusedGoalView malformedFailure)
    assertEqual "validation failure does not start candidate observation"
        CandidateObservationNotStarted
        (obviousFailureCandidateCoverage malformedFailure)

    nonPropositionTarget <- checkedScoped [] empty
    let nonPropositionReport =
            obviousProofReport
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                nonPropositionTarget
    nonPropositionFailure <- maybe
        (assertFailure "non-proposition report omitted its details"
            >> fail "missing")
        pure
        (obviousRunFailure nonPropositionReport)
    assertEqual "malformed checked goals still have a typed bounded summary"
        ObviousTypeSet
        (case obviousFailureCheckedGoal nonPropositionFailure of
            ObviousCoreSummary _context _truncated coreType _term -> coreType)

    irrelevant <- checkedScoped [] membership
    irrelevantClosed <- checkedClosed membership
    let manyHypotheses = replicate 6 irrelevant
        manyImports =
            [ obviousImport (importIx (fromIntegral index)) irrelevantClosed
            | index <- [0 :: Int .. 5]
            ]
        manyViews =
            [ obviousLocalDefinitionView
                (fromIntegral index) DefinitionExactView
            | index <- [0 :: Int .. 5]
            ]
        boundedReport =
            obviousProofReport
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation
                emptyGlobalTyping
                manyHypotheses
                manyImports
                manyViews
                target
    boundedFailure <- maybe
        (assertFailure "bounded-input report unexpectedly succeeded"
            >> fail "missing")
        pure
        (obviousRunFailure boundedReport)
    assertEqual "hypothesis observations retain an exact total and bounded rows"
        (6, 4)
        ( obviousFailureHypothesisCount boundedFailure
        , length (obviousFailureHypotheses boundedFailure)
        )
    assertEqual "import observations retain an exact total and bounded rows"
        (6, 4)
        ( obviousFailureImportCount boundedFailure
        , length (obviousFailureImports boundedFailure)
        )
    assertEqual "local definition observations retain occurrences, not fact identity"
        (6, 4)
        ( obviousFailureLocalDefinitionViewCount boundedFailure
        , length (obviousFailureLocalDefinitionViews boundedFailure)
        )

    deepInput <- checkedScoped [] (nestedNegation 20 membership)
    let truncationReport =
            obviousProofReport
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation
                emptyGlobalTyping
                [deepInput]
                []
                []
                target
    truncationFailure <- maybe
        (assertFailure "truncation report unexpectedly succeeded"
            >> fail "missing")
        pure
        (obviousRunFailure truncationReport)
    case obviousFailureHypotheses truncationFailure of
        [ObviousHypothesisObservation _index summary] ->
            assertBool "the producer truncates at the named depth boundary"
                (coreSummaryIsTruncated summary)
        observations ->
            assertFailure
                ("unexpected truncation observations: " <> show observations)

    proposition <- checkedClosed CTruth
    let duplicate = obviousImport (importIx 7) proposition
    assertFailureKind
        "duplicate ordinary authority index"
        (ObviousMalformedInput (ObviousDuplicateImportIx (importIx 7)))
        (snd
            (obviousProofDetailed
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                [duplicate, duplicate]
                []
                target))

    nonProposition <- checkedClosed empty
    let invalidImport = obviousImport (importIx 8) nonProposition
    assertFailureKind
        "ordinary import must be propositional"
        (ObviousMalformedInput
            (ObviousImportNotPropositional (importIx 8) TySet))
        (snd
            (obviousProofDetailed
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                [invalidImport]
                []
                target))

    nonPropositionalTarget <- checkedScoped [] empty
    assertFailureKind
        "target must be propositional"
        (ObviousMalformedInput (ObviousTargetNotPropositional TySet))
        (snd
            (obviousProofDetailed
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                nonPropositionalTarget))

    mismatchedHypothesis <- checkedScoped [TySet] CTruth
    assertFailureKind
        "hypotheses use the target lexical context"
        (ObviousMalformedInput ObviousHypothesisMetadataMismatch)
        (snd
            (obviousProofDetailed
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                [mismatchedHypothesis]
                []
                []
                target))

    assertFailureKind
        "local definition view names an external hypothesis"
        (ObviousMalformedInput
            (ObviousLocalDefinitionViewOutOfRange 0))
        (snd
            (obviousProofDetailed
                defaultObviousBudget
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                [obviousLocalDefinitionView 0 DefinitionPointwiseView]
                target))

    let excessiveGroundTerms =
            defaultObviousBudget
                { obviousGroundTermLimit = maxBound
                }
    assertFailureKind
        "hard cap outside the Int-backed implementation capacity"
        (ObviousMalformedInput
            (ObviousLimitExceedsImplementationCapacity
                ObviousGroundTermLimit maxBound))
        (snd
            (obviousProofDetailed
                excessiveGroundTerms
                AnyObviousProof
                foundation
                emptyGlobalTyping
                []
                []
                []
                target))

candidateScalingFixture :: Int -> Assertion
candidateScalingFixture factCount = do
    foundation <- expectRight Foundation.checkedFoundation
    irrelevant <- checkedScoped [] membership
    target <- checkedScoped [] otherMembership
    let report =
            obviousProofReport
                defaultObviousBudget
                MustUseCanonicalDefinition
                foundation
                emptyGlobalTyping
                (replicate factCount irrelevant)
                []
                []
                target
    case obviousRunResult report of
        Left ObviousNoMatchingConclusion{} -> pure ()
        Left failure ->
            assertFailure
                ("expected an ordinary focused failure, got " <> show failure)
        Right _proof ->
            assertFailure "the candidate scaling fixture unexpectedly succeeded"
    failureReport <- maybe
        (assertFailure "the candidate scaling report omitted failure evidence"
            >> fail "missing")
        pure
        (obviousRunFailure report)
    assertEqual "ordinary focused exhaustion completes observation"
        CandidateObservationFinished
        (obviousFailureCandidateCoverage failureReport)
    let retained = obviousFailureCandidates failureReport
        expectedCount = min 3 factCount
    assertEqual "the producer retains only the online top three"
        expectedCount
        (length retained)
    assertEqual "stable source order breaks equal candidate ties"
        [CandidateHypothesis (fromIntegral index)
        | index <- [0 .. expectedCount - 1]]
        (obviousCandidateSource <$> retained)
    assertBool "each retained row is an actual conversion rejection"
        (all
            (\candidate ->
                obviousCandidateOutcome candidate
                    == ComparisonRejected ConversionMismatch)
            retained)
    if factCount /= 8
        then pure ()
        else do
            let focusedWork =
                    obviousFocusedWorkConsumed (obviousRunStatistics report)
                stoppedBudget =
                    defaultObviousBudget
                        { obviousFocusedWorkLimit = focusedWork - 1 }
                stoppedReport =
                    obviousProofReport stoppedBudget
                        MustUseCanonicalDefinition foundation
                        emptyGlobalTyping (replicate factCount irrelevant)
                        [] [] target
            stoppedFailure <- maybe
                (assertFailure "one-short focused report unexpectedly succeeded"
                    >> fail "missing")
                pure
                (obviousRunFailure stoppedReport)
            assertEqual "terminal focused exhaustion marks evidence partial"
                CandidateObservationStoppedEarly
                (obviousFailureCandidateCoverage stoppedFailure)

assertSingleCandidateOutcome
    :: CandidateBaseSource
    -> CandidateComparisonView
    -> CandidateOutcome
    -> ObviousRunReport global
    -> Assertion
assertSingleCandidateOutcome expectedSource expectedView expectedOutcome report = do
    failureReport <- maybe
        (assertFailure "candidate report unexpectedly succeeded" >> fail "missing")
        pure
        (obviousRunFailure report)
    case obviousFailureCandidates failureReport of
        candidate : _rest ->
            assertEqual "the best observed candidate"
                (expectedSource, expectedView, expectedOutcome)
                ( obviousCandidateSource candidate
                , obviousCandidateView candidate
                , obviousCandidateOutcome candidate
                )
        [] -> assertFailure "candidate report retained no observed comparison"

reportsDefinitionCandidateParticipation :: Assertion
reportsDefinitionCandidateParticipation = do
    foundation <- expectRight Foundation.checkedFoundation
    goal <- checkedGlobalScoped []
        (CApp (CGlobal predicateObject) empty)
    fact <- checkedGlobalScoped []
        (CApp (CGlobal factPredicateObject) empty)
    membershipFact <- checkedGlobalScoped [] membership
    irrelevant <- checkedGlobalScoped [] otherMembership
    goalDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal predicateObject) (CBound 0))
                membership))
    factDefinition <- checkedGlobalClosed
        (CForall TySet
            (CEq TyProp
                (CApp (CGlobal factPredicateObject) (CBound 0))
                membership))
    let report target hypotheses object definition =
            obviousProofReport defaultObviousBudget AnyObviousProof
                foundation globalType hypotheses []
                [obviousImportedDefinitionView
                    object DefinitionPointwiseView
                    (obviousImport (importIx 0) definition)]
                target
        goalReport = report goal [irrelevant]
            predicateObject goalDefinition
        factReport = report irrelevant [fact, membershipFact]
            factPredicateObject factDefinition
    projectedTarget <- checkedGlobalScoped []
        (member (pair empty empty) empty)
    projectedFact <- checkedGlobalScoped []
        (CAnd membership otherMembership)
    let projectedReport =
            obviousProofReport defaultObviousBudget AnyObviousProof
                foundation globalType [projectedFact] [] [] projectedTarget
    goalCandidate <- bestCandidate goalReport
    assertEqual "goal reconstruction carries its exact definition lineage"
        ( CandidateDefinitionGoalView [0] False
        , CandidateGoalDefinitionParticipation [0] False
        )
        ( obviousCandidateRootView goalCandidate
        , obviousCandidateDefinitionParticipation goalCandidate
        )
    factCandidate <- bestCandidate factReport
    assertEqual "fact exposure carries its exact definition occurrence"
        ( CandidateOriginalGoalView
        , CandidateFactDefinitionParticipation [0] False
        )
        ( obviousCandidateRootView factCandidate
        , obviousCandidateDefinitionParticipation factCandidate
        )
    projectedCandidate <- bestCandidate projectedReport
    assertEqual "projected exact comparisons retain their view depth"
        (CandidateHypothesis 0, CandidateProjectedView 1)
        ( obviousCandidateSource projectedCandidate
        , obviousCandidateView projectedCandidate
        )
    theorem <- checkedGlobalScoped [] (CImp membership otherMembership)
    let auxiliaryReport =
            obviousProofReport defaultObviousBudget
                MustUseCanonicalDefinition foundation globalType
                [membershipFact, theorem] [] [] irrelevant
    auxiliaryCandidate <- bestCandidate auxiliaryReport
    assertEqual "an owning theorem claims auxiliary requirement evidence once"
        ( Just
            (CandidateAuxiliaryRequirementRejected
                AuxiliaryTheoremAntecedent)
        , []
        , 0
        )
        ( obviousCandidateAuxiliaryCause auxiliaryCandidate
        , maybe [] obviousFailureAuxiliaryCauses
            (obviousRunFailure auxiliaryReport)
        , maybe 0 obviousFailureAdditionalAuxiliaryCauseCount
            (obviousRunFailure auxiliaryReport)
        )
  where
    bestCandidate report = do
        failure <- maybe
            (assertFailure "definition candidate report unexpectedly succeeded"
                >> fail "missing")
            pure
            (obviousRunFailure report)
        case obviousFailureCandidates failure of
            candidate : _rest -> pure candidate
            [] -> assertFailure "definition candidate report retained no candidate"

coreSummaryIsTruncated :: ObviousCoreSummary global -> Bool
coreSummaryIsTruncated
        (ObviousCoreSummary context contextTruncated coreType term) =
    contextTruncated
        || any typeSummaryIsTruncated context
        || typeSummaryIsTruncated coreType
        || termSummaryIsTruncated term

typeSummaryIsTruncated :: ObviousTypeSummary -> Bool
typeSummaryIsTruncated = \case
    ObviousTypeTruncated -> True
    ObviousTypeArrow argument result ->
        typeSummaryIsTruncated argument || typeSummaryIsTruncated result
    ObviousTypeProposition -> False
    ObviousTypeSet -> False

termSummaryIsTruncated :: ObviousTermSummary global -> Bool
termSummaryIsTruncated = \case
    ObviousGlobalTruncated -> True
    ObviousTermTruncated -> True
    ObviousLogicalSelection coreType -> typeSummaryIsTruncated coreType
    ObviousApplication function argument ->
        termSummaryIsTruncated function || termSummaryIsTruncated argument
    ObviousLambda binderType body ->
        typeSummaryIsTruncated binderType || termSummaryIsTruncated body
    ObviousNegation proposition -> termSummaryIsTruncated proposition
    ObviousConjunction left right -> binary left right
    ObviousDisjunction left right -> binary left right
    ObviousImplication left right -> binary left right
    ObviousEquality operandType left right ->
        typeSummaryIsTruncated operandType || binary left right
    ObviousUniversal binderType body ->
        typeSummaryIsTruncated binderType || termSummaryIsTruncated body
    ObviousExistential binderType body ->
        typeSummaryIsTruncated binderType || termSummaryIsTruncated body
    ObviousBoundVariable{} -> False
    ObviousGlobal{} -> False
    ObviousIntrinsic{} -> False
    ObviousOpaqueInteger{} -> False
    ObviousFalsum -> False
    ObviousTruth -> False
  where
    binary left right =
        termSummaryIsTruncated left || termSummaryIsTruncated right

assertFailureKind
    :: (Eq global, Show global)
    => String
    -> ObviousFailure global
    -> Either (ObviousFailure global) (ObviousProof global)
    -> Assertion
assertFailureKind label expected = \case
    Left actual -> assertEqual label expected actual
    Right _proof -> assertFailure (label <> " unexpectedly succeeded")

assertObvious
    :: [ScopedCheckedCore Void]
    -> [ObviousImport Void]
    -> ScopedCheckedCore Void
    -> Assertion
assertObvious hypotheses imports target = do
    proof <- expectRight =<< runObvious hypotheses imports target
    assertEqual
        "the constructed proof has the exact target"
        target
        (KernelProof.builtProofStatement (obviousBuiltProof proof))

runObvious
    :: [ScopedCheckedCore Void]
    -> [ObviousImport Void]
    -> ScopedCheckedCore Void
    -> IO (Either (ObviousFailure Void) (ObviousProof Void))
runObvious hypotheses imports target = do
    foundation <- expectRight Foundation.checkedFoundation
    let result =
            obviousProof
            defaultObviousBudget
            foundation
            emptyGlobalTyping
            hypotheses
            imports
            []
            target
    case result of
        Left _failure -> pure result
        Right proof -> do
            assertCandidateReplays
                foundation emptyGlobalTyping hypotheses imports target proof
            pure result

assertCandidateReplays
    :: Eq global
    => Foundation.CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> ScopedCheckedCore global
    -> ObviousProof global
    -> Assertion
assertCandidateReplays
        foundation resolver hypotheses imports target proof = do
    let used = obviousUsedImports proof
        retained =
            List.filter
                ((`Set.member` used) . obviousImportIndex)
                imports
        indexedRetained = zip [0 :: Int ..] retained
        remapping =
            Map.fromList
                [ ( obviousImportIndex imported
                  , importIx (fromIntegral denseIndex)
                  )
                | (denseIndex, imported) <- indexedRetained
                ]
        expectedDenseImports =
            Set.fromList
                [ importIx (fromIntegral denseIndex)
                | (denseIndex, _imported) <- indexedRetained
                ]
    remapped <-
        maybe
            (assertFailure
                "the candidate selected an import outside its exact request"
                >> fail "missing obvious import remapping")
            pure
            (remapKernelDerivationImports
                (`Map.lookup` remapping)
                (KernelProof.builtProofDerivation
                    (obviousBuiltProof proof)))
    replayImports <-
        traverse
            (expectRight
                . derivationImportJudgement
                . obviousImportStatement
                . snd)
            indexedRetained
    replayed <-
        expectRight
            (replayScopedKernelDerivation
                foundation
                defaultKernelReplayLimits
                resolver
                (Vector.fromList replayImports)
                (Vector.fromList hypotheses)
                target
                remapped)
    assertEqual "replay uses exactly the densely retained imports"
        expectedDenseImports
        (replayedScopedKernelImportUses replayed)

focusedBudget :: Word -> ObviousBudget
focusedBudget focused =
    defaultObviousBudget {obviousFocusedWorkLimit = focused}

-- Compact written syntax with more than two million units of demanded head
-- work. This crosses the fixed operation policy without growing the fixture's
-- canonical syntax or changing the production pool to manufacture exhaustion.
expensiveProposition :: CanonicalTerm global -> CanonicalTerm global
expensiveProposition = expensiveIdentity TyProp

expensiveSet :: CanonicalTerm global -> CanonicalTerm global
expensiveSet = expensiveIdentity TySet

expensiveIdentity :: CoreType -> CanonicalTerm global -> CanonicalTerm global
expensiveIdentity coreType = CApp repeated
  where
    twice = CLam (TyArrow coreType coreType)
        (CLam coreType (CApp (CBound 1) (CApp (CBound 1) (CBound 0))))
    repeated = foldr (\_ term -> CApp twice term)
        (CLam coreType (CBound 0)) [1 .. 18 :: Int]

assertConversionPoolBoundary
    :: (Eq global, Show global)
    => String
    -> (ObviousBudget -> (ObviousStatistics, Either (ObviousFailure global) (ObviousProof global)))
    -> ObviousBudget
    -> ObviousStatistics
    -> ObviousProof global
    -> Assertion
assertConversionPoolBoundary label run budget statistics proof = do
    let used = obviousConversionWorkConsumed statistics
        exactBudget = budget {obviousConversionPool = Conversion.conversionPool used}
        shortBudget = budget {obviousConversionPool = Conversion.conversionPool (used - 1)}
        (exactStatistics, exactResult) = run exactBudget
        (shortStatistics, shortResult) = run shortBudget
    assertBool (label <> " consumes conversion work") (used > 0)
    exactProof <- expectRight exactResult
    assertEqual (label <> " exact pool preserves the checked target")
        (KernelProof.builtProofStatement (obviousBuiltProof proof))
        (KernelProof.builtProofStatement (obviousBuiltProof exactProof))
    assertEqual (label <> " exact pool preserves selected imports")
        (obviousUsedImports proof) (obviousUsedImports exactProof)
    assertEqual (label <> " exact pool preserves the complete debit")
        used (obviousConversionWorkConsumed exactStatistics)
    case shortResult of
        Left (ObviousResourceExhausted ObviousConversionPoolLimit) -> pure ()
        Left failure -> assertFailure (label <> " unexpected one-less failure: " <> show failure)
        Right _ -> assertFailure (label <> " produced a proof with one less conversion unit")
    assertEqual (label <> " exhaustion preserves consumed work without overdraft")
        (used - 1) (obviousConversionWorkConsumed shortStatistics)

checkedClosed
    :: CanonicalTerm Void
    -> IO (FrozenCheckedCore Void)
checkedClosed =
    expectRight . checkCanonicalCore emptyGlobalTyping

checkedScoped
    :: [CoreType]
    -> CanonicalTerm Void
    -> IO (ScopedCheckedCore Void)
checkedScoped context =
    expectRight . checkScopedCanonicalCore emptyGlobalTyping context

expectRight
    :: Show error
    => Either error value
    -> IO value
expectRight =
    either (assertFailure . show) pure

globalFixture :: GlobalTypingFixture
globalFixture =
    globalTypingFixture
        [ TyArrow TySet TyProp
        , TyArrow TySet TySet
        , TyArrow TySet TyProp
        , TyArrow TySet (TyArrow TySet TyProp)
        , TySet
        ]

globalType :: GlobalTyping ObjectId
globalType = fixtureGlobalTyping globalFixture

predicateObject, functionObject, factPredicateObject,
    binaryPredicateObject, namedSetObject :: ObjectId
( predicateObject
    , functionObject
    , factPredicateObject
    , binaryPredicateObject
    , namedSetObject
    ) =
        case fixtureObjectIds globalFixture of
            [predicate, function, factPredicate, binaryPredicate, namedSet] ->
                ( predicate
                , function
                , factPredicate
                , binaryPredicate
                , namedSet
                )
            _ -> error "the obvious global fixture changed arity"

checkedGlobalClosed
    :: CanonicalTerm ObjectId
    -> IO (FrozenCheckedCore ObjectId)
checkedGlobalClosed =
    expectRight . checkCanonicalCore globalType

checkedGlobalScoped
    :: [CoreType]
    -> CanonicalTerm ObjectId
    -> IO (ScopedCheckedCore ObjectId)
checkedGlobalScoped context =
    expectRight . checkScopedCanonicalCore globalType context

empty :: CanonicalTerm global
empty = CIntrinsic Empty

pair
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
pair left right =
    CApp (CApp (CIntrinsic PairSet) left) right

member
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
member element set =
    CApp (CApp (CIntrinsic Member) element) set

membership :: CanonicalTerm global
membership = member empty empty

otherMembership :: CanonicalTerm global
otherMembership = member empty (pair empty empty)
