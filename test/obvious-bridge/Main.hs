{-# LANGUAGE RankNTypes #-}

module Main (main) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Elimination qualified as Elimination
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Obvious.Conversion qualified as Effort
import Felix.Checking.Obvious.Refutation qualified as Ground
import Felix.Checking.Obvious.Driver qualified as Scope
import Felix.Checking.Obvious.LogicalView qualified as Logical
import Felix.Checking.Obvious.Match qualified as Match
import Felix.Checking.Obvious.Search qualified as Search
import Felix.Checking.Obvious.Template qualified as Template
import Felix.Checking.Semantic qualified as Semantic
import Felix.Math.Codec (hashBlake2b256)
import Felix.Module
import Felix.Source

import Control.Monad (unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word)
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit
import EndpointChecks qualified
import EqualityChecks qualified
import ChoiceChecks qualified
import CatalogueChecks qualified
import MatcherChecks qualified
import ExtensionalityChecks qualified
import SharedSyntaxChecks qualified

-- The historical feature controls disable the later search extensions.
extensionalityTestPolicy :: Scope.SearchPolicy
extensionalityTestPolicy = Scope.productionSearchPolicy
    { Scope.policyEndpoints = Scope.EndpointsDisabled }

existentialTestPolicy :: Scope.SearchPolicy
existentialTestPolicy = extensionalityTestPolicy
    { Scope.policyExtensionality = Scope.ExtensionalityDisabled }

main :: IO ()
main = defaultMain (testGroup "Certified Obvious bridge"
    [ testCase "selects predicate projections consistently with canonical equations" predicateProjectionTargets
    , testCase "classifies ordinary and canonical shared cycles" sharedCycles
    , ChoiceChecks.tests
    , testCase "delivers consumer publication and completion without registration rescans" consumerDelivery
    , CatalogueChecks.tests
    , MatcherChecks.tests
    , ExtensionalityChecks.tests
    , SharedSyntaxChecks.tests
    , EqualityChecks.tests
    , EndpointChecks.tests
    , testCase "distinguishes preparatory conversion from actual exhaustion" preparationConversion
    , testCase "debits failed preparatory builders without replacing the real pool" preparationBuilder
    , testCase "charges ground ownership and publication without focused credit" groundWithoutFocusedCredit
    , testCase "yields at ground publications and commits work before another query" ownedGroundPublicationQuantum
    , testCase "propagates signed Boolean evidence before splitting" booleanSplitPropagation
    , testCase "retains canonical split support after Boolean simplification" booleanSplitSupport
    , testCase "matches conjunction and truth premises and reconstructs their original trees" exactPremiseRecipes
    , testCase "upgrades exact premise recipes without repeating logical instances" exactPremiseSupport
    , testCase "uses conjunction premises in case branches without leaking sibling evidence" exactPremiseBranches
    , testCase "replays incremental universal conjunction projections" exactRuleProjections
    , testCase "retains full and partial projection grammar coverage" exactProjectionCoverage
    , testCase "selects existing existential witnesses and replays their body proofs" existingWitnesses
    , testCase "bounds and deduplicates existential choices across nested searches" boundedWitnesses
    , testCase "keeps derived existential bodies inside the original term domain" witnessDomains
    , testCase "retains existential attempts for later canonical body support" witnessSupport
    , testCase "opens supplied existentials and replays discharged branches" suppliedExistentials
    , testCase "bounds existential openings without reopening weakened ancestors" boundedExistentials
    , testCase "keeps existential witnesses and assumptions inside their branch" existentialScopes
    , testCase "retains one existential branch for later canonical evidence" existentialSupport
    , testCase "charges existential setup and discharge to the complete request" existentialResources
    , testCase "replays selected membership extensionality with one shared attempt" membershipExtensionality
    , testCase "keeps membership extensionality guards and evidence necessary" membershipExtensionalityBoundaries
    , testCase "isolates membership extensionality scopes and restricted descendants" membershipExtensionalityScopes
    , testCase "retains membership extensionality branches for canonical evidence" membershipExtensionalitySupport
    , testCase "charges membership extensionality setup and discharge to shared budgets" membershipExtensionalityResources
    , testCase "cancels a pending fact domain only after its consumer is satisfied" cancelsPendingFactDomain
    , testCase "queries selected Boolean theorem premises and replays their actual evidence" premiseQueries
    , testCase "shares and reuses a bounded allowance across selected theorem premises" boundedPremiseQueries
    , testCase "keeps premise queries inside their inherited terms and nominal assumptions" premiseQueryDomains
    , testCase "retains canonical support through selected theorem premise queries" premiseQuerySupport
    , testCase "distinguishes quantified Boolean instances from supplied ground facts" universalInstanceBaseline
    , testCase "replays generic universal instances through binders, views and branches" universalInstances
    , testCase "bounds generic attempts without claiming missing terms or empty inventories" universalInstanceLimits
    , testCase "upgrades existing universal instances after their attempt allowance stops" universalInstanceSupport
    , testCase "shares generic attempts across suspended owned queries" universalInstanceOwnership
    , testCase "retains one generic turn ahead of a pending split across yields" universalInstanceSplitTurn
    , testCase "gives another universal its turn after a speculative miss" universalInstanceSourceTurns
    , testCase "keeps universal arguments fixed across equality and late proposition rows" universalInstanceInventory
    , testCase "inherits parent attempts while charging each sibling's new instance" universalInstanceInheritance
    , testCase "does not export a branch-local universal to its sibling" universalInstanceSibling
    , testCase "isolates the existing-term universal ordering gap" universalHintOrdering
    , testCase "keeps hint stops separate from the enumerable pair set" universalHintLimits
    , testCase "shares the last hint turn across owned queries" universalHintOwnership
    , testCase "keeps fallback source order independent of the hint streak" universalHintSourceFairness
    , testCase "uses positive atoms and negative equalities as complementary hint events" universalHintSignedLeaves
    , testCase "preserves hint allowances at late source and signed-event frontiers" universalHintArrivals
    , testCase "streams polarity-directed universal hints with exact work boundaries" universalHintLeaves
    , testCase "stops universal hints at nested binders and undetermined leaves" universalHintBoundaries
    , testCase "preserves ambient typing in universal hint patterns" universalHintAmbient
    , testCase "replays a certified view with non-dense imports" sameContext
    , testCase "weakens a parent view and discharges only the child assumption" descendantContext
    , testCase "rebuilds roots below a universal in a nested ambient context" universalContext
    , testCase "rejects sibling scopes, opaque term lifting and mismatched statements" rejectsWrongAssociations
    , testCase "never asserts parent-goal seed syntax" seedIsNotEvidence
    , testCase "charges failed catalogue admissions across queries" failedAdmissions
    , testCase "shares branch and conversion allowances across queries" cumulativeResources
    , testCase "admits the bridged discharge through the declaration method policy" declarationAdmission
    , testCase "resumes root preparation and splits with the serial result and costs" incrementalGround
    , testCase "rejects replenishment when a ground session resumes" rejectsSessionReplenishment
    , testCase "yields between exact rule applications and equality orientations" incrementalRuleApplications
    , testCase "freezes family seeds before the first residual query" firstResidualUsesFrozenSeed
    , testCase "shares a paid frozen domain across separately budgeted queries" sharedFrozenDomain
    , testCase "keeps family syntax, asserted roots and query negations separate" frozenSyntaxIsNotEvidence
    , testCase "rejects non-propositional expansion by residuals and certified inputs" rejectsFrozenDomainExpansion
    , testCase "rejects frozen-domain reuse below a new term binder" rejectsFrozenDomainContext
    , testCase "rejects owned domains across same-shaped sibling scopes" rejectsSameShapedOwnedDomains
    , testCase "shares an owned domain with its assumption descendants" sharesOwnedDomainWithDescendants
    , testCase "resumes the current owned query after another query spends work" resumesCurrentOwnedQuery
    , testCase "resumes existing split children with a late certified parent fact" resumesSplitWithCertifiedInput
    , testCase "keeps duplicate and outside-domain late inputs neutral and charged" ignoresUnusableLateInputs
    , testCase "propagates canonical source use through actual ground recipes" groundSupportRecipes
    , testCase "upgrades an existing ground rule instance from a late duplicate" groundSupportExistingInstance
    , testCase "keeps child support upgrades out of sibling recipes" groundSupportBranches
    , testCase "retains ordinary ground closure before later canonical roots" groundSupportPendingRoots
    , testCase "resumes canonical demand on the same closed ground query" groundSupportClosedInput
    , testCase "retains either closed sibling while seeking canonical support" groundSupportClosedSiblings
    , testCase "upgrades existing ground equalities and signed transport" groundSupportEquality
    , testCase "upgrades an existing rule instance through its equality witness" groundSupportEqualityInstance
    , testCase "publishes canonical ground evidence without focused credit" ownedCanonicalGround
    , testCase "delivers shared ground evidence after focused work is exhausted" sharedGroundDelivery
    , testCase "seeds selected goal variants without granting premise seed rights" selectedGoalGround
    , testCase "exposes local aliases in predicate arguments with checked transport" localAliasArguments
    , testCase "uses a cited predicate equation before an incidental argument alias" citedPredicateBeforeAlias
    , testCase "uses the cited equality operand before an uncited representation" citedEqualityOperand
    , testCase "directly eliminates a cited membership equation" citedMembershipEquation
    , testCase "uses concrete congruence before expanding unrelated facts" concreteEqualityBeforeConversion
    , testCase "applies a theorem through a supplied local argument equality" suppliedArgumentEquality
    , testCase "assembles nested conjunctions without searching intermediate groups" conjunctionTree
    , testCase "retains a supplied theorem for an internal conjunction" conjunctionTheorem
    , testCase "proves alias-dependent premises of a cited definition" citedDefinitionPremise
    , testCase "uses either orientation of an equality from a cited definition" citedDefinitionEquality
    , testCase "bounds directed goal-view cycles without asserting syntax" selectedGoalCycle
    , testCase "feeds a selected fact to the existing ground query" publishedFactGround
    , testCase "starts a frozen query with one or two certified selected facts" selectedFactStartup
    , testCase "retains charged input preparation across a selected domain" preparedFrozenInput
    , testCase "keeps published fact views out of sibling assumption scopes" publishedFactScopeIsolation
    ])

allowance :: Scope.GroundAllowance
allowance = Scope.GroundAllowance 1000000 10000 256 1000 Scope.UniversalsDisabled

emptySet :: CanonicalTerm global
emptySet = CIntrinsic Empty

one :: CanonicalTerm global
one = CApp (CApp (CIntrinsic OrderedPair) emptySet) emptySet

p, q, d :: CanonicalTerm global -> CanonicalTerm global
p argument = CApp (CApp (CIntrinsic Member) argument) emptySet
q argument = CApp (CApp (CIntrinsic Member) argument) one
d argument = CEq TySet argument one

equation :: CanonicalTerm global -> CanonicalTerm global
equation argument = CEq TyProp (d argument) (COr (p argument) (q argument))

checked :: [CoreType] -> CanonicalTerm Void -> IO (ScopedCheckedCore Void)
checked context = expectRight . checkScopedCanonicalCore emptyGlobalTyping context

expectRight :: Show failure => Either failure result -> IO result
expectRight = either (\failure -> assertFailure (show failure) >> fail "unexpected failure") pure

groundProof
    :: Scope.ScopeId request
    -> [ScopedCheckedCore Void]
    -> [Scope.Evidence request Void]
    -> ScopedCheckedCore Void
    -> Scope.Scoped request Void (Scope.Evidence request Void)
groundProof scope seeds facts target = do
    (_statistics, result) <- Scope.scopeRefute emptyGlobalTyping scope seeds facts target
    case result of
        Left failure -> Except.throwE (Scope.ObviousIntegrityFailure
            (Proof.ProofStructuralCompositionMismatch (fromString (show failure))))
        Right evidence -> pure evidence

groundResult
    :: Scope.ScopeId request
    -> [ScopedCheckedCore Void]
    -> ScopedCheckedCore Void
    -> Scope.Scoped request Void
        (Ground.RefutationStatistics, Either Ground.RefutationFailure ())
groundResult scope seeds target = do
    (statistics, result) <- Scope.scopeRefute emptyGlobalTyping scope seeds [] target
    pure (statistics, () <$ result)

assertReplays
    :: Foundation.CheckedFoundation
    -> [ScopedCheckedCore Void]
    -> [(ImportIx, FrozenCheckedCore Void)]
    -> ScopedCheckedCore Void
    -> Proof.BuiltProof Void
    -> Set HypothesisIx
    -> Assertion
assertReplays foundation hypotheses imports target proof expectedHypotheses = do
    let remapping = Map.fromList [(original, importIx (fromIntegral index))
            | (index, (original, _)) <- zip [0 :: Int ..] imports]
    remapped <- maybe (assertFailure "bridge lost an exact import association" >> fail "bad remapping") pure
        (remapKernelDerivationImports (`Map.lookup` remapping) (Proof.builtProofDerivation proof))
    replayImports <- traverse (expectRight . derivationImportJudgement . snd) imports
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping (Vector.fromList replayImports) (Vector.fromList hypotheses) target remapped)
    assertEqual "exact external hypothesis uses" expectedHypotheses
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "exact densely remapped import uses" (Set.fromList (Map.elems remapping))
        (replayedScopedKernelImportUses replayed)

membershipSubset :: Natural -> Natural -> CanonicalTerm Void
membershipSubset a b = CForall TySet
    (CImp (membershipAt 0 (a + 1)) (membershipAt 0 (b + 1)))

membershipAt :: Natural -> Natural -> CanonicalTerm Void
membershipAt x a = CApp (CApp (CIntrinsic Member) (CBound x)) (CBound a)

membershipSchema :: [CanonicalTerm Void] -> CanonicalTerm Void
membershipSchema guards = CForall TySet (CForall TySet
    (foldr CImp (CEq TySet (CBound 1) (CBound 0))
        (guards <> [membershipSubset 1 0, membershipSubset 0 1])))

-- A and B cover U; each is included in V, which is included in U.
membershipCover :: [CanonicalTerm Void]
membershipCover =
    [ CForall TySet (CImp (membershipAt 0 2) (COr (membershipAt 0 4) (membershipAt 0 3)))
    , membershipSubset 3 0
    , membershipSubset 2 0
    , membershipSubset 0 1
    ]

membershipExtensionality :: Assertion
membershipExtensionality = do
    foundation <- expectRight Foundation.checkedFoundation
    facts <- traverse (checked (replicate 4 TySet)) (membershipSchema [] : membershipCover)
    target <- checked (replicate 4 TySet) (CEq TySet (CBound 1) (CBound 0))
    repeated <- checked (replicate 4 TySet) (CAnd (scopedCoreTerm target) (scopedCoreTerm target))
    let run policy goal = Scope.obviousProofReportWithPolicy
            (extensionalityTestPolicy { Scope.policyExtensionality = policy })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] goal
        off = run Scope.ExtensionalityDisabled target
        zero = run (Scope.MembershipExtensionality 0) target
    assertSearchMiss "the implicit equality needs pointwise scope permission" off
    assertSearchMiss "enabled zero grants no scope" zero
    assertEqual "disabled performs no selected applications" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics off))
    assertBool "disabled does not discover deferred applications"
        (not (Scope.obviousExtensionalityDeferred (Scope.obviousRunStatistics off)))
    assertEqual "enabled zero debits no application" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics zero))
    assertBool "enabled zero observes an actually prevented application"
        (Scope.obviousExtensionalityDeferred (Scope.obviousRunStatistics zero))
    for_ [1, 2, 4] \cap -> for_ [target, repeated] \goal -> do
        let report = run (Scope.MembershipExtensionality cap) goal
        proof <- expectRight (Scope.obviousRunResult report)
        assertReplays foundation facts [] goal (Scope.obviousBuiltProof proof)
            (Set.fromList (hypothesisIx <$> [0 .. 4]))
        assertEqual "both directions and repeated consumers share one application" 1
            (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics report))
    paired <- traverse (checked (replicate 4 TySet))
        (take 3 membershipCover <>
            [ CForall TySet (CImp (membershipAt 0 1) (COr (membershipAt 0 4) (membershipAt 0 3)))
            , membershipSubset 3 1, membershipSubset 2 1 ])
    imported <- expectRight (checkCanonicalCore emptyGlobalTyping (membershipSchema []))
    let report = Scope.obviousProofReportWithPolicy extensionalityTestPolicy
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping paired
            [Scope.obviousImport (importIx 7) imported] [] target
    proof <- expectRight (Scope.obviousRunResult report)
    assertReplays foundation paired [(importIx 7, imported)] target (Scope.obviousBuiltProof proof)
        (Set.fromList (hypothesisIx <$> [0 .. 5]))
    assertEqual "an imported application owns both nontrivial directions" 1
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics report))
    let selectedSchema = CForall TySet (CForall TySet (CImp CTruth
            (CAnd CTruth (CImp (membershipSubset 1 0)
                (CImp (membershipSubset 0 1) (CEq TySet (CBound 1) (CBound 0)))))))
    selectedFacts <- traverse (checked (replicate 4 TySet)) (selectedSchema : membershipCover)
    for_ [target, repeated] \goal -> do
        let selected = Scope.obviousProofReportWithPolicy extensionalityTestPolicy
                Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping selectedFacts [] [] goal
        selectedProof <- expectRight (Scope.obviousRunResult selected)
        assertReplays foundation selectedFacts [] goal (Scope.obviousBuiltProof selectedProof)
            (Set.fromList (hypothesisIx <$> [0 .. 4]))
        assertEqual "a selected program retains one stable scoped application" 1
            (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics selected))

membershipExtensionalityBoundaries :: Assertion
membershipExtensionalityBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checked (replicate 4 TySet) (CEq TySet (CBound 1) (CBound 0))
    let run terms = do
            facts <- traverse (checked (replicate 4 TySet)) terms
            pure (facts, Scope.obviousProofReportWithPolicy extensionalityTestPolicy
                Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] target)
    (_, missingCover) <- run (membershipSchema [] : take 2 membershipCover <> drop 3 membershipCover)
    assertSearchMiss "a missing covering branch cannot be supplied by the schema" missingCover
    (_, missingSchema) <- run membershipCover
    assertSearchMiss "pointwise evidence alone cannot assert equality" missingSchema
    (_, missingGuard) <- run (membershipSchema [p (CBound 1)] : membershipCover)
    assertSearchMiss "a recognized schema does not discharge its guard" missingGuard
    assertEqual "a failed earlier guard does not open pointwise scopes" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics missingGuard))
    (_, pointwiseGuard) <- run (membershipSchema [membershipSubset 1 0] : membershipCover)
    assertSearchMiss "a pointwise-shaped guard keeps ordinary premise restrictions" pointwiseGuard
    assertEqual "only the final pair can receive scope permission" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics pointwiseGuard))
    (guardedFacts, guarded) <- run (membershipSchema [p (CBound 1)] : p (CBound 1) : membershipCover)
    proof <- expectRight (Scope.obviousRunResult guarded)
    assertReplays foundation guardedFacts [] target (Scope.obviousBuiltProof proof)
        (Set.fromList (hypothesisIx <$> [0 .. 5]))
    let unrelated = CForall TySet (CForall TySet
            (CImp (CForall TySet (CImp (membershipAt 0 2) (p (CBound 0))))
                (CImp (membershipSubset 0 1) (CEq TySet (CBound 1) (CBound 0)))))
    (_, nearby) <- run (unrelated : membershipCover)
    assertSearchMiss "an equality and unrelated universal premise do not qualify" nearby
    assertEqual "the nearby theorem receives no application allowance" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics nearby))

membershipExtensionalityScopes :: Assertion
membershipExtensionalityScopes = do
    foundation <- expectRight Foundation.checkedFoundation
    let equality = CEq TySet (CBound 1) (CBound 0)
        missingCover = membershipSchema [] : take 2 membershipCover <> drop 3 membershipCover
        selectedCover = membershipSubset 2 0
        branch = CImp selectedCover equality
        run terms goal = do
            facts <- traverse (checked (replicate 4 TySet)) terms
            target <- checked (replicate 4 TySet) goal
            pure (facts, target, Scope.obviousProofReportWithPolicy
                (extensionalityTestPolicy { Scope.policyExtensionality = Scope.MembershipExtensionality 2 })
                Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] target)
    (facts, siblingTarget, siblings) <- run missingCover
        (CAnd branch (CImp (CAnd selectedCover CTruth) equality))
    proof <- expectRight (Scope.obviousRunResult siblings)
    assertReplays foundation facts [] siblingTarget (Scope.obviousBuiltProof proof)
        (Set.fromList (hypothesisIx <$> [0 .. 3]))
    assertEqual "distinct assumption scopes share the request cap, not their branch" 2
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics siblings))
    (_, _, missingSibling) <- run missingCover (CAnd branch (CImp (p (CBound 1)) equality))
    assertSearchMiss "one sibling cannot inherit the other's covering assumption" missingSibling
    (_, _, restrictedPremise) <- run (CImp equality (q one) : membershipSchema [] : membershipCover) (q one)
    assertSearchMiss "E5 theorem premises cannot acquire extensionality scopes" restrictedPremise
    assertEqual "restricted premises create no application" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics restrictedPremise))
    (_, _, restrictedWitness) <- run (membershipSchema [] : membershipCover)
        (CExists TySet (CEq TySet (CBound 2) (CBound 1)))
    assertSearchMiss "E3 witness bodies cannot acquire extensionality scopes" restrictedWitness
    assertEqual "restricted witnesses create no application" 0
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics restrictedWitness))

membershipExtensionalitySupport :: Assertion
membershipExtensionalitySupport = do
    foundation <- expectRight Foundation.checkedFoundation
    facts <- traverse (checked (replicate 5 TySet)) (membershipSchema [] : membershipCover)
    definition <- checked (replicate 5 TySet)
        (CForall TySet (CEq TyProp (membershipAt 0 1) (membershipAt 0 3)))
    irrelevant <- checked (replicate 5 TySet)
        (CForall TySet (CEq TyProp (membershipAt 0 5) (membershipAt 0 5)))
    target <- checked (replicate 5 TySet) (CEq TySet (CBound 1) (CBound 0))
    repeated <- checked (replicate 5 TySet) (CAnd (scopedCoreTerm target) (scopedCoreTerm target))
    let run requirement view goal = Scope.obviousProofReportWithPolicy extensionalityTestPolicy
            Scope.defaultObviousBudget requirement foundation emptyGlobalTyping (facts <> [view]) []
            [Scope.obviousLocalDefinitionView 5 Semantic.DefinitionMembershipView] goal
        ordinary = run Scope.AnyObviousProof definition repeated
        supported = run Scope.MustUseCanonicalDefinition definition repeated
    ordinaryProof <- expectRight (Scope.obviousRunResult ordinary)
    assertReplays foundation (facts <> [definition]) [] repeated (Scope.obviousBuiltProof ordinaryProof)
        (Set.fromList (hypothesisIx <$> [0 .. 4]))
    supportedProof <- expectRight (Scope.obviousRunResult supported)
    assertReplays foundation (facts <> [definition]) [] repeated (Scope.obviousBuiltProof supportedProof)
        (Set.fromList (hypothesisIx <$> [0 .. 5]))
    assertEqual "canonical support reuses the selected application after its cap" 1
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics supported))
    assertSearchMiss "recognition and an unused definition provide no canonical support"
        (run Scope.MustUseCanonicalDefinition irrelevant target)

membershipExtensionalityResources :: Assertion
membershipExtensionalityResources = do
    foundation <- expectRight Foundation.checkedFoundation
    facts <- traverse (checked (replicate 4 TySet)) (membershipSchema [] : membershipCover)
    target <- checked (replicate 4 TySet) (CEq TySet (CBound 1) (CBound 0))
    let run budget = Scope.obviousProofReportWithPolicy extensionalityTestPolicy
            budget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
        ample = run Scope.defaultObviousBudget
        statistics = Scope.obviousRunStatistics ample
        checks =
            [ (Scope.ObviousFocusedWorkLimit, Scope.obviousFocusedWorkConsumed statistics,
                \work -> Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = work}, Scope.obviousFocusedWorkConsumed)
            , (Scope.ObviousRefutationWorkLimit, Scope.obviousRefutationWorkConsumed statistics,
                \work -> Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = work}, Scope.obviousRefutationWorkConsumed)
            , (Scope.ObviousConversionPoolLimit, Scope.obviousConversionWorkConsumed statistics,
                \work -> Scope.defaultObviousBudget {Scope.obviousConversionPool = Conversion.conversionPool work}, Scope.obviousConversionWorkConsumed)
            ]
    _ <- expectRight (Scope.obviousRunResult ample)
    for_ checks \(resource, spent, budget, consumed) -> do
        assertBool "the complete request spends the tested resource" (spent > 0)
        exact <- expectRight (Scope.obviousRunResult (run (budget spent)))
        assertReplays foundation facts [] target (Scope.obviousBuiltProof exact)
            (Set.fromList (hypothesisIx <$> [0 .. 4]))
        let short = run (budget (spent - 1))
        assertEqual "one-short reconstruction reports its actual exhausted owner"
            (Left (Scope.ObviousResourceExhausted resource)) (() <$ Scope.obviousRunResult short)
        assertEqual "failed work remains spent" (spent - 1) (consumed (Scope.obviousRunStatistics short))
        assertEqual "failure does not refund the selected application" 1
            (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics short))
    let openingAt work = run Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = work}
        opens work = Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics (openingAt work)) > 0
        boundary low high
            | high - low <= 1 = high
            | opens middle = boundary low middle
            | otherwise = boundary middle high
          where middle = low + (high - low) `div` 2
        firstOpening = boundary 0 (Scope.obviousFocusedWorkConsumed statistics)
        failedSetup = openingAt firstOpening
    assertBool "the adjacent lower budget cannot debit scope setup" (not (opens (firstOpening - 1)))
    assertEqual "failed setup preserves the paid application" 1
        (Scope.obviousExtensionalityAttempts (Scope.obviousRunStatistics failedSetup))
    assertEqual "failed setup retains its actual disposition"
        (Left (Scope.ObviousResourceExhausted Scope.ObviousFocusedWorkLimit))
        (() <$ Scope.obviousRunResult failedSetup)
    assertEqual "failed setup spends its whole admitted budget" firstOpening
        (Scope.obviousFocusedWorkConsumed (Scope.obviousRunStatistics failedSetup))

suppliedExistentials :: Assertion
suppliedExistentials = do
    foundation <- expectRight Foundation.checkedFoundation
    let cases =
            [ ("projection", [], [CExists TySet (CAnd (p (CBound 0)) (q (CBound 0)))], CExists TySet (q (CBound 0)), 1)
            , ("uniform consequence", [], [CExists TySet (p (CBound 0)), CForall TySet (CImp (p (CBound 0)) (q one))], q one, 2)
            , ("nested projection", [], [CExists TySet (CExists TySet (CAnd (p (CBound 1)) (q (CBound 0))))], CExists TySet (q (CBound 0)), 1)
            , ("ambient function", [TyArrow TySet TySet],
                [CExists TySet (CAnd (p (CBound 0)) (q (CApp (CBound 1) (CBound 0))))],
                CExists TySet (q (CApp (CBound 1) (CBound 0))), 1)
            ]
    for_ cases \(label, types, terms, goal, sourceCount) -> do
        facts <- traverse (checked types) terms
        target <- checked types goal
        let run policy = Scope.obviousProofReportWithPolicy
                (existentialTestPolicy { Scope.policyExistentials = policy })
                Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
        assertSearchMiss (label <> " needs an opening") (run Scope.ExistentialsDisabled)
        let report = run (Scope.SuppliedExistentials 4)
        proof <- expectRight (Scope.obviousRunResult report)
        assertReplays foundation facts [] target (Scope.obviousBuiltProof proof)
            (Set.fromList (hypothesisIx <$> [0 .. sourceCount - 1]))
        assertBool (label <> " shares the opening allowance")
            (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics report) <= 4)
        assertEqual "an elimination branch starts no selected fact domain" 0
            (Scope.obviousFactDomainsStarted (Scope.obviousRunStatistics report))
    imported <- expectRight (checkCanonicalCore emptyGlobalTyping
        (CExists TySet (CAnd (p (CBound 0)) (q (CBound 0)))))
    importedTarget <- checked [TySet] (CExists TySet (q (CBound 0)))
    let importedReport = Scope.obviousProofReportWithPolicy
            (existentialTestPolicy { Scope.policyExistentials = Scope.SuppliedExistentials 1 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping []
            [Scope.obviousImport (importIx 7) imported] [] importedTarget
    importedProof <- expectRight (Scope.obviousRunResult importedReport)
    assertReplays foundation [] [(importIx 7, imported)] importedTarget
        (Scope.obviousBuiltProof importedProof) Set.empty

boundedExistentials :: Assertion
boundedExistentials = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checked [] (CExists TySet (CAnd (p (CBound 0)) (q (CBound 0))))
    nested <- checked [] (CExists TySet (CExists TySet (CAnd (p (CBound 1)) (q (CBound 0)))))
    target <- checked [] (CExists TySet (q (CBound 0)))
    repeated <- checked [] (CAnd (scopedCoreTerm target) (scopedCoreTerm target))
    let run cap facts goal = Scope.obviousProofReportWithPolicy
            (existentialTestPolicy { Scope.policyExistentials = Scope.SuppliedExistentials cap })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] goal
        zero = run 0 [source] target
    assertSearchMiss "zero cannot open the supplied source" zero
    assertEqual "zero spends no opening" 0 (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics zero))
    assertBool "zero records an actually prevented source" (Scope.obviousExistentialsDeferred (Scope.obviousRunStatistics zero))
    for_ [target, repeated] \goal -> do
        let report = run 1 [source] goal
        proof <- expectRight (Scope.obviousRunResult report)
        assertReplays foundation [source] [] goal (Scope.obviousBuiltProof proof) (Set.singleton (hypothesisIx 0))
        assertEqual "repeated ordinary consumers reuse the one opening" 1
            (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics report))
    assertSearchMiss "one opening cannot supply the nested body" (run 1 [nested] target)
    let nestedReport = run 2 [nested] target
    nestedProof <- expectRight (Scope.obviousRunResult nestedReport)
    assertEqual "the weakened ancestor is skipped and the nested body opens" 2
        (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics nestedReport))
    assertReplays foundation [nested] [] target (Scope.obviousBuiltProof nestedProof) (Set.singleton (hypothesisIx 0))
    -- A supplied but unhelpful ancestor cannot repeatedly open itself below its
    -- own eigenvariable, even when there is ample soft opening credit.
    missingSource <- checked [] (CExists TySet (p (CBound 0)))
    let missing = run 4 [missingSource] target
    assertSearchMiss "missing body evidence stays missing" missing
    assertEqual "an ancestor is not a new source after weakening" 1
        (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics missing))
    assertBool "completed source traversal is not soft truncation"
        (not (Scope.obviousExistentialsDeferred (Scope.obviousRunStatistics missing)))

existentialScopes :: Assertion
existentialScopes = do
    foundation <- expectRight Foundation.checkedFoundation
    let source = CExists TySet (CAnd (p (CBound 0)) (q (CBound 0)))
        target = CExists TySet (q (CBound 0))
        sibling = CAnd (CImp source target) (CImp source target)
        missing = CAnd (CImp source target) (CImp (CExists TySet (p (CBound 0))) target)
        run facts goal = Scope.obviousProofReportWithPolicy
            (existentialTestPolicy { Scope.policyExistentials = Scope.SuppliedExistentials 4 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] goal
    siblingTarget <- checked [] sibling
    proof <- expectRight (Scope.obviousRunResult (run [] siblingTarget))
    assertReplays foundation [] [] siblingTarget (Scope.obviousBuiltProof proof) Set.empty
    missingTarget <- checked [] missing
    assertSearchMiss "a sibling cannot use the other branch's body" (run [] missingTarget)
    premise <- checked [] (CExists TySet (p (CBound 0)))
    independent <- checked [] (p emptySet)
    assertSearchMiss "an eigenvariable cannot become a chosen outer argument" (run [premise] independent)
    -- These compound parents have no supplied existential to open. The source
    -- appears only after a restricted derived child introduces its assumption.
    inhabitant <- checked [] (CEq TySet emptySet emptySet)
    witnessBody <- checked [] (CExists TySet (CImp source target))
    let restrictedWitness = run [inhabitant] witnessBody
    assertSearchMiss "an E3 witness body cannot acquire opening rights" restrictedWitness
    assertEqual "restricted witness assumptions create no opening" 0
        (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics restrictedWitness))
    theorem <- checked [] (CImp (CImp source target) (q one))
    conclusion <- checked [] (q one)
    let restrictedPremise = run [theorem] conclusion
    assertSearchMiss "an E5 premise cannot acquire opening rights" restrictedPremise
    assertEqual "restricted theorem assumptions create no opening" 0
        (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics restrictedPremise))
    -- The only value of this function type is syntax in the other conjunct.
    -- Opening for the existential subgoal must retain the original seed roots;
    -- the fresh set variable alone is not a witness of the required type.
    let functionType = TyArrow TyProp TySet
        value = CLam TyProp emptySet
        needsOriginalSeed = CAnd (CExists functionType (q one))
            (CEq functionType value value)
    constantSource <- checked [] (CExists TySet (q one))
    seededTarget <- checked [] needsOriginalSeed
    seededProof <- expectRight (Scope.obviousRunResult (run [constantSource] seededTarget))
    assertReplays foundation [constantSource] [] seededTarget (Scope.obviousBuiltProof seededProof)
        (Set.singleton (hypothesisIx 0))

existentialSupport :: Assertion
existentialSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checked [] (CExists TySet (CAnd (p (CBound 0)) (q (CBound 0))))
    definition <- checked [] (CForall TySet (CEq TyProp (p (CBound 0)) (q (CBound 0))))
    irrelevant <- checked [] (CForall TySet (CEq TyProp (d (CBound 0)) (d (CBound 0))))
    target <- checked [] (CExists TySet (q (CBound 0)))
    repeated <- checked [] (CAnd (scopedCoreTerm target) (scopedCoreTerm target))
    let run requirement view goal = Scope.obviousProofReportWithPolicy
            (existentialTestPolicy { Scope.policyExistentials = Scope.SuppliedExistentials 1 })
            Scope.defaultObviousBudget requirement foundation emptyGlobalTyping [source, view] []
            [Scope.obviousLocalDefinitionView 1 Semantic.DefinitionPointwiseView] goal
        ordinary = run Scope.AnyObviousProof definition repeated
        supported = run Scope.MustUseCanonicalDefinition definition repeated
    ordinaryProof <- expectRight (Scope.obviousRunResult ordinary)
    assertReplays foundation [source, definition] [] repeated (Scope.obviousBuiltProof ordinaryProof)
        (Set.singleton (hypothesisIx 0))
    supportedProof <- expectRight (Scope.obviousRunResult supported)
    assertReplays foundation [source, definition] [] repeated (Scope.obviousBuiltProof supportedProof)
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])
    assertEqual "canonical consumers reuse the ordinary elimination branch" 1
        (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics supported))
    assertSearchMiss "an unused definition cannot support existential discharge"
        (run Scope.MustUseCanonicalDefinition irrelevant target)

existentialResources :: Assertion
existentialResources = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checked [] (CExists TySet (q one))
    target <- checked [] (q one)
    let run work = Scope.obviousProofReportWithPolicy
            (existentialTestPolicy { Scope.policyExistentials = Scope.SuppliedExistentials 1 })
            Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = work, Scope.obviousRefutationWorkLimit = 0}
            Scope.AnyObviousProof foundation emptyGlobalTyping [source] [] [] target
        ample = run 100000
        spent = Scope.obviousFocusedWorkConsumed (Scope.obviousRunStatistics ample)
    _ <- expectRight (Scope.obviousRunResult ample)
    exact <- expectRight (Scope.obviousRunResult (run spent))
    assertReplays foundation [source] [] target (Scope.obviousBuiltProof exact) (Set.singleton (hypothesisIx 0))
    let short = run (spent - 1)
    assertEqual "one-short existential discharge exhausts its actual owner"
        (Left (Scope.ObviousResourceExhausted Scope.ObviousFocusedWorkLimit))
        (() <$ Scope.obviousRunResult short)
    assertEqual "failed discharge does not refund work" (spent - 1)
        (Scope.obviousFocusedWorkConsumed (Scope.obviousRunStatistics short))
    assertEqual "the failed attempt still owns its one opening" 1
        (Scope.obviousExistentialOpenings (Scope.obviousRunStatistics short))
    -- Find the admission boundary without pinning the test to bookkeeping
    -- constants. At the first paid opening there is no work left for setup.
    case [(work, report) | work <- [1 .. spent - 1], let report = run work,
            Scope.obviousExistentialOpenings (Scope.obviousRunStatistics report) == 1] of
        [] -> assertFailure "no charged opening precedes completed construction"
        (work, report) : _ -> do
            assertEqual "failed setup retains the actual hard failure"
                (Left (Scope.ObviousResourceExhausted Scope.ObviousFocusedWorkLimit))
                (() <$ Scope.obviousRunResult report)
            assertEqual "failed setup spends its admitted work" work
                (Scope.obviousFocusedWorkConsumed (Scope.obviousRunStatistics report))

existingWitnesses :: Assertion
existingWitnesses = do
    foundation <- expectRight Foundation.checkedFoundation
    let conditional coreType = CExists coreType (COr
            (CAnd (CBound 3) (CEq coreType (CBound 0) (CBound 2)))
            (CAnd (CNot (CBound 3)) (CEq coreType (CBound 0) (CBound 1))))
        functionType = TyArrow TySet TySet
        cases =
            [ ("direct equality", [], [], CExists TySet (CEq TySet (CBound 0) emptySet), 1, Set.empty)
            , ("set conditional true", [TySet, TySet, TyProp], [CBound 2], conditional TySet, 1, Set.singleton (hypothesisIx 0))
            , ("set conditional false", [TySet, TySet, TyProp], [CNot (CBound 2)], conditional TySet, 4, Set.singleton (hypothesisIx 0))
            , ("function conditional true", [functionType, functionType, TyProp], [CBound 2], conditional functionType, 1, Set.singleton (hypothesisIx 0))
            , ("function conditional false", [functionType, functionType, TyProp], [CNot (CBound 2)], conditional functionType, 4, Set.singleton (hypothesisIx 0))
            , ("first-order fact", [], [p one], CExists TySet (p (CBound 0)), 1, Set.singleton (hypothesisIx 0))
            , ("inventory fallback", [], [CEq TySet emptySet emptySet], CExists TySet CTruth, 1, Set.empty)
            , ("nested witnesses", [], [CEq TySet emptySet emptySet], CExists TySet (CExists TySet (CEq TySet (CBound 1) (CBound 0))), 1, Set.singleton (hypothesisIx 0))
            ]
    for_ cases \(label, types, facts, goal, minimumPrefix, uses) -> do
        hypotheses <- traverse (checked types) facts
        target <- checked types goal
        let run policy = Scope.obviousProofReportWithPolicy
                (Scope.disabledSearchPolicy { Scope.policyWitnesses = policy })
                Scope.defaultObviousBudget
                Scope.AnyObviousProof foundation emptyGlobalTyping hypotheses [] [] target
        assertSearchMiss (label <> " is new coverage") (run Scope.WitnessesDisabled)
        for_ [prefix | prefix <- [1, 4, 8], prefix >= minimumPrefix] \prefix -> do
            let report = run (Scope.ExistingWitnesses prefix 32)
            proof <- expectRight (Scope.obviousRunResult report)
            assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof) uses
            assertBool (label <> " uses a bounded nonempty witness prefix")
                (Scope.obviousWitnessAttempts (Scope.obviousRunStatistics report) > 0
                 && Scope.obviousWitnessAttempts (Scope.obviousRunStatistics report) <= 32)
        unless (null facts) do
            let missing = Scope.obviousProofReportWithPolicy
                    (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 4 32 })
                    Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping [] [] [] target
            assertSearchMiss (label <> " missing evidence/inhabitant") missing

assertSearchMiss :: String -> Scope.ObviousRunReport Void -> Assertion
assertSearchMiss label report = case Scope.obviousRunResult report of
    Right _ -> assertFailure (label <> ": unexpectedly proved")
    Left failure -> case Scope.obviousFailureClass failure of
        Scope.ObviousIntegrityClass -> assertFailure (label <> ": " <> show failure)
        Scope.ObviousMalformedClass -> assertFailure (label <> ": " <> show failure)
        Scope.ObviousResourceExhaustedClass{} -> assertFailure (label <> ": " <> show failure)
        _ -> pure ()

boundedWitnesses :: Assertion
boundedWitnesses = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TySet, TySet, TyProp]
        bad = CAnd (CBound 3) (CEq TySet (CBound 0) (CBound 2))
        good = CAnd (CNot (CBound 3)) (CEq TySet (CBound 0) (CBound 1))
    fact <- checked types (CNot (CBound 2))
    target <- checked types (CExists TySet (COr bad (COr bad good)))
    let run policy = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = policy })
            Scope.defaultObviousBudget
            Scope.AnyObviousProof foundation emptyGlobalTyping [fact] [] [] target
    for_ [Scope.ExistingWitnesses 0 32, Scope.ExistingWitnesses 1 32, Scope.ExistingWitnesses 8 0, Scope.ExistingWitnesses 8 1] \policy -> do
        let report = run policy
        assertSearchMiss "an exhausted soft prefix does not try the later witness" report
        let statistics = Scope.obviousRunStatistics report
        assertBool "a real candidate is recorded as deferred" (Scope.obviousWitnessesDeferred statistics)
        case policy of
            Scope.ExistingWitnesses perObligation total -> assertBool "the public summary retains zero/one witness policies"
                (Scope.ObviousWitnessBreadth perObligation total (Scope.obviousWitnessAttempts statistics) True
                    `elem` Scope.obviousBreadthObservations statistics)
            Scope.WitnessesDisabled -> assertFailure "the fixture lost its enabled witness policy"
    let report = run (Scope.ExistingWitnesses 2 2)
    proof <- expectRight (Scope.obviousRunResult report)
    assertEqual "duplicate equality hints spend no extra witness attempt" 2
        (Scope.obviousWitnessAttempts (Scope.obviousRunStatistics report))
    assertReplays foundation [fact] [] target (Scope.obviousBuiltProof proof) (Set.singleton (hypothesisIx 0))
    assertBool "exact-cap completion is not a public deferral"
        (Scope.ObviousWitnessBreadth 2 2 2 False `elem` Scope.obviousBreadthObservations (Scope.obviousRunStatistics report))
    inhabitant <- checked [] (CEq TySet emptySet emptySet)
    nested <- checked [] (CExists TySet (CExists TySet (CEq TySet (CBound 1) (CBound 0))))
    let nestedReport = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 8 1 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping [inhabitant] [] [] nested
    assertSearchMiss "nested search shares the request cap" nestedReport
    assertEqual "the nested child cannot refresh its witness allowance" 1
        (Scope.obviousWitnessAttempts (Scope.obviousRunStatistics nestedReport))
    assertBool "the prevented nested witness is reported" (Scope.obviousWitnessesDeferred (Scope.obviousRunStatistics nestedReport))
    equality <- checked [] (CExists TySet (CEq TySet (CBound 0) emptySet))
    let counted work = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 1 1 })
            Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = work, Scope.obviousRefutationWorkLimit = 0}
            Scope.AnyObviousProof foundation emptyGlobalTyping [] [] [] equality
        ample = counted 100000
        spent = Scope.obviousFocusedWorkConsumed (Scope.obviousRunStatistics ample)
    _ <- expectRight (Scope.obviousRunResult ample)
    exact <- expectRight (Scope.obviousRunResult (counted spent))
    assertReplays foundation [] [] equality (Scope.obviousBuiltProof exact) Set.empty
    assertBool "the complete witness path charges discovery and reconstruction" (spent > 1)
    let short = counted (spent - 1)
    assertEqual "one-short complete witness construction exhausts the actual focused owner"
        (Left (Scope.ObviousResourceExhausted Scope.ObviousFocusedWorkLimit))
        (() <$ Scope.obviousRunResult short)
    assertEqual "failed witness work is not refunded" (spent - 1)
        (Scope.obviousFocusedWorkConsumed (Scope.obviousRunStatistics short))

-- The short implication chain completes after the selected outside-domain
-- package has captured its next source opportunity. The final pending snapshot
-- distinguishes cancellation here from a proof that never reached activation.
cancelsPendingFactDomain :: Assertion
cancelsPendingFactDomain = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyArrow TySet TyProp, TyArrow TySet TyProp, TyProp, TySet]
        pairWithEmpty argument = CApp (CApp (CIntrinsic OrderedPair) argument) emptySet
        definition = CForall TySet (CEq TyProp (CApp (CBound 1) (CBound 0))
            (COr (p (pairWithEmpty (CBound 0))) (CBound 3)))
        contradiction = CForall TySet (CImp (p (pairWithEmpty (CBound 0))) CFalsum)
        atom :: Int -> CanonicalTerm Void
        atom position = p (COpaqueInteger (100 + fromIntegral position))
        links = [CImp (atom index) (atom (index + 1)) | index <- [0 .. 3]]
    target <- checked types (CBound 2)
    facts <- traverse (checked types)
        ([CApp (CBound 0) emptySet, definition, contradiction, atom 0]
            <> links <> [CImp (atom 4) (CBound 2)])
    for_ [Scope.WitnessesDisabled, Scope.ExistingWitnesses 4 32] \policy -> do
        let run requirement = Scope.obviousProofReportWithPolicy
                (Scope.disabledSearchPolicy { Scope.policyWitnesses = policy })
                Scope.defaultObviousBudget requirement foundation emptyGlobalTyping facts []
                [Scope.obviousLocalDefinitionView 1 Semantic.DefinitionPointwiseView] target
            ordinary = run Scope.AnyObviousProof
            statistics = Scope.obviousRunStatistics ordinary
        proof <- expectRight (Scope.obviousRunResult ordinary)
        assertEqual "the optional package had reached its captured opportunity" 1
            (Scope.obviousPendingFactDomainOpportunities statistics)
        assertEqual "the completed ordinary consumer cancels that pending start" 0
            (Scope.obviousFactDomainsStarted statistics)
        assertEqual "the later direct proof wins before ground branch search" 0
            (Scope.obviousBranchNodesCreated statistics)
        assertReplays foundation facts [] target (Scope.obviousBuiltProof proof)
            (Set.fromList (map hypothesisIx [3 .. 8]))
        let canonical = run Scope.MustUseCanonicalDefinition
        supported <- expectRight (Scope.obviousRunResult canonical)
        assertEqual "ordinary evidence does not cancel a still-needed canonical consumer" 1
            (Scope.obviousFactDomainsStarted (Scope.obviousRunStatistics canonical))
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList facts) target
            (Proof.builtProofDerivation (Scope.obviousBuiltProof supported)))
        assertBool "the canonical consumer actually uses the selected definition"
            (Set.member (hypothesisIx 1) (replayedScopedKernelExternalHypothesisUses replayed))

sharedCycles :: Assertion
sharedCycles = do
    foundation <- expectRight Foundation.checkedFoundation
    let existential = CExists TySet (p (CBound 0))
    facts <- traverse (checked [])
        [ CEq TyProp (p emptySet) existential, CEq TySet emptySet emptySet ]
    target <- checked [] (CAnd existential existential)
    let run requirement budget = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 1 1
                })
            budget requirement foundation emptyGlobalTyping facts []
            [Scope.obviousLocalDefinitionView 0 Semantic.DefinitionExactView] target
        ordinary = run Scope.AnyObviousProof Scope.defaultObviousBudget
        canonical = run Scope.MustUseCanonicalDefinition Scope.defaultObviousBudget
    -- Ordinary consumers return through the active-request guard; canonical
    -- consumers retain the shared support cycle until the scheduler fixed point.
    case Scope.obviousRunResult ordinary of
        Left Scope.ObviousRepeatedState{} -> pure ()
        other -> assertFailure ("ordinary cycle: " <> show (() <$ other))
    assertEqual "the unmet canonical consumer retains its support failure"
        (Left Scope.ObviousCanonicalDefinitionEvidenceRequired)
        (() <$ Scope.obviousRunResult canonical)
    for_ [Scope.AnyObviousProof, Scope.MustUseCanonicalDefinition] $ \requirement -> do
        let exhausted = run requirement Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = 0}
        assertEqual "resource failure takes precedence over a cyclic miss"
            (Left (Scope.ObviousResourceExhausted Scope.ObviousFocusedWorkLimit))
            (() <$ Scope.obviousRunResult exhausted)

witnessSupport :: Assertion
witnessSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    ordinary <- checked [TySet] (p emptySet)
    definition <- checked [TySet] (CEq TyProp (p emptySet) CTruth)
    let powerset = CApp (CIntrinsic PowerSet) emptySet
    irrelevant <- checked [TySet] (CEq TySet powerset powerset)
    existential <- checked [TySet] (CExists TySet (p (CBound 0)))
    conjunction <- checked [TySet] (CAnd (scopedCoreTerm existential) (scopedCoreTerm existential))
    let view = Scope.obviousLocalDefinitionView 1 Semantic.DefinitionExactView
        run requirement facts views goal = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 1 1 })
            Scope.defaultObviousBudget requirement foundation emptyGlobalTyping facts [] views goal
        supported = run Scope.MustUseCanonicalDefinition [ordinary, definition] [view] conjunction
    proof <- expectRight (Scope.obviousRunResult supported)
    assertEqual "later support and repeated existential consumers reuse one attempt" 1
        (Scope.obviousWitnessAttempts (Scope.obviousRunStatistics supported))
    assertReplays foundation [ordinary, definition] [] conjunction (Scope.obviousBuiltProof proof)
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])
    let ordinaryOnly = run Scope.AnyObviousProof [ordinary] [] conjunction
    reused <- expectRight (Scope.obviousRunResult ordinaryOnly)
    assertEqual "ordinary consumers also share their existential producer" 1
        (Scope.obviousWitnessAttempts (Scope.obviousRunStatistics ordinaryOnly))
    assertReplays foundation [ordinary] [] conjunction (Scope.obviousBuiltProof reused)
        (Set.singleton (hypothesisIx 0))
    assertSearchMiss "merely proposing a term grants no canonical authority"
        (run Scope.MustUseCanonicalDefinition [ordinary, irrelevant] [view] existential)

witnessDomains :: Assertion
witnessDomains = do
    foundation <- expectRight Foundation.checkedFoundation
    let powerset = CApp (CIntrinsic PowerSet)
        excluded term = COr (p term) (CNot (p term))
        goal = CExists TySet (CAnd (CEq TySet (CBound 0) emptySet) (excluded (powerset (CBound 0))))
    target <- checked [] goal
    present <- checked [] (CEq TyProp (p (powerset emptySet)) (p (powerset emptySet)))
    let run facts = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 1 32 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
    assertSearchMiss "a witness body cannot seed its new application" (run [])
    let allowed = run [present]
    proof <- expectRight (Scope.obviousRunResult allowed)
    assertReplays foundation [present] [] target (Scope.obviousBuiltProof proof) Set.empty
    assertEqual "read-only witness search starts no selected fact domains" 0
        (Scope.obviousFactDomainsStarted (Scope.obviousRunStatistics allowed))
    inhabitant <- checked [] (CEq TySet emptySet emptySet)
    underBinder <- checked [] (CExists TySet (CForall TySet (excluded (CBound 0))))
    let restricted = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 1 32 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping [inhabitant] [] [] underBinder
    assertSearchMiss "a witness body cannot acquire a new universal seed family" restricted
    let siblingGoal second = CAnd
            (CImp (p (CBound 1)) (CExists TySet (p (CBound 0))))
            (CImp (second (CBound 0)) (CExists TySet (p (CBound 0))))
        runSibling goal' = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 4 32 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping [] [] [] goal'
    siblings <- checked [TySet, TySet] (siblingGoal p)
    let siblingReport = runSibling siblings
    siblingProof <- expectRight (Scope.obviousRunResult siblingReport)
    assertEqual "same-shaped sibling scopes own separate witnesses" 2
        (Scope.obviousWitnessAttempts (Scope.obviousRunStatistics siblingReport))
    assertReplays foundation [] [] siblings (Scope.obviousBuiltProof siblingProof) Set.empty
    missingSibling <- checked [TySet, TySet] (siblingGoal q)
    assertSearchMiss "a sibling cannot use another assumption scope's existential proof" (runSibling missingSibling)
    let types = [TyArrow TySet TyProp]
        applied = CApp (CBound 1) (CBound 0)
    definition <- checked types (CForall TySet (CEq TyProp applied (excluded (powerset (CBound 0)))))
    viewed <- checked types (CExists TySet (CAnd (CEq TySet (CBound 0) emptySet) applied))
    seeded <- checked types (scopedCoreTerm present)
    let withView facts = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy { Scope.policyWitnesses = Scope.ExistingWitnesses 1 32 })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts []
            [Scope.obviousLocalDefinitionView 0 Semantic.DefinitionPointwiseView] viewed
    assertSearchMiss "a selected witness-body view cannot create a larger seed family" (withView [definition])
    viewedProof <- expectRight (Scope.obviousRunResult (withView [definition, seeded]))
    assertReplays foundation [definition, seeded] [] viewed (Scope.obviousBuiltProof viewedProof)
        (Set.singleton (hypothesisIx 0))

premiseResult :: CanonicalTerm global -> CanonicalTerm global
premiseResult argument = CApp (CApp (CIntrinsic Member) argument)
    (CApp (CApp (CIntrinsic OrderedPair) one) one)

universalInstanceBaseline :: Assertion
universalInstanceBaseline = do
    foundation <- expectRight Foundation.checkedFoundation
    universal <- checked [] (CForall TySet (COr (p (CBound 0)) (q (CBound 0))))
    denied <- checked [] (CNot (p emptySet))
    instanceFact <- checked [] (COr (p emptySet) (q emptySet))
    target <- checked [] (q emptySet)
    let run policy budget facts = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyUniversals = policy
                , Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            budget Scope.AnyObviousProof
            foundation emptyGlobalTyping facts [] [] target
    assertSearchMiss "the quantified disjunction is not already instantiated"
        (run Scope.UniversalsDisabled Scope.defaultObviousBudget [universal, denied])
    let enabled = run (Scope.ExistingUniversals 32) Scope.defaultObviousBudget [universal, denied]
    generated <- expectRight (Scope.obviousRunResult enabled)
    assertReplays foundation [universal, denied] [] target (Scope.obviousBuiltProof generated)
        (Set.fromList (map hypothesisIx [0, 1]))
    assertBool "the complete driver actually uses the experiment"
        (Scope.obviousUniversalAttempts (Scope.obviousRunStatistics enabled) > 0)
    let used = Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics enabled)
        bounded work = run (Scope.ExistingUniversals 32)
            Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = work} [universal, denied]
    _ <- expectRight (Scope.obviousRunResult (bounded used))
    assertEqual "the complete driver charges the last required ground operation"
        (Left (Scope.ObviousResourceExhausted Scope.ObviousRefutationWorkLimit))
        (() <$ Scope.obviousRunResult (bounded (used - 1)))
    assertEqual "failed request work remains spent" (used - 1)
        (Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics (bounded (used - 1))))
    proof <- expectRight (Scope.obviousRunResult
        (run Scope.UniversalsDisabled Scope.defaultObviousBudget [instanceFact, denied]))
    assertReplays foundation [instanceFact, denied] [] target (Scope.obviousBuiltProof proof)
        (Set.fromList (map hypothesisIx [0, 1]))

universalInstances :: Assertion
universalInstances = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        source = CForall TySet (COr (p x) (q x))
        beta body = CApp (CLam TyProp (CBound 0)) body
        cases =
            [ ("disjunction", [], source, emptySet)
            , ("partial projections", [], CForall TySet (CAnd (CEq TySet x x) (COr (p x) (q x))), emptySet)
            , ("nested binders", [], CForall TySet (CForall TySet (COr (p (CBound 1)) (q x))), emptySet)
            , ("ambient argument", [TySet], source, CBound 0)
            , ("source view", [], beta source, emptySet)
            , ("body view", [], CForall TySet (beta (COr (p x) (q x))), emptySet)
            , ("branch sources", [], COr source source, emptySet)
            ]
    for_ cases $ \(label, types, universal, argument) -> for_
        [Ground.ExistingUniversals 256, Ground.HintedUniversals 32 128] $ \policy -> do
        hypotheses <- traverse (checked types) [universal, CNot (p argument)]
        target <- checked types (q argument)
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        let limits = groundLimits {Ground.refutationUniversals = policy}
            run selected = Ground.runRefutation selected emptyGlobalTyping context
                (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
            (statistics, result) = run limits
        candidate <- expectRight result
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
            (Set.fromList (map hypothesisIx [0, 1]))
        reversed <- expectRight (snd (Ground.runRefutation limits emptyGlobalTyping context
            (reverse (zipWith Ground.RefutationHypothesis [0 ..] hypotheses)) target))
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof reversed)
            (Set.fromList (map hypothesisIx [0, 1]))
        assertBool (label <> ": bounded actual attempts")
            (Ground.refutationUniversalAttempts statistics > 0 && Ground.refutationUniversalAttempts statistics <= 256)
        let used = Ground.refutationWorkLimit limits - Ground.refutationRemainingWork statistics
        _ <- expectRight (snd (run limits {Ground.refutationWorkLimit = used}))
        case snd (run limits {Ground.refutationWorkLimit = used - 1}) of
            Left Ground.RefutationWorkExhausted -> pure ()
            other -> assertFailure (label <> ": reconstruction escaped the work boundary: " <> either show (const "proved") other)

universalInstanceLimits :: Assertion
universalInstanceLimits = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        functionType = TyArrow TySet TySet
        predicateType = TyArrow TySet TyProp
        source = CForall TySet (COr (p x) (q x))
        cases =
            [ ("missing premise", [], [source], q emptySet, True)
            , ("missing application", [functionType],
                [CForall TySet (COr (p (CApp (CBound 1) x)) (q x))], q emptySet, True)
            , ("fully covered undetermined binder", [], [CForall TySet (CForall TySet (p (CBound 1)))],
                q emptySet, False)
            , ("empty inventory", [predicateType],
                [CForall TySet (COr (CApp (CBound 1) x) (CNot (CApp (CBound 1) x)))], CFalsum, False)
            ]
    for_ cases $ \(label, types, terms, goal, hasCandidates) -> do
        hypotheses <- traverse (checked types) terms
        target <- checked types goal
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        let run policy = Ground.runRefutation groundLimits {Ground.refutationUniversals = policy}
                emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
            (disabledStatistics, _) = run Ground.UniversalsDisabled
        for_ [Ground.UniversalsDisabled, Ground.ExistingUniversals 0, Ground.ExistingUniversals 1] $ \policy -> do
            let (statistics, result) = run policy
                expectedAttempts = if hasCandidates && policy == Ground.ExistingUniversals 1 then 1 else 0
            case result of
                Left Ground.RefutationSaturated -> pure ()
                Left Ground.RefutationUndeterminedParameter{} | not hasCandidates -> pure ()
                other -> assertFailure (label <> ": unexpected outcome " <> either show (const "proved") other)
            assertEqual (label <> ": only real unique candidates spend attempts") expectedAttempts
                (Ground.refutationUniversalAttempts statistics)
            when (policy /= Ground.ExistingUniversals 1) $
                assertEqual (label <> ": zero and disabled have distinct truncation")
                    (hasCandidates && policy == Ground.ExistingUniversals 0)
                    (Ground.refutationUniversalsDeferred statistics)
            when (label == "missing application" && policy == Ground.ExistingUniversals 1) do
                assertEqual "a speculative missing application publishes no formula"
                    (Ground.refutationSignedFormulas disabledStatistics) (Ground.refutationSignedFormulas statistics)
                assertEqual "a speculative missing application admits no term"
                    (Ground.refutationTerms disabledStatistics) (Ground.refutationTerms statistics)
                assertBool "failed speculative preparation consumes actual work"
                    (Ground.refutationRemainingWork statistics < Ground.refutationRemainingWork disabledStatistics)

universalInstanceSupport :: Assertion
universalInstanceSupport = for_ [Ground.ExistingUniversals 1, Ground.HintedUniversals 1 128] $ \policy -> do
    foundation <- expectRight Foundation.checkedFoundation
    let source = CForall TySet (COr (p (CBound 0)) (q (CBound 0)))
        limits = groundLimits
            { Ground.refutationUniversals = policy
            , Ground.refutationRuleInstanceLimit = 0
            }
    hypotheses <- traverse (checked [])
        [source, COr (p emptySet) (q emptySet), source, CNot (p emptySet)]
    target <- checked [] (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    early <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 0]
        (Ground.startRefutation limits emptyGlobalTyping context
            [Ground.RefutationHypothesis index fact | (index, fact) <- zip [0 ..] hypotheses, index == 0 || index == 3] target))
    (_, _, earlyResult) <- finishCanonicalQuery limits early
    earlyProof <- expectRight earlyResult
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof earlyProof)
        (Set.fromList (map hypothesisIx [0, 3]))
    for_ [False, True] $ \alreadyVisible -> do
        let count = if alreadyVisible then 2 else 1
        initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 2]
            (Ground.startRefutation limits emptyGlobalTyping context
                (zipWith Ground.RefutationHypothesis [0 ..] (take count hypotheses)) target))
        (remaining, before, _, parked) <- parkGroundQuery limits initial
        assertEqual "one actual attempt survives the soft stop" 1 (Ground.refutationUniversalAttempts before)
        assertBool "a later inventory argument was prevented" (Ground.refutationUniversalsDeferred before)
        (canonical, uses) <- hypothesisInput context (hypothesisIx 2)
        resumed <- expectRight (Ground.resumeRefutationWithInput canonical uses parked)
        (afterSupport, supported, _, waiting) <- parkGroundQuery remaining resumed
        assertEqual "a canonical upgrade is not another attempt" 1 (Ground.refutationUniversalAttempts supported)
        assertEqual "canonical evidence does not restart hint work after the instance cap"
            (Ground.refutationUniversalHintSteps before) (Ground.refutationUniversalHintSteps supported)
        assertEqual "a canonical upgrade is not another truth"
            (Ground.refutationSignedFormulas before) (Ground.refutationSignedFormulas supported)
        assertBool "support work is actually charged"
            (Ground.refutationRemainingWork supported < Ground.refutationRemainingWork before)
        (denied, deniedUses) <- hypothesisInput context (hypothesisIx 3)
        closing <- expectRight (Ground.resumeRefutationWithInput denied deniedUses waiting)
        (_, statistics, result) <- finishCanonicalQuery afterSupport closing
        proof <- expectRight result
        assertEqual "proof reconstruction did not restart enumeration" 1 (Ground.refutationUniversalAttempts statistics)
        assertEqual "generic work does not spend an exact-rule instance" 0 (Ground.refutationRuleInstances statistics)
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof proof)
            (Set.fromList (map hypothesisIx [2, 3]))

universalInstanceOwnership :: Assertion
universalInstanceOwnership = do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [])
        [CForall TySet (COr (p (CBound 0)) (q (CBound 0))), CNot (p emptySet), CNot (p one)]
    firstTarget <- checked [] (q emptySet)
    secondTarget <- checked [] (q one)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000)
            allowance {Scope.groundUniversals = Scope.ExistingUniversals 1} context Map.empty \scope -> do
                inputs <- traverse (Scope.scopeHypothesis scope . hypothesisIx) [0, 1, 2]
                first <- Scope.scopeStartGround emptyGlobalTyping scope [] inputs firstTarget
                second <- Scope.scopeStartGround emptyGlobalTyping scope [] inputs secondTarget
                _ <- freezeOwnedQuery second
                (firstStatistics, firstProof) <- finishOwnedQuery first >>= \case
                    Scope.GroundQueryFinished statistics (Right evidence) -> pure (statistics, Scope.evidenceProof evidence)
                    _ -> boundaryFailure "the first query did not construct its universal instance"
                remaining <- lift Scope.currentGroundLimits
                secondStatistics <- finishOwnedQuery second >>= \case
                    Scope.GroundQueryBlocked statistics Ground.RefutationSaturated -> pure statistics
                    _ -> boundaryFailure "the second query escaped the shared allowance"
                pure (firstStatistics, firstProof, remaining, secondStatistics)
    (firstStatistics, firstProof, remaining, secondStatistics) <- expectRight result
    assertEqual "the shared request has no attempts left" (Ground.ExistingUniversals 0)
        (Ground.refutationUniversals remaining)
    assertEqual "the first query spends the last attempt" 1 (Ground.refutationUniversalAttempts firstStatistics)
    assertReplays foundation hypotheses [] firstTarget firstProof
        (Set.fromList (map hypothesisIx [0, 1]))
    assertEqual "the suspended query cannot restore its original attempt" 0 (Ground.refutationUniversalAttempts secondStatistics)
    assertBool "the second query records its prevented candidate" (Ground.refutationUniversalsDeferred secondStatistics)

universalInstanceSplitTurn :: Assertion
universalInstanceSplitTurn = for_ [Ground.ExistingUniversals 32, Ground.HintedUniversals 32 128] $ \policy ->
  for_ [False, True] $ \initialSplit -> do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TySet, TySet, TyArrow TySet TyProp, TyArrow TySet TyProp]
        disjunction offset = COr (CApp (CBound (3 + offset)) (CBound 0))
            (CApp (CBound (2 + offset)) (CBound 0))
    hypotheses <- traverse (checked types)
        (CForall TySet (disjunction 1) : [disjunction 0 | initialSplit])
    target <- checked types (CEq TySet (CBound 0) (CBound 1))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    let limits = groundLimits {Ground.refutationUniversals = policy}
        initial = Ground.startRefutation limits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        untilSplit turns available session = do
            assertBool "the first pending split is serviced" (turns < (1000 :: Int))
            case Ground.advanceRefutation available session of
                (remaining, Ground.RefutationPending next) -> do
                    let statistics = Ground.refutationSessionStatistics next
                    when (Ground.refutationUniversalAttempts statistics == 1) $
                        case Ground.advanceRefutation remaining {Ground.refutationUniversals = case Ground.refutationUniversals remaining of
                                Ground.HintedUniversals _ hints -> Ground.HintedUniversals 32 hints
                                _ -> Ground.ExistingUniversals 32} next of
                            (_, Ground.RefutationFinished _ (Left Ground.RefutationInternalFailure{})) -> pure ()
                            _ -> assertFailure "a retained session accepted a replenished generic attempt"
                    if Ground.refutationBranchNodes statistics > 1 then
                        assertEqual "resuming does not grant another pre-split turn" 1
                            (Ground.refutationUniversalAttempts statistics)
                    else untilSplit (turns + 1) remaining next
                _ -> assertFailure "the fixture stopped before the pending split"
    untilSplit 0 limits initial

universalInstanceSourceTurns :: Assertion
universalInstanceSourceTurns = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyArrow TySet TySet]
        x = CBound 0
        missing = p (CApp (CBound 1) x)
    hypotheses <- traverse (checked types)
        [CForall TySet (COr missing missing), CForall TySet (COr (p x) (q x)), CNot (p emptySet)]
    target <- checked types (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    let inputs = zipWith Ground.RefutationHypothesis [0 ..] hypotheses
        limits = groundLimits {Ground.refutationUniversals = Ground.ExistingUniversals 2}
    for_ [inputs, reverse inputs] $ \ordered -> do
        let (statistics, result) = Ground.runRefutation limits emptyGlobalTyping context ordered target
        candidate <- expectRight result
        assertBool "one source cannot drain the two-attempt allowance"
            (Ground.refutationUniversalAttempts statistics <= 2)
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
            (Set.fromList (map hypothesisIx [1, 2]))

universalInstanceInventory :: Assertion
universalInstanceInventory = for_ [Ground.ExistingUniversals 32, Ground.HintedUniversals 32 128] $ \policy -> do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [])
        [ CForall TySet (CNot (p emptySet))
        , CEq TySet emptySet one
        , CImp (q emptySet) (q emptySet)
        ]
    target <- checked [] CFalsum
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    seeds <- case hypotheses of
        first : second : _ -> pure (first :| [second])
        _ -> assertFailure "the inventory fixture lost its source or equality" >> fail "missing seeds"
    let limits = groundLimits {Ground.refutationUniversals = policy}
    for_ [1, 2] $ \count -> do
        let initial = Ground.startRefutationFromSeed limits emptyGlobalTyping context
                seeds (zipWith Ground.RefutationHypothesis [0 ..] (take count hypotheses)) target
        (remaining, before, failure, parked) <- parkGroundQuery limits initial
        assertEqual "the seed's two concrete set terms remain two candidates" 2
            (Ground.refutationUniversalAttempts before)
        assertEqual "an exhausted finite inventory is not truncated" False (Ground.refutationUniversalsDeferred before)
        assertEqual "no contradictory signed evidence was supplied" Ground.RefutationSaturated failure
        (late, uses) <- hypothesisInput context (hypothesisIx 2)
        resumed <- expectRight (Ground.resumeRefutationWithInput late uses parked)
        (_, after, _, _) <- parkGroundQuery remaining resumed
        assertEqual "late proposition admission does not restart the fixed inventory" 2
            (Ground.refutationUniversalAttempts after)

universalInstanceInheritance :: Assertion
universalInstanceInheritance = for_ [Ground.ExistingUniversals, \count -> Ground.HintedUniversals count 128] $ \policy -> do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [])
        [ CForall TySet (CNot (p (CBound 0)))
        , COr (q emptySet) (q one)
        , CImp (q emptySet) (p one)
        , CImp (q one) (p one)
        ]
    target <- checked [] CFalsum
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let run count = Ground.runRefutation groundLimits {Ground.refutationUniversals = policy count}
            emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        (statistics, result) = run 3
    candidate <- expectRight result
    assertEqual "one inherited parent attempt and one fresh attempt in each sibling" 3
        (Ground.refutationUniversalAttempts statistics)
    assertEqual "both Boolean alternatives actually ran" 3 (Ground.refutationBranchNodes statistics)
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
        (Set.fromList (map hypothesisIx [0, 1, 2, 3]))
    case snd (run 2) of
        Left Ground.RefutationSaturated -> pure ()
        other -> assertFailure ("the right sibling reused a child-only attempt: " <> either show (const "proved") other)

universalInstanceSibling :: Assertion
universalInstanceSibling = for_ [Ground.ExistingUniversals 32, Ground.HintedUniversals 32 128] $ \policy -> do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [])
        [COr (CForall TySet (COr (p (CBound 0)) (q (CBound 0)))) (p one), CNot (p emptySet)]
    target <- checked [] (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let (statistics, result) = Ground.runRefutation
            groundLimits {Ground.refutationUniversals = policy}
            emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
    assertEqual "the branch containing the universal and its sibling both ran" 3
        (Ground.refutationBranchNodes statistics)
    case result of
        Left Ground.RefutationSaturated -> pure ()
        other -> assertFailure ("a universal escaped its branch: " <> either show (const "proved") other)

premiseQueries :: Assertion
premiseQueries = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        cases =
            [ ("excluded middle", [], COr (p x) (CNot (p x)), True, True)
            , ("De Morgan", [CNot (CAnd (CNot (p emptySet)) (CNot (q emptySet)))], COr (p x) (q x), True, True)
            , ("direct disjunction", [COr (p emptySet) (q emptySet)], COr (p x) (q x), False, True)
            , ("missing premise", [], COr (p x) (q x), True, False)
            ]
    for_ cases \(label, terms, premise, needsQuery, hasProof) -> do
        facts <- traverse (checked []) terms
        theorem <- expectRight (checkCanonicalCore emptyGlobalTyping
            (CForall TySet (CImp premise (premiseResult x))))
        target <- checked [] (premiseResult emptySet)
        let run policy budget = Scope.obviousProofReportWithPolicy
                (Scope.disabledSearchPolicy
                    { Scope.policyPremiseQueries = policy
                    , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                    })
                budget Scope.AnyObviousProof foundation emptyGlobalTyping
                facts [Scope.obviousImport (importIx 7) theorem] [] target
        for_ [Scope.PremiseQueriesDisabled, Scope.ExistingPremiseQueries 0,
                Scope.ExistingPremiseQueries 1, Scope.ExistingPremiseQueries 2] \policy -> do
            let report = run policy Scope.defaultObviousBudget
                statistics = Scope.obviousRunStatistics report
                permitted = case policy of
                    Scope.PremiseQueriesDisabled -> False
                    Scope.ExistingPremiseQueries limit -> limit > 0
            if hasProof && (not needsQuery || permitted) then do
                proof <- expectRight (Scope.obviousRunResult report)
                assertReplays foundation facts [(importIx 7, theorem)] target (Scope.obviousBuiltProof proof)
                    (if null facts then Set.empty else Set.singleton (hypothesisIx 0))
            else assertSearchMiss label report
            assertEqual (label <> ": one whole premise owns its query")
                (if needsQuery && permitted then 1 else 0)
                (Scope.obviousPremiseQueriesStarted statistics)
            case policy of
                Scope.PremiseQueriesDisabled -> pure ()
                Scope.ExistingPremiseQueries total -> assertBool (label <> ": public premise-query policy and observations")
                    (Scope.ObviousPremiseQueryBreadth total (if needsQuery && permitted then 1 else 0)
                        (needsQuery && total == 0) `elem` Scope.obviousBreadthObservations statistics)
            assertEqual (label <> ": only a prevented query reports truncation")
                (needsQuery && policy == Scope.ExistingPremiseQueries 0)
                (Scope.obviousPremiseQueriesDeferred statistics)
            assertEqual (label <> ": no new fact domain") 0
                (Scope.obviousFactDomainsStarted statistics)
        when (label == "De Morgan") do
            let report = run (Scope.ExistingPremiseQueries 1) Scope.defaultObviousBudget
                used = Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics report)
                bounded work = run (Scope.ExistingPremiseQueries 1)
                    Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = work}
            assertBool "the complete premise query uses real ground work" (used > 0)
            exact <- expectRight (Scope.obviousRunResult (bounded used))
            assertReplays foundation facts [(importIx 7, theorem)] target (Scope.obviousBuiltProof exact)
                (Set.singleton (hypothesisIx 0))
            assertEqual "one short fails in the real shared pool"
                (Left (Scope.ObviousResourceExhausted Scope.ObviousRefutationWorkLimit))
                (() <$ Scope.obviousRunResult (bounded (used - 1)))
            assertEqual "failed work remains spent" (used - 1)
                (Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics (bounded (used - 1))))

boundedPremiseQueries :: Assertion
boundedPremiseQueries = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        first = COr (p x) (CNot (p x))
        second = COr (q x) (CNot (q x))
    target <- checked [] (premiseResult emptySet)
    for_ [("repeated", first, 1), ("distinct", second, 2)] \(label, premise, needed) -> do
        theorem <- expectRight (checkCanonicalCore emptyGlobalTyping
            (CForall TySet (CImp first (CImp premise (premiseResult x)))))
        let run limit = Scope.obviousProofReportWithPolicy
                (Scope.disabledSearchPolicy
                    { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries limit
                    , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                    })
                Scope.defaultObviousBudget Scope.AnyObviousProof
                foundation emptyGlobalTyping [] [Scope.obviousImport (importIx 0) theorem] [] target
        for_ [0, 1, 2] \limit -> do
            let report = run limit
                statistics = Scope.obviousRunStatistics report
            if limit < needed then assertSearchMiss (label <> " needs another query") report else do
                proof <- expectRight (Scope.obviousRunResult report)
                assertReplays foundation [] [(importIx 0, theorem)] target (Scope.obviousBuiltProof proof) Set.empty
            assertEqual (label <> ": query starts") (min limit needed)
                (Scope.obviousPremiseQueriesStarted statistics)
            assertEqual (label <> ": prevented query") (limit < needed)
                (Scope.obviousPremiseQueriesDeferred statistics)
    -- A failed query for q(a) and a nested theorem's premise cannot each claim
    -- a fresh request allowance. Ordinary focused composition remains usable.
    nested <- traverse (expectRight . checkCanonicalCore emptyGlobalTyping)
        [ CForall TySet (CImp (q x) (premiseResult x))
        , CForall TySet (CImp first (q x)) ]
    let runNested limit = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries limit
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.AnyObviousProof
            foundation emptyGlobalTyping [] (zipWith Scope.obviousImport (map importIx [0, 1]) nested) [] target
    for_ [1, 2] \limit -> do
        let report = runNested limit
        if limit < 2 then assertSearchMiss "nested applications share the query allowance" report else do
            proof <- expectRight (Scope.obviousRunResult report)
            assertReplays foundation [] (zip (map importIx [0, 1]) nested) target
                (Scope.obviousBuiltProof proof) Set.empty
        assertEqual "nested query starts" limit
            (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics report))
        assertEqual "a nested prevented query is reported" (limit < 2)
            (Scope.obviousPremiseQueriesDeferred (Scope.obviousRunStatistics report))
    circular <- expectRight (checkCanonicalCore emptyGlobalTyping
        (CForall TySet (CImp (premiseResult x) (premiseResult x))))
    let circle = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.AnyObviousProof
            foundation emptyGlobalTyping [] [Scope.obviousImport (importIx 0) circular] [] target
    assertSearchMiss "a premise query cannot justify itself" circle
    assertBool "circular demands do not restart their query"
        (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics circle) <= 1)
    opposite <- traverse (expectRight . checkCanonicalCore emptyGlobalTyping)
        [ CForall TySet (CImp (p x) (premiseResult x))
        , CForall TySet (CImp (CNot (p x)) (q x)) ]
    -- Disjunction alternatives explore both missing premises. Each retains
    -- an unproved extra conjunct, so their disjunction is not a tautology.
    both <- checked [] (COr
        (CAnd (premiseResult emptySet) (p one))
        (CAnd (q emptySet) (q one)))
    let isolated = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.AnyObviousProof
            foundation emptyGlobalTyping [] (zipWith Scope.obviousImport (map importIx [0, 1]) opposite) [] both
    assertSearchMiss "opposite query negations cannot become each other's evidence" isolated
    assertEqual "both opposing queries were actually attempted" 2
        (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics isolated))

premiseQueryDomains :: Assertion
premiseQueryDomains = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        powerset = CApp (CIntrinsic PowerSet)
        excluded term = COr (p term) (CNot (p term))
        theoremTerm premise = CForall TySet (CImp premise (premiseResult x))
        run hypotheses theorem views target = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping
            hypotheses [Scope.obviousImport (importIx 0) theorem] views target
    target <- checked [] (premiseResult emptySet)
    theorem <- expectRight (checkCanonicalCore emptyGlobalTyping (theoremTerm (excluded (powerset x))))
    present <- checked [] (CEq TyProp (p (powerset emptySet)) (p (powerset emptySet)))
    let absent = run [] theorem [] target
    assertSearchMiss "a theorem premise cannot seed its missing application" absent
    assertEqual "the failed speculative query still spends its start" 1
        (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics absent))
    admitted <- expectRight (Scope.obviousRunResult (run [present] theorem [] target))
    assertReplays foundation [present] [(importIx 0, theorem)] target (Scope.obviousBuiltProof admitted) Set.empty
    let types = [TyArrow TySet TyProp]
        applied = CApp (CBound 1) x
    definition <- checked types (CForall TySet (CEq TyProp applied (excluded (powerset x))))
    viewedTheorem <- checked types (theoremTerm applied)
    viewedTarget <- checked types (scopedCoreTerm target)
    viewedSeed <- checked types (scopedCoreTerm present)
    let view = Scope.obviousLocalDefinitionView 0 Semantic.DefinitionPointwiseView
    for_ [False, True] \seeded -> do
        let facts = [definition, viewedTheorem] <> [viewedSeed | seeded]
            report = Scope.obviousProofReportWithPolicy
                (Scope.disabledSearchPolicy
                    { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                    , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                    })
                Scope.defaultObviousBudget Scope.AnyObviousProof
                foundation emptyGlobalTyping facts [] [view] viewedTarget
        if seeded then do
            proof <- expectRight (Scope.obviousRunResult report)
            assertReplays foundation facts [] viewedTarget (Scope.obviousBuiltProof proof)
                (Set.fromList [hypothesisIx 0, hypothesisIx 1])
        else assertSearchMiss "a selected premise view cannot enlarge the domain" report
        assertEqual "the selected premise view starts no fact domains" 0
            (Scope.obviousFactDomainsStarted (Scope.obviousRunStatistics report))
    universal <- expectRight (checkCanonicalCore emptyGlobalTyping
        (theoremTerm (CForall TySet (excluded x))))
    let underBinder = run [] universal [] target
    assertSearchMiss "a theorem premise cannot open a new binder domain" underBinder
    assertEqual "the new binder has no premise-query permission" 0
        (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics underBinder))
    ordinary <- expectRight (checkCanonicalCore emptyGlobalTyping (theoremTerm (COr (p x) (q x))))
    let sufficient = CNot (CAnd (CNot (p emptySet)) (CNot (q emptySet)))
        siblingGoal assumption = CAnd
            (CImp sufficient (premiseResult emptySet))
            (CImp assumption (premiseResult emptySet))
    for_ [("compatible assumptions", CAnd sufficient CTruth, True),
            ("unrelated sibling", p one, False)] \(label, assumption, succeeds) -> do
        sibling <- checked [] (siblingGoal assumption)
        let report = run [] ordinary [] sibling
        if succeeds then do
            proof <- expectRight (Scope.obviousRunResult report)
            assertReplays foundation [] [(importIx 0, ordinary)] sibling (Scope.obviousBuiltProof proof) Set.empty
        else assertSearchMiss label report

premiseQuerySupport :: Assertion
premiseQuerySupport = do
    foundation <- expectRight Foundation.checkedFoundation
    let premise = COr (p (CBound 0)) (q (CBound 0))
        source = CForall TySet (CImp premise (premiseResult (CBound 0)))
        condition = CNot (CAnd (CNot (p emptySet)) (CNot (q emptySet)))
    target <- checked [] (premiseResult emptySet)
    ordinary <- checked [] condition
    definition <- checked [] (CEq TyProp condition CTruth)
    theorem <- expectRight (checkCanonicalCore emptyGlobalTyping source)
    let run facts imports views goal = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 1
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.MustUseCanonicalDefinition foundation emptyGlobalTyping
            facts imports views goal
        view = Scope.obviousLocalDefinitionView 1 Semantic.DefinitionExactView
        later = run [ordinary, definition] [Scope.obviousImport (importIx 0) theorem] [view] target
    proof <- expectRight (Scope.obviousRunResult later)
    assertReplays foundation [ordinary, definition] [(importIx 0, theorem)] target
        (Scope.obviousBuiltProof proof) (Set.fromList [hypothesisIx 0, hypothesisIx 1])
    conjunction <- checked [] (CAnd (scopedCoreTerm target) (scopedCoreTerm target))
    let repeated = run [ordinary, definition] [Scope.obviousImport (importIx 0) theorem] [view] conjunction
    repeatedProof <- expectRight (Scope.obviousRunResult repeated)
    assertReplays foundation [ordinary, definition] [(importIx 0, theorem)] conjunction
        (Scope.obviousBuiltProof repeatedProof) (Set.fromList [hypothesisIx 0, hypothesisIx 1])
    for_ [later, repeated] \report -> do
        assertEqual "later support and duplicate consumers reuse the query" 1
            (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics report))
        assertBool "support demand is still usable at the query cap"
            (not (Scope.obviousPremiseQueriesDeferred (Scope.obviousRunStatistics report)))
    -- A reflexive equation on `one` can legitimately support transport into
    -- q(a). This application's syntax is disjoint from every proved target.
    let unrelated = CApp (CIntrinsic PowerSet) emptySet
    irrelevant <- checked [] (CEq TySet unrelated unrelated)
    assertSearchMiss "an unused definition cannot bless a premise proof"
        (run [ordinary, irrelevant] [Scope.obviousImport (importIx 0) theorem] [view] target)
    supplied <- checked [TyProp] (CBound 0)
    theoremDefinition <- checked [TyProp] (CEq TyProp (CBound 0) source)
    scopedCondition <- checked [TyProp] condition
    scopedTarget <- checked [TyProp] (scopedCoreTerm target)
    let supportedSource = run [scopedCondition, supplied, theoremDefinition] []
            [Scope.obviousLocalDefinitionView 2 Semantic.DefinitionExactView] scopedTarget
    fromSource <- expectRight (Scope.obviousRunResult supportedSource)
    assertReplays foundation [scopedCondition, supplied, theoremDefinition] [] scopedTarget
        (Scope.obviousBuiltProof fromSource) (Set.fromList (map hypothesisIx [0, 1, 2]))
    assertEqual "a canonical theorem permits an ordinary ground premise proof" 1
        (Scope.obviousPremiseQueriesStarted (Scope.obviousRunStatistics supportedSource))
    direct <- traverse (checked []) [p emptySet, CImp (p emptySet) (q emptySet)]
    consequent <- checked [] (q emptySet)
    let unattributed = run direct [] [] consequent
    failure <- maybe (assertFailure "ordinary evidence acquired canonical support" >> fail "missing rejection")
        pure (Scope.obviousRunFailure unattributed)
    assertEqual "the theorem owns its shared premise's requirement rejection" []
        (Scope.obviousFailureAuxiliaryCauses failure)
    assertBool "the rejection is still attributed to a root candidate"
        (any ((== Just (Scope.CandidateAuxiliaryRequirementRejected Scope.AuxiliaryTheoremAntecedent))
            . Scope.obviousCandidateAuxiliaryCause) (Scope.obviousFailureCandidates failure))

sameContext :: Assertion
sameContext = do
    foundation <- expectRight Foundation.checkedFoundation
    defined <- checked [] (d emptySet)
    denied <- checked [] (CNot (p emptySet))
    target <- checked [] (q emptySet)
    definition <- expectRight (checkCanonicalCore emptyGlobalTyping (equation emptySet))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [defined, denied])
    let imports = [(importIx 7, definition)]
        (result, remaining, _pool) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance
            context (Map.fromList imports) \scope -> do
                source <- Scope.scopeHypothesis scope (hypothesisIx 0)
                equality <- Scope.scopeImported scope (importIx 7)
                view <- Scope.scopeApplyEquality scope equality source
                negative <- Scope.scopeHypothesis scope (hypothesisIx 1)
                Scope.evidenceProof <$> groundProof scope [] [view, negative] target
    proof <- expectRight result
    assertBool "bridge preparation is charged" (remaining < 1000000)
    assertReplays foundation [defined, denied] imports target proof
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])

descendantContext :: Assertion
descendantContext = do
    foundation <- expectRight Foundation.checkedFoundation
    defined <- checked [] (d emptySet)
    denied <- checked [] (CNot (p emptySet))
    residual <- checked [] (q emptySet)
    target <- checked [] (CImp (CNot (p emptySet)) (q emptySet))
    definition <- expectRight (checkCanonicalCore emptyGlobalTyping (equation emptySet))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [defined])
    let imports = [(importIx 7, definition)]
        (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance
            context (Map.fromList imports) \parent -> do
                source <- Scope.scopeHypothesis parent (hypothesisIx 0)
                equality <- Scope.scopeImported parent (importIx 7)
                view <- Scope.scopeApplyEquality parent equality source
                child <- Scope.scopeAssume parent denied
                negative <- Scope.scopeHypothesis child (hypothesisIx 0)
                body <- groundProof child [target] [view, negative] residual
                Scope.evidenceProof <$> Scope.scopeIntroduceImplication parent body
    proof <- expectRight result
    assertReplays foundation [defined] imports target proof (Set.singleton (hypothesisIx 0))

universalContext :: Assertion
universalContext = do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [TySet])
        [d (CBound 0), CNot (p (CBound 0)), equation (CBound 0)]
    residual <- checked [TySet, TySet] (q (CBound 1))
    target <- checked [TySet] (CForall TySet (q (CBound 1)))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [TySet] hypotheses)
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance
            context Map.empty \parent -> do
                child <- Scope.scopeBind parent TySet
                source <- Scope.scopeHypothesis child (hypothesisIx 0)
                negative <- Scope.scopeHypothesis child (hypothesisIx 1)
                equality <- Scope.scopeHypothesis child (hypothesisIx 2)
                view <- Scope.scopeApplyEquality child equality source
                body <- groundProof child [] [view, negative] residual
                Scope.evidenceProof <$> Scope.scopeIntroduceForall parent body
    proof <- expectRight result
    assertReplays foundation hypotheses [] target proof
        (Set.fromList [hypothesisIx 0, hypothesisIx 1, hypothesisIx 2])

rejectsWrongAssociations :: Assertion
rejectsWrongAssociations = do
    foundation <- expectRight Foundation.checkedFoundation
    proposition <- checked [] (p emptySet)
    other <- checked [] (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [proposition])
    let run :: (forall request. Scope.ScopeId request -> Scope.Scoped request Void ())
            -> Either (Scope.ObviousFailure Void) ()
        run action = case Scope.runScoped 10000 (Conversion.conversionPool 10000) allowance context Map.empty action of
            (result, _, _) -> result
        reject label result = case result of
            Left Scope.ObviousIntegrityFailure{} -> pure ()
            _ -> assertFailure (label <> " was not rejected as an integrity failure")
    reject "sibling evidence" (run \parent -> do
        left <- Scope.scopeAssume parent proposition
        right <- Scope.scopeAssume parent proposition
        evidence <- Scope.scopeHypothesis left (hypothesisIx 0)
        () <$ Scope.scopeAt right evidence)
    reject "opaque proof under a term binder" (run \parent -> do
        evidence <- Scope.scopeHypothesis parent (hypothesisIx 0)
        child <- Scope.scopeBind parent TySet
        () <$ Scope.scopeAt child evidence)
    reject "different statement" (run \scope -> do
        evidence <- Scope.scopeHypothesis scope (hypothesisIx 0)
        Scope.scopeRequireStatement other evidence)
    reject "unpermitted import association" (run \scope -> () <$ Scope.scopeImported scope (importIx 7))

seedIsNotEvidence :: Assertion
seedIsNotEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    parentGoal <- checked [] (CAnd (p emptySet) (q emptySet))
    target <- checked [] (p emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let (result, _, _) = Scope.runScoped 10000 (Conversion.conversionPool 10000) allowance context Map.empty \scope ->
            snd <$> groundResult scope [parentGoal] target
    outcome <- expectRight result
    case outcome of
        Left Ground.RefutationSaturated -> pure ()
        Left failure -> assertFailure ("wrong seed-only failure: " <> show failure)
        Right _ -> assertFailure "parent-goal syntax became an assumption"

failedAdmissions :: Assertion
failedAdmissions = do
    foundation <- expectRight Foundation.checkedFoundation
    firstTarget <- checked [] (p emptySet)
    secondTarget <- checked [] (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let run ground = Scope.runScoped 10000 (Conversion.conversionPool 10000) ground context Map.empty
            \scope -> do
                first <- groundResult scope [] firstTarget
                second <- groundResult scope [] secondTarget
                pure (first, second)
        (result, _, _) = run allowance {Scope.groundTerms = 1}
    ((firstStats, first), (secondStats, second)) <- expectRight result
    assertTermsExhausted first
    assertTermsExhausted second
    assertEqual "the failed first query spent its one admitted row" 1 (Ground.refutationTerms firstStats)
    assertEqual "the second query cannot reallocate that row" 0 (Ground.refutationTerms secondStats)
  where
    assertTermsExhausted = \case
        Left Ground.RefutationGroundTermsExhausted -> pure ()
        Left failure -> assertFailure ("wrong admission failure: " <> show failure)
        Right _ -> assertFailure "term-limited query unexpectedly succeeded"

cumulativeResources :: Assertion
cumulativeResources = do
    foundation <- expectRight Foundation.checkedFoundation
    truth <- checked [] CTruth
    both <- checked [] (CAnd CTruth CTruth)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let run ground firstTarget secondTarget = Scope.runScoped 10000 (Conversion.conversionPool 1000000)
            ground context Map.empty \scope -> do
                first <- groundResult scope [] firstTarget
                second <- groundResult scope [] secondTarget
                pure (first, second)
        (branchResult, _, _) = run allowance {Scope.groundBranches = 1} truth both
    ((firstStats, first), (secondStats, second)) <- expectRight branchResult
    _ <- expectRight first
    case second of
        Left Ground.RefutationBranchesExhausted -> pure ()
        Left failure -> assertFailure ("wrong branch failure: " <> show failure)
        Right _ -> assertFailure "the second query replenished root branches"
    assertEqual "the first query owns the only branch" 1 (Ground.refutationBranchNodes firstStats)
    assertEqual "the second query cannot allocate another root" 0 (Ground.refutationBranchNodes secondStats)
    firstBeta <- checked [] (CApp (CLam TyProp (CBound 0)) CTruth)
    secondBeta <- checked [] (CApp (CLam TyProp CTruth) CTruth)
    let (conversionResult, _, finalPool) = run allowance firstBeta secondBeta
    ((firstConversion, firstProof), (secondConversion, secondProof)) <- expectRight conversionResult
    _ <- expectRight firstProof
    _ <- expectRight secondProof
    let afterFirst = Conversion.conversionPoolAmount (Ground.refutationRemainingConversionPool firstConversion)
        afterSecond = Conversion.conversionPoolAmount (Ground.refutationRemainingConversionPool secondConversion)
    assertBool "the first query consumed conversion" (afterFirst < 1000000)
    assertBool "the second query debits the already-spent pool" (afterSecond < afterFirst)
    assertEqual "the request retains the cumulative remaining pool"
        afterSecond (Conversion.conversionPoolAmount finalPool)

declarationAdmission :: Assertion
declarationAdmission = do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [])
        [d emptySet, CNot (p emptySet), equation emptySet]
    target <- checked [] (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance
            context Map.empty \scope -> do
                source <- Scope.scopeHypothesis scope (hypothesisIx 0)
                negative <- Scope.scopeHypothesis scope (hypothesisIx 1)
                equality <- Scope.scopeHypothesis scope (hypothesisIx 2)
                view <- Scope.scopeApplyEquality scope equality source
                Scope.evidenceProof <$> groundProof scope [] [view, negative] target
    bridged <- expectRight result
    publicHypotheses <- traverse (checked [])
        [d emptySet, CNot (p emptySet), CEq TyProp (d emptySet) (q emptySet)]
    public <- expectRight (Scope.obviousProofWithRequirement
        Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = 0}
        Scope.MustUseCanonicalDefinition foundation emptyGlobalTyping publicHypotheses []
        [Scope.obviousLocalDefinitionView 2 Semantic.DefinitionExactView] target)
    viewHypotheses <- traverse (checked [TyProp])
        [CBound 0, CNot (p emptySet), CEq TyProp (CBound 0) (COr (p emptySet) (q emptySet))]
    viewTarget <- checked [TyProp] (q emptySet)
    selectedView <- expectRight (Scope.obviousProofWithRequirement Scope.defaultObviousBudget
        Scope.MustUseCanonicalDefinition foundation emptyGlobalTyping viewHypotheses []
        [Scope.obviousLocalDefinitionView 2 Semantic.DefinitionExactView] viewTarget)
    for_ [(hypotheses, target, bridged), (publicHypotheses, target, Scope.obviousBuiltProof public),
          (viewHypotheses, viewTarget, Scope.obviousBuiltProof selectedView)] $ \(selectedHypotheses, selectedTarget, proof) -> do
        let derivation = eliminateKernelDerivationVoid (Proof.builtProofDerivation proof)
            scopedHypotheses = map eliminateScopedVoid selectedHypotheses
            types = scopedCoreContext selectedTarget
            closedDerivation = foldl' (flip forallIntroductionDerivation)
                (foldl' (flip implicationIntroductionDerivation) derivation scopedHypotheses) types
            closedTerm = foldl' (flip CForall)
                (foldl' (flip CImp) (scopedCoreTerm (eliminateScopedVoid selectedTarget))
                    (map scopedCoreTerm scopedHypotheses)) types
        closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
        proposition <- expectRight (Identity.validatePropositionContent closure closedTerm)
        relative <- expectRight (safeRelativePath "obvious-bridge.tex")
        let owner = moduleNameFromParts
                (sourceNamespaceIdFromDigest (hashBlake2b256 "obvious-bridge-namespace")) relative
            resolver = Declaration.vampireResolver \_ ->
                assertFailure "certified bridge requested external proof authority" >> fail "unexpected resolver call"
        importCheck <- Declaration.newImportCheck foundation
        imports <- Declaration.prepareImports importCheck [] >>= expectRight
        let run policy = do
                outcome <- Declaration.runModuleDriverFreshIO foundation owner imports resolver
                    (Declaration.admitCheckedDeclaration
                        (Declaration.checkedProofDeclaration (Semantic.proofSyntaxId "obvious-bridge") [] [] [] Nothing
                            [Declaration.checkedCandidate (Declaration.candidateSpec proposition Semantic.SearchEligible [])
                                (Declaration.checkedNoExternalSourceProofPlanning []) :| []] ())
                        (\() -> \case
                            [candidate :| []] -> authorize candidate policy
                            _ -> error "obvious bridge fixture shape"))
                expectRight outcome
            authorize candidate policy =
                Declaration.authorizeKernelProofCandidate candidate do
                    _ <- Declaration.acceptScopedKernelDischarge policy []
                        (Vector.fromList scopedHypotheses) (eliminateScopedVoid selectedTarget) derivation
                    pure closedDerivation
        accepted <- run Declaration.KernelImplicitObvious
        case accepted of
            Declaration.DriverSucceeded{} -> pure ()
            _ -> assertFailure "Declaration rejected the valid bridged discharge"
        definition <- run (Declaration.KernelDefinition (Set.singleton (hypothesisIx 2)))
        case definition of
            Declaration.DriverSucceeded{} -> pure ()
            _ -> assertFailure "Declaration rejected canonical ground evidence with confined DNE"
        missing <- run (Declaration.KernelDefinition Set.empty)
        case missing of
            Declaration.DriverFailed (Declaration.DriverDeclarationFailed
                Declaration.KernelDefinitionEvidenceMissing) _ -> pure ()
            _ -> assertFailure "Definition accepted DNE without actual authorized canonical source use"

groundLimits :: Ground.RefutationLimits
groundLimits = Ground.RefutationLimits 1000000 (Conversion.conversionPool 1000000) 10000 256 1000 True True Ground.UniversalsDisabled

exactPremiseRecipes :: Assertion
exactPremiseRecipes = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        conclusion argument = CApp (CApp (CIntrinsic Member) argument) (COpaqueInteger 91)
        beta proposition = CApp (CLam TyProp (CBound 0)) proposition
        forallRule premise = CForall TySet (CImp premise (conclusion x))
        facts = [p emptySet, q emptySet]
        cases =
            [ ("curried control", [], CForall TySet (CImp (p x) (CImp (q x) (conclusion x))), facts, conclusion emptySet, False)
            , ("conjunction", [], forallRule (CAnd (p x) (q x)), facts, conclusion emptySet, True)
            , ("repeated leaf and truth", [], forallRule (CAnd (CAnd (p x) CTruth) (CAnd (q x) (p x))), facts, conclusion emptySet, True)
            , ("reassociated leaves", [], forallRule (CAnd (p x) (CAnd (q x) (p x))), facts, conclusion emptySet, True)
            , ("several antecedents", [], CForall TySet (CImp (CAnd CTruth (p x)) (CImp CTruth (CImp (CAnd (q x) CTruth) (conclusion x)))), facts, conclusion emptySet, True)
            , ("converted leaf", [], forallRule (CAnd (beta (p x)) (q x)), facts, conclusion emptySet, True)
            , ("converted conjunction", [], forallRule (beta (CAnd (p x) (q x))), facts, conclusion emptySet, True)
            , ("truth demand", [], forallRule CTruth, [], conclusion emptySet, True)
            , ("compound truth demand", [], CForall TySet (CImp (CAnd CTruth CTruth) (CImp CTruth (conclusion x))), [], conclusion emptySet, True)
            , ("equality leaf", [], forallRule (CAnd (p x) (CEq TySet x one)), [p emptySet, CEq TySet emptySet one], conclusion emptySet, True)
            , ("ambient term", [TySet], CForall TySet (CImp (CAnd (p x) (CApp (CApp (CIntrinsic Member) x) (CBound 1))) (conclusion x)),
                [p emptySet, CApp (CApp (CIntrinsic Member) emptySet) (CBound 0)], conclusion emptySet, True)
            , ("two binders", [], CForall TySet (CForall TySet (CImp (CAnd (p (CBound 1)) (q x)) (conclusion (CBound 1)))),
                [p emptySet, q one], conclusion emptySet, True)
            ]
    for_ cases $ \(label, types, rule, premises, goal, newCoverage) -> do
        target <- checked types goal
        for_ [False, True] $ \reversed -> do
            hypotheses <- traverse (checked types) ((if reversed then reverse else id) (rule : premises))
            context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
            let run limits = Ground.runRefutation limits emptyGlobalTyping context
                    (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
                enabled = groundLimits {Ground.refutationExtendedRules = True}
                (statistics, result) = run enabled
                replay candidate = do
                    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                        emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
                        (Proof.builtProofDerivation (Ground.refutationCandidateProof candidate)))
                    assertBool (label <> " uses the original theorem")
                        (Set.member (hypothesisIx (if reversed then fromIntegral (length premises) else 0))
                            (replayedScopedKernelExternalHypothesisUses replayed))
            candidate <- expectRight result
            replay candidate
            assertBool (label <> " exercises exact rule construction") (Ground.refutationRuleInstances statistics > 0)
            case snd (run groundLimits {Ground.refutationExtendedRules = False}) of
                Left Ground.RefutationSaturated | newCoverage -> pure ()
                Right previous | not newCoverage -> replay previous
                previous -> assertFailure (label <> " has an unexpected feature-off outcome: " <>
                    either show (const "proved") previous)
            let used = Ground.refutationWorkLimit enabled - Ground.refutationRemainingWork statistics
            _ <- expectRight (snd (run enabled {Ground.refutationWorkLimit = used}))
            case snd (run enabled {Ground.refutationWorkLimit = used - 1}) of
                Left Ground.RefutationWorkExhausted -> pure ()
                _ -> assertFailure (label <> " did not charge its full reconstruction")
            let instances = Ground.refutationRuleInstances statistics
            _ <- expectRight (snd (run enabled {Ground.refutationRuleInstanceLimit = instances}))
            case snd (run enabled {Ground.refutationRuleInstanceLimit = instances - 1}) of
                Left Ground.RefutationRuleInstancesExhausted -> pure ()
                _ -> assertFailure (label <> " did not bound its actual logical instances")
    for_ [(forallRule (CAnd (p x) (q x)), [p emptySet], Ground.RefutationSaturated),
          (forallRule (COr (p x) (q x)), [p emptySet], Ground.RefutationSaturated),
          (CForall TySet (CForall TySet (CAnd (conclusion (CBound 1)) (q x))), [], Ground.RefutationUndeterminedParameter 1),
          (CForall TySet (CForall TySet (CImp CTruth (conclusion (CBound 1)))), [], Ground.RefutationUndeterminedParameter 1)] $
        \(rule, premises, expected) -> do
            hypotheses <- traverse (checked []) (rule : premises)
            target <- checked [] (conclusion emptySet)
            context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
            case snd (Ground.runRefutation groundLimits {Ground.refutationExtendedRules = True}
                    emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target) of
                Left failure -> assertEqual "missing evidence or unsupported binding stays unavailable" expected failure
                Right _ -> assertFailure "a rule invented its missing premise or binder"

exactPremiseSupport :: Assertion
exactPremiseSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        conclusion argument = CApp (CApp (CIntrinsic Member) argument) (COpaqueInteger 91)
        conjunctive = CForall TySet (CImp (CAnd (p x) (CAnd (q x) (p x))) (conclusion x))
        unconditional = CForall TySet (CImp (CAnd CTruth CTruth) (conclusion x))
        projected = CForall TySet (CAnd (p x) (CImp CTruth (conclusion x)))
        limits = groundLimits {Ground.refutationExtendedRules = True}
    for_ [([conjunctive, p emptySet, q emptySet], p emptySet),
          ([conjunctive, p emptySet, q emptySet], conjunctive),
          ([unconditional], unconditional), ([projected], projected)] $ \(initialTerms, duplicate) -> do
        hypotheses <- traverse (checked []) (initialTerms <> [duplicate])
        target <- checked [] (conclusion emptySet)
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
        let lateIndex = fromIntegral (length initialTerms)
        initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis lateIndex]
            (Ground.startRefutation limits emptyGlobalTyping context
                (zipWith Ground.RefutationHypothesis [0 ..] (take (length initialTerms) hypotheses)) target))
        (ordinaryLimits, ordinary, retained) <- awaitOrdinaryGround limits initial
        assertEqual "initial closure has no unavailable canonical source" Nothing
            (Ground.refutationCandidateCanonicalSource ordinary)
        (remaining, before, failure, waiting) <- parkGroundQuery ordinaryLimits retained
        assertEqual "the canonical consumer survives ordinary success" Ground.RefutationCanonicalSupportMissing failure
        (late, uses) <- hypothesisInput context (hypothesisIx lateIndex)
        resumed <- expectRight (Ground.resumeRefutationWithInput late uses waiting)
        (_, upgraded, result) <- finishCanonicalQuery remaining resumed
        candidate <- expectRight result
        assertEqual "the late predecessor supports the retained recipe"
            (Just (Ground.RefutationCanonicalHypothesis lateIndex)) (Ground.refutationCandidateCanonicalSource candidate)
        assertEqual "support spends no additional logical instance"
            (Ground.refutationRuleInstances before) (Ground.refutationRuleInstances upgraded)
        assertEqual "support spends no additional signed admission"
            (Ground.refutationSignedFormulas before) (Ground.refutationSignedFormulas upgraded)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (Proof.builtProofDerivation (Ground.refutationCandidateProof candidate)))
        assertBool "replay consumes the canonical predecessor"
            (Set.member (hypothesisIx lateIndex) (replayedScopedKernelExternalHypothesisUses replayed))

exactPremiseBranches :: Assertion
exactPremiseBranches = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        sideCondition argument = CApp (CApp (CIntrinsic Member) argument) (COpaqueInteger 91)
        conclusion argument = CApp (CApp (CIntrinsic Member) argument) (COpaqueInteger 92)
        source predicate = CForall TySet (CImp (CAnd (predicate x) (sideCondition x)) (conclusion x))
        rules = [source p, source q]
        cases =
            [ (True, [COr (p emptySet) (q emptySet), sideCondition emptySet])
            , (False, [COr (p emptySet) (q emptySet)])
            , (False, [COr (CAnd (p emptySet) (sideCondition emptySet)) (q emptySet)])
            ]
    target <- checked [] (conclusion emptySet)
    for_ cases $ \(expectedSuccess, premises) -> do
        hypotheses <- traverse (checked []) (rules <> premises)
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
        for_ [False, True] $ \extended -> do
            let limits = groundLimits {Ground.refutationExtendedRules = extended}
                initial = Ground.startRefutation limits emptyGlobalTyping context
                    (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
                drain steps remaining session = do
                    assertBool "case reasoning yields under bounded rule work" (steps < (3000 :: Int))
                    let before = Ground.refutationRuleInstances (Ground.refutationSessionStatistics session)
                        checkQuantum statistics = assertBool "one advance admits at most one logical instance"
                            (Ground.refutationRuleInstances statistics >= before
                                && Ground.refutationRuleInstances statistics - before <= 1)
                    case Ground.advanceRefutation remaining session of
                        (following, Ground.RefutationPending next) -> do
                            checkQuantum (Ground.refutationSessionStatistics next)
                            drain (steps + 1) following next
                        (_, Ground.RefutationBlocked statistics failure _) -> do
                            checkQuantum statistics
                            pure (statistics, Left failure)
                        (_, Ground.RefutationFinished statistics result) -> do
                            checkQuantum statistics
                            pure (statistics, result)
            (statistics, result) <- drain 0 limits initial
            assertBool "the fixture performs actual case reasoning" (Ground.refutationBranchNodes statistics > 1)
            case result of
                Right candidate | expectedSuccess && extended -> do
                    _ <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                        emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
                        (Proof.builtProofDerivation (Ground.refutationCandidateProof candidate)))
                    pure ()
                Left Ground.RefutationSaturated | not (expectedSuccess && extended) -> pure ()
                _ -> assertFailure ("unexpected case-reasoning result: " <> either show (const "proved") result)

exactRuleProjections :: Assertion
exactRuleProjections = do
    foundation <- expectRight Foundation.checkedFoundation
    let x = CBound 0
        conclusion argument = CApp (CApp (CIntrinsic Member) argument) (COpaqueInteger 91)
        conjunction = CForall TySet (CAnd (p x) (q x))
        cases =
            [ ([], [conjunction], p emptySet)
            , ([], [conjunction], q emptySet)
            , ([], [CForall TySet (CAnd (p x) (CAnd (q x) (conclusion x)))], conclusion emptySet)
            , ([], [CForall TySet (CAnd (COr (p x) (q x)) (conclusion x))], conclusion emptySet)
            , ([], [CForall TySet (CAnd (p x) (CImp (q x) (conclusion x))), q emptySet], conclusion emptySet)
            , ([], [CForall TySet (CApp (CLam TyProp (CBound 0)) (CAnd (p x) (q x)))], q emptySet)
            , ([TySet], [CForall TySet (CAnd (p x) (CApp (CApp (CIntrinsic Member) x) (CBound 1)))],
                CApp (CApp (CIntrinsic Member) emptySet) (CBound 0))
            , ([], [COr conjunction conjunction], q emptySet)
            ]
    for_ cases $ \(types, terms, goal) -> do
        hypotheses <- traverse (checked types) terms
        target <- checked types goal
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        let enabled = groundLimits {Ground.refutationExtendedRules = True}
            run limits = Ground.runRefutation limits emptyGlobalTyping context
                (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
            (statistics, result) = run enabled
        proof <- expectRight result
        _ <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (Proof.builtProofDerivation (Ground.refutationCandidateProof proof)))
        case snd (run groundLimits {Ground.refutationExtendedRules = False}) of
            Left Ground.RefutationSaturated -> pure ()
            _ -> assertFailure "a projection fixture was already discharged without projected rules"
        let work = Ground.refutationWorkLimit enabled - Ground.refutationRemainingWork statistics
        _ <- expectRight (snd (run enabled {Ground.refutationWorkLimit = work}))
        case snd (run enabled {Ground.refutationWorkLimit = work - 1}) of
            Left Ground.RefutationWorkExhausted -> pure ()
            _ -> assertFailure "projection reconstruction escaped its work budget"

universalHintOrdering :: Assertion
universalHintOrdering = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 1000
        source = CForall TySet (COr (p (CBound 0)) (q one))
        negative = CNot (p a)
        irrelevant = [CEq TySet (COpaqueInteger index) (COpaqueInteger index) | index <- [10 .. 41]]
        run facts target = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyUniversals = Scope.ExistingUniversals 32
                , Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
    target <- checked [] (q one)
    lateFacts <- traverse (checked []) (source : irrelevant <> [negative])
    earlyFacts <- traverse (checked []) ([source, negative] <> irrelevant)
    let late = run lateFacts target
        early = run earlyFacts target
    assertSearchMiss "the useful existing argument lies beyond fallback's prefix" late
    assertEqual "the unchanged fallback spends its fixed allowance" 32
        (Scope.obviousUniversalAttempts (Scope.obviousRunStatistics late))
    assertBool "fallback has more eligible pairs"
        (Scope.obviousUniversalsDeferred (Scope.obviousRunStatistics late))
    proof <- expectRight (Scope.obviousRunResult early)
    assertEqual "moving the same evidence earlier exposes the needed argument" 3
        (Scope.obviousUniversalAttempts (Scope.obviousRunStatistics early))
    assertReplays foundation earlyFacts [] target (Scope.obviousBuiltProof proof)
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])
    let runHinted turns budget = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyUniversals = Scope.HintedUniversals 32 turns
                , Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            budget Scope.AnyObviousProof foundation emptyGlobalTyping lateFacts [] [] target
        hinted = runHinted 256 Scope.defaultObviousBudget
        hintedStats = Scope.obviousRunStatistics hinted
    hintedProof <- expectRight (Scope.obviousRunResult hinted)
    assertReplays foundation lateFacts [] target (Scope.obviousBuiltProof hintedProof)
        (Set.fromList [hypothesisIx 0, hypothesisIx 33])
    assertBool "hint ordering leaves room in the unchanged instance allowance"
        (Scope.obviousUniversalAttempts hintedStats < 32)
    assertBool "the integrated hint work is counted"
        (Scope.obviousUniversalHintSteps hintedStats > 0 && Scope.obviousUniversalHintSteps hintedStats <= 256)

    let used = Scope.obviousRefutationWorkConsumed hintedStats
        bounded work = runHinted 256 Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = work}
    _ <- expectRight (Scope.obviousRunResult (bounded used))
    assertEqual "the integrated hint path respects its complete-request work boundary"
        (Left (Scope.ObviousResourceExhausted Scope.ObviousRefutationWorkLimit))
        (() <$ Scope.obviousRunResult (bounded (used - 1)))
    assertEqual "a failed hint request keeps its actual expenditure" (used - 1)
        (Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics (bounded (used - 1))))

    -- Stopping hint work leaves the same fallback universe. Use the early
    -- argument control, whose proof does not depend on finding a late hint.
    let shorter = Scope.obviousProofReportWithPolicy
            (Scope.disabledSearchPolicy
                { Scope.policyUniversals = Scope.HintedUniversals 32 1
                , Scope.policyPremiseQueries = Scope.ExistingPremiseQueries 2
                , Scope.policyWitnesses = Scope.ExistingWitnesses 4 32
                })
            Scope.defaultObviousBudget Scope.AnyObviousProof foundation emptyGlobalTyping earlyFacts [] [] target
    shorterProof <- expectRight (Scope.obviousRunResult shorter)
    assertReplays foundation earlyFacts [] target (Scope.obviousBuiltProof shorterProof)
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])
    assertEqual "fallback completes after the single hint turn" 1
        (Scope.obviousUniversalHintSteps (Scope.obviousRunStatistics shorter))
    assertBool "a hint stop does not remove fallback candidates"
        (not (Scope.obviousUniversalsDeferred (Scope.obviousRunStatistics shorter)))

universalHintLimits :: Assertion
universalHintLimits = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checked [] (CForall TySet (CNot (p (CBound 0))))
    seed <- checked [] (p one)
    target <- checked [] CFalsum
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [source])
    let run policy = finishFrozenQuery groundLimits {Ground.refutationUniversals = policy}
            (Ground.startRefutationFromSeed groundLimits {Ground.refutationUniversals = policy}
                emptyGlobalTyping context (source :| [seed]) [Ground.RefutationHypothesis 0 source] target)
    (_, fallback, fallbackResult) <- run (Ground.ExistingUniversals 32)
    case fallbackResult of
        Left Ground.RefutationSaturated -> pure ()
        _ -> assertFailure "negative facts alone proved falsity"
    for_ [(Ground.HintedUniversals 32 0, Just 0), (Ground.HintedUniversals 32 1, Just 1),
            (Ground.HintedUniversals 32 128, Nothing)] $ \(policy, expectedSteps) -> do
        (_, statistics, result) <- run policy
        case result of
            Left Ground.RefutationSaturated -> pure ()
            _ -> assertFailure "hint scanning changed the signed-fact semantics"
        assertEqual "the snapshot contains one source and two unique eligible pairs" 2
            (Ground.refutationUniversalAttempts statistics)
        assertEqual "enumeration stays on the one unsplit branch" 1 (Ground.refutationBranchNodes statistics)
        assertEqual "hints neither invent nor lose admissible instances"
            (Ground.refutationSignedFormulas fallback) (Ground.refutationSignedFormulas statistics)
        assertEqual "enumerating every pair is not truncation" False (Ground.refutationUniversalsDeferred statistics)
        for_ expectedSteps $ \steps -> assertEqual "the hint stop preserves its exact spent allowance" steps
            (Ground.refutationUniversalHintSteps statistics)
        when (expectedSteps == Just 0) $
            assertEqual "zero hint allowance performs no hint discovery"
                (Ground.refutationRemainingWork fallback) (Ground.refutationRemainingWork statistics)
    (_, zero, _) <- run (Ground.HintedUniversals 0 128)
    assertEqual "no instance allowance means no hint work" 0 (Ground.refutationUniversalHintSteps zero)
    assertEqual "a hint cannot bypass the instance cap" 0 (Ground.refutationUniversalAttempts zero)
    assertBool "the real untried pair is still reported" (Ground.refutationUniversalsDeferred zero)

universalHintSignedLeaves :: Assertion
universalHintSignedLeaves = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = COpaqueInteger 1000
        irrelevant = [CEq TySet (COpaqueInteger index) (COpaqueInteger index) | index <- [10 .. 41]]
        cases =
            [ (CForall TySet (CNot (p (CBound 0))), p a, CFalsum)
            , (CForall TySet (COr (CEq TySet (CBound 0) emptySet) (q one)), CNot (CEq TySet a emptySet), q one)
            ]
    for_ cases $ \(source, event, goal) -> do
        hypotheses <- traverse (checked []) (source : irrelevant <> [event])
        target <- checked [] goal
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
        let run policy = Ground.runRefutation groundLimits {Ground.refutationUniversals = policy}
                emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        case snd (run (Ground.ExistingUniversals 32)) of
            Left Ground.RefutationSaturated -> pure ()
            _ -> assertFailure "the signed hint fixture lost its fallback-ordering gap"
        let (statistics, result) = run (Ground.HintedUniversals 32 128)
        candidate <- expectRight result
        assertBool "a complementary signed event selects the useful argument within the same cap"
            (Ground.refutationUniversalAttempts statistics < 32)
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
            (Set.fromList (map hypothesisIx [0, 33]))

universalHintSourceFairness :: Assertion
universalHintSourceFairness = do
    foundation <- expectRight Foundation.checkedFoundation
    let goal = q emptySet
        useful = CForall TySet (COr goal goal)
        distractor index = CForall TySet (CNot (CApp (CApp (CIntrinsic Member) (CBound 0)) (COpaqueInteger index)))
    hypotheses <- traverse (checked []) (useful : map distractor [10 .. 13])
    target <- checked [] goal
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    for_ [Ground.ExistingUniversals 1, Ground.HintedUniversals 1 128] $ \policy -> do
        let (statistics, result) = Ground.runRefutation groundLimits {Ground.refutationUniversals = policy}
                emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        candidate <- expectRight result
        assertEqual "the first fallback source retains the one available instance" 1
            (Ground.refutationUniversalAttempts statistics)
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
            (Set.singleton (hypothesisIx 0))

universalHintOwnership :: Assertion
universalHintOwnership = do
    foundation <- expectRight Foundation.checkedFoundation
    hypotheses <- traverse (checked [])
        [CForall TySet (COr (p (CBound 0)) (q (CBound 0))), CNot (p emptySet), CNot (p one)]
    firstTarget <- checked [] (q emptySet)
    secondTarget <- checked [] (q one)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000)
            allowance {Scope.groundUniversals = Scope.HintedUniversals 32 1} context Map.empty \scope -> do
                inputs <- traverse (Scope.scopeHypothesis scope . hypothesisIx) [0, 1, 2]
                first <- Scope.scopeStartGround emptyGlobalTyping scope [] inputs firstTarget
                second <- Scope.scopeStartGround emptyGlobalTyping scope [] inputs secondTarget
                _ <- freezeOwnedQuery second
                let finish query = finishOwnedQuery query >>= \case
                        Scope.GroundQueryFinished statistics (Right evidence) -> pure (statistics, Scope.evidenceProof evidence)
                        _ -> boundaryFailure "the shared hint fixture did not prove its target"
                firstResult <- finish first
                afterFirst <- lift Scope.currentGroundLimits
                secondResult <- finish second
                pure (firstResult, afterFirst, secondResult)
    ((firstStatistics, firstProof), remaining, (secondStatistics, secondProof)) <- expectRight result
    assertEqual "the first query spends the final hint turn" 1 (Ground.refutationUniversalHintSteps firstStatistics)
    assertEqual "the suspended query cannot replenish hint work" 0 (Ground.refutationUniversalHintSteps secondStatistics)
    case Ground.refutationUniversals remaining of
        Ground.HintedUniversals attempts 0 -> assertBool "instance search retains its separate allowance" (attempts > 0)
        _ -> assertFailure "the shared hint remainder was lost"
    assertReplays foundation hypotheses [] firstTarget firstProof (Set.fromList (map hypothesisIx [0, 1]))
    assertReplays foundation hypotheses [] secondTarget secondProof (Set.fromList (map hypothesisIx [0, 2]))

universalHintArrivals :: Assertion
universalHintArrivals = do
    foundation <- expectRight Foundation.checkedFoundation
    let source = CForall TySet (COr (p (CBound 0)) (q one))
        irrelevant = [CEq TySet (COpaqueInteger index) (COpaqueInteger index) | index <- [10 .. 41]]
    hypotheses <- traverse (checked []) (source : irrelevant <> [CNot (p (COpaqueInteger 1000))])
    target <- checked [] (q one)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    seeds <- case hypotheses of
        first : rest -> pure (first :| rest)
        [] -> fail "the arrival fixture has no source"
    let limits = groundLimits {Ground.refutationUniversals = Ground.HintedUniversals 32 256}
        start omitted = Ground.startRefutationFromSeed limits emptyGlobalTyping context seeds
            [Ground.RefutationHypothesis index fact | (index, fact) <- zip [0 ..] hypotheses, index /= omitted] target
        afterFirstHint available session = case Ground.advanceRefutation available session of
            (remaining, Ground.RefutationPending next)
                | Ground.refutationUniversalHintSteps (Ground.refutationSessionStatistics next) == 0 ->
                    afterFirstHint remaining next
                | otherwise -> pure (remaining, next)
            _ -> fail "the source stopped before its first hint turn"
    for_ [0, 33] $ \lateIndex -> do
        (remaining, paused, before) <- if lateIndex == 0 then do
            (available, _, _, pending) <- parkGroundQuery limits (start lateIndex)
            pure (available, pending, Ground.refutationSessionStatistics pending)
          else do
            (available, pending) <- afterFirstHint limits (start lateIndex)
            case Ground.refutationUniversals available of
                Ground.HintedUniversals attempts hints ->
                    case Ground.advanceRefutation available {Ground.refutationUniversals = Ground.HintedUniversals attempts (hints + 1)} pending of
                        (_, Ground.RefutationFinished _ (Left Ground.RefutationInternalFailure{})) -> pure ()
                        _ -> assertFailure "a retained session replenished its hint allowance"
                _ -> assertFailure "the paused source lost its hint policy"
            -- New certified input enters only at a retained frontier, not in
            -- the middle of a native search quantum. Reaching that frontier
            -- spends the instance prefix while this premise is still absent.
            (parkedLimits, statistics, _, frontier) <- parkGroundQuery available pending
            pure (parkedLimits, frontier, statistics)
        (input, uses) <- hypothesisInput context (hypothesisIx lateIndex)
        resumed <- expectRight (Ground.resumeRefutationWithInput input uses paused)
        (_, statistics, result) <- finishFrozenQuery remaining resumed
        assertBool "late evidence uses the original finite hint allowance"
            (Ground.refutationUniversalHintSteps statistics > 0 && Ground.refutationUniversalHintSteps statistics <= 256)
        if lateIndex == 0 then do
            candidate <- expectRight result
            assertBool "the late source sees existing signed events before the same cap"
                (Ground.refutationUniversalAttempts statistics < 32)
            assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
                (Set.fromList (map hypothesisIx [0, 33]))
          else do
            case result of
                Left Ground.RefutationSaturated -> pure ()
                _ -> assertFailure "a late event restored the exhausted instance prefix"
            assertEqual "the missing premise had already spent the fixed prefix" 32
                (Ground.refutationUniversalAttempts before)
            assertEqual "the late event cannot restart hint work after that cap"
                (Ground.refutationUniversalHintSteps before) (Ground.refutationUniversalHintSteps statistics)

universalHintFixture
    :: [CoreType] -> CanonicalTerm Void
    -> IO (Search.Catalogue Void, Search.CataloguedLogicalView Void)
universalHintFixture types term = do
    proposition <- checked types term
    template <- expectRight (Template.retainCheckedPropositionTemplate proposition)
    prepared <- expectRight =<< Logical.prepareCompiledLogicalViewCounted (const (pure Nothing)) (pure ()) template
    let (collected, _, _) = Search.collectInitialCatalogue emptyGlobalTyping 1000000 10000 types (((), prepared) :| [])
    initial <- expectRight collected
    case Search.initialRootViews initial of
        (_, root) :| [] -> pure (Search.initialCatalogue initial, root)
        _ -> fail "universal hint fixture lost its root view"

collectUniversalHints
    :: Search.Catalogue Void -> Search.CataloguedLogicalView Void -> IO [Match.UniversalHint Void]
collectUniversalHints catalogue view = maybe (pure []) drain (Match.startUniversalHints view)
  where
    drain cursor = do
        let run work = Match.advanceUniversalHints emptyGlobalTyping work catalogue cursor
            (result, remaining) = run 1000000
            used = 1000000 - remaining
        step <- expectRight result
        assertBool "every hint turn spends structural work" (used > 0)
        _ <- expectRight (fst (run used))
        case run (used - 1) of
            (Left Match.MatchWorkExhausted, 0) -> pure ()
            _ -> assertFailure "a short hint turn was mistaken for missing syntax"
        case step of
            Match.UniversalHintsFinished -> pure []
            Match.UniversalHintsPending following -> drain following
            Match.UniversalHintFound hint following -> (hint :) <$> drain following

universalHintLeaves :: Assertion
universalHintLeaves = do
    let x = CBound 0
        cases =
            [ (COr (p x) (q x), [(True, False), (True, False)])
            , (CImp (p x) (CNot (q x)), [(False, False), (False, False)])
            , (CNot (CAnd (p x) (CNot (q x))), [(False, False), (True, False)])
            , (CAnd CTruth (CEq TySet x emptySet), [(True, True)])
            ]
        observation hint = (Match.universalHintPositive hint, case Match.universalHintPattern hint of
            Match.AtomicPremise{} -> False
            Match.EqualityPremise{} -> True)
    for_ cases $ \(body, expected) -> do
        (catalogue, view) <- universalHintFixture [] (CForall TySet body)
        hints <- collectUniversalHints catalogue view
        assertEqual "signed leaves retain their written order and logical polarity" expected (map observation hints)

universalHintBoundaries :: Assertion
universalHintBoundaries = do
    let x = CBound 0
        cases =
            [ (CForall TySet (CForall TySet (COr (p (CBound 1)) (q x))), 0)
            , (CForall TySet (CAnd (CExists TySet (p (CBound 1))) (q x)), 1)
            , (CForall TySet (COr (p emptySet) (q one)), 0)
            , (CForall TyProp (CBound 0), 0)
            , (p emptySet, 0)
            ]
    for_ cases $ \(term, count) -> do
        (catalogue, view) <- universalHintFixture [] term
        hints <- collectUniversalHints catalogue view
        assertEqual "only a supported leaf determining the one opened set binder produces a hint"
            count (length hints)
        case Logical.logicalViewNode view of
            Logical.LogicalUniversal _ body -> assertBool "an under-binder view cannot stand in for a source root"
                (isNothing (Match.startUniversalHints body))
            _ -> pure ()

universalHintAmbient :: Assertion
universalHintAmbient = do
    let body = CApp (CApp (CIntrinsic Member) (CBound 0)) (CBound 1)
    (catalogue, view) <- universalHintFixture [TySet] (CForall TySet body)
    hints <- collectUniversalHints catalogue view
    case hints of
        [Match.UniversalHint True (Match.AtomicPremise _ [argument, ambient])] -> do
            assertEqual "only the quantified argument is a matcher slot"
                (Set.singleton (Template.MatcherSlot 0)) (Match.termPatternSlots argument)
            assertEqual "the ambient value remains fixed" Set.empty (Match.termPatternSlots ambient)
            assertEqual "the pattern retains its checked nominal context" [TySet]
                (Template.binderEnvironmentAmbientContext
                    (Template.compiledTemplateBinderEnvironment (Match.termPatternTemplate argument)))
            case Match.termPatternNode ambient of
                Match.PatternRigid (Match.RigidAmbient 0) [] -> pure ()
                _ -> assertFailure "the ambient value was confused with the opened binder"
        _ -> assertFailure "the ambient membership pattern was not retained"

exactProjectionCoverage :: Assertion
exactProjectionCoverage = do
    let x = CBound 0
        cases =
            [ (CForall TySet (CAnd (p x) (q x)), 2, Match.FullRuleCoverage)
            , (CForall TySet (CAnd (COr (p x) (q x)) (p x)), 1, Match.PartialRuleCoverage)
            , (CForall TySet (CForall TySet (CAnd (p (CBound 1)) (q x))), 2, Match.FullRuleCoverage)
            ]
    for_ cases $ \(term, expectedRules, expectedCoverage) -> do
        proposition <- checked [] term
        template <- expectRight (Template.retainCheckedPropositionTemplate proposition)
        prepared <- expectRight =<< Logical.prepareCompiledLogicalViewCounted (const (pure Nothing)) (pure ()) template
        let (collected, _, _) = Search.collectInitialCatalogue emptyGlobalTyping 1000000 10000 [] (((), prepared) :| [])
        initial <- expectRight collected
        view <- case Search.initialRootViews initial of
            (_, root) :| [] -> pure root
            _ -> assertFailure "projection fixture lost its source view" >> fail "missing view"
        let catalogue = Search.initialCatalogue initial
        cursor <- expectRight (fst (Match.recognizeRule True emptyGlobalTyping 1000000 catalogue view)) >>= \case
            Match.ProjectedRules pending -> pure pending
            _ -> assertFailure "leading universal conjunction was not recognized" >> fail "missing projections"
        let drain count pending = do
                let (result, remaining) = Match.advanceRuleProjections emptyGlobalTyping 1000000 catalogue pending
                    used = 1000000 - remaining
                    withWork work = Match.advanceRuleProjections emptyGlobalTyping work catalogue pending
                progress <- expectRight result
                _ <- expectRight (fst (withWork used))
                case fst (withWork (used - 1)) of
                    Left Match.MatchWorkExhausted -> pure ()
                    _ -> assertFailure "compilation exhaustion was mistaken for unsupported grammar"
                case progress of
                    Match.RuleProjectionPending following -> drain count following
                    Match.RuleProjectionFound _ following -> drain (count + 1) following
                    Match.RuleProjectionFinished coverage -> pure (count, coverage)
        (count, coverage) <- drain (0 :: Int) cursor
        assertEqual "each supported projection has its own rule view" expectedRules count
        assertEqual "coverage is independent of whether all parameters can be determined" expectedCoverage coverage

booleanSplitPropagation :: Assertion
booleanSplitPropagation = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 4 TyProp
        a = CBound 0
        b = CBound 1
        c = CBound 2
        fourth = CBound 3
        cases =
            [ ("left disjunct", [COr a b, CNot a], b)
            , ("right disjunct", [COr a b, CNot b], a)
            , ("left conjunct", [CNot (CAnd a b), a], CNot b)
            , ("right conjunct", [CNot (CAnd a b), b], CNot a)
            , ("contraposition", [CImp (COr a b) c, CNot c], CNot (COr a b))
            , ("compound implication", [CImp (COr a b) c, COr a b], c)
            , ("satisfied disjunction", [COr a b, a, COr c fourth, CImp c b, CImp fourth b], b)
            , ("proposition equality", [COr a b, CEq TyProp a c, CNot c], b)
            , ("converted disjunct", [COr (CApp (CLam TyProp (CBound 0)) a) b, CNot a], b)
            , ("converted conjunct", [CNot (CAnd (CApp (CLam TyProp (CBound 0)) a) b), a], CNot b)
            ]
    for_ cases $ \(label, terms, goal) -> do
        hypotheses <- traverse (checked types) terms
        target <- checked types goal
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        let run enabled work = Ground.runRefutation
                groundLimits {Ground.refutationBooleanPropagation = enabled, Ground.refutationWorkLimit = work}
                emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
            (offStatistics, off) = run False 1000000
            (onStatistics, enabledResult) = run True 1000000
        for_ [off, enabledResult] $ \result -> do
            candidate <- expectRight result
            _ <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
                (Proof.builtProofDerivation (Ground.refutationCandidateProof candidate)))
            pure ()
        assertBool (label <> " eliminates an unnecessary branch")
            (Ground.refutationBranchNodes onStatistics < Ground.refutationBranchNodes offStatistics)
        let used = 1000000 - Ground.refutationRemainingWork onStatistics
        _ <- expectRight (snd (run True used))
        case snd (run True (used - 1)) of
            Left Ground.RefutationWorkExhausted -> pure ()
            _ -> assertFailure (label <> " did not charge its complete proof reconstruction")
        let small = groundLimits {Ground.refutationBranchNodeLimit = Ground.refutationBranchNodes onStatistics}
            bounded enabled = Ground.runRefutation small {Ground.refutationBooleanPropagation = enabled}
                emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        _ <- expectRight (snd (bounded True))
        case snd (bounded False) of
            Left Ground.RefutationBranchesExhausted -> pure ()
            _ -> assertFailure (label <> " lost its bounded-branch coverage difference")
        reversedContext <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types (reverse hypotheses))
        for_ [False, True] $ \enabled -> do
            reversed <- expectRight (snd (Ground.runRefutation
                groundLimits {Ground.refutationBooleanPropagation = enabled}
                emptyGlobalTyping reversedContext
                (zipWith Ground.RefutationHypothesis [0 ..] (reverse hypotheses)) target))
            _ <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList (reverse hypotheses)) target
                (Proof.builtProofDerivation (Ground.refutationCandidateProof reversed)))
            pure ()
    for_ [([COr a b], b), ([CNot (CAnd a b)], CNot b), ([CImp a b], CNot a)] $ \(terms, goal) -> do
        hypotheses <- traverse (checked types) terms
        target <- checked types goal
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        for_ [False, True] $ \enabled ->
            case snd (Ground.runRefutation groundLimits {Ground.refutationBooleanPropagation = enabled}
                    emptyGlobalTyping context (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target) of
                Left Ground.RefutationSaturated -> pure ()
                _ -> assertFailure "missing signed evidence was treated as its opposite"

booleanSplitSupport :: Assertion
booleanSplitSupport = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 3 TyProp
        a = CBound 0
        b = CBound 1
        c = CBound 2
    for_ [[COr a b, CNot a, CImp b c, COr a b],
          [a, COr a b, CImp a c, COr a b]] $ \terms -> do
        hypotheses <- traverse (checked types) terms
        target <- checked types c
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 3]
            (Ground.startRefutation groundLimits emptyGlobalTyping context
                (zipWith Ground.RefutationHypothesis [0 ..] (take 3 hypotheses)) target))
        (ordinaryLimits, ordinary, retained) <- awaitOrdinaryGround groundLimits initial
        assertEqual "ordinary success does not claim the unavailable canonical source"
            Nothing (Ground.refutationCandidateCanonicalSource ordinary)
        (remaining, _, failure, waiting) <- parkGroundQuery ordinaryLimits retained
        assertEqual "the unsupported closure retains its support frontier"
            Ground.RefutationCanonicalSupportMissing failure
        (late, uses) <- hypothesisInput context (hypothesisIx 3)
        resumed <- expectRight (Ground.resumeRefutationWithInput late uses waiting)
        (_, _, result) <- finishCanonicalQuery remaining resumed
        candidate <- expectRight result
        assertEqual "late source use supports the existing propagation or fallback split"
            (Just (Ground.RefutationCanonicalHypothesis 3))
            (Ground.refutationCandidateCanonicalSource candidate)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target
            (Proof.builtProofDerivation (Ground.refutationCandidateProof candidate)))
        assertBool "the replayed proof actually consumes the canonical disjunction"
            (Set.member (hypothesisIx 3) (replayedScopedKernelExternalHypothesisUses replayed))

groundSupportRecipes :: Assertion
groundSupportRecipes = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = p emptySet
        b = q emptySet
        c = q one
    for_
        [ ("source", [a, CImp a b], b, 0, [0, 1])
        , ("duplicate premise", [a, a, CImp a b], b, 1, [1, 2])
        , ("left premise", [a, b, a, CImp a (CImp b c)], c, 2, [1, 2, 3])
        , ("right premise", [a, b, b, CImp a (CImp b c)], c, 2, [0, 2, 3])
        ] \(label, terms, goal, canonical, expected) -> do
            hypotheses <- traverse (checked []) terms
            target <- checked [] goal
            context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
            let inputs = zipWith Ground.RefutationHypothesis [0 ..] hypotheses
                start limits = Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis canonical]
                    (Ground.startRefutation limits emptyGlobalTyping context inputs target)
            initial <- expectRight (start groundLimits)
            (_, statistics, result) <- finishFrozenQuery groundLimits initial
            proof <- expectRight result
            assertEqual (label <> " retains its exact source witness")
                (Just (Ground.RefutationCanonicalHypothesis canonical))
                (Ground.refutationCandidateCanonicalSource proof)
            assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof proof)
                (Set.fromList (map hypothesisIx expected))
            let cost = Ground.refutationWorkLimit groundLimits - Ground.refutationRemainingWork statistics
                exactLimits = groundLimits {Ground.refutationWorkLimit = cost}
                shortLimits = groundLimits {Ground.refutationWorkLimit = cost - 1}
            (_, _, exactResult) <- finishFrozenQuery exactLimits =<< expectRight (start exactLimits)
            _ <- expectRight exactResult
            (_, shortStatistics, shortResult) <- finishFrozenQuery shortLimits =<< expectRight (start shortLimits)
            case shortResult of
                Left Ground.RefutationWorkExhausted -> pure ()
                _ -> assertFailure (label <> " escaped its exact structural boundary")
            assertEqual "failed support construction remains charged" 0
                (Ground.refutationRemainingWork shortStatistics)
    hypotheses <- traverse (checked []) [a, CImp a b, c]
    target <- checked [] b
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let start = Ground.startRefutation groundLimits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        track = Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 2]
    initial <- expectRight (track start)
    (_, _, result) <- finishFrozenQuery groundLimits initial
    proof <- expectRight result
    assertEqual "an available but unused source does not support the proof"
        Nothing (Ground.refutationCandidateCanonicalSource proof)
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof proof)
        (Set.fromList (map hypothesisIx [0, 1]))
    case track initial of
        Left Ground.RefutationInternalFailure{} -> pure ()
        _ -> assertFailure "canonical tracking was registered twice"
    case Ground.advanceRefutation groundLimits start of
        (_, Ground.RefutationPending prepared) -> case track prepared of
            Left Ground.RefutationInternalFailure{} -> pure ()
            _ -> assertFailure "canonical tracking retroactively replaced a prepared query"
        _ -> assertFailure "ground preparation unexpectedly finished in one transition"

groundSupportBranches :: Assertion
groundSupportBranches = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = p emptySet
        b = q emptySet
        c = p one
        goal = q one
    hypotheses <- traverse (checked [])
        [a, COr b c, CImp b a, CImp a (CImp b goal), CImp a (CImp c goal)]
    target <- checked [] goal
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 2]
        (Ground.startRefutation groundLimits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target))
    (_, _, result) <- finishFrozenQuery groundLimits initial
    proof <- expectRight result
    assertEqual "the left case supports the result"
        (Just (Ground.RefutationCanonicalHypothesis 2)) (Ground.refutationCandidateCanonicalSource proof)
    -- The right child still needs the original a. Reusing the left child's
    -- supported a would leak its b assumption, which independent replay rejects.
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof proof)
        (Set.fromList (map hypothesisIx [0, 1, 2, 3, 4]))

groundSupportExistingInstance :: Assertion
groundSupportExistingInstance = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = p emptySet
        b = q emptySet
        c = q one
        premise = p one
    hypotheses <- traverse (checked []) [a, CImp a b, CImp b (CImp premise c), a, premise]
    target <- checked [] c
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 3]
        (Ground.startRefutation groundLimits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] (take 3 hypotheses)) target))
    (remaining, before, _, parked) <- parkGroundQuery groundLimits initial
    let input index = do
            let (result, _, _) = Scope.runScoped 10000 (Conversion.conversionPool 1000000) allowance
                    context Map.empty \scope -> do
                        evidence <- Scope.scopeHypothesis scope (hypothesisIx index)
                        pure (Scope.evidenceProof evidence, Scope.evidenceUses evidence)
            expectRight result
    (canonical, uses) <- input 3
    supported <- expectRight (Ground.resumeRefutationWithInput canonical uses parked)
    (afterSupport, upgraded, _, waiting) <- parkGroundQuery remaining supported
    assertEqual "support is not a new logical instance"
        (Ground.refutationRuleInstances before) (Ground.refutationRuleInstances upgraded)
    assertEqual "support is not a new signed formula"
        (Ground.refutationSignedFormulas before) (Ground.refutationSignedFormulas upgraded)
    assertBool "the late duplicate and recipe upgrade are charged"
        (Ground.refutationRemainingWork upgraded < Ground.refutationRemainingWork before)
    (lastPremise, lastUses) <- input 4
    resumed <- expectRight (Ground.resumeRefutationWithInput lastPremise lastUses waiting)
    (_, _, result) <- finishFrozenQuery afterSupport resumed
    proof <- expectRight result
    assertEqual "the actual late source propagates through the old rule instance"
        (Just (Ground.RefutationCanonicalHypothesis 3)) (Ground.refutationCandidateCanonicalSource proof)
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof proof)
        (Set.fromList (map hypothesisIx [1, 2, 3, 4]))

statisticsObservation :: Ground.RefutationStatistics -> (Word, Word, Word, Word, Word, Word, Word)
statisticsObservation statistics =
    ( Ground.refutationRemainingWork statistics
    , Conversion.conversionPoolAmount (Ground.refutationRemainingConversionPool statistics)
    , Ground.refutationBranchNodes statistics
    , Ground.refutationTerms statistics
    , Ground.refutationSignedFormulas statistics
    , Ground.refutationEqualityEvents statistics
    , Ground.refutationRuleInstances statistics
    )

awaitOrdinaryGround
    :: Ground.RefutationLimits -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Ground.RefutationCandidate Void, Ground.RefutationSession Void)
awaitOrdinaryGround = go (0 :: Int)
  where
    go steps limits session = case Ground.refutationSessionAnyCandidate session of
        Just candidate -> pure (limits, candidate, session)
        Nothing -> do
            assertBool "ordinary ground publication is bounded" (steps < 3000)
            case Ground.advanceRefutation limits session of
                (remaining, Ground.RefutationPending next) -> go (steps + 1) remaining next
                (_, Ground.RefutationBlocked _ failure _) -> assertFailure (show failure) >> fail "no ordinary certificate"
                (_, Ground.RefutationFinished _ result) -> assertFailure
                    ("expected retained ordinary publication: " <> either show (const "already canonical") result)
                        >> fail "no retained ordinary frontier"

groundSupportPendingRoots :: Assertion
groundSupportPendingRoots = do
    foundation <- expectRight Foundation.checkedFoundation
    proposition <- checked [] (p emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [proposition, proposition])
    let start limits = Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 1]
            (Ground.startRefutation limits emptyGlobalTyping context
                [Ground.RefutationHypothesis 0 proposition, Ground.RefutationHypothesis 1 proposition] proposition)
    initial <- expectRight (start groundLimits)
    (remaining, ordinary, retained) <- awaitOrdinaryGround groundLimits initial
    assertReplays foundation [proposition, proposition] [] proposition (Ground.refutationCandidateProof ordinary)
        (Set.singleton (hypothesisIx 0))
    let before = Ground.refutationSessionStatistics retained
    (_, statistics, result) <- finishCanonicalQuery remaining retained
    canonical <- expectRight result
    assertEqual "the later pending root supplies support"
        (Just (Ground.RefutationCanonicalHypothesis 1)) (Ground.refutationCandidateCanonicalSource canonical)
    assertReplays foundation [proposition, proposition] [] proposition (Ground.refutationCandidateProof canonical)
        (Set.singleton (hypothesisIx 1))
    assertEqual "support continues the same frozen domain"
        (Ground.refutationTerms before) (Ground.refutationTerms statistics)
    assertEqual "support continues the same root branch" 1 (Ground.refutationBranchNodes statistics)
    let cost = Ground.refutationWorkLimit groundLimits - Ground.refutationRemainingWork statistics
        exactLimits = groundLimits {Ground.refutationWorkLimit = cost}
        shortLimits = groundLimits {Ground.refutationWorkLimit = cost - 1}
    (_, _, exactResult) <- finishCanonicalQuery exactLimits =<< expectRight (start exactLimits)
    _ <- expectRight exactResult
    (_, exhausted, shortResult) <- finishCanonicalQuery shortLimits =<< expectRight (start shortLimits)
    case shortResult of
        Left Ground.RefutationWorkExhausted -> pure ()
        _ -> assertFailure "canonical root publication escaped its exact structural boundary"
    assertEqual "failed publication spends the actual remainder" 0 (Ground.refutationRemainingWork exhausted)
    (_, _, noWorkResult) <- finishCanonicalQuery remaining {Ground.refutationWorkLimit = 0} retained
    case noWorkResult of
        Left Ground.RefutationWorkExhausted -> pure ()
        _ -> assertFailure "a saved ordinary proof erased real canonical-search exhaustion"

groundSupportClosedInput :: Assertion
groundSupportClosedInput = do
    foundation <- expectRight Foundation.checkedFoundation
    proposition <- checked [] (p emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [proposition, proposition])
    initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 1]
        (Ground.startRefutation groundLimits emptyGlobalTyping context [Ground.RefutationHypothesis 0 proposition] proposition))
    (remaining, ordinary, retained) <- awaitOrdinaryGround groundLimits initial
    (afterSearch, before, failure, waiting) <- parkGroundQuery remaining retained
    assertEqual "an ordinary certificate does not satisfy canonical demand"
        Ground.RefutationCanonicalSupportMissing failure
    assertReplays foundation [proposition, proposition] [] proposition (Ground.refutationCandidateProof ordinary)
        (Set.singleton (hypothesisIx 0))
    (proof, uses) <- hypothesisInput context (hypothesisIx 1)
    resumed <- expectRight (Ground.resumeRefutationWithInput proof uses waiting)
    (_, statistics, result) <- finishCanonicalQuery afterSearch {Ground.refutationBranchNodeLimit = 0} resumed
    candidate <- expectRight result
    assertReplays foundation [proposition, proposition] [] proposition (Ground.refutationCandidateProof candidate)
        (Set.singleton (hypothesisIx 1))
    assertEqual "a closed query resumes without a replacement branch"
        (Ground.refutationBranchNodes before) (Ground.refutationBranchNodes statistics)
    assertEqual "the duplicate adds no formula event"
        (Ground.refutationSignedFormulas before) (Ground.refutationSignedFormulas statistics)

groundSupportClosedSiblings :: Assertion
groundSupportClosedSiblings = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 4 TyProp
        a = CBound 0
        b = CBound 1
        goal = CBound 2
        intermediate = CBound 3
        limits = groundLimits {Ground.refutationBranchNodeLimit = 3}
    for_ [(a, [0, 2, 3, 4]), (b, [0, 1, 3, 4])] \(supportingSide, used) -> do
        hypotheses <- traverse (checked types)
            [COr a b, CImp a goal, CImp b goal, CImp supportingSide intermediate, CImp intermediate goal]
        target <- checked types goal
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 4]
            (Ground.startRefutation limits emptyGlobalTyping context
                (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target))
        (remaining, ordinary, retained) <- awaitOrdinaryGround limits initial
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof ordinary)
            (Set.fromList (map hypothesisIx [0, 1, 2]))
        (_, statistics, result) <- finishCanonicalQuery remaining retained
        candidate <- expectRight result
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
            (Set.fromList (map hypothesisIx used))
        assertEqual "the completed sibling and existing split are retained" 3
            (Ground.refutationBranchNodes statistics)

groundSupportEquality :: Assertion
groundSupportEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let a = CBound 0
        b = CBound 1
        c = CBound 2
        equation = CEq TySet
        run label types terms goal ordinaryUses canonical expected mergeDelta = do
            hypotheses <- traverse (checked types) terms
            target <- checked types goal
            context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
            let start limits = Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis canonical]
                    (Ground.startRefutation limits emptyGlobalTyping context
                        (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target)
            initial <- expectRight (start groundLimits)
            (remaining, ordinary, retained) <- awaitOrdinaryGround groundLimits initial
            assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof ordinary)
                (Set.fromList (map hypothesisIx ordinaryUses))
            let before = Ground.refutationSessionStatistics retained
            (_, statistics, result) <- finishCanonicalQuery remaining retained
            candidate <- expectRight result
            assertEqual (label <> " selects actual canonical evidence")
                (Just (Ground.RefutationCanonicalHypothesis canonical)) (Ground.refutationCandidateCanonicalSource candidate)
            assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
                (Set.fromList (map hypothesisIx expected))
            assertEqual (label <> " does not invent an equality merge") mergeDelta
                (Ground.refutationEqualityEvents statistics - Ground.refutationEqualityEvents before)
            let cost = Ground.refutationWorkLimit groundLimits - Ground.refutationRemainingWork statistics
                exact = groundLimits {Ground.refutationWorkLimit = cost}
                short = groundLimits {Ground.refutationWorkLimit = cost - 1}
            (_, _, exactResult) <- finishCanonicalQuery exact =<< expectRight (start exact)
            _ <- expectRight exactResult
            (_, exhausted, shortResult) <- finishCanonicalQuery short =<< expectRight (start short)
            assertEqual (label <> " failed work remains charged") 0 (Ground.refutationRemainingWork exhausted)
            case shortResult of
                Left Ground.RefutationWorkExhausted -> pure ()
                _ -> assertFailure (label <> " escaped its exact work boundary")
    run "reversed duplicate" [TySet, TySet] [equation a b, equation b a] (equation a b) [0] 1 [1] 0
    run "alternate path" [TySet, TySet, TySet] [equation a b, equation b c, equation a c]
        (equation a b) [0] 2 [1, 2] 1
    let function = CBound 2
        nested term = CApp function (CApp function term)
    run "existing congruence" [TySet, TySet, TyArrow TySet TySet]
        [equation (nested a) (nested b), equation a b]
        (equation (nested a) (nested b)) [0] 1 [1] 2
    run "positive equivalent fact" [TyProp, TyProp]
        [a, CEq TyProp a b, b] a [0] 2 [1, 2] 1
    run "negative equivalent fact" [TyProp, TyProp]
        [CNot a, CEq TyProp a b, CNot b] (CNot a) [0] 2 [1, 2] 1
    -- The canonical edge must be consumed even when the requested equality is
    -- reflexive. An empty path cannot carry its support.
    run "supported reflexive cycle" [TySet, TySet]
        [equation a a, equation a b] (equation a a) [] 1 [1] 1

groundSupportEqualityInstance :: Assertion
groundSupportEqualityInstance = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TySet, TySet, TyProp]
        a = CBound 0
        b = CBound 1
        goal = CBound 2
        equality = CEq TySet a b
    hypotheses <- traverse (checked types) [equality, p a, CImp (p b) goal, equality]
    target <- checked types goal
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    initial <- expectRight (Ground.trackRefutationCanonicalSources [Ground.RefutationCanonicalHypothesis 3]
        (Ground.startRefutation groundLimits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] (take 3 hypotheses)) target))
    (remaining, ordinary, retained) <- awaitOrdinaryGround groundLimits initial
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof ordinary)
        (Set.fromList (map hypothesisIx [0, 1, 2]))
    (afterSearch, before, failure, waiting) <- parkGroundQuery remaining retained
    assertEqual "an unrelated source is not consumed before arrival"
        Ground.RefutationCanonicalSupportMissing failure
    (proof, uses) <- hypothesisInput context (hypothesisIx 3)
    resumed <- expectRight (Ground.resumeRefutationWithInput proof uses waiting)
    (_, statistics, result) <- finishCanonicalQuery afterSearch resumed
    candidate <- expectRight result
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
        (Set.fromList (map hypothesisIx [1, 2, 3]))
    assertEqual "an upgraded equality witness does not refire its rule"
        (Ground.refutationRuleInstances before) (Ground.refutationRuleInstances statistics)
    assertEqual "an upgraded equality witness does not merge its endpoints again"
        (Ground.refutationEqualityEvents before) (Ground.refutationEqualityEvents statistics)
    assertEqual "an upgraded equality witness does not readmit its formula"
        (Ground.refutationSignedFormulas before) (Ground.refutationSignedFormulas statistics)

ownedCanonicalGround :: Assertion
ownedCanonicalGround = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyProp, TyProp]
        a = CBound 0
        b = CBound 1
        budget = Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = 0}
    hypotheses <- traverse (checked types) [a, CEq TyProp a b, b]
    target <- checked types a
    let run limits = Scope.obviousProofDetailed limits Scope.MustUseCanonicalDefinition
            foundation emptyGlobalTyping hypotheses [] [Scope.obviousLocalDefinitionView 1 Semantic.DefinitionExactView] target
        (statistics, result) = run budget
    proof <- expectRight result
    assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
        (Set.fromList (map hypothesisIx [0, 1]))
    assertEqual "ground publication does not borrow focused work" 0 (Scope.obviousFocusedWorkConsumed statistics)
    assertEqual "ordinary and canonical support share the root branch" 1 (Scope.obviousBranchNodesCreated statistics)
    assertEqual "the ground certificate is reported as completed"
        Scope.ObviousTierCandidateBuilt (Scope.obviousRefutationTierOutcome statistics)
    let cost = Scope.obviousRefutationWorkConsumed statistics
        (exactStatistics, exact) = run budget {Scope.obviousRefutationWorkLimit = cost}
        (shortStatistics, short) = run budget {Scope.obviousRefutationWorkLimit = cost - 1}
    _ <- expectRight exact
    assertEqual "the source audit is included in exact ground work" cost (Scope.obviousRefutationWorkConsumed exactStatistics)
    case short of
        Left Scope.ObviousResourceExhausted{} -> pure ()
        _ -> assertFailure "canonical ground publication escaped its exact owner allowance"
    assertEqual "a failed final audit remains charged" (cost - 1) (Scope.obviousRefutationWorkConsumed shortStatistics)

sharedGroundDelivery :: Assertion
sharedGroundDelivery = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyProp, TyProp]
    hypotheses <- traverse (checked types)
        [ COr (CBound 0) (CBound 1), CNot (CBound 0)
        , CForall TySet (CEq TySet (CBound 0) (CBound 0)) ]
    target <- checked types (CBound 1)
    convertedTarget <- checked types (CApp (CLam TyProp (CBound 0)) (CBound 1))
    let runTarget policy budget facts goal = Scope.obviousProofReportWithPolicy
            (Scope.productionSearchPolicy { Scope.policyEndpoints = policy })
            budget Scope.AnyObviousProof foundation emptyGlobalTyping facts [] [] goal
        run policy budget facts = runTarget policy budget facts target
    for_ [Scope.EndpointApplications 16, Scope.EndpointsDisabled] \policy -> do
        for_ ([0, 32, 64, 128, 256, 512, 1024] <> [27..40]) \focusedWork -> do
            let budget = Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = focusedWork}
                report = run policy budget hypotheses
                statistics = Scope.obviousRunStatistics report
                label = show policy <> ", focused allowance " <> show focusedWork
            proof <- either (\failure -> assertFailure (label <> ": " <> show failure) >> fail "unreachable")
                pure (Scope.obviousRunResult report)
            assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
                (Set.fromList (map hypothesisIx [0, 1]))
            assertBool (label <> ": focused work stays within its allowance")
                (Scope.obviousFocusedWorkConsumed statistics <= focusedWork)
            assertBool (label <> ": ground work is charged")
                (Scope.obviousRefutationWorkConsumed statistics > 0)
            -- At larger allowances the mixed fork can deliver ground evidence
            -- before focused search finishes; that is not focused exhaustion.
            when (focusedWork == 0 || (policy == Scope.EndpointApplications 16 && focusedWork <= 36)) do
                assertEqual (label <> ": the failed focused component remains visible")
                    (Scope.ObviousTierResourceExhausted Scope.ObviousFocusedWorkLimit)
                    (Scope.obviousFocusedTierOutcome statistics)
        let noNegation = take 1 hypotheses <> drop 2 hypotheses
            zeroGround = Scope.defaultObviousBudget
                {Scope.obviousFocusedWorkLimit = 32, Scope.obviousRefutationWorkLimit = 0}
            zeroConversion = Scope.defaultObviousBudget
                {Scope.obviousFocusedWorkLimit = 32, Scope.obviousConversionPool = Conversion.conversionPool 0}
        for_ [("missing negation", run policy Scope.defaultObviousBudget noNegation),
                ("zero ground credit", run policy zeroGround hypotheses),
                ("required conversion without credit", runTarget policy zeroConversion hypotheses convertedTarget)] \(label, report) ->
            case Scope.obviousRunResult report of
                Left _ -> pure ()
                Right _ -> assertFailure (show policy <> ": " <> label <> " gave a free proof")
        assertEqual "zero ground credit charges no ground work" 0
            (Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics (run policy zeroGround hypotheses)))
        converted <- expectRight (Scope.obviousRunResult (runTarget policy
            Scope.defaultObviousBudget {Scope.obviousFocusedWorkLimit = 32} hypotheses convertedTarget))
        assertReplays foundation hypotheses [] convertedTarget (Scope.obviousBuiltProof converted)
            (Set.fromList (map hypothesisIx [0, 1]))

citedDefinitionEquality :: Assertion
citedDefinitionEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let member element set = CApp (CApp (CIntrinsic Member) element) set
        body = CApp (CApp (CIntrinsic Sep) (CBound 1))
            (CLam TySet (CEq TySet (CBound 0) (CBound 1)))
        object = Identity.transparentObject (Identity.theoryId foundation)
            (TyArrow TySet (TyArrow TySet TySet)) (CLam TySet (CLam TySet body))
        container set element = CApp (CApp (CGlobal (Identity.assertedObjectId object)) set) element
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [object])
    let typing = Identity.globalTypingFromClosure closure
        check = expectRight . checkScopedCanonicalCore typing (replicate 3 TySet)
    definition <- expectRight (checkCanonicalCore typing (CForall TySet (CForall TySet (CForall TySet
        (CEq TyProp (member (CBound 0) (container (CBound 2) (CBound 1)))
            (CAnd (member (CBound 0) (CBound 2)) (CEq TySet (CBound 0) (CBound 1))))))))
    hypothesis <- check (member (CBound 0) (container (CBound 2) (CBound 1)))
    judgement <- expectRight (derivationImportJudgement definition)
    let imported = Scope.obviousImport (importIx 0) definition
        view = Scope.obviousImportedDefinitionView (Identity.assertedObjectId object)
            Semantic.DefinitionMembershipView imported
    for_ [CEq TySet (CBound 0) (CBound 1), CEq TySet (CBound 1) (CBound 0)] \equality -> do
        target <- check equality
        let report = Scope.obviousProofReport
                Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0, Scope.obviousFocusedWorkLimit = 4096}
                Scope.MustUseCanonicalDefinition foundation typing [hypothesis] [imported] [view] target
        proof <- expectRight (Scope.obviousRunResult report)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            typing (Vector.singleton judgement) (Vector.singleton hypothesis) target
            (Proof.builtProofDerivation (Scope.obviousBuiltProof proof)))
        assertEqual "the projected equality consumes the cited definition" (Set.singleton (importIx 0))
            (replayedScopedKernelImportUses replayed)
        assertEqual "the projected equality consumes its membership premise" (Set.singleton (hypothesisIx 0))
            (replayedScopedKernelExternalHypothesisUses replayed)

citedDefinitionPremise :: Assertion
citedDefinitionPremise = do
    foundation <- expectRight Foundation.checkedFoundation
    let member element set = CApp (CApp (CIntrinsic Member) element) set
        subsetBody = CForall TySet (CImp (member (CBound 0) (CBound 2)) (member (CBound 0) (CBound 1)))
        object = Identity.transparentObject (Identity.theoryId foundation)
            (TyArrow TySet (TyArrow TySet TyProp)) (CLam TySet (CLam TySet subsetBody))
        subset left right = CApp (CApp (CGlobal (Identity.assertedObjectId object)) left) right
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [object])
    let typing = Identity.globalTypingFromClosure closure
        check = expectRight . checkScopedCanonicalCore typing (replicate 4 TySet)
    definition <- expectRight (checkCanonicalCore typing (CForall TySet (CForall TySet
        (CEq TyProp (subset (CBound 1) (CBound 0)) subsetBody))))
    hypotheses <- traverse check [CEq TySet (CBound 1) (CBound 2),
        subset (CBound 1) (CBound 3), member (CBound 0) (CBound 2)]
    target <- check (member (CBound 0) (CBound 3))
    judgement <- expectRight (derivationImportJudgement definition)
    let imported = Scope.obviousImport (importIx 0) definition
        views = [Scope.obviousLocalDefinitionView 0 Semantic.DefinitionExactView,
            Scope.obviousImportedDefinitionView (Identity.assertedObjectId object)
                Semantic.DefinitionPointwiseView imported]
        report = Scope.obviousProofReport
            Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0, Scope.obviousFocusedWorkLimit = 4096}
            Scope.MustUseCanonicalDefinition foundation typing hypotheses [imported] views target
    proof <- expectRight (Scope.obviousRunResult report)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        typing (Vector.singleton judgement) (Vector.fromList hypotheses) target
        (Proof.builtProofDerivation (Scope.obviousBuiltProof proof)))
    assertEqual "subset elimination consumes the cited definition" (Set.singleton (importIx 0))
        (replayedScopedKernelImportUses replayed)
    assertEqual "the alias and both premises are required" (Set.fromList (map hypothesisIx [0, 1, 2]))
        (replayedScopedKernelExternalHypothesisUses replayed)

conjunctionTheorem :: Assertion
conjunctionTheorem = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = TySet : replicate 4 (TyArrow TySet TyProp)
        atom index argument = CApp (CBound index) argument
        conjunction argument offset = CAnd (atom (2 + offset) argument)
            (CAnd (atom (3 + offset) argument) (atom (4 + offset) argument))
        theorem = CForall TySet (CImp (atom 2 (CBound 0)) (conjunction (CBound 0) 1))
        premise = atom 1 (CBound 0)
        group = conjunction (CBound 0) 0
        budget = Scope.defaultObviousBudget
            {Scope.obviousRefutationWorkLimit = 0, Scope.obviousFocusedWorkLimit = 65536}
    hypotheses <- traverse (checked types) [premise, theorem]
    for_ [CAnd premise group, CAnd group premise] \term -> do
        target <- checked types term
        let report = Scope.obviousProofReport budget Scope.AnyObviousProof
                foundation emptyGlobalTyping hypotheses [] [] target
        proof <- expectRight (Scope.obviousRunResult report)
        assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
            (Set.fromList (map hypothesisIx [0, 1]))

conjunctionTree :: Assertion
conjunctionTree = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 17 (TyArrow TySet TyProp)
        body = foldr1 CAnd [CApp (CBound index) (CBound 0) | index <- [1 .. 16]]
        definition = CForall TySet (CEq TyProp (CApp (CBound 17) (CBound 0)) body)
        atoms = [CApp (CBound index) emptySet | index <- [15, 14 .. 0]]
        budget = Scope.defaultObviousBudget
            {Scope.obviousRefutationWorkLimit = 0, Scope.obviousFocusedWorkLimit = 65536}
    hypotheses <- traverse (checked types) [definition, CApp (CBound 16) emptySet]
    for_ [foldr1 CAnd atoms, foldl1 CAnd atoms] \tree -> do
        target <- checked types tree
        let (statistics, result) = Scope.obviousProofDetailed budget Scope.MustUseCanonicalDefinition
                foundation emptyGlobalTyping hypotheses []
                [Scope.obviousLocalDefinitionView 0 Semantic.DefinitionPointwiseView] target
        proof <- expectRight result
        assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
            (Set.fromList (map hypothesisIx [0, 1]))
        assertEqual "conjunction assembly needs no ground search" 0
            (Scope.obviousRefutationWorkConsumed statistics)

concreteEqualityBeforeConversion :: Assertion
concreteEqualityBeforeConversion = do
    foundation <- expectRight Foundation.checkedFoundation
    let pair left right = CApp (CApp (CIntrinsic OrderedPair) left) right
        body = CLam TySet (CLam TySet (pair (CBound 1) (CBound 0)))
        twice = CLam (TyArrow TyProp TyProp) (CLam TyProp
            (CApp (CBound 1) (CApp (CBound 1) (CBound 0))))
        slowIdentity = foldr (const (CApp twice)) (CLam TyProp (CBound 0)) [1 .. 18 :: Int]
        noise = Identity.transparentObject (Identity.theoryId foundation)
            TyProp (CApp slowIdentity CTruth)
        object = Identity.transparentObject (Identity.theoryId foundation)
            (TyArrow TySet (TyArrow TySet TySet)) body
        function = CGlobal (Identity.assertedObjectId object)
        application argument = CApp (CApp function argument) argument
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [object, noise])
    let typing = Identity.globalTypingFromClosure closure
        check = expectRight . checkScopedCanonicalCore typing [TySet, TySet]
    hypothesis <- check (CAnd CTruth (CEq TySet (CBound 0) (CBound 1)))
    target <- check (CEq TySet (application (CBound 0)) (application (CBound 1)))
    unrelated <- check (CGlobal (Identity.assertedObjectId noise))
    let report = Scope.obviousProofReport
            Scope.defaultObviousBudget
                { Scope.obviousRefutationWorkLimit = 0
                , Scope.obviousConversionPool = Conversion.conversionPool 256
                }
            Scope.AnyObviousProof foundation typing [hypothesis, unrelated] [] [] target
    proof <- expectRight (Scope.obviousRunResult report)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        typing Vector.empty (Vector.fromList [hypothesis, unrelated]) target
        (Proof.builtProofDerivation (Scope.obviousBuiltProof proof)))
    assertEqual "congruence replays the original target" target (replayedScopedKernelTarget replayed)
    assertEqual "congruence consumes the supplied projected equality"
        (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "concrete congruence needs no ground search" 0
        (Scope.obviousRefutationWorkConsumed (Scope.obviousRunStatistics report))

citedMembershipEquation :: Assertion
citedMembershipEquation = do
    foundation <- expectRight Foundation.checkedFoundation
    let member element set = CApp (CApp (CIntrinsic Member) element) set
        pair left right = CApp (CApp (CIntrinsic PairSet) left) right
        object = Identity.transparentObject (Identity.theoryId foundation)
            (TyArrow TySet (TyArrow TySet TySet))
            (CLam TySet (CLam TySet (pair (CBound 1) (CBound 0))))
        container left right = CApp (CApp (CGlobal (Identity.assertedObjectId object)) left) right
        alternatives = COr (CEq TySet (CBound 0) (CBound 2)) (CEq TySet (CBound 0) (CBound 1))
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [object])
    let typing = Identity.globalTypingFromClosure closure
        check = expectRight . checkScopedCanonicalCore typing (replicate 3 TySet)
    definition <- expectRight (checkCanonicalCore typing (CForall TySet (CForall TySet (CForall TySet
        (CEq TyProp (member (CBound 0) (container (CBound 2) (CBound 1))) alternatives)))))
    hypothesis <- check (member (CBound 0) (container (CBound 2) (CBound 1)))
    target <- check alternatives
    judgement <- expectRight (derivationImportJudgement definition)
    let imported = Scope.obviousImport (importIx 0) definition
        view = Scope.obviousImportedDefinitionView (Identity.assertedObjectId object)
            Semantic.DefinitionMembershipView imported
        report = Scope.obviousProofReport
            Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0, Scope.obviousFocusedWorkLimit = 4096}
            Scope.MustUseCanonicalDefinition foundation typing [hypothesis] [imported] [view] target
    proof <- expectRight (Scope.obviousRunResult report)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        typing (Vector.singleton judgement) (Vector.singleton hypothesis) target
        (Proof.builtProofDerivation (Scope.obviousBuiltProof proof)))
    assertEqual "the cited membership equation is consumed" (Set.singleton (importIx 0))
        (replayedScopedKernelImportUses replayed)
    assertEqual "the membership premise is consumed" (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)

citedEqualityOperand :: Assertion
citedEqualityOperand = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        pair left right = CApp (CApp (CIntrinsic OrderedPair) left) right
        representation = foldr (\_ rest -> pair (CBound 0) rest) (CBound 0) [1 .. 16 :: Int]
        fObject = Identity.transparentObject theory (TyArrow TySet TySet) (CLam TySet representation)
        fTerm = CApp (CGlobal (Identity.assertedObjectId fObject))
        value term = pair term emptySet
        gObject = Identity.transparentObject theory (TyArrow TySet TySet)
            (CLam TySet (fTerm (value (CBound 0))))
        gTerm = CApp (CGlobal (Identity.assertedObjectId gObject))
    closure <- expectRight (Identity.validateObjectClosure theory [fObject, gObject])
    let typing = Identity.globalTypingFromClosure closure
        check = expectRight . checkScopedCanonicalCore typing [TySet, TySet, TySet]
    statements <- traverse (expectRight . checkCanonicalCore typing)
        [ CForall TySet (CEq TySet (fTerm (CBound 0)) representation)
        , CForall TySet (CEq TySet (gTerm (CBound 0)) (fTerm (value (CBound 0)))) ]
    judgements <- traverse (expectRight . derivationImportJudgement) statements
    let imports = zipWith (Scope.obviousImport . importIx) [0 ..] statements
        views = zipWith (\object imported -> Scope.obviousImportedDefinitionView
            (Identity.assertedObjectId object) Semantic.DefinitionPointwiseView imported)
            [fObject, gObject] imports
        budget = Scope.defaultObviousBudget
            {Scope.obviousRefutationWorkLimit = 0, Scope.obviousFocusedWorkLimit = 16384}
    alias <- check (CEq TySet (CBound 0) (value (CBound 1)))
    named <- check (CEq TySet (CBound 2) (gTerm (CBound 1)))
    let cases =
            [ (gTerm (CBound 1), [alias], views)
            , (CBound 2, [alias, named],
                Scope.obviousLocalDefinitionView 1 Semantic.DefinitionExactView : views) ]
    for_ cases \(operand, hypotheses, selectedViews) ->
        for_ [(fTerm (CBound 0), operand), (operand, fTerm (CBound 0))] \(left, right) -> do
            target <- check (CEq TySet left right)
            let report = Scope.obviousProofReport budget Scope.MustUseCanonicalDefinition
                    foundation typing hypotheses (drop 1 imports) selectedViews target
            proof <- expectRight (Scope.obviousRunResult report)
            replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                typing (Vector.fromList judgements) (Vector.fromList hypotheses) target
                (Proof.builtProofDerivation (Scope.obviousBuiltProof proof)))
            assertEqual "uses the cited operand's equation" (Set.singleton (importIx 1))
                (replayedScopedKernelImportUses replayed)
            assertEqual "retains the supplied aliases"
                (Set.fromList (map hypothesisIx [0 .. fromIntegral (length hypotheses) - 1]))
                (replayedScopedKernelExternalHypothesisUses replayed)

citedPredicateBeforeAlias :: Assertion
citedPredicateBeforeAlias = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        qObject = Identity.transparentObject theory (TyArrow TySet TyProp)
            (CLam TySet (CEq TySet (CBound 0) emptySet))
        qTerm = CApp (CGlobal (Identity.assertedObjectId qObject))
        pObject = Identity.transparentObject theory (TyArrow TySet TyProp)
            (CLam TySet (COr (qTerm (CBound 0)) CFalsum))
        pTerm = CApp (CGlobal (Identity.assertedObjectId pObject))
    closure <- expectRight (Identity.validateObjectClosure theory [qObject, pObject])
    let typing = Identity.globalTypingFromClosure closure
        check = expectRight . checkScopedCanonicalCore typing [TySet, TySet]
    definition <- expectRight (checkCanonicalCore typing (CForall TySet
        (CEq TyProp (pTerm (CBound 0)) (COr (qTerm (CBound 0)) CFalsum))))
    alias <- check (CEq TySet (CBound 0) (CBound 1))
    fact <- check (qTerm (CBound 0))
    target <- check (pTerm (CBound 0))
    judgement <- expectRight (derivationImportJudgement definition)
    let imported = Scope.obviousImport (importIx 0) definition
        views = [Scope.obviousLocalDefinitionView 0 Semantic.DefinitionExactView,
            Scope.obviousImportedDefinitionView (Identity.assertedObjectId pObject)
                Semantic.DefinitionPointwiseView imported]
        report = Scope.obviousProofReport
            Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0}
            Scope.MustUseCanonicalDefinition foundation typing [alias, fact] [imported] views target
    proof <- expectRight (Scope.obviousRunResult report)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        typing (Vector.singleton judgement) (Vector.fromList [alias, fact]) target
        (Proof.builtProofDerivation (Scope.obviousBuiltProof proof)))
    assertEqual "the cited predicate equation is consumed" (Set.singleton (importIx 0))
        (replayedScopedKernelImportUses replayed)
    assertEqual "the unrelated argument alias is unnecessary" (Set.singleton (hypothesisIx 1))
        (replayedScopedKernelExternalHypothesisUses replayed)

suppliedArgumentEquality :: Assertion
suppliedArgumentEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let binaryType = TyArrow TySet (TyArrow TySet TySet)
        relationType = TyArrow TySet (TyArrow TySet TyProp)
        types = replicate 3 TySet <> [binaryType, relationType, relationType]
        binary index left right = CApp (CApp (CBound index) left) right
        value = binary 3 (CBound 1) (CBound 2)
        guard = binary 5 (CBound 1) (CBound 2)
        theorem = CForall TySet (CForall TySet
            (CImp (binary 7 (CBound 1) (CBound 0))
                (binary 6 emptySet (binary 5 (CBound 1) (CBound 0)))))
        budget = Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0}
        run facts target = Scope.obviousProofDetailed budget Scope.AnyObviousProof
            foundation emptyGlobalTyping facts [] [] target
    target <- checked types (binary 4 emptySet (CBound 0))
    for_ [CEq TySet (CBound 0) value, CEq TySet value (CBound 0)] \equationTerm -> do
        hypotheses <- traverse (checked types) [guard, CAnd CTruth equationTerm, theorem]
        let (statistics, result) = run hypotheses target
        proof <- expectRight result
        assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
            (Set.fromList (map hypothesisIx [0, 1, 2]))
        assertEqual "argument transport needs no ground work" 0
            (Scope.obviousRefutationWorkConsumed statistics)
    missing <- traverse (checked types) [guard, CTruth, theorem]
    case snd (run missing target) of
        Left failure -> assertBool "absence of equality is an ordinary search failure"
            (Scope.obviousFailureClass failure `notElem` [Scope.ObviousMalformedClass, Scope.ObviousIntegrityClass])
        Right _ -> assertFailure "argument transport manufactured an equality"

localAliasArguments :: Assertion
localAliasArguments = do
    foundation <- expectRight Foundation.checkedFoundation
    let binaryType = TyArrow TySet (TyArrow TySet TySet)
        types = replicate 8 TySet <> [binaryType, binaryType, TyArrow TySet TyProp]
        property = CApp (CBound 10)
        binary index left right = CApp (CApp (CBound index) left) right
        productOf left right = binary 9 (CBound left) (CBound right)
        first = binary 8 (productOf 0 1) (productOf 2 3)
        second = binary 8 (productOf 2 1) (productOf 0 3)
        closure index = CForall TySet (CForall TySet
            (CImp (CApp (CBound 12) (CBound 1))
                (CImp (CApp (CBound 12) (CBound 0))
                    (CApp (CBound 12) (binary (index + 2) (CBound 1) (CBound 0))))))
        raw = map (property . CBound) [0 .. 5]
            <> [CEq TySet (CBound 6) first, CEq TySet (CBound 7) second, closure 8, closure 9]
        views = [Scope.obviousLocalDefinitionView index Semantic.DefinitionExactView | index <- [6, 7]]
        budget = Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0}
        run requirement facts target = Scope.obviousProofDetailed budget requirement
            foundation emptyGlobalTyping facts [] views target
    hypotheses <- traverse (checked types) raw
    target <- checked types (CAnd (property (CBound 6)) (property (CBound 7)))
    for_ [Scope.AnyObviousProof, Scope.MustUseCanonicalDefinition] \requirement -> do
        let (statistics, result) = run requirement hypotheses target
        proof <- expectRight result
        assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
            (Set.fromList (map hypothesisIx [0, 1, 2, 3, 6, 7, 8, 9]))
        assertEqual "local alias transport needs no ground work" 0 (Scope.obviousRefutationWorkConsumed statistics)
        assertEqual "local alias transport admits no ground terms" 0 (Scope.obviousTermsAdmitted statistics)
    missing <- traverse (checked types) (take 3 raw <> [CTruth] <> drop 4 raw)
    case snd (run Scope.AnyObviousProof missing target) of
        Left failure -> assertBool "a missing closure premise is an ordinary search failure"
            (Scope.obviousFailureClass failure `notElem` [Scope.ObviousMalformedClass, Scope.ObviousIntegrityClass])
        Right _ -> assertFailure "alias exposure manufactured a missing closure premise"

selectedGoalGround :: Assertion
selectedGoalGround = do
    foundation <- expectRight Foundation.checkedFoundation
    let functionType = TyArrow TySet TyProp
        application = CApp (CBound 0) emptySet
        body = p (CApp (CApp (CIntrinsic OrderedPair) (CBound 0)) emptySet)
        definition = CForall TySet (CEq TyProp (CApp (CBound 1) (CBound 0)) (COr body (CNot body)))
        view = Scope.obviousLocalDefinitionView 0 Semantic.DefinitionPointwiseView
    hypothesis <- checked [functionType] definition
    target <- checked [functionType] application
    let (statistics, result) = Scope.obviousProofDetailed Scope.defaultObviousBudget
            Scope.MustUseCanonicalDefinition foundation emptyGlobalTyping [hypothesis] [] [view] target
    proof <- expectRight result
    assertReplays foundation [hypothesis] [] target (Scope.obviousBuiltProof proof)
        (Set.singleton (hypothesisIx 0))
    assertEqual "the selected residual publishes a ground certificate"
        Scope.ObviousTierCandidateBuilt (Scope.obviousRefutationTierOutcome statistics)
    assertBool "the selected syntax pays for a frozen variant" (Scope.obviousTermsAdmitted statistics > 0)
    -- The same view below a theorem premise has no new seed rights. Its closed
    -- pair application is absent from the root's original frozen syntax.
    let types = [functionType, TyProp]
    premiseDefinition <- checked types definition
    theorem <- checked types (CImp application (CBound 1))
    conclusion <- checked types (CBound 1)
    let (negativeStatistics, rejected) = Scope.obviousProofDetailed Scope.defaultObviousBudget
            Scope.AnyObviousProof foundation emptyGlobalTyping [premiseDefinition, theorem] [] [view] conclusion
    case rejected of
        Left Scope.ObviousResourceExhausted{} -> assertFailure "the finite premise control exhausted its production allowance"
        Left failure | Scope.obviousFailureClass failure == Scope.ObviousIntegrityClass -> assertFailure (show failure)
        Left _ -> pure ()
        Right _ -> assertFailure "a theorem-premise view obtained a fresh ground seed"
    assertBool "the forbidden variant does not trigger unbounded search"
        (Scope.obviousFocusedWorkConsumed negativeStatistics < 100000)

selectedGoalCycle :: Assertion
selectedGoalCycle = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyProp, TyProp]
        a = CBound 0
        b = CBound 1
    hypotheses <- traverse (checked types) [CEq TyProp a b, CEq TyProp b a]
    target <- checked types a
    let views = [Scope.obviousLocalDefinitionView index Semantic.DefinitionExactView | index <- [0, 1]]
        (statistics, result) = Scope.obviousProofDetailed Scope.defaultObviousBudget
            Scope.AnyObviousProof foundation emptyGlobalTyping hypotheses [] views target
    case result of
        Left Scope.ObviousResourceExhausted{} -> assertFailure "a view cycle kept allocating fresh families"
        Left failure | Scope.obviousFailureClass failure == Scope.ObviousIntegrityClass -> assertFailure (show failure)
        Left _ -> pure ()
        Right _ -> assertFailure "view syntax became asserted evidence"
    assertEqual "two domains also admit four late reflexive proposition rows" (12, 2)
        (Scope.obviousTermsAdmitted statistics, Scope.obviousBranchNodesCreated statistics)

publishedFactGround :: Assertion
publishedFactGround = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyProp]
        a = CBound 0
    hypotheses <- traverse (checked types) [a, CNot (p emptySet), CEq TyProp a (COr (p emptySet) (q emptySet))]
    target <- checked types (q emptySet)
    let view = Scope.obviousLocalDefinitionView 2 Semantic.DefinitionExactView
        run requirement views = Scope.obviousProofDetailed Scope.defaultObviousBudget
            requirement foundation emptyGlobalTyping hypotheses [] views target
        (statistics, result) = run Scope.MustUseCanonicalDefinition [view]
    proof <- expectRight result
    assertReplays foundation hypotheses [] target (Scope.obviousBuiltProof proof)
        (Set.fromList (map hypothesisIx [0, 1, 2]))
    assertEqual "the existing query propagates the selected disjunction without splitting" 1 (Scope.obviousBranchNodesCreated statistics)
    assertEqual "the selected fact closes through the owned ground service"
        Scope.ObviousTierCandidateBuilt (Scope.obviousRefutationTierOutcome statistics)
    let withOrdinary = hypotheses <> [target]
    supported <- expectRight (Scope.obviousProofWithRequirement Scope.defaultObviousBudget
        Scope.MustUseCanonicalDefinition foundation emptyGlobalTyping withOrdinary [] [view] target)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.fromList withOrdinary) target
        (Proof.builtProofDerivation (Scope.obviousBuiltProof supported)))
    assertBool "an early ordinary target does not erase the actual canonical fact route"
        (Set.member (hypothesisIx 2) (replayedScopedKernelExternalHypothesisUses replayed))
    case snd (run Scope.AnyObviousProof []) of
        Left Scope.ObviousResourceExhausted{} -> assertFailure "the finite unexposed control exhausted production work"
        Left failure | Scope.obviousFailureClass failure == Scope.ObviousIntegrityClass -> assertFailure (show failure)
        Left _ -> pure ()
        Right _ -> assertFailure "the control unexpectedly supplied the selected fact view"

-- Prepare selected views through the focused checker, then enter the existing
-- frozen-seed service with those proofs already among its roots. This isolates
-- evidence packaging from the driver's activation schedule.
selectedFactStartup :: Assertion
selectedFactStartup = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyArrow TySet TyProp, TyArrow TySet TyProp, TyProp, TySet]
        pair argument = CApp (CApp (CIntrinsic OrderedPair) argument) emptySet
        secondPredicate depth argument = CApp (CApp (CIntrinsic Member) argument) (CBound depth)
        firstView = CForall TySet (CEq TyProp (CApp (CBound 1) (CBound 0))
            (COr (p (pair (CBound 0))) (CBound 3)))
        secondView = CForall TySet (CEq TyProp (CApp (CBound 2) (CBound 0))
            (COr (secondPredicate 4 (pair (CBound 0))) (CBound 3)))
        contradiction = CForall TySet (CForall TySet
            (CImp (p (pair (CBound 1))) (CImp (secondPredicate 5 (pair (CBound 0))) CFalsum)))
    for_ [False, True] $ \twoFacts -> do
        hypotheses <- traverse (checked types)
            [ CApp (CBound 0) emptySet, CApp (CBound 1) (CBound 3)
            , firstView, secondView
            , if twoFacts then contradiction else CForall TySet (CImp (p (pair (CBound 0))) CFalsum) ]
        target <- checked types (CBound 2)
        selected <- traverse (checked types) (take (if twoFacts then 2 else 1)
            [COr (p (pair emptySet)) (CBound 2), COr (secondPredicate 3 (pair (CBound 3))) (CBound 2)])
        context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        inputs <- forM selected $ \statement -> do
            proof <- expectRight (Scope.obviousProofWithRequirement
                Scope.defaultObviousBudget {Scope.obviousRefutationWorkLimit = 0}
                Scope.MustUseCanonicalDefinition foundation emptyGlobalTyping hypotheses []
                [Scope.obviousLocalDefinitionView index Semantic.DefinitionPointwiseView | index <- [2, 3]] statement)
            let built = Scope.obviousBuiltProof proof
                (summary, _) = countedKernelDerivationSourceUses 100000 (Proof.builtProofDerivation built)
            uses <- maybe (assertFailure "selected proof source audit exhausted" >> fail "missing audit") pure summary
            pure (Ground.RefutationCertified built uses)
        let roots = zipWith Ground.RefutationHypothesis [0 ..] hypotheses
            start limits syntax facts = Ground.startRefutationFromSeed limits emptyGlobalTyping context
                (target :| (hypotheses <> syntax)) (roots <> facts) target
            run limits syntax facts = finishFrozenQuery limits (start limits syntax facts)
        (_, statistics, result) <- run groundLimits selected inputs
        proof <- expectRight result
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof proof)
            (Set.fromList (map hypothesisIx (if twoFacts then [0, 1, 2, 3, 4] else [0, 2, 4])))
        assertBool "startup uses one finite branch tree" (Ground.refutationBranchNodes statistics <= 7)
        for_ ([] : [take i inputs <> drop (i + 1) inputs | i <- [0 .. length inputs - 1]]) $ \incomplete -> do
            (_, _, missing) <- run groundLimits selected incomplete
            case missing of
                Left Ground.RefutationSaturated -> pure ()
                Left Ground.RefutationUnsupportedTermOutsideUniverse -> pure ()
                _ -> assertFailure "seed syntax or a missing selected proof established the target"
        (_, outsideStatistics, outside) <- run groundLimits [] inputs
        case outside of
            Left Ground.RefutationUnsupportedTermOutsideUniverse -> pure ()
            _ -> assertFailure "certified evidence granted its own missing seed syntax"
        assertEqual "unauthorized input fails before root creation" 0 (Ground.refutationBranchNodes outsideStatistics)
        let admitted = Ground.refutationTerms statistics
        (_, _, exact) <- run groundLimits {Ground.refutationGroundTermLimit = admitted} selected inputs
        _ <- expectRight exact
        (_, shortStatistics, short) <- run groundLimits {Ground.refutationGroundTermLimit = admitted - 1} selected inputs
        case short of
            Left Ground.RefutationGroundTermsExhausted -> pure ()
            _ -> assertFailure "one-short startup replenished admissions"
        assertEqual "failed startup keeps its admission debit" (admitted - 1) (Ground.refutationTerms shortStatistics)

preparedFrozenInput :: Assertion
preparedFrozenInput = do
    foundation <- expectRight Foundation.checkedFoundation
    seed <- checked [] (p emptySet)
    source <- checked [] (CApp (CLam TyProp (CBound 0)) (p one))
    target <- checked [] (p one)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [source])
    (available, domain, _) <- prepareFrozenFamily groundLimits
        (Ground.startRefutationFromSeed groundLimits emptyGlobalTyping context (seed :| []) [] seed)
    (built, uses) <- hypothesisInput context (hypothesisIx 0)
    let (remaining, result) = Ground.prepareFrozenFact available emptyGlobalTyping context domain built uses
        cost = Ground.refutationWorkLimit available - Ground.refutationWorkLimit remaining
        run limits = Ground.prepareFrozenFact limits emptyGlobalTyping context domain built uses
    (prepared, compatible) <- expectRight result
    assertBool "the original immutable domain still excludes the closed pair" (not compatible)
    assertBool "even outside input pays preparation and conversion"
        (cost > 0 && Ground.refutationConversionPool remaining /= Ground.refutationConversionPool available)
    assertEqual "a neutral probe admits no terms"
        (Ground.refutationGroundTermLimit available) (Ground.refutationGroundTermLimit remaining)
    assertEqual "a neutral probe creates no branches"
        (Ground.refutationBranchNodeLimit available) (Ground.refutationBranchNodeLimit remaining)
    _ <- expectRight (snd (run available {Ground.refutationWorkLimit = cost}))
    let (shortRemaining, short) = run available {Ground.refutationWorkLimit = cost - 1}
    case short of
        Left Ground.RefutationWorkExhausted -> pure ()
        _ -> assertFailure "a failed compatibility probe concealed structural exhaustion"
    assertEqual "failed preparation keeps its actual debit" 0 (Ground.refutationWorkLimit shortRemaining)
    let start fact = Ground.startRefutationFromSeed remaining emptyGlobalTyping context
            (seed :| [source]) [fact] target
    (_, preparedStatistics, preparedResult) <- finishFrozenQuery remaining (start (Ground.RefutationPrepared prepared))
    (_, rawStatistics, rawResult) <- finishFrozenQuery remaining (start (Ground.RefutationCertified built uses))
    for_ [preparedResult, rawResult] $ \outcome -> do
        proof <- expectRight outcome
        assertReplays foundation [source] [] target (Ground.refutationCandidateProof proof)
            (Set.singleton (hypothesisIx 0))
    assertBool "startup reuses the checked logical view instead of converting it again"
        (Ground.refutationRemainingConversionPool preparedStatistics > Ground.refutationRemainingConversionPool rawStatistics)

publishedFactScopeIsolation :: Assertion
publishedFactScopeIsolation = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TyProp, TyProp]
        a = CBound 0
        b = CBound 1
        goal = q emptySet
    hypotheses <- traverse (checked types) [CEq TyProp a (COr (p emptySet) goal), CNot (p emptySet)]
    target <- checked types (CAnd (CImp a goal) (CImp b goal))
    let (_, result) = Scope.obviousProofDetailed Scope.defaultObviousBudget Scope.AnyObviousProof
            foundation emptyGlobalTyping hypotheses []
            [Scope.obviousLocalDefinitionView 0 Semantic.DefinitionExactView] target
    case result of
        Left Scope.ObviousResourceExhausted{} -> assertFailure "the finite sibling control exhausted production work"
        Left failure | Scope.obviousFailureClass failure == Scope.ObviousIntegrityClass -> assertFailure (show failure)
        Left _ -> pure ()
        Right _ -> assertFailure "a selected fact crossed same-shaped sibling assumption scopes"

incrementalGround :: Assertion
incrementalGround = do
    foundation <- expectRight Foundation.checkedFoundation
    let conclusion = CApp (CApp (CIntrinsic Member) one) one
    hypotheses <- traverse (checked [])
        [ COr (p emptySet) (q emptySet)
        , CImp (p emptySet) conclusion
        , CImp (q emptySet) conclusion
        ]
    target <- checked [] conclusion
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let facts = zipWith Ground.RefutationHypothesis [0 ..] hypotheses
        initial = Ground.startRefutation groundLimits emptyGlobalTyping context facts target
        initialStats = Ground.refutationSessionStatistics initial
        (serialStats, serialResult) = Ground.runRefutation groundLimits emptyGlobalTyping context facts target
        drain steps observations limits session = do
            assertBool "the finite branch fixture does not spin" (steps < (1000 :: Int))
            let before = Ground.refutationSessionStatistics session
                observed = statisticsObservation before
            assertEqual "observing a suspended session does not advance it" observed
                (statisticsObservation (Ground.refutationSessionStatistics session))
            case Ground.advanceRefutation limits session of
                (remaining, Ground.RefutationPending next) ->
                    drain (steps + 1) (before : observations) remaining next
                (_remaining, Ground.RefutationBlocked statistics failure _suspended) ->
                    pure (reverse observations, statistics, Left failure)
                (_remaining, Ground.RefutationFinished statistics result) ->
                    pure (reverse observations, statistics, result)
    assertEqual "startup has not traversed or seeded roots" (1000000, 1000000, 0, 0, 0, 0, 0)
        (statisticsObservation initialStats)
    (observations, incrementalStats, incrementalResult) <- drain 0 [] groundLimits initial
    serial <- expectRight serialResult
    incremental <- expectRight incrementalResult
    assertEqual "serial and resumed searches have identical costs"
        (statisticsObservation serialStats) (statisticsObservation incrementalStats)
    assertEqual "serial and resumed searches retain exact imports"
        (Ground.refutationCandidateImports serial) (Ground.refutationCandidateImports incremental)
    assertBool "the session yields while collecting roots, before any branch exists"
        (any (\statistics -> Ground.refutationTerms statistics > 0
            && Ground.refutationBranchNodes statistics == 0) observations)
    assertBool "the session yields after the left branch starts and before the right starts"
        (any ((== 2) . Ground.refutationBranchNodes) observations)
    assertBool "the fixture actually visited both split children"
        (Ground.refutationBranchNodes incrementalStats >= 3)
    for_ [serial, incremental] \candidate ->
        assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
            (Set.fromList [hypothesisIx 0, hypothesisIx 1, hypothesisIx 2])

rejectsSessionReplenishment :: Assertion
rejectsSessionReplenishment = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checked [] CTruth
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let initial = Ground.startRefutation groundLimits emptyGlobalTyping context [] target
    case Ground.advanceRefutation groundLimits initial of
        (remaining, Ground.RefutationPending suspended) -> do
            assertBool "the first transition spent work"
                (Ground.refutationWorkLimit remaining < Ground.refutationWorkLimit groundLimits)
            case Ground.advanceRefutation groundLimits suspended of
                (_, Ground.RefutationFinished _ (Left Ground.RefutationInternalFailure{})) -> pure ()
                _ -> assertFailure "resumption accepted a replenished allowance"
            for_ [remaining {Ground.refutationBooleanPropagation = False},
                  remaining {Ground.refutationExtendedRules = False},
                  remaining {Ground.refutationUniversals = Ground.ExistingUniversals 0}] $ \changed ->
                case Ground.advanceRefutation changed suspended of
                    (_, Ground.RefutationFinished _ (Left Ground.RefutationInternalFailure{})) -> pure ()
                    _ -> assertFailure "resumption changed the session's inference policy"
            let reduced = remaining {Ground.refutationWorkLimit = 0}
            case Ground.advanceRefutation reduced suspended of
                (_, Ground.RefutationFinished _ (Left Ground.RefutationWorkExhausted)) -> pure ()
                _ -> assertFailure "another task's expenditure was not respected on resumption"
        _ -> assertFailure "startup failed to yield before root admission"

incrementalRuleApplications :: Assertion
incrementalRuleApplications = do
    foundation <- expectRight Foundation.checkedFoundation
    let rule = CForall TySet (CForall TySet
            (CImp (CEq TySet (CBound 1) (CBound 0))
                (CImp (p (CBound 1)) (q (CBound 0)))))
    hypotheses <- traverse (checked [TySet, TySet])
        [rule, CEq TySet (CBound 0) (CBound 1), p (CBound 0), p (CBound 1)]
    target <- checked [TySet, TySet] CFalsum
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [TySet, TySet] hypotheses)
    let initial = Ground.startRefutation groundLimits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] hypotheses) target
        drain steps limits session = do
            assertBool "the exact-rule fixture does not spin" (steps < (3000 :: Int))
            let before = Ground.refutationRuleInstances (Ground.refutationSessionStatistics session)
                checkStep statistics = do
                    let nextCount = Ground.refutationRuleInstances statistics
                    assertBool "one advance publishes at most one exact instance"
                        (before <= nextCount && nextCount - before <= 1)
            case Ground.advanceRefutation limits session of
                (remaining, Ground.RefutationPending next) -> do
                    checkStep (Ground.refutationSessionStatistics next)
                    drain (steps + 1) remaining next
                (remaining, Ground.RefutationBlocked statistics failure suspended) -> do
                    checkStep statistics
                    assertEqual "ordinary open-query diagnostic" Ground.RefutationSaturated failure
                    assertEqual "the blocked query retains its actual spent work"
                        (statisticsObservation statistics)
                        (statisticsObservation (Ground.refutationSessionStatistics suspended))
                    case Ground.advanceRefutation remaining suspended of
                        (_, Ground.RefutationBlocked unchanged _ _) ->
                            assertEqual "no new evidence leaves the query parked without more work"
                                (statisticsObservation statistics) (statisticsObservation unchanged)
                        _ -> assertFailure "a parked query restarted itself"
                    pure statistics
                (_, Ground.RefutationFinished statistics result) -> do
                    checkStep statistics
                    case result of
                        Left Ground.RefutationSaturated -> pure statistics
                        Left failure -> assertFailure (show failure) >> fail "unexpected rule outcome"
                        Right _ -> assertFailure "consistent rule roots proved falsity" >> fail "invalid closure"
    statistics <- drain 0 groundLimits initial
    assertBool "both equality orientations produced an instance"
        (Ground.refutationRuleInstances statistics >= 2)

-- Stop before a query allocates its root branch. The family has paid for the
-- immutable syntax; subsequent queries debit the returned remaining allowance.
prepareFrozenFamily
    :: Ground.RefutationLimits
    -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Ground.FrozenDomain Void, Ground.RefutationStatistics)
prepareFrozenFamily = go (0 :: Int)
  where
    go steps limits session = do
        assertBool "family preparation terminates" (steps < 1000)
        case Ground.refutationSessionDomain session of
            Just domain -> pure (limits, domain, Ground.refutationSessionStatistics session)
            Nothing -> case Ground.advanceRefutation limits session of
                (remaining, Ground.RefutationPending next) -> go (steps + 1) remaining next
                (_, Ground.RefutationBlocked _ failure _) ->
                    assertFailure ("family blocked before freezing: " <> show failure) >> fail "missing domain"
                (_, Ground.RefutationFinished _ result) ->
                    assertFailure ("family preparation ended before freezing: " <>
                        either show (const "unexpected proof") result) >> fail "missing domain"

finishFrozenQuery
    :: Ground.RefutationLimits
    -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Ground.RefutationStatistics,
        Either Ground.RefutationFailure (Ground.RefutationCandidate Void))
finishFrozenQuery = finishGroundQuery True

finishCanonicalQuery
    :: Ground.RefutationLimits -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Ground.RefutationStatistics,
        Either Ground.RefutationFailure (Ground.RefutationCandidate Void))
finishCanonicalQuery = finishGroundQuery False

finishGroundQuery
    :: Bool -> Ground.RefutationLimits -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Ground.RefutationStatistics,
        Either Ground.RefutationFailure (Ground.RefutationCandidate Void))
finishGroundQuery ordinary = go (0 :: Int)
  where
    go steps limits session = do
        assertBool "the bounded query terminates" (steps < 1000)
        case Ground.advanceRefutation limits session of
            (remaining, Ground.RefutationPending next) -> case if ordinary then Ground.refutationSessionAnyCandidate next else Nothing of
                Just candidate -> pure (remaining, Ground.refutationSessionStatistics next, Right candidate)
                Nothing -> go (steps + 1) remaining next
            (remaining, Ground.RefutationBlocked statistics failure _) -> pure (remaining, statistics, Left failure)
            (remaining, Ground.RefutationFinished statistics result) -> pure (remaining, statistics, result)

sharedFrozenDomain :: Assertion
sharedFrozenDomain = do
    foundation <- expectRight Foundation.checkedFoundation
    left <- checked [] (CEq TySet emptySet emptySet)
    right <- checked [] (CEq TySet one one)
    parent <- checked [] (CAnd (scopedCoreTerm left) (scopedCoreTerm right))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let limits = groundLimits {Ground.refutationBranchNodeLimit = 2}
    (available, domain, familyStats) <- prepareFrozenFamily limits
        (Ground.startRefutation limits emptyGlobalTyping context [] parent)
    assertBool "the family paid for its syntax" (Ground.refutationTerms familyStats > 0)
    assertEqual "freezing has not allocated a query branch" 0 (Ground.refutationBranchNodes familyStats)
    let run remaining target = finishFrozenQuery remaining
            (Ground.startCertifiedRefutationInDomain remaining emptyGlobalTyping context domain [] target)
    (afterLeft, leftStats, leftResult) <- run available left
    (afterRight, rightStats, rightResult) <- run afterLeft right
    for_ [(left, leftResult), (right, rightResult)] \(target, result) -> do
        proof <- expectRight result
        assertReplays foundation [] [] target (Ground.refutationCandidateProof proof) Set.empty
    assertEqual "both queries reuse the family's admitted syntax" (0, 0)
        (Ground.refutationTerms leftStats, Ground.refutationTerms rightStats)
    assertEqual "each actual query owns its root branch" (1, 1)
        (Ground.refutationBranchNodes leftStats, Ground.refutationBranchNodes rightStats)
    assertBool "query work debits the family remainder"
        (Ground.refutationWorkLimit afterRight < Ground.refutationWorkLimit afterLeft
            && Ground.refutationWorkLimit afterLeft < Ground.refutationWorkLimit available)
    (_, thirdStats, thirdResult) <- run afterRight left
    case thirdResult of
        Left Ground.RefutationBranchesExhausted -> pure ()
        _ -> assertFailure "a later query replenished the two root branches"
    assertEqual "an exhausted query creates no branch" 0 (Ground.refutationBranchNodes thirdStats)

frozenSyntaxIsNotEvidence :: Assertion
frozenSyntaxIsNotEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    positive <- checked [] (p emptySet)
    negative <- checked [] (CNot (p emptySet))
    parent <- checked [] (CAnd (p emptySet) (CNot (p emptySet)))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [positive])
    (available, domain, _) <- prepareFrozenFamily groundLimits
        (Ground.startRefutation groundLimits emptyGlobalTyping context
            [Ground.RefutationHypothesis 0 positive] parent)
    let run remaining inputs target = finishFrozenQuery remaining
            (Ground.startCertifiedRefutationInDomain remaining emptyGlobalTyping context domain inputs target)
    (afterPositive, _, positiveResult) <- run available [] positive
    (afterNegative, _, negativeResult) <- run afterPositive [] negative
    for_ [positiveResult, negativeResult] \case
        Left Ground.RefutationSaturated -> pure ()
        Left failure -> assertFailure ("unexpected query failure: " <> show failure)
        Right _ -> assertFailure "a query inherited seed assertions or another query's negation"
    let (built, _, _) = Scope.runScoped 10000 (Conversion.conversionPool 1000000) allowance
            context Map.empty \scope -> do
                evidence <- Scope.scopeHypothesis scope (hypothesisIx 0)
                pure (Scope.evidenceProof evidence, Scope.evidenceUses evidence)
    input <- expectRight built
    (_, _, assertedResult) <- run afterNegative [input] positive
    proof <- expectRight assertedResult
    assertReplays foundation [positive] [] positive (Ground.refutationCandidateProof proof)
        (Set.singleton (hypothesisIx 0))

rejectsFrozenDomainExpansion :: Assertion
rejectsFrozenDomainExpansion = do
    foundation <- expectRight Foundation.checkedFoundation
    seed <- checked [] (p emptySet)
    outside <- checked [] (p one)
    truth <- checked [] CTruth
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [outside])
    (available, domain, _) <- prepareFrozenFamily groundLimits
        (Ground.startRefutation groundLimits emptyGlobalTyping context [] seed)
    let (built, _, _) = Scope.runScoped 10000 (Conversion.conversionPool 1000000) allowance
            context Map.empty \scope -> do
                evidence <- Scope.scopeHypothesis scope (hypothesisIx 0)
                pure (Scope.evidenceProof evidence, Scope.evidenceUses evidence)
    input <- expectRight built
    for_ [([], outside), ([input], truth)] \(inputs, target) -> do
        (_, statistics, result) <- finishFrozenQuery available
            (Ground.startCertifiedRefutationInDomain available emptyGlobalTyping context domain inputs target)
        case result of
            Left Ground.RefutationUnsupportedTermOutsideUniverse -> pure ()
            Left failure -> assertFailure ("unexpected frozen-domain failure: " <> show failure)
            Right _ -> assertFailure "a residual target or certified fact thawed the domain"
        assertEqual "outside-domain input publishes no branch" 0 (Ground.refutationBranchNodes statistics)

rejectsFrozenDomainContext :: Assertion
rejectsFrozenDomainContext = do
    foundation <- expectRight Foundation.checkedFoundation
    seed <- checked [] (p emptySet)
    target <- checked [TySet] (p (CBound 0))
    root <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    child <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [TySet] [])
    (available, domain, _) <- prepareFrozenFamily groundLimits
        (Ground.startRefutation groundLimits emptyGlobalTyping root [] seed)
    (_, statistics, result) <- finishFrozenQuery available
        (Ground.startCertifiedRefutationInDomain available emptyGlobalTyping child domain [] target)
    case result of
        Left Ground.RefutationInternalFailure{} -> pure ()
        _ -> assertFailure "a domain was reused under a different term binder"
    assertEqual "context rejection allocates no branch" 0 (Ground.refutationBranchNodes statistics)

parkGroundQuery
    :: Ground.RefutationLimits
    -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Ground.RefutationStatistics, Ground.RefutationFailure,
        Ground.RefutationSession Void)
parkGroundQuery = go (0 :: Int)
  where
    go steps limits session = do
        assertBool "the open query terminates" (steps < 3000)
        case Ground.advanceRefutation limits session of
            (remaining, Ground.RefutationPending next) -> go (steps + 1) remaining next
            (remaining, Ground.RefutationBlocked statistics failure suspended) ->
                pure (remaining, statistics, failure, suspended)
            (_, Ground.RefutationFinished _ result) ->
                assertFailure ("expected an open query: " <> either show (const "unexpected proof") result)
                    >> fail "query was not parked"

hypothesisInput
    :: Proof.ProofContext Void
    -> HypothesisIx
    -> IO (Proof.BuiltProof Void, KernelSourceUses)
hypothesisInput context index = do
    let (result, _, _) = Scope.runScoped 10000 (Conversion.conversionPool 1000000) allowance
            context Map.empty \scope -> do
                evidence <- Scope.scopeHypothesis scope index
                pure (Scope.evidenceProof evidence, Scope.evidenceUses evidence)
    expectRight result

resumesSplitWithCertifiedInput :: Assertion
resumesSplitWithCertifiedInput = do
    foundation <- expectRight Foundation.checkedFoundation
    let conclusion = CApp (CApp (CIntrinsic Member) one) one
    hypotheses <- traverse (checked [])
        [ COr (p emptySet) (q emptySet)
        , CImp (p emptySet) conclusion
        , CImp (q emptySet) conclusion
        ]
    target <- checked [] conclusion
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let initial = Ground.startRefutation groundLimits emptyGlobalTyping context
            (zipWith Ground.RefutationHypothesis [0 ..] (take 2 hypotheses)) target
    (remaining, before, failure, parked) <- parkGroundQuery groundLimits initial
    assertEqual "the missing right rule leaves an ordinary open query" Ground.RefutationSaturated failure
    assertBool "the query has already created both disjunction children"
        (Ground.refutationBranchNodes before >= 3)
    (proof, uses) <- hypothesisInput context (hypothesisIx 2)
    resumed <- expectRight (Ground.resumeRefutationWithInput proof uses parked)
    assertEqual "enqueuing evidence preserves all spent query costs"
        (statisticsObservation before)
        (statisticsObservation (Ground.refutationSessionStatistics resumed))
    -- Existing branches suffice. A restarted query or split cannot pass this.
    let restricted = remaining {Ground.refutationBranchNodeLimit = 0}
    (afterQuery, statistics, result) <- finishFrozenQuery restricted resumed
    candidate <- expectRight result
    assertEqual "resumption reuses the root and already-created children"
        (Ground.refutationBranchNodes before) (Ground.refutationBranchNodes statistics)
    assertBool "late-input processing spends the existing work remainder"
        (Ground.refutationWorkLimit afterQuery < Ground.refutationWorkLimit remaining)
    assertReplays foundation hypotheses [] target (Ground.refutationCandidateProof candidate)
        (Set.fromList [hypothesisIx 0, hypothesisIx 1, hypothesisIx 2])

ignoresUnusableLateInputs :: Assertion
ignoresUnusableLateInputs = do
    foundation <- expectRight Foundation.checkedFoundation
    known <- checked [] (p emptySet)
    outside <- checked [] (p one)
    target <- checked [] CFalsum
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [known, outside])
    let initial = Ground.startRefutation groundLimits emptyGlobalTyping context
            [Ground.RefutationHypothesis 0 known] target
    (remaining, before, originalFailure, parked) <- parkGroundQuery groundLimits initial
    duplicate <- hypothesisInput context (hypothesisIx 0)
    unusable <- hypothesisInput context (hypothesisIx 1)
    let resume limits oldStatistics session (proof, uses) = do
            pending <- expectRight (Ground.resumeRefutationWithInput proof uses session)
            (afterQuery, statistics, failure, suspended) <- parkGroundQuery limits pending
            assertEqual "a skipped late input does not poison the query diagnostic" originalFailure failure
            assertEqual "skipped input publishes no terms, signed facts, instances or branches"
                ( Ground.refutationTerms oldStatistics, Ground.refutationSignedFormulas oldStatistics
                , Ground.refutationRuleInstances oldStatistics, Ground.refutationBranchNodes oldStatistics)
                ( Ground.refutationTerms statistics, Ground.refutationSignedFormulas statistics
                , Ground.refutationRuleInstances statistics, Ground.refutationBranchNodes statistics)
            assertBool "failed and redundant preparation remain charged"
                (Ground.refutationWorkLimit afterQuery < Ground.refutationWorkLimit limits)
            pure (afterQuery, statistics, suspended)
    (afterDuplicate, duplicateStats, duplicateParked) <- resume remaining before parked duplicate
    _ <- resume afterDuplicate duplicateStats duplicateParked unusable
    pure ()

consumerDelivery :: Assertion
consumerDelivery = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checked [] (p emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [target])
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance context Map.empty \scope -> do
            evidence <- Scope.scopeHypothesis scope (hypothesisIx 0)
            Scope.scopeConsumerDelivery (error "registration inspected an old waiter") scope evidence
    (uninspected, returns) <- expectRight result
    uninspected @?= 2
    assertEqual "FIFO publication, immediate late evidence, then support completion without another attachment"
        ([1 .. 8] <> [10, 9]) (fst <$> returns)
    for_ returns \(ordinal, outcome) -> case (ordinal, outcome) of
        (9, Left Scope.ObviousCanonicalDefinitionEvidenceRequired) -> pure ()
        (9, _) -> assertFailure "ordinary evidence incorrectly satisfied canonical demand"
        _ -> do
            proof <- expectRight outcome
            replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits emptyGlobalTyping
                Vector.empty (Vector.singleton target) target (Proof.builtProofDerivation proof))
            replayedScopedKernelTarget replayed @?= target
            replayedScopedKernelExternalHypothesisUses replayed @?= Set.singleton (hypothesisIx 0)

-- These tests use only the driver's opaque handles. In particular, the caller
-- cannot supply a different context or an earlier service snapshot on resume.
freezeOwnedQuery
    :: Scope.GroundQuery request Void -> Scope.Scoped request Void (Scope.GroundDomain request Void)
freezeOwnedQuery = go (0 :: Int)
  where
    go advances query
        | advances >= 1000 = boundaryFailure "owned domain did not finish preparation"
        | otherwise = Scope.scopeGroundDomain query >>= \case
            Just domain -> pure domain
            Nothing -> Scope.scopeAdvanceGround query >>= \case
                Scope.GroundQueryPending -> go (advances + 1) query
                _ -> boundaryFailure "owned query stopped before freezing"

finishOwnedQuery
    :: Scope.GroundQuery request Void -> Scope.Scoped request Void (Scope.GroundQueryProgress (Scope.Evidence request Void))
finishOwnedQuery = go (0 :: Int)
  where
    go advances query
        | advances >= 3000 = boundaryFailure "owned query did not stop"
        | otherwise = Scope.scopeAdvanceGround query >>= \case
            Scope.GroundQueryPending -> go (advances + 1) query
            outcome -> pure outcome

boundaryFailure :: Text -> Scope.Scoped request Void result
boundaryFailure = Except.throwE . Scope.ObviousIntegrityFailure . Proof.ProofStructuralCompositionMismatch

rejectsSameShapedOwnedDomains :: Assertion
rejectsSameShapedOwnedDomains = do
    foundation <- expectRight Foundation.checkedFoundation
    root <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    atom <- checked [] (p emptySet)
    reflexive <- checked [TySet] (CEq TySet (CBound 0) (CBound 0))
    let run binder = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance root Map.empty \parent -> do
            let sibling = if binder then Scope.scopeBind parent TySet else Scope.scopeAssume parent atom
                target = if binder then reflexive else atom
            left <- sibling
            right <- sibling
            query <- Scope.scopeStartGround emptyGlobalTyping left [] [] target
            domain <- freezeOwnedQuery query
            () <$ Scope.scopeStartGroundInDomain domain right [] target
    for_ [False, True] \binder -> case run binder of
        (Left Scope.ObviousIntegrityFailure{}, _, _) -> pure ()
        _ -> assertFailure "equal context shapes authorized reuse across nominal sibling scopes"

sharesOwnedDomainWithDescendants :: Assertion
sharesOwnedDomainWithDescendants = do
    foundation <- expectRight Foundation.checkedFoundation
    atom <- checked [] (p emptySet)
    seed <- checked [] (CAnd (p emptySet) (q emptySet))
    target <- checked [] (CImp (p emptySet) (p emptySet))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000) allowance
            context Map.empty \parent -> do
                initial <- Scope.scopeStartGround emptyGlobalTyping parent [] [] seed
                domain <- freezeOwnedQuery initial
                child <- Scope.scopeAssume parent atom
                input <- Scope.scopeHypothesis child (hypothesisIx 0)
                query <- Scope.scopeStartGroundInDomain domain child [input] atom
                finishOwnedQuery query >>= \case
                    Scope.GroundQueryFinished statistics (Right body) -> do
                        proof <- Scope.scopeIntroduceImplication parent body
                        pure (statistics, Scope.evidenceProof proof)
                    _ -> boundaryFailure "a valid family descendant did not close"
    (statistics, proof) <- expectRight result
    assertEqual "the descendant reused all paid syntax" 0 (Ground.refutationTerms statistics)
    assertEqual "only the actual child query allocated a branch" 1 (Ground.refutationBranchNodes statistics)
    assertReplays foundation [] [] target proof Set.empty

resumesCurrentOwnedQuery :: Assertion
resumesCurrentOwnedQuery = do
    foundation <- expectRight Foundation.checkedFoundation
    let conclusion = CApp (CApp (CIntrinsic Member) one) one
    hypotheses <- traverse (checked [])
        [COr (p emptySet) (q emptySet), CImp (p emptySet) conclusion, CImp (q emptySet) conclusion]
    target <- checked [] conclusion
    truth <- checked [] CTruth
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    let (result, _, _) = Scope.runScoped 1000000 (Conversion.conversionPool 1000000)
            allowance context Map.empty \scope -> do
                inputs <- traverse (Scope.scopeHypothesis scope . hypothesisIx) [0, 1]
                query <- Scope.scopeStartGround emptyGlobalTyping scope [] inputs target
                -- Retaining this original handle must still name the current
                -- split frontier after every intervening advance.
                before <- finishOwnedQuery query >>= \case
                    Scope.GroundQueryBlocked statistics Ground.RefutationSaturated -> pure statistics
                    _ -> boundaryFailure "the initial query did not retain an open split"
                _ <- groundProof scope [] [] truth
                late <- Scope.scopeHypothesis scope (hypothesisIx 2)
                Scope.scopeResumeGround query late
                finishOwnedQuery query >>= \case
                    Scope.GroundQueryFinished after (Right evidence) -> do
                        again <- Scope.scopeAdvanceGround query
                        pure (before, after, Scope.evidenceProof evidence, case again of
                            Scope.GroundQueryFinished statistics (Right cached) ->
                                let uses = Scope.evidenceUses cached
                                in Just (statisticsObservation statistics,
                                    kernelSourceImportUses uses, kernelSourceExternalHypothesisUses uses)
                            _ -> Nothing)
                    _ -> boundaryFailure "the retained query failed to consume its late input"
    (before, after, proof, cached) <- expectRight result
    assertBool "the initial query retained a split" (Ground.refutationBranchNodes before >= 3)
    assertEqual "resumption allocated no new branch"
        (Ground.refutationBranchNodes before) (Ground.refutationBranchNodes after)
    assertBool "resumption debited an already-spent allowance"
        (Ground.refutationRemainingWork after < Ground.refutationRemainingWork before)
    assertEqual "a completed query retains only its certificate and final counters"
        (Just (statisticsObservation after, Set.empty, Set.fromList (map hypothesisIx [0, 1, 2]))) cached
    assertReplays foundation hypotheses [] target proof (Set.fromList (map hypothesisIx [0, 1, 2]))


preparationConversion :: Assertion
preparationConversion = do
    source <- checked [] (CApp (CLam TyProp (CBound 0)) (p emptySet))
    target <- checked [] (p emptySet)
    different <- checked [] (q emptySet)
    let real = Conversion.conversionPool 10000000
        operation = \limit -> Conversion.convertibleChecked emptyGlobalTyping limit source target
        completed = operation (Conversion.conversionLimit 2000000)
        cost = Conversion.conversionCostAmount (Conversion.conversionCost completed)
        run offered pool = case Effort.runPreparatoryConversion (Conversion.conversionLimit offered) pool operation of
            Left _ -> assertFailure "valid converter reported inconsistent accounting" >> fail "accounting"
            Right value -> pure value
    assertBool "the fixture requires conversion" (cost > 1)
    (_, afterExact, exact) <- run cost real
    assertEqual "success at the exact offered boundary is completion"
        (Effort.PreparationFinished (Right Conversion.Convertible)) exact
    assertEqual "successful probe debits the original owner" (10000000 - cost)
        (Conversion.conversionPoolAmount afterExact)
    (_, afterSmall, small) <- run (cost - 1) real
    assertEqual "one less unit is a policy stop"
        (Effort.NeedsMoreEffort (Conversion.conversionLimit (cost - 1))) small
    assertEqual "failed probe is charged" (10000000 - cost + 1)
        (Conversion.conversionPoolAmount afterSmall)
    (_, afterRetry, retry) <- run cost afterSmall
    assertEqual "a larger effort can complete with a smaller real pool" exact retry
    assertEqual "both executions are paid" (10000000 - cost * 2 + 1)
        (Conversion.conversionPoolAmount afterRetry)
    (owner, exhaustedPool, exhausted) <- run (cost - 1) (Conversion.conversionPool (cost - 1))
    assertEqual "a tied request pool owns the real exhaustion" Effort.ObviousConversionPoolOwner owner
    assertEqual "real exhaustion is not resumable policy work"
        (Effort.PreparationFinished (Left (Conversion.ConversionLimitExhausted
            (Conversion.conversionLimit (cost - 1))))) exhausted
    assertEqual "no overdraft" 0 (Conversion.conversionPoolAmount exhaustedPool)
    case Effort.runPreparatoryConversion (Conversion.conversionLimit 10000) real
            (\limit -> Conversion.convertibleChecked emptyGlobalTyping limit target different) of
        Right (_, _, Effort.PreparationFinished (Right Conversion.NotConvertible)) -> pure ()
        _ -> assertFailure "genuine mismatch was turned into a deferred operation"

preparationBuilder :: Assertion
preparationBuilder = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checked [] (p emptySet)
    target <- checked [] (CApp (CLam TyProp (CBound 0)) (p emptySet))
    different <- checked [] (q emptySet)
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [source])
    premise <- expectRight (Proof.indexedHypothesisProof context (hypothesisIx 0))
    let real = Conversion.conversionPool 10000000
        operation work pool = Proof.runCountedProof work pool
            (Proof.countedConversionProof context premise target)
        (complete, _, afterFull) = operation 10000 real
        cost = 10000000 - Conversion.conversionPoolAmount afterFull
        run amount pool = Effort.runPreparatoryBuilder (Conversion.conversionLimit amount) 10000 pool operation
    _ <- expectRight complete
    assertBool "the compound builder needs conversion" (cost > 1)
    let (exact, exactWork, exactPool) = run cost real
    proof <- case exact of
        Effort.PreparationFinished result -> expectRight result
        _ -> assertFailure "the exact builder slice did not finish" >> fail "incomplete"
    assertReplays foundation [source] [] target proof
        (Set.singleton (hypothesisIx 0))
    assertEqual "the builder returns the real remainder" afterFull exactPool
    assertBool "compound construction is structurally charged" (exactWork < 10000)
    let (small, smallWork, smallPool) = run (cost - 1) real
    case small of
        Effort.NeedsMoreEffort offered -> assertEqual "the retained retry threshold is the offered slice"
            (cost - 1) (Conversion.conversionLimitAmount offered)
        _ -> assertFailure "one-short builder did not retain a policy stop"
    assertBool "failure preserves structural work" (smallWork < 10000)
    assertEqual "failure debits only the local consumption" (10000000 - cost + 1)
        (Conversion.conversionPoolAmount smallPool)
    let (exhausted, _, exhaustedPool) = run (cost - 1) (Conversion.conversionPool (cost - 1))
    case exhausted of
        Effort.PreparationFinished (Left (CountedCoreOperationFailed
                (Proof.ProofConversionLimitExhausted Proof.ProofConversionAggregatePool _))) -> pure ()
        _ -> assertFailure "a real builder-pool limit was relabelled as preparation"
    assertEqual "real builder exhaustion never overdrafts" 0 (Conversion.conversionPoolAmount exhaustedPool)
    let mismatch work pool = Proof.runCountedProof work pool
            (Proof.countedConversionProof context premise different)
        (failed, _, _) = Effort.runPreparatoryBuilder (Conversion.conversionLimit 10000) 10000 real mismatch
    case failed of
        Effort.PreparationFinished (Left (CountedCoreOperationFailed Proof.ProofConversionNotConvertible)) -> pure ()
        _ -> assertFailure "the builder's required-conversion mismatch lost its fatal identity"
    for_ [(10001, Conversion.conversionPool 1), (10000, Conversion.conversionPool 2)] \(work, pool) -> do
        let (invalid, _, _) = Effort.runPreparatoryBuilder (Conversion.conversionLimit 1) 10000 real
                (\_ _ -> (Right (), work, pool))
        case invalid of
            Effort.PreparationFinished (Left (CountedCoreOperationFailed Proof.ProofStructuralCompositionMismatch{})) -> pure ()
            _ -> assertFailure "a replenished local allowance was accepted"

-- The fixture admits its nominal root with one focused unit, leaving none for
-- query setup or certification. Those operations belong to the ground owner.
groundWithoutFocusedCredit :: Assertion
groundWithoutFocusedCredit = do
    foundation <- expectRight Foundation.checkedFoundation
    target <- checked [] (COr (p emptySet) (CNot (p emptySet)))
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [])
    let run work = Scope.runScoped 1 (Conversion.conversionPool 1000000)
            allowance {Scope.groundWork = work} context Map.empty \scope -> do
                (statistics, groundResultValue) <- Scope.scopeRefute emptyGlobalTyping scope [] [] target
                evidence <- either (boundaryFailure . fromString . show) pure groundResultValue
                pure (statistics, Scope.evidenceProof evidence)
        (result, focused, _) = run 1000000
    (statistics, proof) <- expectRight result
    assertEqual "ground setup and publication do not borrow focused credit" 0 focused
    assertReplays foundation [] [] target proof Set.empty
    let used = 1000000 - Ground.refutationRemainingWork statistics
        (exact, _, _) = run used
        (short, _, _) = run (used - 1)
    (exactStatistics, exactProof) <- expectRight exact
    assertEqual "publication is included in the actual ground remainder" 0
        (Ground.refutationRemainingWork exactStatistics)
    assertReplays foundation [] [] target exactProof Set.empty
    case short of
        Left (Scope.ObviousResourceExhausted Scope.ObviousRefutationWorkLimit) -> pure ()
        _ -> assertFailure "one short must fail at the real ground owner, including certification"

-- Compare the actual driver quantum with individual refuter transitions. A
-- second owned query spends work between the two publication boundaries.
ownedGroundPublicationQuantum :: Assertion
ownedGroundPublicationQuantum = do
    foundation <- expectRight Foundation.checkedFoundation
    proposition <- checked [] (p emptySet)
    truth <- checked [] CTruth
    let hypotheses = [proposition, proposition]
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    initial <- expectRight (Ground.trackRefutationCanonicalSources
        [Ground.RefutationCanonicalHypothesis 1]
        (Ground.startRefutation groundLimits emptyGlobalTyping context
            [Ground.RefutationHypothesis 0 proposition, Ground.RefutationHypothesis 1 proposition]
            proposition))
    let advance session = do
            progress <- lift (Scope.advanceOwnedGround session)
            remaining <- lift Scope.currentGroundLimits
            case progress of
                Ground.RefutationPending next -> do
                    unless (Ground.refutationRemainingWork (Ground.refutationSessionStatistics next)
                            == Ground.refutationWorkLimit remaining)
                        (boundaryFailure "a publication returned before committing its debit")
                    pure (remaining, next)
                _ -> boundaryFailure "a quantum passed the requested publication boundary"
        untilPublished published session = do
            (remaining, next) <- advance session
            if published next then pure (remaining, next) else untilPublished published next
        (result, _, _) = Scope.runScoped 1000000 (Ground.refutationConversionPool groundLimits)
            allowance context Map.empty \scope -> do
                (domainLimits, frozen) <- untilPublished
                    (isJust . Ground.refutationSessionDomain) initial
                _ <- groundProof scope [] [] truth
                afterOther <- lift Scope.currentGroundLimits
                (ordinaryLimits, ordinary) <- untilPublished
                    (isJust . Ground.refutationSessionAnyCandidate) frozen
                pure (domainLimits, frozen, afterOther, ordinaryLimits, ordinary)
    (domainLimits, frozen, afterOther, ordinaryLimits, ordinary) <- expectRight result
    let freeze limits session
            | isJust (Ground.refutationSessionDomain session) = pure (limits, session)
            | otherwise = case Ground.advanceRefutation limits session of
                (remaining, Ground.RefutationPending next) -> freeze remaining next
                _ -> assertFailure "reference failed before domain publication" >> fail "domain"
    (expectedLimits, expectedFrozen) <- freeze groundLimits initial
    assertEqual "domain publication yields before root admission" 0
        (Ground.refutationBranchNodes (Ground.refutationSessionStatistics frozen))
    assertEqual "the quantum stops at the first domain publication"
        (statisticsObservation (Ground.refutationSessionStatistics expectedFrozen))
        (statisticsObservation (Ground.refutationSessionStatistics frozen))
    assertBool "domain publication commits its actual allowance" (expectedLimits == domainLimits)
    assertBool "the intervening query spends the retained owner's allowance"
        (Ground.refutationWorkLimit afterOther < Ground.refutationWorkLimit domainLimits)
    (expectedOrdinaryLimits, _, expectedOrdinary) <- awaitOrdinaryGround afterOther expectedFrozen
    assertEqual "ordinary publication yields at the first certificate"
        (statisticsObservation (Ground.refutationSessionStatistics expectedOrdinary))
        (statisticsObservation (Ground.refutationSessionStatistics ordinary))
    assertBool "resumption uses the spent allowance, not the old session allowance"
        (expectedOrdinaryLimits == ordinaryLimits)
    candidate <- maybe (assertFailure "missing ordinary proof" >> fail "publication") pure
        (Ground.refutationSessionAnyCandidate ordinary)
    assertEqual "the first certificate does not pretend to satisfy canonical demand"
        Nothing (Ground.refutationCandidateCanonicalSource candidate)
    assertReplays foundation hypotheses [] proposition (Ground.refutationCandidateProof candidate)
        (Set.singleton (hypothesisIx 0))
    (_, _, canonicalResult) <- finishCanonicalQuery ordinaryLimits ordinary
    canonical <- expectRight canonicalResult
    assertReplays foundation hypotheses [] proposition (Ground.refutationCandidateProof canonical)
        (Set.singleton (hypothesisIx 1))

firstResidualUsesFrozenSeed :: Assertion
firstResidualUsesFrozenSeed = do
    foundation <- expectRight Foundation.checkedFoundation
    positive <- checked [] (p emptySet)
    negative <- checked [] (CNot (p emptySet))
    seed <- checked [] (CAnd (p emptySet) (q emptySet))
    outside <- checked [] (p (CApp (CApp (CIntrinsic OrderedPair) one) one))
    truth <- checked [] CTruth
    context <- expectRight (Proof.scopedProofContext foundation emptyGlobalTyping [] [positive, outside])
    let start inputs target = Ground.startRefutationFromSeed groundLimits emptyGlobalTyping context (seed :| []) inputs target
    (available, domain, familyStatistics) <- prepareFrozenFamily groundLimits (start [] positive)
    assertEqual "the first residual freezes before allocating any branch" 0
        (Ground.refutationBranchNodes familyStatistics)
    (_, missingStatistics, missing) <- finishFrozenQuery groundLimits (start [] positive)
    case missing of
        Left Ground.RefutationSaturated -> pure ()
        _ -> assertFailure "family syntax was asserted as evidence in its first query"
    (_, provedStatistics, proved) <- finishFrozenQuery groundLimits
        (start [Ground.RefutationHypothesis 0 positive] positive)
    candidate <- expectRight proved
    assertReplays foundation [positive, outside] [] positive
        (Ground.refutationCandidateProof candidate) (Set.singleton (hypothesisIx 0))
    assertEqual "asserted roots do not change seed admissions"
        (Ground.refutationTerms missingStatistics) (Ground.refutationTerms provedStatistics)
    (_, _, independent) <- finishFrozenQuery available
        (Ground.startRefutationInDomain available emptyGlobalTyping context domain [] negative)
    case independent of
        Left Ground.RefutationSaturated -> pure ()
        _ -> assertFailure "another query inherited the first query's positive target or negation"
    (_, truthStatistics, truthResult) <- finishFrozenQuery groundLimits (start [] truth)
    _ <- expectRight truthResult
    -- Truth may add its permitted proposition row. Rejected non-propositional
    -- syntax must not add anything beyond the family and the actual target.
    for_ [([], outside, Ground.refutationTerms familyStatistics)
         , ([Ground.RefutationHypothesis 1 outside], truth, Ground.refutationTerms truthStatistics)]
        \(inputs, target, admitted) -> do
        (_, statistics, rejected) <- finishFrozenQuery groundLimits (start inputs target)
        case rejected of
            Left Ground.RefutationUnsupportedTermOutsideUniverse -> pure ()
            _ -> assertFailure "the first query expanded its authorized seed with residual or fact syntax"
        assertEqual "rejected inputs cannot add non-propositional syntax"
            admitted (Ground.refutationTerms statistics)
        assertEqual "outside-domain rejection happens before query branch admission" 0
            (Ground.refutationBranchNodes statistics)

-- The fast lambda-telescope path must agree with pointwise beta opening,
-- including inner binders and non-lambda aliases that need the fallback.
predicateProjectionTargets :: Assertion
predicateProjectionTargets = do
    let ty = TyArrow TySet (TyArrow TySet TyProp)
        body = CAnd (CEq TySet (CBound 1) (CBound 0))
            (CForall TySet (CEq TySet (CBound 2) (CBound 0)))
        bodies :: [CanonicalTerm Int]
        bodies = [CLam TySet (CLam TySet body), CGlobal 1,
            CLam TySet (CApp (CGlobal 1) (CBound 0))]
        paths = [Elimination.ConjunctionHere,
            Elimination.ConjunctionLeft Elimination.ConjunctionHere,
            Elimination.ConjunctionRight Elimination.ConjunctionHere,
            Elimination.ConjunctionRight (Elimination.ConjunctionLeft Elimination.ConjunctionHere)]
    for_ bodies \definition -> for_ paths \path ->
        assertEqual "selected telescope target"
            (Elimination.definitionProjectionTarget path
                (canonicalDefinitionEquationTarget 0 ty definition))
            (Elimination.predicateProjectionTarget 0 ty definition path)
    Elimination.predicateProjectionTarget (0 :: Int) TySet (CGlobal 1)
        Elimination.ConjunctionHere @?= Nothing
    Elimination.predicateProjectionTarget (0 :: Int) (TyArrow TyProp TyProp)
        (CLam TyProp (CBound 0)) Elimination.ConjunctionHere @?= Nothing
