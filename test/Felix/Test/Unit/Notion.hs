{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

module Felix.Test.Unit.Notion (unitTests) where

import Base
import System.Environment qualified as Environment
import GHC.Clock qualified as Clock
import Felix.Checking.Notion.Catalog qualified as Catalog
import Felix.Checking.Notion.Projection qualified as Projection
import Felix.Checking.Notion.Introduction qualified as Introduction
import Felix.Checking.Notion.WholePattern qualified as WholePattern
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Notion.Goal qualified as Goal
import Felix.Checking.Notion.SuppliedUniversal qualified as SuppliedUniversal
import Felix.Checking.Notion.ScopedSource qualified as ScopedSource
import Felix.Checking.Notion.LeafIndex qualified as Leaves
import Control.Monad (filterM, foldM, replicateM_, unless, when)
import Data.Functor.Identity (runIdentity)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping qualified as GlobalTyping
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Kernel.Derivation qualified as Derivation
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.Composite qualified as Composite
import Felix.Checking.Notion.Support qualified as Support
import Felix.Checking.Notion.Relational qualified as Relational
import Felix.Checking.Notion.Pattern qualified as Pattern
import Felix.Checking.Notion.TermIndex qualified as Terms
import Felix.Checking.Notion.Request qualified as Request
import Felix.Checking.Notion.FormulaIndex qualified as Formulas
import Felix.Checking.Notion.Unification qualified as Unification
import Felix.Checking.Notion.Join qualified as Join
import Felix.Checking.Notion.Rule qualified as Rule
import Felix.Checking.Notion.Evaluation qualified as Evaluation
import Felix.Checking.Notion.Diagnostics qualified as Diagnostics
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Predicate qualified as Predicate
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Module
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Test.Support.Declarations qualified as DeclTest
import Felix.Test.Support.GlobalTyping
import Felix.Test.Support.FormationReference qualified as Reference
import Felix.Test.Support.FormationProduction qualified as Production
import Felix.Test.Support.FormationReferenceImports qualified as ReferenceImports
import Felix.Test.Support.FormationReferenceReplay qualified as ReferenceReplay

import Data.Bifunctor qualified as Bifunctor
import Data.Maybe (catMaybes)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Data.Word (Word)
import Hedgehog (Gen, Property, classify, evalEither, evalIO, evalMaybe, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog (testPropertyNamed)


unitTests :: TestTree
unitTests =
    testGroup "Notion"
        [ testCase "supplied universals adapt exact guards and results through scoped replay" suppliedUniversalReplay
        , testCase "finite Horn semantics uses exact truth and a fixed structural universe" finiteHornSemantics
        , testCase "finite query semantics preserves witnesses, alternatives and fixed equality" finiteQuerySemantics
        , testCase "finite support cursor agrees with exhaustive one-layer construction" finiteSupportCursor
        , testCase "whole premises wait for later atomic answers without binding parameters" wholeGroundSubscriptions
        , testCase "whole producer attempts count selections independently of continuation work" wholeProducerAccounting
        , testCase "whole classifications use collectively determined relational premises" wholeCoveringActivation
        , testCase "whole closure agrees with independent exhaustive rounds" wholeReferenceAgreement
        , testCase "prepared operand comparisons agree with direct comparisons under binders" preparedOperandComparisons
        , testCase "paired notion leaves preserve atoms and residuals with shared paths" pairedNotionLeaves
        , testCase "arena accounting retains allocated nodes on exhaustion" countsArenaAllocations
        , testCase "witness arenas prune alternatives and share diamonds through replay" diamondArenaReplay
        , testCase "shared projection prefixes stay linear through fresh kernel replay" sharedProjectionReplay
        , testCase "whole head inputs retain exact values without decomposing operands" wholeHeadInputs
        , testCase "whole roots retain independent inputs and only written argument views" wholeRootInputs
        , testCase "whole support shares one frozen layer across opaque and written templates" wholeTemplateSupport
        , testCase "quantified projections share guard and proof prefixes" projectionPrefixSharing
        , testCase "introduction recipes discharge fresh binders and local assumptions" scopedIntroductionReplay
        , testCase "simple registered implications avoid population-wide preparation" seedRuleLocality
        , testCase "closed schema values retain scope and atomic support without source identity" closedSchemaValues
        , testCase "nested guarded registrations retain phase-neutral accounting" nestedGuardedFormation
        , testCase "incompatible producers still contribute to the fixed reference domain" incompatibleProducerSupport
        , testCase "fresh support queries reuse prepared catalogue descriptions with measured headroom"
            preparedCatalogueLocality
        , testCase "whole-head lookup ignores unrelated formula size" wholeHeadLocality
        , testCase "whole producers do not rebuild dormant atomic closures" wholeFrontierLocality
        , testCase "tabled producers and forward views yield founded answers before later alternatives"
            demandSelectiveAlternatives
        , testCase "ground equality endpoint discovery retains subject transport and scope" equalityEndpointDiscovery
        , testCase "ground requests avoid unrelated same-head answers" fineGroundBuckets
        , testCase "partial requests use bound argument postings" partialArgumentBuckets
        , testCase "equality class lookup avoids equivalent argument products" equalityArgumentLocality
        , testCase "ground instances retain one immutable founded proof" groundActivationAlternatives
        , testCase "duplicate proofs keep saturated misses inexpensive" calibratedFailureAllowance
        , testCase "ground conjunctions do not enumerate premise subsets" groundedJoinLocality
        , testCase "a suspended join mode can discover an anchor needed by a ground guard" deferredJoinAnchors
        , testCase "determined rules precede population-wide parameter discovery" determinedProducerLocality
        , testCase "scoped producers keep captures fixed during quantified discovery" scopedProducerInputs
        , testCase "scoped support fixes captured terms without reseeding derived terms" scopedTemplateSupport
        , testCase "source rows prioritize anchored discovery without supplying missing guards" anchoredProducerLocality
        , testCase "specific nested results precede generic wrapper results" nestedProducerLocality
        , testCase "partial producer selection retains constructor-headed and correlated answers"
            partialProducerSelection
        , testCase "rigid catalog lookup traverses terms only for the requested head" catalogHeadLocality
        , testCase "record-result discovery indexes the written provider" catalogProviderLocality
        , testCase "body-only components retain one witness across many callers" componentWitnessSharing
        , testCase "group roots fix one domain independently of order or direct discharge" ruleGroupDomain
        , testCase "resumes bounded table work and externally supplied proofs" relationalResumption
        , testCase "delivers root evidence before exploring unrelated producers" relationalRootCompletion
        , testCase "delivers causal evidence before expensive sibling witnesses" relationalCausalDelivery
        , testCase "new demands precede alternate witnesses without losing later answers" relationalWitnessDemand
        , testCase "leaf lookup cost is independent of constructor population" leafIndexScaling
        , testCase "replays exact denotation answers with bounded evidence costs" replaysFormationConversion
        , testCase "keeps denotation answers separate from source rows" referenceDenotationAnswers
        , testCase "forward definitions expand observed and derived source rows" productionForwardViews
        , testCase "initial root evidence stops before unrelated forward closure" initialRootCompletion
        , testCase "initial goal ancestors precede lower-ranked unrelated views" initialAncestorPriority
        , testCase "ground initial rows need no second request admission" initialRowsAdmission
        , testCase "rule snapshots select relevance and reject only definition cycles" productionRuleSnapshot
        , testCase "registration reuse preserves snapshots and removes repeated graph preparation" registryReuseScaling
        , testCase "initial views seed support without allowing derived reseeding" productionInitialEvidence
        , testCase "instantiates atomic templates without erasing shape"
            instantiatesAtomicTemplateShape
        , testCase "preserves canonical atom and source metadata ordering" preservesSourceAtomOrdering
        , testCase "constructs binary membership atoms by invariant"
            constructsBinaryMembershipAtoms
        , testCase "rejects rich shapes with mismatched logical evidence"
            rejectsMismatchedRichGoalEvidence
        , testCase "retains selected materialized hypothesis origins"
            retainsMaterializedHypothesisOrigins
        , testCase "transports checked notion evidence through equality"
            transportsCheckedNotionEvidence
        , testCase "retains direct priority and first-founded composite witnesses"
            retainsFoundedWitnesses
        , testCase "bounds complete equality-transport chains"
            boundsEqualityTransportChains
        , testCase "materializes and replays growing directed transport chains"
            replaysGrowingEqualityTransportChains
        , testCase "replays a backward rule with conjunctive premises under its consumer"
            replaysBackwardFormationRule
        , testCase "preserves source providers through Core transformations"
            preservesSourceProvidersThroughCoreTransformations
        , testCase "replaces source aliases without erasing written providers" replacesScopedSourceAliases
        , testCase "constructs only exact intrinsic source providers"
            constructsExactIntrinsicSourceProviders
        , testPropertyNamed
            "finite-set source providers obey their representation law"
            "prop_finiteSetLiteralProviderRepresentation"
            prop_finiteSetLiteralProviderRepresentation
        , testCase "preserves nested finite-set providers through Core transformations"
            preservesNestedFiniteSetProviders
        , testCase "source sealing checks discarded globals in its own snapshot"
            sealsSourceGlobalsInOwnSnapshot
        , testCase "reference determination is independent of premise order"
            referenceDeterminationPermutations
        , testCase "reference answer indexing preserves distinct support summaries"
            indexesReferenceAnswers
        , testCase "reference term sets charge deep ordering and preserve canonical sets"
            countsReferenceTermSets
        , testCase "reference support admits one frozen template layer"
            referenceFrozenSupport
        , testPropertyNamed "symbolic support agrees with explicit template enumeration"
            "prop_symbolicSupport" prop_symbolicSupport
        , testPropertyNamed "prepared catalogue seeds and support agree with the independent closure"
            "prop_preparedCatalogSupport" prop_preparedCatalogSupport
        , testCase "symbolic support does not enumerate substitutions or reseed queries"
            symbolicSupportAvoidsEnumeration
        , testCase "partial requests exclude shapes with no frozen ground completion"
            partialSupportFeasibility
        , testCase "prepared support profiles retain exact closed and repeated-variable maxima"
            preparedSupportProfiles
        , testCase "formation patterns preserve repeated outputs and classify support boundaries"
            formationPatternBoundaries
        , testCase "request IDs preserve pins, heads, and output correlations"
            formationRequestIdentity
        , testCase "formation unification preserves complete rows and shared constraints"
            formationUnificationBoundaries
        , testCase "joins preserve premise-order independence and checked row capability"
            formationAnchoredJoins
        , testCase "rule completion retains every premise and independently replays"
            formationRuleCompletion
        , testCase "reference requests derived rows without guessing their outputs"
            referenceDerivedRows
        , testCase "reference joins retain correlations in every premise order"
            referenceCorrelatedJoins
        , testPropertyNamed "reference relational joins agree with generated finite closure"
            "prop_referenceRelationalClosure" prop_referenceRelationalClosure
        , testCase "relational tables match and deliver once in either arrival order"
            relationalSchedulerDeliversOnce
        , testCase "reference terminates growing and cyclic partial requests"
            referenceFiniteRequests
        , testCase "reference retains founded witnesses with distinct eligibility"
            referenceWitnessAlternatives
        , testCase "reference freezes canonical support before classification search"
            referenceCanonicalSnapshot
        , testCase "reference relevance includes every producer of a reached head"
            referenceMembershipHeadClosure
        , testCase "reference rejects cyclic and undetermined definition views"
            referenceDefinitionSnapshotBoundaries
        , testCase "rejects malformed rich rule provider applications"
            rejectsMalformedRuleProviderApplications
        , testCase "preserves ordered pairs through Core transformations"
            preservesOrderedPairsThroughCoreTransformations
        , testCase "substitutes complete source-term occurrences"
            substitutesCompleteSourceTermOccurrences
        , testCase "queries source-terminal evidence directly"
            queriesSourceTerminalEvidenceDirectly
        , testCase "selects duplicate direct witnesses by ordinal"
            selectsDuplicateDirectWitnessesByOrdinal
        , testCase "rejects a mismatched registered theorem"
            rejectsMismatchedTheorem
        , testCase "rejects sparse view variables without range allocation"
            rejectsSparseViewVariables
        , testCase "validates provider-result rule invariants"
            validatesProviderResultRuleInvariants
        , testCase "rejects source-terminal nullary classifications"
            rejectsSourceTerminalNullaryClassifications
        , testCase "shares one budget across provider and unary search"
            sharesProviderSearchBudget
        , testCase "charges cached source-index work to every query budget"
            chargesSourceIndexWork
        ]

-- Synthetic row owners exercise scheduler semantics here. The three module
-- consumer chains separately compile these recipes and replay them in the kernel.
finiteHornSemantics :: Assertion
finiteHornSemantics = do
    fixture <- makeFixture 3
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        atom :: Natural -> term -> Semantic.NotionLeaf (Semantic.AtomTemplate term) whole
        atom index term = Semantic.AtomicLeaf (row index term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        pair left right = Semantic.TemplateOrderedPair left right
        denote = \case
            Semantic.TemplateVariable (Reference.OpaqueSeed index) -> Core.CBound index
            Semantic.TemplateOrderedPair left right ->
                Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (denote left)) (denote right)
            _ -> error "unexpected finite Horn fixture term"
        atomFormula assertion = case assertion of
            Semantic.StructureAtomTemplate head' arguments ->
                let ordinal = fromMaybe (error "unknown Horn fixture head")
                        (List.elemIndex head' [fixtureHead fixture i | i <- [0..2]])
                in Core.CEq Core.TySet (Core.COpaqueInteger (fromIntegral ordinal)) (denote (Vector.head arguments))
            _ -> error "unexpected finite Horn fixture atom"
        residual = Semantic.WholeLeaf . Semantic.ResidualTemplate
        rule = Reference.ReferenceWholeRule
        whole = Core.CExists Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1))
        run domain rules facts = expectRight (fst (Reference.runReference 1000000
            (Reference.evaluateFiniteHorn domain denote atomFormula rules facts)))
    -- Collective binding has no distinguished row or shared subject. Exact
    -- whole evidence can discharge an atomic premise without furnishing a view.
    joined <- run [a,b]
        [rule 2 [atom 0 x,atom 1 y] (residual whole)]
        [(atom 0 a,False),(Semantic.WholeLeaf (atomFormula (row 1 b)),False)]
    assertBool "collectively determined opaque conclusion" (Set.member (Semantic.WholeLeaf whole,False) joined)
    -- A query-independent producer supplies a premise for a disconnected rule.
    generated <- run [a,b]
        [rule 1 [] (atom 0 x),rule 1 [atom 0 x] (atom 2 (Semantic.TemplateClosed (closedFixtureValue (Core.COpaqueInteger 7))))]
        []
    assertBool "free parameters range over all of U" (Set.member (atom 0 b,True) generated)
    assertBool "relational operands outside U reject the instance"
        (all (\case (Semantic.AtomicLeaf r,_) -> r /= row 2 (Semantic.TemplateClosed (closedFixtureValue (Core.COpaqueInteger 7))); _ -> True)
            (Set.toList generated))
    bounded <- run [a,b,pair a a]
        [rule 1 [atom 0 x] (atom 0 (pair x x))] [(atom 0 a,True)]
    assertBool "one template layer can derive a represented term" (Set.member (atom 0 (pair a a),True) bounded)
    assertBool "derived terms do not reseed the universe" (not (Set.member (atom 0 (pair (pair a a) (pair a a)),True) bounded))
    cyclic <- run [a] [rule 1 [atom 0 x] (atom 1 x),rule 1 [atom 1 x] (atom 0 x)] []
    cyclic @?= Set.empty

finiteQuerySemantics :: Assertion
finiteQuerySemantics = do
    fixture <- makeFixture 3
    let row :: Natural -> Semantic.SetTermTemplate variable -> Reference.FiniteFormula variable
        row index term = Reference.FiniteAtom (Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term))
        a = referenceSeed 0
        b = referenceSeed 1
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        f value = Semantic.TemplateOrderedPair value value
        run domain equations clauses facts goals = expectRight (fst (Reference.runReference 1000000
            (Reference.evaluateFiniteQueries domain equations clauses facts goals)))
        exists :: Reference.FiniteFormula (Maybe variable) -> Reference.FiniteFormula variable
        exists = Reference.FiniteExists
        bound :: Semantic.SetTermTemplate (Maybe variable)
        bound = Semantic.TemplateVariable Nothing
        nested = exists (exists (Reference.FiniteAnd
            (row 0 (Semantic.TemplateVariable (Just Nothing)))
            (Reference.FiniteEquality bound (f (Semantic.TemplateVariable (Just Nothing))))))
    run [a,f a] [] [] [row 0 a] [nested] >>= (@?= [True])
    run [a] [] [] [row 0 a] [nested] >>= (@?= [False])
    run [] [] [] [] [exists Reference.FiniteTruth] >>= (@?= [False])
    run [a] [] [] [] [exists Reference.FiniteTruth] >>= (@?= [True])
    let disjunctive = Reference.FiniteClause 1
            [Reference.FiniteOr (row 0 x) (row 1 x)] (row 2 x)
    run [a,b] [] [disjunctive] [row 0 a,row 1 b] [row 2 a,row 2 b] >>= (@?= [True,True])
    run [a,b] [(a,b)] [] [row 0 (f a)] [row 0 (f b)] >>= (@?= [False])
    run [a,b,f a,f b] [(a,b)]
        [Reference.FiniteClause 1 [row 0 x] (row 1 (f x))]
        [row 0 a] [row 1 (f b)] >>= (@?= [True])
    let y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
    run [a,b] [] [Reference.FiniteClause 2 [row 0 x,row 1 y] (Reference.FiniteEquality x y)]
        [row 0 a,row 1 b] [Reference.FiniteEquality a b,row 0 b] >>= (@?= [True,False])
    run [a] [] [] [Reference.FiniteIff (row 0 a) (row 1 a)] [row 1 a] >>= (@?= [False])
    run [a] [] [] [Reference.FiniteIff (row 0 a) (row 1 a),row 0 a] [row 1 a] >>= (@?= [True])
    run [a] [] [] [exists (row 0 bound)] [row 0 a] >>= (@?= [False])

finiteSupportCursor :: Assertion
finiteSupportCursor = do
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        empty = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        templates = [power x,Semantic.TemplateOrderedPair x x,Semantic.TemplateOrderedPair x y,empty]
        charge = Reference.chargeReferenceWork . fromIntegral
        collect found cursor = Support.nextSupportTerm charge cursor >>= \case
            Nothing -> pure found
            Just (candidate,next) -> collect (maybe found (`Set.insert` found) candidate) next
        enumerate seeds allowance = Reference.runReference allowance do
            support <- Support.buildSymbolicSupport charge seeds templates
            collect Set.empty (Support.supportCursor support)
    for_ [[],[referenceSeed 0,referenceSeed 1]] \seeds -> do
        expected <- expectRight (fst (Reference.enumerateSupport 100000 (Set.fromList seeds) (Set.fromList templates)))
        let measured@(result,work) = enumerate seeds 100000
        result @?= Right (Reference.referenceUniverse expected)
        enumerate seeds work @?= measured
        fst (enumerate seeds (work-1)) @?= Left Reference.ReferenceWorkExhausted
    let selected size = do
            (prepared,profile) <- expectRight (fst (Reference.runReference 10000000 do
                unrelated <- foldM (\known owner -> fst <$> Support.extendOwnedTemplateSupport charge owner
                    [Semantic.TemplateClosed (closedFixtureValue (Core.COpaqueInteger (fromIntegral owner)))] known)
                    Support.emptyTemplateSupport [1..size]
                Support.extendOwnedTemplateSupport charge 0 templates unrelated))
            let result = Reference.runReference 100000 do
                    support <- Support.freezeSelectedSupport charge [referenceSeed 0]
                        (Support.selectTemplateSupport prepared (Set.singleton 0) profile)
                    collect Set.empty (Support.supportCursor support)
            _ <- expectRight (fst result)
            pure result
    small <- selected 32
    large <- selected 512
    fst small @?= fst large
    assertBool "finite enumeration visits selected owners, with only index-depth growth"
        (snd large < 2 * snd small)
    let filtered size = do
            let seeds = [referenceSeed i | i <- [0..size-1]]
                target = Semantic.TemplateOrderedPair
                    (Semantic.TemplateVariable (Pattern.Pinned (Reference.OpaqueSeed 0)))
                    (Semantic.TemplateVariable (Pattern.Output 0))
                collectMatching found cursor = Support.nextMatchingSupportTerm Nothing charge
                    (Just (Unification.mayUnifyPartialTerm charge target)) cursor >>= \case
                        Nothing -> pure found
                        Just (candidate,next) -> collectMatching (maybe found (`Set.insert` found) candidate) next
                measured = Reference.runReference 1000000 do
                    support <- Support.buildSymbolicSupport charge seeds [Semantic.TemplateOrderedPair x y]
                    collectMatching Set.empty (Support.supportCursor support)
            fst measured @?= Right (Set.fromList [Semantic.TemplateOrderedPair (referenceSeed 0) seed | seed <- seeds])
            pure (snd measured)
    eight <- filtered 8
    sixteen <- filtered 16
    assertBool "a pinned operand prunes assignments before their Cartesian suffix"
        (sixteen < 3 * eight)

preparedOperandComparisons :: Assertion
preparedOperandComparisons = do
    let slot = Core.CBound 3
        a = Core.CBound 0
        b = Core.CBound 1
        hole = Core.CBound 2
        pair x y = Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) x) y
        equals = Core.CEq Core.TySet
        cases =
            [ (equals (pair slot slot) a, equals (pair a b) a)
            , (equals (pair slot b) a, equals (pair a b) a)
            , (equals (pair slot b) a, equals hole b)
            , (equals a b, equals a b)
            , (Core.CForall Core.TySet (equals (Core.CBound 4) (Core.CBound 0)),
               Core.CForall Core.TySet (equals (Core.CBound 1) (Core.CBound 0)))
            , (Core.CForall Core.TySet (equals (Core.CBound 4) (Core.CBound 0)),
               Core.CForall Core.TySet (equals (Core.CBound 0) (Core.CBound 0)))
            ]
    forM_ cases \(template,target) -> do
        prepared <- WholePattern.prepareOperandComparison (const (pure ())) 2 3 template target
        forM_ [a,b,hole,pair a hole] \candidate -> do
            actual <- Core.instantiateCanonicalPrefixWith (pure ()) 4
                (\depth index -> pure (Core.shiftCanonical depth 0 (if index == 3 then candidate else Core.CBound index)))
                0 template
            expected <- WholePattern.mayEqualOperands (const (pure ())) 2 actual target
            result <- prepared (pure candidate)
            assertEqual "prepared comparison preserves the conservative filter" expected result

wholeReferenceAgreement :: Assertion
wholeReferenceAgreement = do
    fixture <- makeFixture 7
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        atomicLeaf :: Natural -> term -> Semantic.NotionLeaf (Semantic.AtomTemplate term) whole
        atomicLeaf index term = Semantic.AtomicLeaf (row index term)
        member a b = Semantic.AtomicLeaf (Semantic.MembershipAtomTemplate a b)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        value = Semantic.TemplateVariable (Reference.OpaqueSeed 0)
        second = Semantic.TemplateVariable (Reference.OpaqueSeed 1)
        opaque = Semantic.TemplateVariable (Reference.OpaqueSeed 10)
        pair = Semantic.TemplateOrderedPair
        aliasPair term = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "whole-alias" 0)) (Vector.fromList [term,term])
        aliasIdentity term = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "whole-alias" 1)) (Vector.fromList [term,term])
        aliasErase a b = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "whole-alias" 1)) (Vector.fromList [a,b])
        seeds = [value,second,opaque]
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        formula = Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)
        universal = Core.CForall Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1))
        adapterTarget = Core.CForall Core.TySet (Core.CAnd
            (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1))
            (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1)))
        whole = Semantic.WholeLeaf . Semantic.ResidualTemplate
        rule = Reference.ReferenceWholeRule
        source = [(atomicLeaf 0 value, True)]
        covering = [rule 1 [atomicLeaf 0 x, atomicLeaf 1 x] (whole formula)]
        derived = [rule 1 [atomicLeaf 0 x] (atomicLeaf 1 x), rule 1 [atomicLeaf 1 x] (whole formula)]
        late = [rule 1 [whole universal, atomicLeaf 0 x] (atomicLeaf 2 x), rule 1 [atomicLeaf 0 x] (whole universal)]
        adapters = [(universal, adapterTarget)]
        consumer = rule 1 [whole adapterTarget, atomicLeaf 0 x] (atomicLeaf 2 x)
        closed = Core.CNot Core.CFalsum
        negative index term = Semantic.AtomicLeaf (Semantic.withAtomPolarity Semantic.NegativePolarity (row index term))
        guardFormula = Core.CEq Core.TySet (Core.CIntrinsic Core.Empty) (Core.CIntrinsic Core.Empty)
        cases =
            [ ("opaque head still admits finite constructor instances", [rule 1 [atomicLeaf 0 x] (atomicLeaf 2 (pair x x))],
                source, [], atomicLeaf 2 opaque, True)
            , ("complete operands preserve a shared parameter through an opaque head",
                [rule 1 [atomicLeaf 0 x] (member (pair x x) x)], source, [], member opaque value, True)
            , ("inconsistent opaque and complete operands cannot choose independent parameters",
                [rule 1 [atomicLeaf 0 x] (member (pair x x) x)], source, [], member opaque second, False)
            , ("different rich heads can have the same exact value", [rule 1 [atomicLeaf 0 x] (atomicLeaf 2 (aliasPair x))],
                source, [], atomicLeaf 2 (pair value value), True)
            , ("a partial demand discovers a different rich head",
                [rule 1 [atomicLeaf 0 x] (atomicLeaf 1 (aliasPair x)),rule 2 [atomicLeaf 1 (pair y y)] (atomicLeaf 2 x)],
                source, [], atomicLeaf 2 value, True)
            , ("an alternate rich head still needs its guard",
                [rule 1 [atomicLeaf 0 x] (atomicLeaf 1 (aliasPair x)),rule 2 [atomicLeaf 1 (pair y y)] (atomicLeaf 2 x)],
                [], [], atomicLeaf 2 value, False)
            , ("a provider can denote a rigid bound value", [rule 1 [atomicLeaf 0 x] (atomicLeaf 2 (aliasIdentity x))],
                source, [], atomicLeaf 2 value, True)
            , ("matching provider heads may erase different arguments",
                [rule 2 [atomicLeaf 0 x,atomicLeaf 1 y] (atomicLeaf 2 (aliasErase x y))],
                source <> [(atomicLeaf 1 second,True)], [], atomicLeaf 2 (aliasErase value value), True)
            , ("a matching premise view cannot fix an erased body-only argument",
                [rule 2 [atomicLeaf 0 (aliasErase x y),whole (atomicLeafFormula (row 1 second))] (atomicLeaf 2 x)],
                [(atomicLeaf 0 (aliasErase value value),True),(atomicLeaf 1 second,True)],
                [], atomicLeaf 2 value, True)
            , ("different atomic heads retain the same exact truth",
                [rule 1 [atomicLeaf 1 x] (atomicLeaf 0 x)],
                [(atomicLeaf 1 value,True)], [], atomicLeaf 3 value, True)
            , ("supplied atomic heads retain the same exact truth", [],
                [(atomicLeaf 0 value,True)], [], atomicLeaf 3 value, True)
            , ("partial demands discover equal-Core supplied atoms",
                [rule 2 [atomicLeaf 3 y] (atomicLeaf 2 x)],
                [(atomicLeaf 0 second,True)], [], atomicLeaf 2 value, True)
            , ("partial demands discover equal-Core derived atoms",
                [rule 1 [atomicLeaf 1 x] (atomicLeaf 0 x),
                 rule 2 [atomicLeaf 3 y] (atomicLeaf 2 x)],
                [(atomicLeaf 1 second,True)], [], atomicLeaf 2 value, True)
            , ("equal truth need not identify different heads' complete operands",
                [rule 1 [atomicLeaf 1 x] (atomicLeaf 4 x)],
                [(atomicLeaf 1 value,True)], [], atomicLeaf 0 opaque, True)
            , ("erased head operands cannot constrain a peer's clause inputs",
                [rule 1 [atomicLeaf 1 x] (atomicLeaf 5 x)],
                [(atomicLeaf 1 second,True)], [], atomicLeaf 6 value, True)
            , ("equal-Core atomic cycles still need a founded source",
                [rule 1 [atomicLeaf 0 x] (atomicLeaf 3 x),rule 1 [atomicLeaf 3 x] (atomicLeaf 0 x)],
                [], [], atomicLeaf 0 value, False)
            , ("a faithful head keeps its inputs while a premise uses another view",
                [rule 1 [atomicLeaf 0 (pair x x)] (atomicLeaf 2 x)],
                [(atomicLeaf 0 opaque,True)], [], atomicLeaf 2 value,True)
            , ("partial whole-only inputs retain their product shape",
                [rule 1 [whole formula] (atomicLeaf 1 x),rule 2 [atomicLeaf 1 (pair x y)] (atomicLeaf 2 x)],
                [(Semantic.WholeLeaf (Core.CEq Core.TySet
                    (Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (Core.CBound 0)) (Core.CBound 1))
                    (Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (Core.CBound 0)) (Core.CBound 1))),False)],
                [], atomicLeaf 2 value,True)
            , ("opaque premise triggers finite discovery", [rule 2 [atomicLeaf 0 (pair y y)] (atomicLeaf 2 x)],
                [(atomicLeaf 0 opaque,True)], [], atomicLeaf 2 value,True)
            , ("exact-only body rows trigger finite discovery", [rule 2 [atomicLeaf 0 y] (atomicLeaf 2 x)],
                [(atomicLeaf 0 second,False)], [], atomicLeaf 2 value,True)
            , ("first covering source", covering, [(atomicLeaf 0 value,True),(atomicLeaf 1 value,False)], [], Semantic.WholeLeaf formula, True)
            , ("second covering source", covering, [(atomicLeaf 0 value,False),(atomicLeaf 1 value,True)], [], Semantic.WholeLeaf formula, True)
            , ("exact rows discharge ground instances", covering, [(atomicLeaf 0 value,False),(atomicLeaf 1 value,False)], [], Semantic.WholeLeaf formula, True)
            , ("whole demand discovers derived relational premises", derived, source, [], Semantic.WholeLeaf formula, True)
            , ("derived source row", rule 1 [atomicLeaf 1 x, whole formula] (atomicLeaf 2 x):derived, source, [], atomicLeaf 2 value, True)
            , ("late derived universal", late, source, [], atomicLeaf 2 value, True)
            , ("missing whole producer", take 1 late, source, [], atomicLeaf 2 value, False)
            , ("whole cycle", [rule 1 [atomicLeaf 0 x, whole formula] (whole formula)], source, [], Semantic.WholeLeaf formula, False)
            , ("closed producer", [rule 0 [] (whole closed)], [], [], Semantic.WholeLeaf closed, True)
            , ("whole head parameter without a body row", [rule 1 [] (whole formula)], [], [], Semantic.WholeLeaf formula, True)
            , ("negative body rows bind body-only variables", [rule 2 [negative 0 y] (atomicLeaf 2 x)],
                [(negative 0 second,True)], [], atomicLeaf 2 value,True)
            , ("positive evidence cannot discharge a negative premise", [rule 2 [negative 0 y] (atomicLeaf 2 x)],
                [(atomicLeaf 0 second,True)], [], atomicLeaf 2 value,False)
            , ("checked negative conclusions compose", [rule 1 [atomicLeaf 0 x] (negative 1 x),rule 1 [negative 1 x] (atomicLeaf 2 x)],
                source, [], atomicLeaf 2 value,True)
            , ("closed guarded producer", [rule 0 [whole guardFormula] (whole closed)], [], [], Semantic.WholeLeaf closed, False)
            , ("closed guard supplied", [rule 0 [whole guardFormula] (whole closed)], [(Semantic.WholeLeaf guardFormula,False)], [], Semantic.WholeLeaf closed, True)
            , ("supplied universal adapter", [consumer], (Semantic.WholeLeaf universal,False):source, adapters, atomicLeaf 2 value, True)
            , ("derived universal cannot adapt", [consumer,rule 1 [atomicLeaf 0 x] (whole universal)], source, adapters, atomicLeaf 2 value, False)
            , ("whole truth discharges an atomic premise", [rule 1 [atomicLeaf 1 x] (atomicLeaf 2 x)],
                [(Semantic.WholeLeaf (atomicLeafFormula (row 1 value)),False)], [], atomicLeaf 2 value, True)
            , ("whole truth discharges an atomic root", [],
                [(Semantic.WholeLeaf (atomicLeafFormula (row 1 value)),False)], [], atomicLeaf 1 value, True)
            , ("atomic producer discharges a whole root", [rule 1 [atomicLeaf 0 x] (atomicLeaf 1 x)], source,
                [], Semantic.WholeLeaf (atomicLeafFormula (row 1 value)), True)
            , ("whole producer discharges an atomic root", [rule 1 [atomicLeaf 0 x] (whole (atomicLeafFormula (row 1 value)))], source,
                [], atomicLeaf 1 value, True)
            , ("a whole premise preserves body-variable correlation",
                [rule 2 [atomicLeaf 0 x, atomicLeaf 1 y, whole (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1))] (atomicLeaf 2 x)],
                [(atomicLeaf 0 value,True),(atomicLeaf 1 value,True),(atomicLeaf 1 second,True),
                 (Semantic.WholeLeaf (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1)),False)], [], atomicLeaf 2 value,True)
            , ("a body-only whole guard retains sparse formal slots",
                [rule 2 [atomicLeaf 0 x, atomicLeaf 1 y, whole (Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 1))] (atomicLeaf 2 x)],
                [(atomicLeaf 0 value,True),(atomicLeaf 1 second,True),(Semantic.WholeLeaf formula,False)], [], atomicLeaf 2 value,False)
            ]
        denote = \case
            Semantic.TemplateVariable (Reference.OpaqueSeed 10) -> denote (pair value value)
            Semantic.TemplateVariable (Reference.OpaqueSeed index) -> Core.CBound index
            Semantic.TemplateOrderedPair a b -> Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (denote a)) (denote b)
            Semantic.TemplateProvider provider arguments
                | provider == Semantic.GlobalSourceProvider (binaryProviderReference "whole-alias" 0) ->
                    denote (pair (Vector.head arguments) (Vector.last arguments))
                | provider == Semantic.GlobalSourceProvider (binaryProviderReference "whole-alias" 1) -> denote (Vector.head arguments)
            _ -> error "whole reference fixture acquired an unsupported term"
        atomicLeafFormula assertion = case assertion of
            Semantic.NegativeAtomTemplate body -> Core.CNot (atomicLeafFormula body)
            Semantic.MembershipAtomTemplate element set ->
                Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) (denote element)) (denote set)
            Semantic.StructureAtomTemplate head' arguments ->
                let ordinal = fromMaybe (error "unknown fixture head") (List.elemIndex head' [fixtureHead fixture i | i <- [0..6]])
                    argument = Vector.head arguments
                in case ordinal of
                    1 -> Core.CNot (Core.CEq Core.TySet (Core.COpaqueInteger 1) (denote argument))
                    2 -> Core.CNot (Core.CNot (Core.CEq Core.TySet (Core.COpaqueInteger 2) (denote argument)))
                    4 -> Core.CEq Core.TySet (Core.COpaqueInteger 0) (denote (pair argument argument))
                    5 -> Core.CEq Core.TySet (Core.COpaqueInteger 0) (Core.COpaqueInteger 7)
                    6 -> Core.CEq Core.TySet (Core.COpaqueInteger 0) (Core.COpaqueInteger 7)
                    _ -> Core.CEq Core.TySet (Core.COpaqueInteger (if ordinal == 3 then 0 else fromIntegral ordinal)) (denote argument)
            _ -> error "whole reference fixture acquired another atomicLeaf family"
        typing = fixtureGlobalTyping (globalTypingFixture [])
        context = [Core.TySet,Core.TySet]
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        intern term = do
            checked <- either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
                (Core.checkScopedCanonicalCore typing context term)
            table <- State.get
            (identifier, next) <- either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
                (fst (Formulas.internFormula 100000 checked table))
            State.put next
            pure identifier
        leafId = \case
            Semantic.AtomicLeaf assertion -> pure (Semantic.AtomicLeaf assertion)
            Semantic.WholeLeaf term -> Semantic.WholeLeaf <$> intern term
        runProduction = runScopedProduction Rule.OpenRuleInputs
        runScopedProduction inputs useInputs eliminate introduce rules facts eligible target = State.evalStateT (do
            compiled <- for rules \(Reference.ReferenceWholeRule arity premises conclusion) -> do
                let body = fmap (\case Semantic.AtomicLeaf a -> Semantic.RulePremiseAtom a
                                       Semantic.WholeLeaf w -> Semantic.RulePremiseResidual w) premises
                compiled <- Rule.RegisteredClassification <$> admit (case (inputs,conclusion) of
                    (Rule.ScopedRuleInputs captures, Semantic.AtomicLeaf assertion) ->
                        Rule.compileScopedRule charge arity (Map.keysSet captures) body assertion
                    _ -> Rule.compileConclusionRule charge arity body conclusion)
                let checked = \case
                        Semantic.AtomicLeaf atom -> atomicLeafFormula (fmap (\(Semantic.ViewVariableIx i) ->
                            Reference.OpaqueSeed i) <$> atom)
                        Semantic.WholeLeaf (Semantic.ResidualTemplate formula') -> formula'
                let contextual leaf = (replicate (fromIntegral arity) Core.TySet,checked leaf)
                admit (Rule.describeRuleFormulas charge (contextual <$> premises) (contextual conclusion) compiled)
            projections <- if not eliminate then pure [] else fmap concat $ for compiled \entry -> do
                generated <- admit (Projection.compileWholeEliminations charge (Rule.registeredRule entry))
                pure [Rule.RegisteredClassification derivedRule | (_,_,derivedRule) <- generated]
            introductions <- if not introduce then pure [] else fmap concat $ for compiled \entry -> do
                generated <- admit (Introduction.compileIntroductions charge (Rule.registeredRule entry))
                pure (Rule.RegisteredClassification . Introduction.introductionRule <$> generated)
            catalog <- Catalog.insertRules charge (zip [0 :: Natural ..] (compiled <> projections <> introductions)) Catalog.emptyCatalog
            initial <- for (zip [0 :: Natural ..] facts) \(ordinal, (leaf, capable)) -> do
                identified <- leafId leaf
                pure (Evaluation.RuleAnswer identified (1000+ordinal, identified)
                    (if capable then Join.SourceRow else Join.ExactAnswer) ())
            adapted <- traverse (intern . snd) [pair | pair@(supplied, _) <- eligible
                , (Semantic.WholeLeaf supplied, False) `elem` facts]
            sourceFormulas <- traverse (intern . \case
                Semantic.AtomicLeaf atom -> atomicLeafFormula atom
                Semantic.WholeLeaf formula' -> formula') (fst <$> facts)
            sourceShapes <- for facts \(leaf,capable) -> do
                let (formula', view) = case leaf of
                        Semantic.AtomicLeaf atom -> (atomicLeafFormula atom, if capable then Just (Rule.atomSignature atom) else Nothing)
                        Semantic.WholeLeaf formula' -> (formula',Nothing)
                shape <- Formulas.residualShape (charge 1) context formula'
                pure (shape,view)
            let supplied signature shape = pure (any (\(candidate,view) -> candidate == shape && view /= Just signature) sourceShapes)
            let owner = Evaluation.RuleEvaluator (const (pure inputs)) charge (intern . atomicLeafFormula)
                    (const (pure ())) (const (pure ()))
                    (\ordinal _ leaf -> pure (Just ((ordinal, leaf), ())))
                    (\requested answer -> do
                        expected <- intern (atomicLeafFormula requested)
                        actual <- case Evaluation.ruleAnswerLeaf answer of
                            Semantic.WholeLeaf identifier -> pure identifier
                            Semantic.AtomicLeaf atom -> intern (atomicLeafFormula atom)
                        pure (if expected == actual then Just ((998,Semantic.AtomicLeaf requested),()) else Nothing))
                    (\value' -> pure (value',False)) False (const (pure ()))
                    (\_ _ values -> \case
                        Semantic.WholeResidual (Semantic.ResidualTemplate body) -> do
                            actual <- Core.instantiateCanonicalPrefixWith (charge 1) (maybe 0 (\(Semantic.ViewVariableIx index,_) -> index+1) (Map.lookupMax values))
                                (\depth index -> pure (Core.shiftCanonical depth 0 (denote (values Map.! Semantic.ViewVariableIx index)))) 0 body
                            identifier <- intern actual
                            pure (Request.WholeRequest identifier Nothing)
                        _ -> lift (Reference.invalidReferenceInput "fixture adapter template missing its Core"))
                    (\requested -> let identifier = Request.wholeRequestFormula requested
                        in pure (if identifier `elem` (adapted <> sourceFormulas) then Just ((999,Semantic.WholeLeaf identifier),()) else Nothing))
                    (\_ _ -> pure Nothing)
                    (\active shape -> Just . uncurry Evaluation.WholeCandidates <$> Catalog.matchingWholeRules charge active shape catalog)
                    (\identifier -> do
                        formulas <- State.get
                        actual <- maybe (lift (Reference.invalidReferenceInput "whole shape lost its formula")) pure
                            (either (const Nothing) id (fst (Formulas.lookupFormula 10000 identifier formulas)))
                        Formulas.residualShape (charge 1) context (Core.scopedCoreTerm actual))
                    (\shape -> pure [identifier | ((candidate,_),identifier) <- zip sourceShapes sourceFormulas, candidate == shape])
                    (\assertion -> Just <$> intern (atomicLeafFormula assertion))
                    (\signature -> Catalog.atomicWholeTruthPossible charge (supplied signature) signature catalog)
                    (\active head' known -> Catalog.possibleSource charge (\case
                        Semantic.AtomicLeaf signature -> pure (Set.member signature active)
                        Semantic.WholeLeaf shape -> pure (any ((== shape) . fst) sourceShapes)) head' catalog known)
                    (\case Semantic.TemplateVariable (Reference.OpaqueSeed 10) -> pure False; _ -> pure True)
                    (\term -> pure $ if not useInputs then Nothing else case denote term of
                        Core.CBound index -> Just (Reference.OpaqueSeed index)
                        value' | value' == (denote opaque :: Core.CanonicalTerm Identity.ObjectId) -> Just (Reference.OpaqueSeed 10)
                        _ -> Nothing)
                    (\pattern' identifier -> if not useInputs then pure (Just Map.empty) else do
                        formulas <- State.get
                        actual <- maybe (lift (Reference.invalidReferenceInput "whole input lost its formula")) pure
                            (either (const Nothing) id (fst (Formulas.lookupFormula 10000 identifier formulas)))
                        matched <- WholePattern.matchWholePattern charge pattern' (Core.scopedCoreTerm actual)
                        pure (Map.mapMaybe (\case
                            Core.CBound index -> Just (Reference.OpaqueSeed index)
                            term | term == denote opaque -> Just (Reference.OpaqueSeed 10)
                            _ -> Nothing) <$> matched))
                    (\consumerRule waiting producer values -> if not useInputs then pure (Just Map.empty) else
                        case Rule.ruleExactConclusion producer of
                            Nothing -> pure (Just Map.empty)
                            Just conclusion -> do
                                let partial rule' residual bindings = do
                                        let (arity,_,_) = Rule.ruleDescription rule'
                                        Core.instantiateCanonicalPrefixWith (charge 1) arity
                                            (\depth slot -> pure (Core.shiftCanonical depth 0
                                                (maybe (Core.CBound 2) (denote . fmap (fromMaybe (Reference.OpaqueSeed 2)))
                                                    (Map.lookup (Semantic.ViewVariableIx slot) bindings))))
                                            0 (Semantic.residualTemplateFormula residual)
                                requested <- partial consumerRule (Rule.wholeWaitingDescription waiting)
                                    (fmap (maybe (Semantic.TemplateVariable Nothing) (fmap Just)) (Rule.wholeWaitingInputs waiting))
                                candidate <- partial producer conclusion values
                                possible <- WholePattern.mayEqualOperands charge 2 requested candidate
                                if not possible then pure Nothing else case Rule.ruleConclusionPattern producer of
                                    Nothing -> pure (Just Map.empty)
                                    Just pattern' -> do
                                        matched <- WholePattern.matchPartialWholePattern charge 2 pattern' requested
                                        pure (Map.mapMaybe (\case
                                            Core.CBound index -> Just (Reference.OpaqueSeed index)
                                            term | term == denote opaque -> Just (Reference.OpaqueSeed 10)
                                            _ -> Nothing) <$> matched))
                    (\consumerRule waiting producer values slot -> pure (\partial -> isJust <$>
                        Evaluation.ruleMatchPartialWhole owner consumerRule waiting producer (Map.insert slot partial values)))
                    (\rule' description fixed slot identifier -> pure (\partial -> if not useInputs then pure True else do
                        let values = Map.insert slot partial fixed
                        let (arity,_,_) = Rule.ruleDescription rule'
                        candidate <- Core.instantiateCanonicalPrefixWith (charge 1) arity
                            (\depth slot -> pure (Core.shiftCanonical depth 0
                                (denote (fromMaybe (Reference.OpaqueSeed 2) <$>
                                    Map.findWithDefault (Semantic.TemplateVariable Nothing) (Semantic.ViewVariableIx slot) values))))
                            0 (Semantic.residualTemplateFormula description)
                        formulas <- State.get
                        target' <- maybe (lift (Reference.invalidReferenceInput "partial match lost its formula")) pure
                            (either (const Nothing) id (fst (Formulas.lookupFormula 10000 identifier formulas)))
                        WholePattern.mayEqualOperands charge 2 candidate (Core.scopedCoreTerm target')))
                    (\atom identifier -> if not useInputs then pure (Just Map.empty) else do
                        let prototype = State.evalState (traverse (const (State.state
                                (\slot -> (Semantic.TemplateVariable (Reference.OpaqueSeed slot),slot+1)))) atom) 0
                        pattern' <- WholePattern.compileWholePattern charge (fromIntegral (length (toList atom)))
                            (atomicLeafFormula prototype)
                        formulas <- State.get
                        actual <- maybe (lift (Reference.invalidReferenceInput "atomic inputs lost their formula")) pure
                            (either (const Nothing) id (fst (Formulas.lookupFormula 10000 identifier formulas)))
                        matched <- WholePattern.matchWholePattern charge pattern' (Core.scopedCoreTerm actual)
                        pure (Map.mapKeysMonotonic (\(Semantic.ViewVariableIx slot) -> fromIntegral slot) . Map.mapMaybe (\case
                            Core.CBound index -> Just (Reference.OpaqueSeed index)
                            term | term == denote opaque -> Just (Reference.OpaqueSeed 10)
                            _ -> Nothing) <$> matched))
                    (\left right -> if not useInputs then pure True else
                        WholePattern.mayEqualOperands charge 2
                            (denote (fromMaybe (Reference.OpaqueSeed 2) <$> left))
                            (denote (fromMaybe (Reference.OpaqueSeed 2) <$> right)))
                    Nothing (const (pure []))
            targetId <- leafId target
            let snapshot = case target of
                    Semantic.AtomicLeaf assertion -> do
                        shape <- Formulas.residualShape (charge 1) context (atomicLeafFormula assertion)
                        admit (Catalog.selectSnapshotHeads charge [Semantic.AtomicLeaf (Rule.atomSignature assertion),Semantic.WholeLeaf shape] catalog)
                    Semantic.WholeLeaf term -> Formulas.residualShape (charge 1) context term
                        >>= \shape -> admit (Catalog.selectWholeSnapshot charge shape catalog)
                requested = case targetId of
                    Semantic.AtomicLeaf assertion -> Semantic.AtomicLeaf assertion
                    Semantic.WholeLeaf identifier -> Semantic.WholeLeaf (Request.WholeRequest identifier Nothing)
            result <- admit (Evaluation.solveCatalogLeaves owner catalog initial seeds requested snapshot)
            pure (case result of Evaluation.FoundAnswer{} -> True
                                 Evaluation.SearchAnswers answers _ -> not (Set.null (Relational.relationalRootAnswers answers))))
                (Formulas.emptyFormulas context)
    for_ cases \(label,rules,facts,adapters',target,expected) -> do
        support <- expectRight (fst (Reference.enumerateSupport 100000 (Set.fromList seeds)
            (Set.fromList [term | Reference.ReferenceWholeRule _ premises conclusion <- rules,
                Semantic.AtomicLeaf atom <- conclusion:premises, term <- toList atom])))
        reachable <- expectRight (fst (Reference.runReference 1000000
            (Reference.evaluateFiniteHorn (Set.toList (Reference.referenceUniverse support)) denote atomicLeafFormula rules
                (facts <> [(Semantic.WholeLeaf result,False) | (supplied,result) <- adapters', (Semantic.WholeLeaf supplied,False) `elem` facts]))))
        let truth = \case Semantic.AtomicLeaf atom -> atomicLeafFormula atom; Semantic.WholeLeaf f -> f
        assertEqual (label <> " (reference)") expected (any ((== truth target) . truth . fst) (Set.toList reachable))
        for_ [(ordered,useInputs) | ordered <- [rules, reverse rules], useInputs <- [False,True]] \(ordered,useInputs) ->
            assertEqual (label <> " (production)") (Right expected)
                (fst (Reference.runReference 1000000 (runProduction useInputs False False ordered facts adapters' target)))

    -- A scoped parameter already has a source value. A demand can check that
    -- capture, but cannot replace it with its own complete-operand constraint.
    let captured = Rule.ScopedRuleInputs (Map.singleton (Semantic.ViewVariableIx 0) value)
        capturedRule = rule 1 [atomicLeaf 0 x] (member (pair x x) x)
    for_ [(member opaque value,True), (member opaque second,False),
          (member (pair second second) value,False)] \(target,expected) ->
        assertEqual "shared-parameter filtering retains fixed captures" (Right expected)
            (fst (Reference.runReference 1000000
                (runScopedProduction captured True False False [capturedRule] source [] target)))

    let formalCore = fmap (\(Semantic.ViewVariableIx index) -> Reference.OpaqueSeed index)
        eitherPremise term = Semantic.describedResidualTemplate
            (Core.COr (atomicLeafFormula (formalCore <$> row 0 term)) (atomicLeafFormula (formalCore <$> row 1 term)))
            (SourceEvidence.SourceOr (SourceEvidence.SourceAtom (row 0 term)) (SourceEvidence.SourceAtom (row 1 term)))
        clause = rule 2 [Semantic.WholeLeaf (eitherPremise y)] (atomicLeaf 2 x)
        finiteClause = Reference.FiniteClause 2
            [Reference.FiniteOr (Reference.FiniteAtom (row 0 y)) (Reference.FiniteAtom (row 1 y))]
            (Reference.FiniteAtom (row 2 x))
        unknownBranch = Core.COr (atomicLeafFormula (row 0 second)) (atomicLeafFormula (row 1 second))
    for_ [("positive whole premise",[(atomicLeaf 1 second,True)],[Reference.FiniteAtom (row 1 second)]),
          ("exact unknown alternative",[(Semantic.WholeLeaf unknownBranch,False)],
            [Reference.FiniteOr (Reference.FiniteAtom (row 0 second)) (Reference.FiniteAtom (row 1 second))]),
          ("missing positive premise",[],[])] \(label,facts,referenceFacts) -> do
        expected <- expectRight (fst (Reference.runReference 1000000
            (Reference.evaluateFiniteQueries seeds [] [finiteClause] referenceFacts [Reference.FiniteAtom (row 2 value)])))
        for_ [False,True] \useInputs -> assertEqual (label <> " with optional operand filters") (Right expected)
            (fmap pure (fst (Reference.runReference 1000000
                (runProduction useInputs False True [clause] facts [] (atomicLeaf 2 value)))))

    -- The oracle receives explicit ground Horn consequences. Production gets
    -- only the original whole template and compiles its projection itself.
    -- A spare original parameter must disappear from that generated schema.
    let conjunction = Core.CAnd
            (atomicLeafFormula (row 0 (Semantic.TemplateVariable (Reference.OpaqueSeed 0))))
            (atomicLeafFormula (row 1 (Semantic.TemplateVariable (Reference.OpaqueSeed 0))))
        schema = rule 2 [atomicLeaf 2 x, whole conjunction] (atomicLeaf 2 y)
        consequence = rule 1 [whole conjunction] (atomicLeaf 0 x)
        universalSource = Core.CForall Core.TySet
            (atomicLeafFormula (row 0 (Semantic.TemplateVariable (Reference.OpaqueSeed 0))))
        universalSchema = rule 1 [whole universalSource] (atomicLeaf 2 x)
        universalConsequence = rule 1 [whole universalSource] (atomicLeaf 0 x)
        vacuousSource = Core.CForall Core.TySet
            (atomicLeafFormula (row 0 (Semantic.TemplateVariable (Reference.OpaqueSeed 1))))
        checks =
            [("thin unused outer parameter",schema,consequence,conjunction,True,value,True)
            ,("wrong complete operand",schema,consequence,conjunction,True,second,False)
            ,("missing whole source",schema,consequence,conjunction,False,value,False)
            ,("instantiate a founded universal",universalSchema,universalConsequence,universalSource,True,second,True)
            ,("instantiate an unused quantified binder",rule 1 [whole vacuousSource] (atomicLeaf 2 x),
                rule 1 [whole vacuousSource] (atomicLeaf 0 x),vacuousSource,True,value,True)]
    for_ checks \(label,original,projected,sourceFormula,present,argument,expected) -> do
        let facts = [(Semantic.WholeLeaf sourceFormula,False) | present]
            target = atomicLeaf 0 argument
        reachable <- expectRight (fst (Reference.runReference 1000000
            (Reference.evaluateFiniteHorn seeds denote atomicLeafFormula [original,projected] facts)))
        assertEqual (label <> " (oracle)") expected
            (any (\(leaf,_) -> case leaf of
                Semantic.AtomicLeaf assertion -> atomicLeafFormula assertion == atomicLeafFormula (row 0 argument)
                Semantic.WholeLeaf formula' -> formula' == atomicLeafFormula (row 0 argument)) (Set.toList reachable))
        for_ [False,True] \useInputs -> assertEqual (label <> " (compiled elimination)") (Right expected)
            (fst (Reference.runReference 1000000 (runProduction useInputs True False [original] facts [] target)))

wholeCoveringActivation :: Assertion
wholeCoveringActivation = do
    fixture <- makeFixture 2
    let formula = Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)
        typing = fixtureGlobalTyping (globalTypingFixture [])
        context = [Core.TySet]
    checked <- expectRight (Core.checkScopedCanonicalCore typing context formula)
    (whole,formulas) <- expectRight (fst (Formulas.internFormula 10000 checked (Formulas.emptyFormulas context)))
    unrelated <- expectRight (Core.checkScopedCanonicalCore typing context Core.CFalsum)
    (other,_) <- expectRight (fst (Formulas.internFormula 10000 unrelated formulas))
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index argument = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton argument)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        value = Semantic.TemplateVariable (0 :: Natural)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        conclusion = Semantic.WholeLeaf (Semantic.ResidualTemplate formula)
        run firstCapability secondCapability = Reference.runReference 100000 do
            rule <- admit (Rule.compileConclusionRule charge 1
                [Semantic.RulePremiseAnd (Semantic.RulePremiseAtom (row 0 x)) (Semantic.RulePremiseAtom (row 1 x))]
                conclusion)
            catalog <- Catalog.insertRule charge () (Rule.RegisteredClassification rule) Catalog.emptyCatalog
            shape <- Formulas.residualShape (charge 1) context formula
            snapshot <- admit (Catalog.selectWholeSnapshot charge shape catalog)
            let owner = (Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
                    (const (pure ())) (const (pure ()))
                    (\ordinal _ -> pure (Just (ordinal + 1, ())))
                    (\_ _ -> pure Nothing) pure (const (pure ())))
                    { Evaluation.ruleWholeRequest = \_ _ values _ -> do
                        unless (Map.elems values == [value]) (Reference.invalidReferenceInput "covering match lost a parameter")
                        pure (Request.WholeRequest whole Nothing)
                    , Evaluation.ruleWholeEvidence = const (pure Nothing)
                    , Evaluation.ruleFormulaShape = const (pure shape)
                    , Evaluation.ruleAtomicFormula = \_ -> pure (Just other)
                    }
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row index value)) key capability ()
                    | (index,key,capability) <- [(0,100,firstCapability),(1,101,secondCapability)]]
            result <- admit (Evaluation.solveCatalogLeaves owner catalog facts []
                (Semantic.WholeLeaf (Request.WholeRequest whole Nothing)) (pure snapshot))
            pure (case result of
                Evaluation.FoundAnswer{} -> True
                Evaluation.SearchAnswers answers _ -> not (Set.null (Relational.relationalRootAnswers answers)))
    fst (run Join.ExactAnswer Join.SourceRow) @?= Right True
    fst (run Join.SourceRow Join.ExactAnswer) @?= Right True
    fst (run Join.ExactAnswer Join.ExactAnswer) @?= Right True
    (void <$> fst (Reference.runReference 10000 (Rule.compileConclusionRule charge 2
        [Semantic.RulePremiseAtom (row 0 x),Semantic.RulePremiseAtom (row 1 y)] conclusion)))
        @?= Right (Right ())

wholeGroundSubscriptions :: Assertion
wholeGroundSubscriptions = do
    fixture <- makeFixture 3
    let typing = fixtureGlobalTyping (globalTypingFixture [])
        context = [Core.TySet]
        member = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) (Core.CBound 0)) (Core.CIntrinsic Core.Empty)
        universalMember = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) (Core.CBound 0)) (Core.CBound 1)
    checked <- expectRight (Core.checkScopedCanonicalCore typing context member)
    (whole, formulas) <- expectRight (fst (Formulas.internFormula 10000 checked (Formulas.emptyFormulas context)))
    otherChecked <- expectRight (Core.checkScopedCanonicalCore typing context (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)))
    (other, otherFormulas) <- expectRight (fst (Formulas.internFormula 10000 otherChecked formulas))
    absentChecked <- expectRight (Core.checkScopedCanonicalCore typing context
        (Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) (Core.CIntrinsic Core.Empty)) (Core.CIntrinsic Core.Empty)))
    (absent, _) <- expectRight (fst (Formulas.internFormula 10000 absentChecked otherFormulas))
    quantified <- expectRight (Core.checkScopedCanonicalCore typing context (Core.CForall Core.TySet universalMember))
    (quantifiedId, _) <- expectRight (fst (Formulas.internFormula 10000 quantified formulas))
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index argument = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton argument)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        value = Semantic.TemplateVariable (0 :: Natural)
        emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        membership term = Semantic.MembershipAtomTemplate term emptySet
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        run producer = Reference.runReference 100000 do
            root <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAnd (Semantic.RulePremiseResidual (Semantic.ResidualTemplate member))
                    (Semantic.RulePremiseAtom (row 1 x))] (row 2 x))
            middle <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAnd (Semantic.RulePremiseAtom (row 0 x))
                    (Semantic.RulePremiseAtom (membership x))] (row 1 x))
            lastRule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row 0 x)] (membership x))
            catalog <- Catalog.insertRules charge [(0 :: Natural,root),(1,middle)] Catalog.emptyCatalog
            complete <- if producer then Catalog.insertRule charge 2 lastRule catalog else pure catalog
            snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 2 value)) complete)
            let owner = (Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
                    (const (pure ())) (const (pure ()))
                    (\ordinal _ -> pure (Just (ordinal + 1, ())))
                    (\_ _ -> pure Nothing) pure (const (pure ())))
                    { Evaluation.ruleWholeRequest = \_ _ values _ -> do
                        unless (Map.size values == 1) (Reference.invalidReferenceInput "whole premise was not determined")
                        pure (Request.WholeRequest (if Map.elems values == [value] then whole else absent) Nothing)
                    , Evaluation.ruleWholeEvidence = const (pure Nothing)
                    , Evaluation.ruleFormulaShape = const (Formulas.residualShape (charge 1) context member)
                    , Evaluation.ruleAtomicFormula = \atom -> pure (Just (if atom == membership value then whole else other))
                    }
            result <- admit (Evaluation.solveCatalogRules owner complete
                [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 0 value)) 100 Join.SourceRow ()]
                [] (row 2 value) (pure snapshot))
            pure (case result of
                Evaluation.FoundAnswer{} -> False
                Evaluation.SearchAnswers answers _ -> not (Set.null (Relational.relationalRootAnswers answers)))
    fst (run True) @?= Right True
    fst (run False) @?= Right False
    -- Equal Core does not collapse distinct supplied matching attempts.
    let indexed = Reference.runReference 100000 do
            support <- Support.buildSymbolicSupport charge [value] []
            (exact, table) <- Request.internWholeRequest charge (Request.WholeRequest quantifiedId Nothing)
                (Request.emptyRequestTable support)
            let target = SourceEvidence.UniversalBind (SourceEvidence.UniversalReturn (SourceEvidence.AtomLeaf
                    (Just (Semantic.MembershipAtomTemplate
                        (Semantic.TemplateVariable (SourceEvidence.UniversalBound 0))
                        (Semantic.TemplateVariable (SourceEvidence.UniversalOuter (0 :: Natural)))), universalMember)))
            (flexible, second) <- Request.internWholeRequest charge (Request.WholeRequest quantifiedId (Just target)) table
            (reused, _) <- Request.internWholeRequest charge (Request.WholeRequest quantifiedId (Just target)) second
            pure (exact /= flexible && reused == flexible)
    fst indexed @?= Right True

wholeProducerAccounting :: Assertion
wholeProducerAccounting = do
    fixture <- makeFixture 3
    let context = [Core.TySet,Core.TySet]
        formula left right = Core.COr (Core.CEq Core.TySet (Core.CBound left) (Core.CBound right)) Core.CTruth
        typing = fixtureGlobalTyping (globalTypingFixture [])
    (identities,_) <- foldM (\(known,table) term -> do
        checked <- expectRight (Core.checkScopedCanonicalCore typing context term)
        (identifier,next) <- expectRight (fst (Formulas.internFormula 10000 checked table))
        pure ((term,identifier):known,next)) ([],Formulas.emptyFormulas context)
        [formula a b | a <- [0,1], b <- [0,1]]
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        value = Semantic.TemplateVariable :: Natural -> Semantic.SetTermTemplate Natural
        identify term = fromMaybe (error "whole accounting fixture lost its formula") (List.lookup term identities)
        denotation identifier = fromMaybe (error "whole accounting fixture lost its identity")
            (List.lookup identifier [(identifier',term) | (term,identifier') <- identities])
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        run open repeated reporting = Reference.runReference 1000000 $ State.runStateT (do
            producers <- for [0,1] \index -> admit (Rule.compileConclusionRule charge 1
                [Semantic.RulePremiseAtom (row index x)]
                (Semantic.WholeLeaf (Semantic.ResidualTemplate (formula 0 0))))
            root <- admit (Rule.compileRule charge 2
                [Semantic.RulePremiseResidual (Semantic.ResidualTemplate (formula 1 0))] (row 2 x))
            let rules = if open then root:producers else take 1 (Rule.asIntroduction <$> producers)
            catalog <- Catalog.insertRules charge (zip [0 :: Natural ..] (Rule.RegisteredClassification <$> rules))
                Catalog.emptyCatalog
            shape <- Formulas.residualShape (charge 1) context (formula 0 0)
            let event event' = when reporting $ case event' of
                    Diagnostics.Count operation amount -> State.modify' (Diagnostics.countOperation operation amount)
                    _ -> pure ()
                owner = (Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
                    (const (pure ())) event (\_ _ -> pure Nothing)
                    (\_ _ -> pure Nothing) pure (const (pure ())))
                    { Evaluation.ruleCompleted = \ordinal _ leaf -> pure (Just ((ordinal,leaf),()))
                    , Evaluation.ruleWholeRequest = \_ _ bindings -> \case
                        Semantic.WholeResidual (Semantic.ResidualTemplate term) -> do
                            let width = maybe 0 (\(Semantic.ViewVariableIx index,_) -> index+1) (Map.lookupMax bindings)
                            actual <- Core.instantiateCanonicalPrefixWith (charge 1) width
                                (\depth index -> case bindings Map.! Semantic.ViewVariableIx index of
                                    Semantic.TemplateVariable v -> pure (Core.CBound (depth+v))
                                    _ -> error "whole accounting fixture expected a concrete variable") 0 term
                            pure (Request.WholeRequest (identify actual) Nothing)
                        _ -> error "whole accounting fixture expected a residual premise"
                    , Evaluation.ruleWholeEvidence = const (pure Nothing)
                    , Evaluation.ruleWholeCandidates = \active selected -> Just . uncurry Evaluation.WholeCandidates
                        <$> Catalog.matchingWholeRules charge active selected catalog
                    , Evaluation.ruleFormulaShape = const (pure shape)
                    , Evaluation.ruleArgumentValue = \case Semantic.TemplateVariable v -> pure (Just v); _ -> pure Nothing
                    , Evaluation.ruleMatchWhole = \pattern' identifier -> do
                        matched <- WholePattern.matchWholePattern charge pattern' (denotation identifier)
                        pure (Map.map (\case Core.CBound v -> v; _ -> error "nonvariable fixture binding") <$> matched)
                    }
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row index (value index)))
                    (100+index+copy,Semantic.AtomicLeaf (row index (value index))) Join.SourceRow ()
                    | index <- [0,1], copy <- if repeated then [0,10] else [0]]
            if open then do
                snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 2 (value 0))) catalog)
                (result,_) <- admit (Evaluation.evaluateCatalogRules owner catalog snapshot facts [] (row 2 (value 0)))
                pure (Relational.relationalSaturated result,not (Set.null (Relational.relationalRootAnswers result)))
            else do
                snapshot <- admit (Catalog.selectWholeSnapshot charge shape catalog)
                result <- admit (Evaluation.solveCatalogLeaves owner catalog facts []
                    (Semantic.WholeLeaf (Request.evidenceOnlyRequest (Request.WholeRequest (identify (formula 0 0)) Nothing)))
                    (pure snapshot))
                pure (case result of
                    Evaluation.FoundAnswer{} -> (False,True)
                    Evaluation.SearchAnswers answers _ ->
                        (Relational.relationalSaturated answers,not (Set.null (Relational.relationalRootAnswers answers)))))
                Diagnostics.emptyDiagnostics
        attempts = Map.findWithDefault 0 Diagnostics.AttemptedProducer . Diagnostics.operationCounts
    for_ [False,True] \open -> do
        let (measured,work) = run open False True
            (silent,silentWork) = run open False False
        (answer,counts) <- expectRight measured
        (silentAnswer,_) <- expectRight silent
        assertEqual "whole event collection preserves execution" (answer,work) (silentAnswer,silentWork)
        answer @?= (True,open)
        -- Open: the atomic root selects once; its open premise and the ground
        -- premise after binding each select both whole producers. The second
        -- produces (b=b) or True, incompatible with the pinned right operand a.
        -- Ground: the one returned introduction is ineligible for elimination.
        assertEqual "each request counts its returned producer candidates" (if open then 5 else 1) (attempts counts)
        (repeatedAnswer,repeatedCounts) <- expectRight (fst (run open True True))
        repeatedAnswer @?= answer
        assertEqual "additional deliveries do not reselect a producer" (attempts counts) (attempts repeatedCounts)

closedFixtureComprehension :: Core.CanonicalTerm Identity.ObjectId
closedFixtureComprehension = Core.CApp (Core.CApp (Core.CIntrinsic Core.Sep) (Core.CIntrinsic Core.Empty))
    (Core.CLam Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)))

closedFixtureValue :: Core.CanonicalTerm Identity.ObjectId -> Semantic.ClosedSetValue
closedFixtureValue term = fromMaybe (error "closed fixture was not a closed set")
    (Semantic.closedSetValue (expectPureRight (Core.checkScopedCanonicalCore
        (fixtureGlobalTyping (globalTypingFixture [])) [] term)))

closedSchemaValues :: Assertion
closedSchemaValues = do
    let typing = fixtureGlobalTyping (globalTypingFixture [])
        value = closedFixtureValue closedFixtureComprehension
        term :: Semantic.SetTermTemplate Reference.OpaqueSeed
        term = Semantic.TemplateClosed value
        compile context core = do
            checked <- expectRight (Core.checkScopedCanonicalCore typing context core)
            pure (Semantic.closedSetValue checked)
        sourceTemplate arity context core = do
            checked <- expectRight (Core.checkScopedCanonicalCore typing context core)
            pure (Notion.compileSourceRuleTermTemplate arity (SourceTerm.sourceTermOccurrence checked
                (Core.scopedCoreType checked) ("closed fixture" :: Text)))
        charge = Reference.chargeReferenceWork . fromIntegral
        run allowance = Reference.runReference allowance do
            prepared <- Support.prepareTemplateSupport charge [Semantic.TemplateClosed value]
            support <- Support.freezeSupport charge ([] :: [Reference.GroundTerm]) prepared
            (present,first) <- Support.symbolicSupportContains charge term support
            (absent,last') <- Support.symbolicSupportContains charge
                (Semantic.TemplateClosed (closedFixtureValue (Core.COpaqueInteger 8))) first
            pure (present,absent,Support.symbolicSupportMaximumTermSize last')
    compile [] closedFixtureComprehension >>= (@?= Just value)
    compile [Core.TySet] closedFixtureComprehension >>= (@?= Just value)
    sourceTemplate 0 [] closedFixtureComprehension >>= (@?= Right (Semantic.TemplateClosed value))
    sourceTemplate 1 [Core.TySet] closedFixtureComprehension >>= (@?= Right (Semantic.TemplateClosed value))
    sourceTemplate 1 [Core.TySet] (Core.CBound 0) >>= (@?= Right (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))
    for_ [([Core.TySet],Core.CBound 0), ([],Core.CTruth),
            ([Core.TySet],Core.CApp (Core.CLam Core.TySet (Core.CBound 1)) (Core.CIntrinsic Core.Empty))] \(context,core) ->
        compile context core >>= (@?= Nothing)
    let measured@(outcome,used) = run 100000
    outcome @?= Right (True,False,1)
    run used @?= measured
    fst (run (used - 1)) @?= Left Reference.ReferenceWorkExhausted
    reference <- expectRight (fst (Reference.enumerateSupport 100000 Set.empty
        (Set.singleton (Semantic.TemplateClosed value))))
    Reference.referenceUniverse reference @?= Set.singleton term
    Reference.referenceMaximumTermSize reference @?= 1
    assertBool "the closed payload is charged separately from its atomic support size" (used > 20)

scopedTemplateSupport :: Assertion
scopedTemplateSupport = do
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        captured = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        pair = Semantic.TemplateOrderedPair
        a = referenceSeed 0
        b = referenceSeed 1
        charge = Reference.chargeReferenceWork . fromIntegral
        run allowance = Reference.runReference allowance do
            support <- Support.freezeSupportWithCaptures charge
                [([pair captured x], Map.singleton (Semantic.ViewVariableIx 1) (pair a a))]
                [b] Support.emptyTemplateSupport
            (valid, first) <- Support.symbolicSupportContains charge (pair (pair a a) b) support
            (changed, second) <- Support.symbolicSupportContains charge (pair b b) first
            (reseeding, third) <- Support.symbolicSupportContains charge (pair (pair a a) (pair (pair a a) b)) second
            pure (valid,changed,reseeding,Support.symbolicSupportMaximumTermSize third)
    let measured@(outcome,work) = run 100000
    outcome @?= Right (True,False,False,7)
    run work @?= measured
    fst (run (work - 1)) @?= Left Reference.ReferenceWorkExhausted

scopedProducerInputs :: Assertion
scopedProducerInputs = do
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        captured = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        conclusion = Semantic.MembershipAtomTemplate x (Semantic.TemplateOrderedPair captured x)
        a = referenceSeed 0
        b = referenceSeed 1
        c = referenceSeed 2
        pin = fmap Pattern.Pinned
        output = Semantic.TemplateVariable (Pattern.Output 0)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        run allowance = Reference.runReference allowance do
            templates <- Support.prepareTemplateSupport charge [x,captured,Semantic.TemplateOrderedPair captured x]
            support <- Support.freezeSupport charge [a,b,c] templates
            let request left right = fst <$> admit (Pattern.normalizeFormationPattern charge support
                    (Semantic.MembershipAtomTemplate left right))
            ground <- request (pin a) (Semantic.TemplateOrderedPair (pin b) (pin a))
            partial <- request output (Semantic.TemplateOrderedPair (pin b) output)
            wrong <- request (pin a) (Semantic.TemplateOrderedPair (pin c) (pin a))
            rule <- admit (Rule.compileScopedRule charge 2 (Set.singleton (Semantic.ViewVariableIx 1))
                [Semantic.RulePremiseAtom (Semantic.MembershipAtomTemplate x captured)] conclusion)
            let inputs = Rule.ScopedRuleInputs (Map.singleton (Semantic.ViewVariableIx 1) b)
                start = Rule.startRuleWithInputs charge 16 inputs rule
                undetermined = \case Right (Just _) -> True; _ -> False
            accepted <- start ground >>= \case
                Right (Just state) -> Rule.ruleOptions charge 16 state >>= \case
                    [(_,Right waiting)] -> pure (Rule.ruleWaitingIsGround waiting)
                    _ -> pure False
                _ -> pure False
            unready <- undetermined <$> start partial
            rigid <- start wrong >>= \case Right Nothing -> pure True; _ -> pure False
            noCaptures <- admit (Rule.compileScopedRule charge 1 Set.empty [] (Semantic.MembershipAtomTemplate x x))
            emptyCaptureRequest <- request output output
            policy <- undetermined <$> Rule.startRule charge 16 noCaptures emptyCaptureRequest
            pure (accepted,unready,rigid,policy)
    let measured@(outcome,work) = run 100000
    outcome @?= Right (True,True,True,True)
    run work @?= measured
    fst (run (work - 1)) @?= Left Reference.ReferenceWorkExhausted

productionInitialEvidence :: Assertion
productionInitialEvidence = do
    fixture <- makeFixture 4
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row head' = Semantic.StructureAtomTemplate (fixtureHead fixture head') . Vector.fromList
        power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        rules = Map.fromList [(0,Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 0 [x])]
                (row 1 [power (power x),x]) Set.empty),
            (1,Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 1 [y,x])]
                (row 2 [Semantic.TemplateOrderedPair y y,x]) Set.empty),
            (2,Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 2 [y,x])] (row 3 [x]) Set.empty)]
        facts = [Reference.ReferenceFact (row 0 [a]) (referenceSummary 0)]
        target = row 3 [a]
    initial <- runProductionWithViews (Set.singleton 0) rules facts target
    assertReferenceAnswer "a term exposed by an initial view belongs to the frozen seed domain" True target initial
    derived <- runProductionRules rules facts target
    assertReferenceAnswer "an ordinary derived term cannot reseed support" False target derived
    let emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        closed = Map.insert 3 (Reference.ReferenceRule 0 [] (row 0 [emptySet]) Set.empty) rules
        closedTarget = row 3 [emptySet]
    unconditional <- runProductionWithViews (Set.singleton 0) closed [] closedTarget
    assertReferenceAnswer "closed results enter initial view expansion with their own recipes" True closedTarget unconditional
    forM_ [(True,initial),(False,derived)] \(isView,production) -> do
        let registrations = Map.mapWithKey (\ordinal rule ->
                if isView && ordinal == 0 then Reference.DefinitionRule rule else Reference.ClassificationRule rule) rules
        (_,reference) <- expectRight (fst (Reference.evaluateFormation 1000000 registrations facts Set.empty target))
        let found evaluation = Set.fromList [summary | ((atom',summary),_) <- Map.toList (Reference.referenceAnswers evaluation), atom' == target]
        assertEqual "production initial support agrees with the independent snapshot reference" (found reference) (found production)

initialRootCompletion :: Assertion
initialRootCompletion = do
    fixture <- makeFixture 2
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        ground = Semantic.TemplateVariable (0 :: Natural)
        power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton value)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        run allowance solve expensive = Reference.runReference allowance do
            first <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 0 variable) (row 1 variable))
            later <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 0 variable) (row 1 (power variable)))
            snapshot <- admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature (row 1 ground))
                (Map.fromList [(0,first),(1,later)]))
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (\_ -> pure ()) (\_ -> pure ())
                    (\ordinal _ -> do
                        when (expensive && ordinal == 1) (charge 10000)
                        pure (Just (ordinal + 1, ())))
                    (\_ _ -> pure Nothing) pure
                    (Reference.invalidReferenceInput . Text.pack . show)
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 0 ground)) 0 Join.SourceRow ()]
            if solve then admit (Evaluation.solveRules owner snapshot facts [] (row 1 ground)) >>= \case
                Evaluation.FoundAnswer answer -> pure (Set.singleton (Evaluation.ruleAnswerKey answer))
                Evaluation.SearchAnswers result _ -> pure (Relational.relationalRootAnswers result)
            else do
                (result, _) <- admit (Evaluation.evaluateRules owner snapshot facts [] (row 1 ground))
                pure (Map.keysSet (Relational.relationalAnswers result))
        solved = run 2000 True True
    assertEqual "checked initial evidence solves within the ordinary small account"
        (Right (Set.singleton 1)) (fst solved)
    assertEqual "no work is charged for the unused forward alternative"
        solved (run 2000 True False)
    assertEqual "exhaustive evaluation still charges the expensive alternative"
        (Left Reference.ReferenceWorkExhausted) (fst (run 2000 False True))
    assertEqual "completed exhaustive evaluation retains both derived rows"
        (Right (Set.fromList [0,1,2])) (fst (run 100000 False True))

initialAncestorPriority :: Assertion
initialAncestorPriority = do
    fixture <- makeFixture 6
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = Semantic.TemplateVariable (0 :: Natural)
        b = Semantic.TemplateVariable (1 :: Natural)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
    catalog <- expectRight (fst (Reference.runReference 100000 do
        views <- forM [(0,1),(1,2),(3,4)] \(source,result) ->
            Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row source x) (row result x))
        -- This ordinary alternative makes heads 3 and 4 relevant to the
        -- full query, but they cannot expose the goal through initial views.
        alternative <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            (Semantic.RulePremiseAtom <$> [row 4 x,row 5 x]) (row 2 x))
        Catalog.insertRules charge [((),entry) | entry <- views <> [alternative]] Catalog.emptyCatalog))
    let run allowance stop expensive target reverseSources = Reference.runReference allowance do
            snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature target) catalog)
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (const (pure ())) (const (pure ()))
                    (\ordinal completed -> do
                        when (expensive && ordinal == 2) (charge 10000)
                        pure (Just (Production.completedAtom completed, ())))
                    (\_ _ -> pure Nothing) pure
                    (Reference.invalidReferenceInput . Text.pack . show)
                sources = [row 0 a,row 3 a]
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf atom) atom Join.SourceRow ()
                    | atom <- if reverseSources then reverse sources else sources]
            Evaluation.prepareRuleSupport stop owner snapshot facts [] target >>= \case
                Left answer -> pure (True,Set.singleton (Production.atomicAnswer answer))
                Right (_,answers) -> pure (False,Set.fromList (Production.atomicAnswer <$> answers))
        allRows = Set.fromList [row head' a | head' <- [0..4]]
    forM_ [False,True] \reverseSources -> do
        let solved@(result,used) = run 3000 True True (row 2 a) reverseSources
        assertEqual "a two-view witness precedes unrelated rank-zero expansion"
            (Right (True,Set.singleton (row 2 a))) result
        assertEqual "the unrelated completion is never invoked on success"
            solved (run 3000 True False (row 2 a) reverseSources)
        run used True True (row 2 a) reverseSources @?= solved
        fst (run (used-1) True True (row 2 a) reverseSources) @?= Left Reference.ReferenceWorkExhausted
        assertEqual "a miss still pays for the complete closure"
            (Left Reference.ReferenceWorkExhausted)
            (fst (run 3000 True True (row 2 b) reverseSources))
        assertEqual "a completed miss retains every initial consequence"
            (Right (False,allRows))
            (fst (run 100000 True True (row 2 b) reverseSources))
        assertEqual "exhaustive evaluation retains the same closure despite a goal witness"
            (Right (False,allRows))
            (fst (run 100000 False True (row 2 a) reverseSources))

initialRowsAdmission :: Assertion
initialRowsAdmission = do
    fixture <- makeFixture 2
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        ground = Semantic.TemplateVariable (0 :: Natural)
        population = 512 :: Natural
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        run allowance solve = Reference.runReference allowance do
            rule <- Rule.RegisteredClassification <$> admit
                (Rule.compileRule charge 1 [Semantic.RulePremiseAtom (row 0 variable)] (row 1 variable))
            snapshot <- admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature (row 1 ground)) (Map.singleton 0 rule))
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (\_ -> pure ()) (\_ -> pure ())
                    (\_ _ -> pure (Just (population, ())))
                    (\_ _ -> pure Nothing) pure
                    (Reference.invalidReferenceInput . Text.pack . show)
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 0 (Semantic.TemplateVariable index))) index Join.SourceRow ()
                    | index <- [0..population - 1]]
            if solve then admit (Evaluation.solveRules owner snapshot facts [] (row 1 ground)) >>= \case
                Evaluation.FoundAnswer _ -> Reference.invalidReferenceInput "a classification must use ordinary search"
                Evaluation.SearchAnswers result _ -> pure (Relational.relationalRootAnswers result)
            else do
                (result, _) <- admit (Evaluation.evaluateRules owner snapshot facts [] (row 1 ground))
                pure (Relational.relationalRootAnswers result)
        (solved, used) = run 131072 True
    assertEqual "a large initial population fits the unchanged inference account"
        (Right (Set.singleton population)) solved
    assertEqual "exhaustive evaluation agrees on the requested root"
        solved (fst (run 131072 False))
    assertEqual "all actual work remains metered" (solved, used) (run used True)
    assertEqual "one-short fails explicitly"
        (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1) True))

productionRuleSnapshot :: Assertion
productionRuleSnapshot = do
    fixture <- makeFixture 5
    let row head' = Semantic.StructureAtomTemplate (fixtureHead fixture head')
            (Vector.singleton (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        run allowance cyclic prepared = Reference.runReference allowance do
            first <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 0) (row 1))
            second <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 1) (row 2))
            closing <- if cyclic
                then Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 2) (row 0))
                else Rule.RegisteredClassification <$> admit
                    (Rule.compileRule charge 1 [Semantic.RulePremiseAtom (row 2)] (row 0))
            unrelated <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 4) (row 4))
            let registrations = Map.fromList [(0,first),(1,second),(2,closing),(3,unrelated)]
            snapshot <- if prepared then do
                catalog <- foldM (\known entry -> Catalog.insertRule charge () entry known)
                    Catalog.emptyCatalog (Map.elems registrations)
                Catalog.selectSnapshot charge (Rule.atomSignature (row 2)) catalog
              else Rule.prepareRuleSnapshot charge (Rule.atomSignature (row 2)) registrations
            pure ((\selected -> (Map.keys (Rule.snapshotRules selected),
                Rule.snapshotHeads selected, fst <$> Rule.snapshotForwardOrder selected,
                Map.map Map.keys (Map.restrictKeys (Rule.snapshotProducers selected) (Rule.snapshotHeads selected)),
                Map.map Map.keys (Rule.snapshotForwardSources selected))) <$> snapshot)
        (outcome,used) = run 100000 False False
    selected <- expectRight =<< expectRight outcome
    assertEqual "backward relevance excludes unrelated invalid view graphs"
        ([0,1,2],Set.fromList (Rule.atomSignature . row <$> [0,1,2]),[0,1],
            Map.fromList [(Rule.atomSignature (row head'), [ordinal]) | (head',ordinal) <- [(0,2),(1,0),(2,1)]],
            Map.fromList [(Rule.atomSignature (row head'), [ordinal]) | (head',ordinal) <- [(0,0),(1,1)]]) selected
    assertEqual "snapshot work shares the exact allowance" (outcome,used) (run used False False)
    assertEqual "one-short snapshot is exhaustion" (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1) False False))
    fst (run 100000 False True) @?= outcome
    for_ [False,True] \prepared -> do
        rejected <- expectRight (fst (run 100000 True prepared))
        case rejected of
            Left Rule.CyclicDefinitionDependency{} -> pure ()
            Right _ -> assertFailure "a selected definition cycle cannot seed support"

catalogHeadLocality :: Assertion
catalogHeadLocality = do
    fixture <- makeFixture 3
    let row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        provider index value = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "catalog" index))
            (Vector.fromList [value,variable])
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        prepared = Reference.runReference 100000 do
            entries <- traverse (\conclusion -> Rule.RegisteredClassification <$> admit
                (Rule.compileRule charge 1 [] conclusion))
                [row 0 variable, row 0 (provider 0 variable), row 1 (provider 0 variable), row 2 variable]
            foldM (\catalog entry -> Catalog.insertRule charge () entry catalog) Catalog.emptyCatalog entries
    catalog <- expectRight (fst prepared)
    let query allowance goal = Reference.runReference allowance
            (fmap fst <$> Catalog.matchingRules charge goal catalog)
        nested depth = foldr (const (provider 0)) variable [1 .. depth :: Int]
        shallow = query 100000 (row 2 (nested 1))
        deep = query 100000 (row 2 (nested 500))
    assertEqual "an unrelated rigid head does not charge goal traversal" shallow deep
    assertEqual "flexible rules remain available" (Right [3]) (fst deep)
    assertEqual "matching rigid candidates precede flexible candidates deterministically"
        (Right [1,0]) (fst (query 100000 (row 0 (provider 0 variable))))
    assertEqual "an incompatible rigid constructor is excluded"
        (Right [0]) (fst (query 100000 (row 0 (provider 1 variable))))
    assertEqual "lookup uses its exact allowance" shallow (query (snd shallow) (row 2 (nested 500)))
    assertEqual "one-short lookup reports exhaustion"
        (Left Reference.ReferenceWorkExhausted) (fst (query (snd shallow - 1) (row 2 (nested 500))))

catalogProviderLocality :: Assertion
catalogProviderLocality = do
    fixture <- makeFixture 2
    let variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        provider index = Semantic.GlobalSourceProvider (binaryProviderReference "record-result" index)
        conclusion index = Semantic.StructureAtomTemplate (fixtureHead fixture 0)
            (Vector.singleton (Semantic.TemplateProvider (provider index) (Vector.fromList [variable,variable])))
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build size = fst (Reference.runReference 1000000 do
            foldM (\catalog index -> do
                entry <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1 [] (conclusion index))
                Catalog.insertRule charge index entry catalog) Catalog.emptyCatalog [0 .. size])
    small <- expectRight (build 2)
    large <- expectRight (build 500)
    let query allowance catalog = Reference.runReference allowance
            (Catalog.providerStructureResults charge (provider 0) catalog)
        observed = query 100000 large
    fst (query 100000 small) @?= Right [0]
    fst observed @?= Right [0]
    assertBool "unrelated provider results add only index lookup work" (snd observed < 100)
    query (snd observed) large @?= observed
    fst (query (snd observed - 1) large) @?= Left Reference.ReferenceWorkExhausted

incompatibleProducerSupport :: Assertion
incompatibleProducerSupport = do
    fixture <- makeFixture 4
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        emptyLiteral = Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider Vector.empty
        power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton value)
        other value = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "support" 0)) (Vector.fromList [value,value])
        rule arity premises conclusion = Reference.ClassificationRule
            (Reference.ReferenceRule arity (Semantic.RulePremiseAtom <$> premises) conclusion Set.empty)
        base = Map.singleton 0 (rule 1 [row 1 x] (row 0 x))
        added = Map.fromList [(1,rule 1 [row 2 x] (row 0 (other x))),
                             (2,rule 0 [] (row 2 (power emptyLiteral)))]
        snapshot rules = expectRight (fst (Reference.prepareReferenceSnapshot 100000 rules
            ([] :: [Reference.ReferenceFact Natural]) Set.empty (row 0 emptyLiteral)))
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        compareProduction rules = do
            reference <- snapshot rules
            let expected = Reference.referenceSnapshotSupport reference
                queries = Set.toAscList (Reference.referenceUniverse expected) <>
                    [other (other emptyLiteral), power (other (power emptyLiteral))]
                run allowance = Reference.runReference allowance do
                    (support,rows,_) <- Production.prepareProductionSupport rules
                        ([] :: [Reference.ReferenceFact Natural]) Set.empty (row 0 emptyLiteral)
                    (answers,final) <- foldM (\(answers,current) term -> do
                        (answer,next) <- Support.symbolicSupportContains charge term current
                        pure (answer:answers,next)) ([],support) queries
                    pure (reverse answers,Support.symbolicSupportMaximumTermSize final,Set.fromList rows)
                (outcome,used) = run 1000000
            actual <- expectRight outcome
            actual @?= ((`Set.member` Reference.referenceUniverse expected) <$> queries,
                Reference.referenceMaximumTermSize expected,
                Set.fromList (Reference.referenceWitnessAtom <$> Map.elems
                    (Reference.referenceWitnesses (Reference.referenceSnapshotInitial reference))))
            run used @?= (outcome,used)
            fst (run (used - 1)) @?= Left Reference.ReferenceWorkExhausted
            pure (Reference.referenceMaximumTermSize expected)
    before <- Reference.referenceSnapshotSupport <$> snapshot base
    extendedSupport <- Reference.referenceSnapshotSupport <$> snapshot (base <> added)
    assertBool "the added closed fact was not an original seed"
        (power emptyLiteral `Set.notMember` Reference.referenceSeeds before)
    assertBool "head reachability introduces its initial seed even for an incompatible producer"
        (power emptyLiteral `Set.member` Reference.referenceSeeds extendedSupport)
    assertBool "the producer template instantiates over that seed"
        (other (power emptyLiteral) `Set.member` Reference.referenceUniverse extendedSupport)
    compareProduction base >>= (@?= 1)
    compareProduction (base <> added) >>= (@?= 5)
    let fromView = Map.fromList
            [(1,added Map.! 1), (2,rule 0 [] (row 3 emptyLiteral)),
             (3,Reference.DefinitionRule (Reference.ReferenceRule 1
                [Semantic.RulePremiseAtom (row 3 x)] (row 2 (power x)) Set.empty))]
    compareProduction (base <> fromView) >>= (@?= 5)
    selected <- expectRight (fst (Reference.runReference 100000 do
        entries <- traverse (\entry -> let r = Reference.registrationRule entry in
            Rule.RegisteredClassification <$> admit (Rule.compileRule charge
                (Reference.referenceRuleArity r) (Reference.referenceRulePremises r)
                (Reference.referenceRuleConclusion r))) (Map.elems (base <> added))
        catalog <- foldM (\current entry -> Catalog.insertRule charge () entry current) Catalog.emptyCatalog entries
        fmap fst <$> Catalog.matchingRules charge
            (row 0 emptyLiteral :: Semantic.AtomTemplate (Semantic.SetTermTemplate Natural)) catalog))
    assertEqual "candidate filtering correctly excludes the rigid producer, not its support contribution" [0] selected

wholeHeadLocality :: Assertion
wholeHeadLocality = do
    let charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        wanted = Core.CNot Core.CTruth
        build size = Reference.runReference 1000000 do
            rules <- for [wanted, foldr (const Core.CNot) Core.CFalsum [1..size]] \formula ->
                Rule.RegisteredClassification <$> admit (Rule.compileConclusionRule charge 0 []
                    (Semantic.WholeLeaf (Semantic.ResidualTemplate formula)))
            Catalog.insertRules charge [((),rule) | rule <- rules] Catalog.emptyCatalog
        shape = runIdentity (Formulas.residualShape (pure ()) [] wanted)
        select catalog = Reference.runReference 10000 do
            selected <- admit (Catalog.selectWholeSnapshot charge shape catalog)
            pure (Rule.snapshotCounts selected)
    results <- for [4,16,64,256] \size -> do
        catalog <- expectRight (fst (build size))
        let (result,work) = select catalog
        result @?= Right (Rule.SnapshotCounts 1 0 0)
        pure work
    assertEqual "an unrelated shape is neither traversed nor charged at lookup"
        1 (length (nubOrd results))

wholeFrontierLocality :: Assertion
wholeFrontierLocality = do
    costs <- for [16,64,256] \size -> do
        fixture <- makeFixture (2 * size)
        let charge = Reference.chargeReferenceWork . fromIntegral
            admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
            x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
            row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton x)
            whole = Semantic.ResidualTemplate (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0))
            view index catalog = do
                rule <- Rule.RegisteredDefinition <$> admit (Rule.compileDescribedForwardRule charge 1
                    (row (size + index)) (Semantic.WholeLeaf whole))
                Catalog.insertRule charge () rule catalog
        prepared <- expectRight (fst (Reference.runReference 10000000 do
            roots <- foldM (\known index -> do
                rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                    [Semantic.RulePremiseResidual whole] (row index))
                Catalog.insertRule charge () rule known) Catalog.emptyCatalog [0..size-1]
            foldM (flip view) roots [0..size-2]))
        let (result,work) = Reference.runReference 1000000 (view (size-1) prepared)
        extended <- expectRight result
        snapshot <- expectRight (fst (Reference.runReference 10000000
            (admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 0)) extended))))
        Rule.snapshotCounts snapshot @?= Rule.SnapshotCounts (size+1) (size+1) size
        pure work
    for_ (zip costs (drop 1 costs)) \(smaller,larger) ->
        assertBool "adding one whole producer does not revisit its dormant consumers"
            (larger < 2 * smaller)

preparedCatalogueLocality :: Assertion
preparedCatalogueLocality = do
    fixture <- makeFixture 2
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        emptySet = Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider Vector.empty
        power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton value)
        other index value = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "prepared-locality" index)) (Vector.fromList [value,value])
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build size = Reference.runReference 10000000 do
            closed <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 0 [] (row 1 (power emptySet)))
            base <- Catalog.insertRule charge () closed Catalog.emptyCatalog
            foldM (\catalog index -> do
                rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                    [Semantic.RulePremiseAtom (row 1 x)] (row 0 (other index x)))
                Catalog.insertRule charge () rule catalog) base [0..size-1]
        query allowance catalog = Reference.runReference allowance do
            snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 0 x)) catalog)
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (const (pure ())) (const (pure ()))
                    (\ordinal _ -> pure (Just (ordinal,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
            prepared <- Evaluation.prepareRuleSupport False owner snapshot [] [] (row 0 emptySet)
            case prepared of
                Left _ -> Reference.invalidReferenceInput "exhaustive support stopped early"
                Right (support,initial) -> do
                    (present,final) <- Support.symbolicSupportContains charge
                        (other 0 (power emptySet) :: Semantic.SetTermTemplate Natural) support
                    pure (present,Support.symbolicSupportMaximumTermSize final,length initial,Rule.snapshotCounts snapshot)
        (smallPrepared,smallWork) = build 32
        (largePrepared,largeWork) = build 256
    small <- expectRight smallPrepared
    large <- expectRight largePrepared
    let (_,smallQueryWork) = query 100000 small
        observed@(result,largeQueryWork) = query 100000 large
    result @?= Right (True,5,1,Rule.SnapshotCounts 257 256 0)
    assertBool "admission scaling is bounded and measured, not a repeated all-roots rebuild"
        (largeWork < 12 * smallWork)
    assertBool "fresh query preparation does not traverse the selected producer population"
        (largeQueryWork < smallQueryWork + 150 && largeQueryWork < 2000)
    query largeQueryWork large @?= observed
    fst (query (largeQueryWork - 1) large) @?= Left Reference.ReferenceWorkExhausted
    added <- expectRight (fst (Reference.runReference 100000 do
        rule <- admit (Rule.compileRule charge 1 [Semantic.RulePremiseAtom (row 1 x)] (row 0 (other 300 x)))
        pure (Rule.RegisteredClassification rule)))
    case fst (Reference.runReference 1 (Catalog.insertRule charge () added large)) of
        Left Reference.ReferenceWorkExhausted -> pure ()
        _ -> assertFailure "underfunded preparation unexpectedly published a catalogue"
    query largeQueryWork large @?= observed
    extended <- expectRight (fst (Reference.runReference 100000 (Catalog.insertRule charge () added large)))
    fst (query 100000 extended) @?= Right (True,5,1,Rule.SnapshotCounts 258 257 0)
    query largeQueryWork large @?= observed
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("prepared support locality: admission=" <> show (smallWork,largeWork)
        <> " fresh-query=" <> show (smallQueryWork,largeQueryWork)))
    denseFrontierLocality
    sharedComponentLocality
    overlappingSummaryCounts
    batchedProjectionLocality

batchedProjectionLocality :: Assertion
batchedProjectionLocality = do
    fixture <- makeFixture 34
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton x)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        rule source target = Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            [Semantic.RulePremiseAtom (row target)] (row source))
    (initial,entry) <- expectRight (fst (Reference.runReference 1000000 do
        initial <- foldM (\known head' -> do
            entry <- rule head' 0
            Catalog.insertRule charge head' entry known) Catalog.emptyCatalog [1..32]
        entry <- rule 0 33
        pure (initial,entry)))
    let supplied = [(index,entry) | index <- [100..115]]
        batch allowance = Reference.runReference allowance (Catalog.insertRules charge supplied initial)
        (result,used) = batch 1000000
        (_,sequential) = Reference.runReference 1000000
            (foldM (\known (source,entry) -> Catalog.insertRule charge source entry known) initial supplied)
    completed <- expectRight result
    assertBool "batch preparation stays below separate admissions and within its allowance"
        (used <= sequential && used < 65536)
    for_ [0..15] \index -> Catalog.lookupSource (32+index) completed @?= Just (100+index)
    void (expectRight (fst (batch used)))
    case fst (batch (used-1)) of
        Left Reference.ReferenceWorkExhausted -> pure ()
        _ -> fail "batched preparation escaped the owning allowance"
    for_ [(initial,1),(completed,17)] \(catalog,expected) -> do
        snapshot <- expectRight (fst (Reference.runReference 100000
            (admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 1)) catalog))))
        Rule.snapshotCounts snapshot @?= Rule.SnapshotCounts expected expected 0
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("same-owner projection admission: sequential=" <> show sequential <> " batch=" <> show used))

overlappingSummaryCounts :: Assertion
overlappingSummaryCounts = do
    fixture <- makeFixture 3
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton x)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        edge source premises catalog = do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                (Semantic.RulePremiseAtom . row <$> premises) (row source))
            Catalog.insertRule charge () rule catalog
    snapshot <- expectRight (fst (Reference.runReference 100000 do
        base <- edge 1 [] Catalog.emptyCatalog
        left <- edge 0 [1] base
        right <- edge 2 [1] left
        joined <- edge 0 [2] right
        admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 0)) joined)))
    -- Both dependency summaries contain the fact at head 1. It contributes
    -- once, while the three distinct premise edges all remain in the count.
    Rule.snapshotCounts snapshot @?= Rule.SnapshotCounts 4 3 0

-- One new edge joins an existing component to a large dependency chain.
-- Every component member has the same extension: merging its complete rule
-- descriptions once per member would make this admission quadratic.
sharedComponentLocality :: Assertion
sharedComponentLocality = do
    let run cyclic size = do
            fixture <- makeFixture (2 * size)
            let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
                row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton x)
                charge = Reference.chargeReferenceWork . fromIntegral
                admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
                edge source target catalog = do
                    rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                        [Semantic.RulePremiseAtom (row target)] (row source))
                    Catalog.insertRule charge () rule catalog
            catalog <- expectRight (fst (Reference.runReference 10000000 do
                component <- if cyclic then do
                    chain <- foldM (\known index -> edge index (index + 1) known)
                        Catalog.emptyCatalog (reverse [0..size-2])
                    edge (size-1) 0 chain
                  else foldM (\known index -> edge index (size-1) known)
                    Catalog.emptyCatalog [0..size-2]
                foldM (\known index -> edge index (index + 1) known)
                    component (reverse [size..2*size-2])))
            let prepare allowance = Reference.runReference allowance
                    (edge (if cyclic then 0 else size-1) size catalog)
                (result,work) = prepare 1000000
            extended <- expectRight result
            for_ [0,size-1] \root -> do
                snapshot <- expectRight (fst (Reference.runReference 1000000
                    (admit (Catalog.selectSnapshot charge (Rule.atomSignature (row root)) extended))))
                let count = if cyclic then 2*size else size + if root == size-1 then 0 else 1
                Rule.snapshotCounts snapshot @?= Rule.SnapshotCounts count count 0
            void (expectRight (fst (prepare work)))
            case fst (prepare (work-1)) of
                Left Reference.ReferenceWorkExhausted -> pure ()
                _ -> fail "shared component preparation escaped its account"
            pure work
    small <- run True 16
    large <- run True 48
    assertBool "component summaries share newly reachable description work" (large < 5 * small)
    assertBool "a broad component extension retains admission headroom" (large < 65536)
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("shared component admission=" <> show (small,large)))
    acyclic <- run False 32
    when (isJust diagnostic) (putStrLn ("shared acyclic block admission=" <> show acyclic))
    assertBool "distinct roots share dependency descriptions under the default allowance" (acyclic < 65536)

-- A transitive cycle contains many reachable heads, but a redundant direct
-- edge adds no head to any root. Its preparation must inspect the direct
-- frontier, not each root's complete dependency population.
denseFrontierLocality :: Assertion
denseFrontierLocality = do
    let run size = do
            fixture <- makeFixture size
            let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
                row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton x)
                charge = Reference.chargeReferenceWork . fromIntegral
                admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
                edge source target catalog = do
                    rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                        [Semantic.RulePremiseAtom (row target)] (row source))
                    Catalog.insertRule charge () rule catalog
            catalog <- expectRight (fst (Reference.runReference 10000000 do
                chain <- foldM (\known index -> edge index (index + 1) known)
                    Catalog.emptyCatalog (reverse [0..size-2])
                edge (size-1) 0 chain))
            let prepare allowance = Reference.runReference allowance (edge 0 (size-1) catalog)
                (result,work) = prepare 1000000
            extended <- expectRight result
            snapshot <- expectRight (fst (Reference.runReference 1000000
                (admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 0)) extended))))
            Rule.snapshotCounts snapshot @?= Rule.SnapshotCounts (size+1) (size+1) 0
            void (expectRight (fst (prepare work)))
            case fst (prepare (work-1)) of
                Left Reference.ReferenceWorkExhausted -> pure ()
                _ -> fail "dense frontier escaped its preparation account"
            pure work
    small <- run 32
    large <- run 96
    assertBool "redundant dense edges do not rescan every reachable head at every root" (large < 5 * small)
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("dense frontier admission=" <> show (small,large)))

partialProducerSelection :: Assertion
partialProducerSelection = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row head' = Semantic.StructureAtomTemplate (fixtureHead fixture head') . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        results = [power x,power (power x),Semantic.TemplateOrderedPair x x]
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
    catalog <- expectRight (fst (Reference.runReference 100000 do
        rules <- traverse (\result -> Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            [Semantic.RulePremiseAtom (row 1 [x])] (row 0 [x,result]))) results
        foldM (\known rule -> Catalog.insertRule charge () rule known) Catalog.emptyCatalog rules))
    let pin = Semantic.TemplateVariable (Pattern.Pinned (0 :: Natural))
        hole = Semantic.TemplateVariable (Pattern.Output 0)
        query allowance requested = Reference.runReference allowance do
            selected <- Catalog.matchingPatternRules charge requested catalog
            let collect current = Catalog.nextCandidateRule charge current >>= \case
                    Nothing -> pure []
                    Just ((ordinal,_),rest) -> (ordinal:) <$> collect rest
            (,) (Catalog.candidateRuleCount selected) <$> collect selected
    for_ [(row 0 [pin,hole],[0,1,2]), (row 0 [pin,power hole],[0,1]),
            (row 0 [pin,power pin],[0]), (row 0 [hole,hole],[0,1,2])] \(requested,expected) -> do
        let measured@(outcome,used) = query 100000 requested
        outcome @?= Right (fromIntegral (length expected),expected)
        query used requested @?= measured
        fst (query (used - 1) requested) @?= Left Reference.ReferenceWorkExhausted
    let source = Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 1 [x])] (row 0 [x,power x]) Set.empty
        consumer = Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 0 [x,y])] (row 2 [x]) Set.empty
        target = row 2 [referenceSeed 0]
    (result,_) <- runReferenceCase [source,consumer]
        [Reference.ReferenceFact (row 1 [referenceSeed 0]) (referenceSummary 0)] target
    assertReferenceAnswer "a demanded output may be a constructed term, not just a seed" True target result
    ordered <- expectRight (fst (Reference.runReference 100000 do
        generic <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
            [Semantic.RulePremiseAtom (row 1 [x]),Semantic.RulePremiseAtom (row 1 [y])] (row 0 [x,y]))
        rigid <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            [Semantic.RulePremiseAtom (row 1 [x])] (row 0 [x,power x]))
        added <- Catalog.insertRule charge () generic Catalog.emptyCatalog >>= Catalog.insertRule charge () rigid
        fmap fst <$> Catalog.matchingRules charge (row 0 [referenceSeed 0,power (referenceSeed 0)]) added))
    assertEqual "rigid results precede earlier generic projections, without discarding either" [1,0] ordered

groundActivationAlternatives :: Assertion
groundActivationAlternatives = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        producer = Reference.ReferenceRule 2 (Semantic.RulePremiseAtom <$>
            [row 0 [x,y], row 1 [y], row 0 [x,y]]) (row 2 [x]) Set.empty
        recursive = Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 2 [x])] (row 2 [x]) Set.empty
        facts = [Reference.ReferenceFact (row 0 [a,b]) (referenceSummary origin) | origin <- [0,1]] <>
            [Reference.ReferenceFact (row 1 [b]) (referenceSummary origin) | origin <- [2,3]]
        goal = row 2 [a]
        origins result = Set.fromList [Reference.witnessOrigins summary |
            ((conclusion,summary),_) <- Map.toList (Reference.referenceAnswers result), conclusion == goal]
        registered = Map.fromList [(0,producer),(1,recursive)]
    forM_ [(facts,Set.fromList [0,2]),(reverse facts,Set.fromList [1,3])] \(ordered,selected) -> do
        result <- runProductionRules registered ordered goal
        origins result @?= Set.singleton selected
    (missing,_) <- runReferenceCase [producer,recursive] (take 2 facts) goal
    origins missing @?= Set.empty

-- Duplicate eligible proofs do not prolong saturation or multiply joins.
-- Timing is diagnostic, never a noisy assertion.
calibratedFailureAllowance :: Assertion
calibratedFailureAllowance = do
    fixture <- makeFixture 19
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        rule premises conclusion = Reference.ClassificationRule
            (Reference.ReferenceRule 1 (Semantic.RulePremiseAtom <$> premises) conclusion Set.empty)
        registrations = Map.fromList
            [ (0, rule [row index x | index <- [0..15]] (row 16 x))
            , (1, rule [row 16 x, row 17 x] (row 18 x))
            ]
        facts = [Reference.ReferenceFact (row index a) (referenceSummary (2 * index + alternative))
            | index <- [0..15], alternative <- [0,1]]
        goal = row 18 a
        allowance = fromIntegral (Notion.formationInferenceWorkRemaining
            (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits))
        run limit sources = Reference.runReference limit
            (Production.evaluateProduction (Production.freeTermsMayAgree (Reference.chargeReferenceWork . fromIntegral))
                pure (\left right -> pure (left == right)) registrations sources Set.empty goal)
    started <- Clock.getMonotonicTimeNSec
    let (missing, smallWork) = run allowance []
    result <- expectRight missing
    assertReferenceAnswer "an unsupported goal reaches a fixed point" False goal result
    assertEqual "increasing the allowance does not extend a saturated miss"
        (missing, smallWork) (run 131072 [])
    saturated <- Clock.getMonotonicTimeNSec
    diagnostic <- Environment.lookupEnv "FELIX_NOTION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("saturated miss: work=" <> show smallWork
        <> " ns=" <> show (saturated - started)))
    forM_ [131072, allowance] \limit -> do
        before <- Clock.getMonotonicTimeNSec
        let (unresolved, spent) = run limit facts
        completed <- expectRight unresolved
        assertReferenceAnswer "a missing premise stays absent despite duplicate proofs" False goal completed
        assertBool "duplicate proofs leave saturation inexpensive" (spent < 131072)
        run spent facts @?= (unresolved,spent)
        fst (run (spent-1) facts) @?= Left Reference.ReferenceWorkExhausted
        stopped <- Clock.getMonotonicTimeNSec
        when (isJust diagnostic) (putStrLn ("duplicate proof control: cap=" <> show limit
            <> " work=" <> show spent <> " ns=" <> show (stopped - before)))

fineGroundBuckets :: Assertion
fineGroundBuckets = do
    fixture <- makeFixture 2
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        value = Semantic.TemplateVariable :: Natural -> Semantic.SetTermTemplate Natural
        goal = row 1 [value 0, value 1]
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        run population allowance = Reference.runReference allowance $ State.runStateT (do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
                [Semantic.RulePremiseAtom (row 0 [x]), Semantic.RulePremiseAtom (row 0 [y])] (row 1 [x,y]))
            snapshot <- admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature goal) (Map.singleton 0 rule))
            let count (Diagnostics.Count operation amount) = State.modify' (Diagnostics.countOperation operation amount)
                count _ = pure ()
                owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
                    (const (pure ())) count (\_ _ -> pure (Just (population, ())))
                    (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 0 [value index])) index Join.SourceRow ()
                    | index <- [0..population-1]]
            (result, _) <- admit (Evaluation.evaluateRules owner snapshot facts [] goal)
            pure (Relational.relationalRootAnswers result)) Diagnostics.emptyDiagnostics
    forM_ [2,128,1024] \population -> do
        let observed@(outcome,work) = run population 10000000
        (roots,counts) <- expectRight outcome
        roots @?= Set.singleton population
        Map.lookup Diagnostics.CandidatePair (Diagnostics.operationCounts counts) @?= Just 3
        run population work @?= observed
        fst (run population (work-1)) @?= Left Reference.ReferenceWorkExhausted

deferredJoinAnchors :: Assertion
deferredJoinAnchors = do
    fixture <- makeFixture 5
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        root = row 0 [a]
        rules = [Reference.ReferenceRule 2 (Semantic.RulePremiseAtom <$>
                    [row 1 [x],row 2 [x,y],row 3 [x,y]]) (row 0 [x]) Set.empty,
                 Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 3 [x,y])] (row 1 [x]) Set.empty,
                 Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 4 [y])] (row 3 [x,y]) Set.empty]
        facts = [Reference.ReferenceFact (row 2 [a,b]) (referenceSummary 0),
                 Reference.ReferenceFact (row 4 [b]) (referenceSummary 1)]
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
    -- The Q(a,?) request cannot use S(b) without an anchor. T(a,b) must
    -- first supply b, after which the Q(a,b) demand unlocks the ground P(a).
    (reference,_) <- runReferenceCase rules facts root
    assertReferenceAnswer "the independent calculus admits this derivation" True root reference
    catalog <- expectRight (fst (Reference.runReference 1000000 do
        entries <- traverse (\rule -> Rule.RegisteredClassification <$> admit (Rule.compileRule charge
            (Reference.referenceRuleArity rule) (Reference.referenceRulePremises rule)
            (Reference.referenceRuleConclusion rule))) rules
        Catalog.insertRules charge [((),entry) | entry <- entries] Catalog.emptyCatalog))
    let run allowance = Reference.runReference allowance do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (const (pure ())) (const (pure ()))
                    (\ordinal _ -> pure (Just (ordinal,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
                initial = [Evaluation.RuleAnswer (Semantic.AtomicLeaf factRow) (10+index) Join.SourceRow ()
                    | (index,Reference.ReferenceFact factRow _) <- zip [0..] facts]
            outcome <- admit (Evaluation.solveCatalogRules owner catalog initial [] root
                (admit (Catalog.selectSnapshot charge (Rule.atomSignature root) catalog)))
            pure (case outcome of
                Evaluation.FoundAnswer _ -> False
                Evaluation.SearchAnswers answers _ -> not (Set.null (Relational.relationalRootAnswers answers)))
        observed@(result,used) = run 100000
    result @?= Right True
    run used @?= observed
    fst (run (used-1)) @?= Left Reference.ReferenceWorkExhausted

determinedProducerLocality :: Assertion
determinedProducerLocality = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        value = referenceSeed 0
        goal = row 0 [value]
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build population = Reference.runReference 10000000 do
            discovering <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
                [Semantic.RulePremiseAtom (row 2 [x,y])] (row 0 [x]))
            determined <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row 1 [x])] (row 0 [x]))
            Catalog.insertRules charge (replicate population ((),discovering) <> [((),determined)]) Catalog.emptyCatalog
        run allowance catalog = Reference.runReference allowance $ State.runStateT (do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) (lift . charge) pure (const (pure ()))
                    (\case Diagnostics.Count operation amount -> State.modify' (Diagnostics.countOperation operation amount); _ -> pure ())
                    (\ordinal _ -> pure (Just (ordinal,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 1 [value])) 10000 Join.SourceRow ()]
            Evaluation.solveCatalogRules owner catalog facts [] goal
                (lift (admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog)))) Diagnostics.emptyDiagnostics
    costs <- forM [16,256] \population -> do
        catalog <- expectRight (fst (build population))
        let (result,used) = run 100000 catalog
        (outcome,counts) <- expectRight result
        case outcome of
            Right (Evaluation.SearchAnswers answers _) ->
                Relational.relationalRootAnswers answers @?= Set.singleton (fromIntegral population)
            _ -> assertFailure "determined classification did not answer the request"
        Map.lookup Diagnostics.AttemptedProducer (Diagnostics.operationCounts counts) @?= Just 1
        -- The complete candidate count is retained, not relabelled as one.
        Map.lookup Diagnostics.SelectedProducer (Diagnostics.operationCounts counts) @?= Just (fromIntegral population+1)
        _ <- expectRight (fst (run used catalog))
        case fst (run (used-1) catalog) of
            Left Reference.ReferenceWorkExhausted -> pure ()
            _ -> assertFailure "one-short producer selection escaped its allowance"
        selected <- expectRight (fst (Reference.runReference 100000 (Catalog.matchingRules charge goal catalog)))
        fmap fst selected @?= fromIntegral population : [0..fromIntegral population-1]
        pure used
    case costs of
        [small,large] -> assertBool "candidate population is not scanned before the local answer"
            (large < small+250)
        _ -> assertFailure "producer scaling fixture lost a population"
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("determined producer locality (16,256 alternatives): " <> show costs))

anchoredProducerLocality :: Assertion
anchoredProducerLocality = do
    fixture <- makeFixture 4
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        goal = row 0 [a]
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build population = Reference.runReference 10000000 do
            determined <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row 1 [x])] (row 0 [x]))
            discovering <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
                [Semantic.RulePremiseAtom (row 2 [x,y]),Semantic.RulePremiseAtom (row 3 [x])] (row 0 [x]))
            Catalog.insertRules charge (replicate population ((),determined) <> [((),discovering)]) Catalog.emptyCatalog
        run allowance guarded catalog = Reference.runReference allowance $ State.runStateT (do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) (lift . charge) pure (const (pure ()))
                    (\case Diagnostics.Count operation amount -> State.modify' (Diagnostics.countOperation operation amount); _ -> pure ())
                    (\ordinal _ -> pure (Just (ordinal,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 2 [a,b])) 10000 Join.SourceRow () :
                    [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 3 [a])) 10001 Join.SourceRow () | guarded]
            outcome <- Evaluation.solveCatalogRules owner catalog facts [] goal
                (lift (admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog)))
            pure (case outcome of
                Right (Evaluation.SearchAnswers answers _) -> not (Set.null (Relational.relationalRootAnswers answers))
                _ -> False)) Diagnostics.emptyDiagnostics
        collect cursor = Catalog.nextCandidateRule charge cursor >>= \case
            Nothing -> pure []
            Just ((ordinal,_),rest) -> (ordinal:) <$> collect rest
    costs <- forM [16,256] \population -> do
        catalog <- expectRight (fst (build population))
        let observed@(result,used) = run 100000 True catalog
        (success,counts) <- expectRight result
        assertBool "anchored discovery supplies a founded answer" success
        Map.lookup Diagnostics.AttemptedProducer (Diagnostics.operationCounts counts) @?= Just 1
        Map.lookup Diagnostics.SelectedProducer (Diagnostics.operationCounts counts) @?= Just (fromIntegral population+1)
        run used True catalog @?= observed
        fst (run (used-1) True catalog) @?= Left Reference.ReferenceWorkExhausted
        selected <- expectRight (fst (Reference.runReference 100000 do
            cursor <- Catalog.matchingActivatedPatternRules charge (Set.singleton (Rule.atomSignature (row 2 [a,b])))
                (fmap (fmap Pattern.Pinned) goal) catalog
            collect cursor))
        selected @?= fromIntegral population : [0..fromIntegral population-1]
        pure used
    case costs of
        [small,large] -> assertBool "active-row selection does not scan unrelated determined producers" (large < small+250)
        _ -> assertFailure "anchored scaling fixture lost a population"
    catalog <- expectRight (fst (build 16))
    (success,_) <- expectRight (fst (run 100000 False catalog))
    assertBool "a source-head hint cannot supply a missing guard" (not success)
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("anchored producer locality (16,256 alternatives): " <> show costs))

nestedProducerLocality :: Assertion
nestedProducerLocality = do
    fixture <- makeFixture 2
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        goal = row 0 (power (power a))
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build population = Reference.runReference 10000000 do
            generic <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row 1 x)] (row 0 (power x)))
            specific <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row 1 x)] (row 0 (power (power x))))
            Catalog.insertRules charge (replicate population ((),generic) <> [((),specific)]) Catalog.emptyCatalog
        run allowance catalog = Reference.runReference allowance $ State.runStateT (do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) (lift . charge) pure (const (pure ()))
                    (\case Diagnostics.Count operation amount -> State.modify' (Diagnostics.countOperation operation amount); _ -> pure ())
                    (\ordinal _ -> pure (Just (ordinal,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
            outcome <- Evaluation.solveCatalogRules owner catalog [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 1 a)) 10000 Join.SourceRow ()] [] goal
                (lift (admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog)))
            pure (case outcome of
                Right (Evaluation.SearchAnswers answers _) -> not (Set.null (Relational.relationalRootAnswers answers))
                _ -> False)) Diagnostics.emptyDiagnostics
    costs <- forM [16,256] \population -> do
        catalog <- expectRight (fst (build population))
        let observed@(result,used) = run 100000 catalog
        (success,counts) <- expectRight result
        assertBool "the nested result is proved" success
        Map.lookup Diagnostics.AttemptedProducer (Diagnostics.operationCounts counts) @?= Just 1
        Map.lookup Diagnostics.SelectedProducer (Diagnostics.operationCounts counts) @?= Just (fromIntegral population+1)
        run used catalog @?= observed
        fst (run (used-1) catalog) @?= Left Reference.ReferenceWorkExhausted
        selected <- expectRight (fst (Reference.runReference 100000 (Catalog.matchingRules charge goal catalog)))
        fmap fst selected @?= fromIntegral population : [0..fromIntegral population-1]
        pure used
    case costs of
        [small,large] -> assertBool "outer-wrapper alternatives are not scanned" (large < small+250)
        _ -> assertFailure "nested scaling fixture lost a population"
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("nested producer locality (16,256 alternatives): " <> show costs))

groundedJoinLocality :: Assertion
groundedJoinLocality = do
    fixture <- makeFixture 129
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        value = Semantic.TemplateVariable (0 :: Natural)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build width = Reference.runReference 1000000 do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row index x) | index <- [1..width]] (row 0 x))
            Catalog.insertRule charge () rule Catalog.emptyCatalog
        run allowance width catalog = Reference.runReference allowance $ State.runStateT (do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) (lift . charge) pure (const (pure ()))
                    (\case Diagnostics.Count operation amount -> State.modify' (Diagnostics.countOperation operation amount); _ -> pure ())
                    (\_ _ -> pure (Just (0,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row index value)) index Join.SourceRow () | index <- [1..width]]
                goal = row 0 value
                snapshot = lift (admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog))
            outcome <- Evaluation.solveCatalogRules owner catalog facts [] goal snapshot
            pure (case outcome of
                Right (Evaluation.SearchAnswers result _) -> not (Set.null (Relational.relationalRootAnswers result))
                _ -> False)) Diagnostics.emptyDiagnostics
    for_ [4,16,64,128] \width -> do
        catalog <- expectRight (fst (build width))
        let observed@(result,used) = run 1000000 width catalog
        (success,counts) <- expectRight result
        assertBool "every conjunct is proved" success
        let count operation = Map.findWithDefault 0 operation (Diagnostics.operationCounts counts)
        assertEqual "one delivery per distinct prerequisite" width (count Diagnostics.Delivery)
        assertEqual "one prepared ground instance" 1 (count Diagnostics.GroundInstance)
        assertEqual "one preparation per premise" width (count Diagnostics.PreparedGroundPremise)
        assertEqual "one answer tuple" 1 (count Diagnostics.AnswerTuple)
        assertEqual "no equivalent join orders" 0 (count Diagnostics.RepeatedJoin)
        assertEqual "one completed conjunction" 1 (count Diagnostics.CompletedRule)
        run used width catalog @?= observed
        fst (run (used-1) width catalog) @?= Left Reference.ReferenceWorkExhausted
        diagnostic <- Environment.lookupEnv "FELIX_FORMATION_TEST_COST"
        when (isJust diagnostic) (putStrLn ("ground conjunction " <> show width <> ": " <> show used <> " " <> show counts))

demandSelectiveAlternatives :: Assertion
demandSelectiveAlternatives = do
    fixture <- makeFixture 3
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        value = Semantic.TemplateVariable (0 :: Natural)
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        build forward = Reference.runReference 100000 do
            producer <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row 0 x)] (row (if forward then 1 else 2) x))
            rest <- if forward then traverse (\result -> Rule.RegisteredDefinition <$>
                    admit (Rule.compileForwardRule charge 1 (row 1 x) result)) [row 2 x,row 2 (power x)]
                else (:[]) . Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                    [Semantic.RulePremiseAtom (row 0 x)] (row 2 x))
            foldM (\catalog rule -> Catalog.insertRule charge () rule catalog) Catalog.emptyCatalog (producer:rest)
        run allowance forward exhaustive catalog = Reference.runReference allowance do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (const (pure ())) (const (pure ()))
                    (\ordinal _ -> do
                        when (ordinal == if forward then 2 else 1) (charge 10000)
                        pure (Just (ordinal,())))
                    (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 0 value)) 100 Join.SourceRow ()]
                goal = row 2 value
                snapshot = admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog)
            if exhaustive then do
                selected <- snapshot
                (result,_) <- admit (Evaluation.evaluateCatalogRules owner catalog selected facts [] goal)
                pure (not (Set.null (Relational.relationalRootAnswers result)),Relational.relationalSaturated result)
            else admit (Evaluation.solveCatalogRules owner catalog facts [] goal snapshot) >>= \case
                Evaluation.FoundAnswer _ -> Reference.invalidReferenceInput "guarded fixture bypassed tabled search"
                Evaluation.SearchAnswers result _ -> pure
                    (not (Set.null (Relational.relationalRootAnswers result)),Relational.relationalSaturated result)
    for_ [False,True] \forward -> do
        catalog <- expectRight (fst (build forward))
        let observed@(outcome,used) = run 5000 forward False catalog
        outcome @?= Right (True,False)
        run used forward False catalog @?= observed
        fst (run (used - 1) forward False catalog) @?= Left Reference.ReferenceWorkExhausted
        fst (run 5000 forward True catalog) @?= Left Reference.ReferenceWorkExhausted
        fst (run 50000 forward True catalog) @?= Right (True,True)

equalityEndpointDiscovery :: Assertion
equalityEndpointDiscovery = do
    fixture <- makeFixture 3
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        b = referenceSeed 1
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        target = row 0 b
        endpoint = row 0 (power a)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
    catalog <- expectRight (fst (Reference.runReference 100000 do
        producer <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            [Semantic.RulePremiseAtom (row 1 x)] (row 0 (power x)))
        alternative <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            [Semantic.RulePremiseAtom (row 2 x)] (row 0 x))
        Catalog.insertRules charge [((),producer),((),alternative)] Catalog.emptyCatalog))
    let run allowance equality = Reference.runReference allowance do
            let owner = (Production.atomicEvaluator
                    (const (pure Rule.OpenRuleInputs)) charge
                    (pure . fmap (\term -> if equality && term == b then power a else term))
                    (const (pure ())) (const (pure ()))
                    (\_ completed -> pure (Just ((False,Production.completedAtom completed),())))
                    (\requested answer -> pure
                        (if equality && requested == target && Production.atomicAnswer answer == endpoint
                            then Just ((True,target),()) else Nothing))
                    pure
                    (const (pure ())))
                    { Evaluation.ruleHasEqualityTransport = equality
                    , Evaluation.ruleTermsMayAgree = \left right -> do
                        direct <- Production.freeTermsMayAgree charge left right
                        if direct || not equality then pure direct else
                            let normalize term = if term == (Just <$> b) then (Just <$> power a) else term
                            in Production.freeTermsMayAgree charge (normalize left) (normalize right)
                    , Evaluation.ruleOpaqueIsRigid = const (pure (not equality)) }
                initial = Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 1 a)) (False,row 1 a) Join.SourceRow ()
            result <- admit (Evaluation.solveCatalogRules owner catalog [initial] [b,power a] target
                (admit (Catalog.selectSnapshot charge (Rule.atomSignature target) catalog)))
            pure (case result of
                Evaluation.FoundAnswer{} -> True
                Evaluation.SearchAnswers answers _ -> not (Set.null (Relational.relationalRootAnswers answers)))
        observed@(outcome,used) = run 5000 True
    assertEqual "a represented endpoint supplies its checked consequence within the small query allowance" (Right True) outcome
    run used True @?= observed
    fst (run (used-1) True) @?= Left Reference.ReferenceWorkExhausted
    assertEqual "the other scope cannot use an absent equality" (Right False) (fst (run 100000 False))

nestedGuardedFormation :: Assertion
nestedGuardedFormation = do
    fixture <- makeFixture 4
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        closed = Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider Vector.empty
        singleton value = Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider (Vector.singleton value)
        provider index value = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "nested" index)) (Vector.fromList [value,value])
        goal :: Semantic.AtomTemplate (Semantic.SetTermTemplate Natural)
        goal = row 2 (provider 0 (singleton closed))
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        prepare = do
            entries <- traverse (\(arity,premises,result) -> Rule.RegisteredClassification <$>
                admit (Rule.compileRule charge arity premises result))
                ([(0,[],row 0 closed),
                  (1,[Semantic.RulePremiseAtom (row 0 x)],row 1 (singleton x)),
                  (1,[Semantic.RulePremiseAtom (row 1 x)],row 2 (provider 0 x))]
                 <> [(1,[Semantic.RulePremiseAtom (row 3 x)],row 2 (provider index x)) | index <- [1..16]])
            foldM (\catalog entry -> Catalog.insertRule charge () entry catalog) Catalog.emptyCatalog entries
        run allowance catalog tracing = Reference.runReference allowance $ State.runStateT (do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) (lift . charge) pure
                    (\phase -> when tracing (State.modify' (\(phases,counts) -> (phase:phases,counts))))
                    (\case
                        Diagnostics.Count operation amount -> State.modify' (\(phases,counts) ->
                            (phases,Diagnostics.countOperation operation amount counts))
                        _ -> pure ())
                    (\ordinal _ -> pure (Just (ordinal,())))
                    (\_ _ -> pure Nothing) pure (const (pure ()))
                snapshot = lift (admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog))
            outcome <- Evaluation.solveCatalogRules owner catalog [] [] goal snapshot
            pure (case outcome of
                Right Evaluation.FoundAnswer{} -> True
                Right (Evaluation.SearchAnswers result _) -> not (Set.null (Relational.relationalRootAnswers result))
                Left _ -> False)) ([],Diagnostics.emptyDiagnostics)
    catalog <- expectRight (fst (Reference.runReference 1000000 prepare))
    let (observed,cost) = run 1000000 catalog True
        (silent,silentCost) = run 1000000 catalog False
    (success,(phases,counts)) <- expectRight observed
    assertBool "a closed fact supplies a guarded classification and then a guarded result" success
    assertEqual "diagnostics do not consume or reset the account" silentCost cost
    assertEqual "diagnostics do not alter the answer or counters" (Right (success,([],counts))) silent
    let measured operation = Map.findWithDefault 0 operation (Diagnostics.operationCounts counts)
    assertEqual "only compatible producers are attempted" 2 (measured Diagnostics.AttemptedProducer)
    assertEqual "a shared table opens the root and its two prerequisites" 3 (measured Diagnostics.UniqueRequest)
    assertEqual "each guarded dependency is delivered once" 2 (measured Diagnostics.Delivery)
    assertEqual "the closed result and two guarded rules are completed" 3 (measured Diagnostics.CompletedRule)
    assertBool "phase boundaries identify the general support path" ("support-start" `elem` phases)
    assertEqual "exact allowance includes the entire nested query" (observed,cost) (run cost catalog True)
    assertEqual "one-short query remains exhaustion" (Left Reference.ReferenceWorkExhausted)
        (fst (run (cost - 1) catalog True))

seedRuleLocality :: Assertion
seedRuleLocality = do
    fixture <- makeFixture 6
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        ground = Semantic.TemplateVariable (0 :: Natural)
        provider :: Natural -> Semantic.SetTermTemplate variable -> Semantic.SetTermTemplate variable
        provider index value = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (binaryProviderReference "locality" index)) (Vector.fromList [value,value])
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        prepare allowance population = Reference.runReference allowance do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAnd (Semantic.RulePremiseAtom (row 1 variable))
                    (Semantic.RulePremiseAtom (row 0 variable))] (row 2 (provider 0 variable)))
            view <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 0 variable) (row 1 variable))
            initial <- Catalog.insertRule charge () rule Catalog.emptyCatalog >>= Catalog.insertRule charge () view
            foldM (\catalog index -> do
                incompatible <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                    [Semantic.RulePremiseAtom (row 3 variable)] (row 2 (provider index variable)))
                Catalog.insertRule charge () incompatible catalog) initial [1..population]
        query allowance catalog present exhaustive = Reference.runReference allowance do
            let owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (\_ -> pure ()) (\_ -> pure ()) (\ordinal _ -> pure (Just (ordinal + 1,())))
                    (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row 0 ground)) 0 Join.SourceRow () | present]
                goal = row 2 (provider 0 ground)
                snapshot = admit (Catalog.selectSnapshot charge (Rule.atomSignature goal) catalog)
            if exhaustive then do
                selected <- snapshot
                (result,_) <- admit (Evaluation.evaluateRules owner selected facts [] goal)
                pure (not (Set.null (Relational.relationalRootAnswers result)))
            else admit (Evaluation.solveCatalogRules owner catalog facts [] goal snapshot) >>= \case
                Evaluation.FoundAnswer _ -> pure True
                Evaluation.SearchAnswers result _ -> pure (not (Set.null (Relational.relationalRootAnswers result)))
    diagnostic <- Environment.lookupEnv "FELIX_FORMATION_COST"
    small <- expectRight (fst (prepare 10000000 16))
    large <- expectRight (fst (prepare 10000000 256))
    let preparationCost = snd (prepare 10000000 256)
    _ <- expectRight (fst (prepare preparationCost 256))
    case fst (prepare (preparationCost - 1) 256) of
        Left Reference.ReferenceWorkExhausted -> pure ()
        _ -> assertFailure "cold compilation/index preparation escaped its shared account"
    let (first,firstCost) = query 1000000 large True False
        (_,smallCost) = query 1000000 small True False
    when (isJust diagnostic) (putStrLn ("formation locality: preparation=" <> show (snd (prepare 10000000 16),snd (prepare 10000000 256))
        <> " query=" <> show (smallCost,firstCost)))
    assertEqual "first query uses a registered conjunction and initial view" (Right True) first
    assertEqual "no unrelated query is needed to warm simple success" (first,firstCost) (query 1000000 large True False)
    assertBool "incompatible same-head bodies are not traversed" (firstCost < smallCost + 250)
    extended <- expectRight (fst (Reference.runReference 1000000 do
        added <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
            [Semantic.RulePremiseAtom (row 3 variable)] (row 3 (provider 300 variable)))
        Catalog.insertRule charge () added large))
    assertEqual "new registration preserves existing compiled descriptions" (Right True) (fst (query 1000000 extended True False))
    assertBool "invalidation does not recompile or prepare the search population"
        (snd (query 1000000 extended True False) < firstCost + 50)
    cyclic <- expectRight (fst (Reference.runReference 1000000 do
        forward <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 4 variable) (row 5 variable))
        backward <- Rule.RegisteredDefinition <$> admit (Rule.compileForwardRule charge 1 (row 5 variable) (row 4 variable))
        Catalog.insertRule charge () forward small >>= Catalog.insertRule charge () backward))
    assertBool "incremental admission notices a newly closed definition cycle" (not (Catalog.catalogAcyclic cyclic))
    assertEqual "unrelated cycles defer initial completion without invalidating the selected calculus"
        (Right True) (fst (query 1000000 cyclic True False))
    assertEqual "all early work belongs to the request account" (first,firstCost) (query firstCost large True False)
    assertEqual "one-short early completion is exhaustion" (Left Reference.ReferenceWorkExhausted)
        (fst (query (firstCost - 1) large True False))
    forM_ [False,True] \present -> assertEqual "early/fallback agrees with exhaustive support"
        (fst (query 1000000 small present True)) (fst (query 1000000 small present False))

registryReuseScaling :: Assertion
registryReuseScaling = do
    fixture <- makeFixture 130
    let row head' = Semantic.StructureAtomTemplate (fixtureHead fixture head')
            (Vector.singleton (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        describe snapshot = (Map.keys (Rule.snapshotRules snapshot),
            Rule.snapshotHeads snapshot, fst <$> Rule.snapshotForwardOrder snapshot,
            Map.map Map.keys (Rule.snapshotProducers snapshot),
            Map.map Map.keys (Rule.snapshotForwardSources snapshot))
        run allowance population reuse = Reference.runReference allowance do
            entries <- traverse (\index -> Rule.RegisteredDefinition <$> admit
                (Rule.compileForwardRule charge 1 (row index) (row (if index < 2 then index + 1 else index))))
                ([0,1] <> [3..population])
            let registrations = Map.fromDistinctAscList (zip [0..] entries)
            snapshots <- if reuse then do
                registry <- Rule.prepareRuleRegistry charge registrations
                traverse (\head' -> admit (Rule.selectRuleSnapshot charge (Rule.atomSignature (row head')) registry)) [1,2]
              else traverse (\head' -> admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature (row head')) registrations)) [1,2]
            pure (describe <$> snapshots)
        (small, smallCost) = run 1000000 16 True
        (large, largeCost) = run 1000000 128 True
        (smallFresh, smallFreshCost) = run 1000000 16 False
        (largeFresh, largeFreshCost) = run 1000000 128 False
    _ <- expectRight large
    assertEqual "cached and fresh small snapshots agree" smallFresh small
    assertEqual "unrelated cycles do not enter either selected snapshot" small large
    assertEqual "cached and fresh large snapshots agree" largeFresh large
    assertBool "reuse removes population-dependent graph rebuilding"
        (largeFreshCost - largeCost > smallFreshCost - smallCost)
    assertEqual "cold construction and both selections share one allowance"
        (large, largeCost) (run largeCost 128 True)
    assertEqual "one-short remains exhaustion"
        (Left Reference.ReferenceWorkExhausted) (fst (run (largeCost - 1) 128 True))

productionForwardViews :: Assertion
productionForwardViews = do
    fixture <- makeFixture 4
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        rules = Map.fromList [(0,Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 0 x)] (row 1 (power x)) Set.empty),
            (1,Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 1 x)] (row 2 x) Set.empty),
            (2,Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 3 x)] (row 0 x) Set.empty)]
        facts = [Reference.ReferenceFact (row 3 a) (referenceSummary 0)]
        views = Set.fromList [0,1]
    derived <- runProductionWithViews views rules facts (row 2 (power a))
    assertReferenceAnswer "view demand reaches a classification producer" True (row 2 (power a)) derived
    eager <- runProductionWithViews views rules [Reference.ReferenceFact (row 0 a) (referenceSummary 0)] (row 2 (power a))
    assertReferenceAnswer "observed source expands through its selected views" True (row 2 (power a)) eager
    assertReferenceAnswer "classification implication is not reversed" False (row 3 a) eager
    reversed <- runProductionWithViews views rules
        [Reference.ReferenceFact (row 1 (power a)) (referenceSummary 0)] (row 0 a)
    assertReferenceAnswer "view components do not synthesize the source" False (row 0 a) reversed
    let charge = Reference.chargeReferenceWork . fromIntegral
        compile arity source = Reference.runReference 10000
            (Rule.compileForwardRule charge arity source (row 1 x))
    valid <- expectRight =<< expectRight (fst (compile 1 (row 0 x)))
    refused <- expectRight (fst (Reference.runReference 10000
        (Rule.applyForwardRule charge 2 valid Join.ExactAnswer (row 0 a) ())))
    assertEqual "denotation-only evidence does not supply a definition source"
        (Left Join.JoinSourceShapeRequired) refused
    forM_ [2,2 ^ (64 :: Int)] \arity -> do
        invalid <- expectRight (fst (compile arity (row 0 x)))
        case invalid of
            Left (Join.JoinUndeterminedVariable 1) -> pure ()
            _ -> assertFailure "a forward source must determine every binder without arity-sized allocation"
    invalid <- expectRight (fst (compile 1 (Semantic.MembershipAtomTemplate x x)))
    case invalid of
        Left Join.JoinInvalidForwardSource -> pure ()
        _ -> assertFailure "a definition view needs a named source"

referenceDenotationAnswers :: Assertion
referenceDenotationAnswers = do
    let reference ordinal pattern' = Semantic.globalBindingRef
            (Semantic.declarationSlot preludeModuleName (localDeclarationOrdinal ordinal))
            (Semantic.SemanticExpressionFunction pattern')
        identity = Semantic.GlobalSourceProvider (reference 900
            (Raw.TokenCons (Raw.Word "identity") (Raw.HoleCons Raw.End)))
        identityTerm value = Semantic.TemplateProvider identity (Vector.singleton value)
        tag :: Natural -> Semantic.SetTermTemplate variable
        tag ordinal = Semantic.TemplateProvider
            (Semantic.GlobalSourceProvider (reference (901 + ordinal)
                (Raw.TokenCons (Raw.Word ("tag" <> fromString (show ordinal))) Raw.End))) Vector.empty
        p value = Semantic.MembershipAtomTemplate value (tag 0)
        q value = Semantic.MembershipAtomTemplate value (tag 1)
        t value = Semantic.MembershipAtomTemplate value (tag 2)
        a = Semantic.TemplateVariable (Reference.OpaqueSeed 0)
        b = Semantic.TemplateVariable (Reference.OpaqueSeed 1)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        observed :: Reference.GroundAtom -> Reference.ReferenceFact Natural
        observed row = Reference.ReferenceFact row (Reference.WitnessSummary (Set.singleton 0) Set.empty Set.empty)
        rule arity premises result = Reference.ClassificationRule
            (Reference.ReferenceRule arity (Semantic.RulePremiseAtom <$> premises) result Set.empty)
        meaning :: Reference.GroundTerm -> Either Text Reference.GroundTerm
        meaning = \case
            Semantic.TemplateProvider provider arguments | provider == identity -> case toList arguments of
                [argument] -> meaning argument
                _ -> Left "invalid identity arity"
            Semantic.TemplateProvider provider arguments -> Semantic.TemplateProvider provider <$> traverse meaning arguments
            Semantic.TemplateOrderedPair left right -> Semantic.TemplateOrderedPair <$> meaning left <*> meaning right
            value -> Right value
        run allowance rules facts target = Reference.evaluateFormationWithDenotation meaning allowance rules facts Set.empty target
    let direct = run 1000000 Map.empty [observed (p a)] (p (identityTerm a))
    (_, directResult) <- expectRight (fst direct)
    assertReferenceAnswer "same Core answers a ground provider goal" True (p (identityTerm a)) directResult
    exact <- expectRight (fst (run (snd direct) Map.empty [observed (p a)] (p (identityTerm a))))
    assertEqual "interpreted requests share the exact work account" (fst direct) (Right exact)
    assertEqual "one-short interpreted work is exhaustion" (Left Reference.ReferenceWorkExhausted)
        (fst (run (snd direct - 1) Map.empty [observed (p a)] (p (identityTerm a))))
    let boundedMeaning value = do
            Reference.chargeReferenceWork 1
            case value of
                Semantic.TemplateProvider provider arguments | provider == identity -> case toList arguments of
                    [argument] -> boundedMeaning argument
                    _ -> Reference.invalidReferenceInput "invalid identity arity"
                Semantic.TemplateProvider provider arguments -> Semantic.TemplateProvider provider <$> traverse boundedMeaning arguments
                Semantic.TemplateOrderedPair left right -> Semantic.TemplateOrderedPair <$> boundedMeaning left <*> boundedMeaning right
                leaf -> pure leaf
        shared allowance prefix = Reference.runReference allowance do
            Reference.chargeReferenceWork prefix
            Reference.evaluateFormationReference boundedMeaning Map.empty [observed (p a)] Set.empty (p (identityTerm a))
        qualified = shared 1000000 11
    assertEqual "metering interpretation does not change reference answers" (fst direct) (fst qualified)
    assertBool "recursive interpretation is charged in addition to the caller's work"
        (snd qualified > snd direct + 11)
    assertEqual "all stages complete with their exact combined allowance" qualified
        (shared (snd qualified) 11)
    assertEqual "one-short combined allowance cannot reset at the interpreter boundary"
        (Left Reference.ReferenceWorkExhausted) (fst (shared (snd qualified - 1) 11))
    assertEqual "caller exhaustion prevents starting formation"
        (Left Reference.ReferenceWorkExhausted, 0) (shared 10 11)
    let core = foldr Core.CAnd Core.CTruth (replicate 32 Core.CTruth)
        compareCore allowance = Reference.runReference allowance do
            Reference.chargeReferenceWork 5
            ReferenceImports.equalReferenceCore core core
        comparison = compareCore 1000000
    assertEqual "counted Core equality uses the same denotation meaning" (Right True) (fst comparison)
    assertBool "Core traversal is charged after the caller prefix" (snd comparison > 5)
    assertEqual "Core's remaining allowance convention preserves exact accounting"
        comparison (compareCore (snd comparison))
    assertEqual "Core exhaustion retains its partial work debit"
        (Left Reference.ReferenceWorkExhausted, snd comparison - 1)
        (compareCore (snd comparison - 1))
    let erased = Map.singleton 0 (rule 2 [Semantic.MembershipAtomTemplate x (identityTerm y)] (t x))
    (_, absent) <- expectRight (fst (run 1000000 erased [observed (Semantic.MembershipAtomTemplate a b)] (t a)))
    assertReferenceAnswer "equal denotation cannot recover an unknown provider argument" False (t a) absent
    (_, present) <- expectRight (fst (run 1000000 erased [observed (Semantic.MembershipAtomTemplate a (identityTerm b))] (t a)))
    assertReferenceAnswer "actual provider source structure supplies the argument" True (t a) present
    let acquiring = Map.singleton 0 (rule 2
            [Semantic.MembershipAtomTemplate x (identityTerm x), Semantic.MembershipAtomTemplate x (identityTerm y)] (t x))
    (_, refused) <- expectRight (fst (run 1000000 acquiring [observed (Semantic.MembershipAtomTemplate a a)] (t a)))
    assertReferenceAnswer "the exact ground premise is available" True (Semantic.MembershipAtomTemplate a (identityTerm a)) refused
    assertReferenceAnswer "an exact-only answer cannot supply another premise's unknown argument" False (t a) refused
    let joined = Map.fromList [(0, rule 1 [p x] (q x)), (1, rule 1 [q x, q (identityTerm x)] (t x))]
    (_, promoted) <- expectRight (fst (run 1000000 joined [observed (p a)] (t a)))
    assertReferenceAnswer "ground denotation answers compose through theorem premises" True (t a) promoted
    let key = (q (identityTerm a), Reference.WitnessSummary (Set.singleton 0) (Set.singleton 0) Set.empty)
        retained = Reference.referenceAnswers promoted Map.! key
        alternatives = [Reference.referenceWitnessRecipe witness
            | witness <- Map.elems (Reference.referenceWitnesses promoted)
            , Reference.referenceWitnessAtom witness == fst key
            , Reference.referenceWitnessSummary witness == snd key]
    assertBool "the fixture first observes an exact-only answer"
        (any (\case Reference.SameDenotation{} -> True; _ -> False) alternatives)
    case Reference.referenceWitnessRecipe (Reference.referenceWitnesses promoted Map.! retained) of
        Reference.AppliedRule{} -> pure ()
        _ -> assertFailure "an exact-only answer hid a later source-capable theorem witness"

    let production allowance registrations input goal = Reference.runReference allowance (State.runStateT (do
            let charge = lift . Reference.chargeReferenceWork . fromIntegral
                admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
                intern row exactOnly = do
                    charge 1
                    known <- State.get
                    let rowKey = (row,exactOnly)
                    case Map.lookup rowKey known of
                        Just identifier -> pure (identifier,())
                        Nothing -> do
                            let identifier = fromIntegral (Map.size known) :: Natural
                            State.put (Map.insert rowKey identifier known)
                            pure (identifier,())
                owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge
                    (lift . Semantic.traverseAtomTemplateArguments boundedMeaning) (\_ -> pure ()) (\_ -> pure ())
                    (\_ completed -> Just <$> intern (Production.completedAtom completed) False)
                    (\requested answer -> do
                        expected <- lift (Semantic.traverseAtomTemplateArguments boundedMeaning requested)
                        actual <- lift (Semantic.traverseAtomTemplateArguments boundedMeaning (Production.atomicAnswer answer))
                        if expected == actual then Just <$> intern requested True else pure Nothing)
                    pure
                    (const (pure ()))
                rules = Reference.registrationRule <$> registrations
            compiled <- traverse (\r -> admit (Rule.compileRule charge (Reference.referenceRuleArity r)
                (Reference.referenceRulePremises r) (Reference.referenceRuleConclusion r))) rules
            facts <- forM input \row -> do
                (rowId,()) <- intern row False
                pure (Evaluation.RuleAnswer (Semantic.AtomicLeaf row) rowId Join.SourceRow ())
            snapshot <- admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature goal) (Rule.RegisteredClassification <$> compiled))
            (result, _) <- admit (Evaluation.evaluateRules owner snapshot facts [] goal)
            pure (Relational.relationalRootAnswers result)) Map.empty)
        cases = [(Map.empty,[p a],p (identityTerm a),True),
            (erased,[Semantic.MembershipAtomTemplate a b],t a,True),
            (erased,[Semantic.MembershipAtomTemplate a (identityTerm b)],t a,True),
            (acquiring,[Semantic.MembershipAtomTemplate a a],t a,True),
            (joined,[p a],t a,True)]
    forM_ cases \(rules,facts,target,expected) -> do
        let (outcome,used) = production 1000000 rules facts target
        (roots,_) <- expectRight outcome
        assertEqual "finite instantiation can check exact truth without inverting opaque evidence" expected (not (Set.null roots))
        assertEqual "conversion and publication share exact accounting" (outcome,used) (production used rules facts target)
        assertEqual "one-short conversion is exhaustion" (Left Reference.ReferenceWorkExhausted)
            (fst (production (used - 1) rules facts target))
    (_, retainedRows) <- expectRight (fst (production 1000000 joined [p a] (t a)))
    assertBool "exact-only evidence does not hide later source-capable evidence"
        (Map.member (q (identityTerm a),True) retainedRows && Map.member (q (identityTerm a),False) retainedRows)

checkedRuleSkeleton
    :: Natural -> Semantic.RulePremiseBundles Semantic.RuleTermTemplate
    -> Semantic.AtomTemplate Semantic.RuleTermTemplate -> Either Text Semantic.CheckedNotionRuleSkeleton
checkedRuleSkeleton arity (Semantic.RulePremiseBundles premises) =
    Semantic.checkedNotionRuleSkeleton arity (toList premises)

referenceDeterminationPermutations :: Assertion
referenceDeterminationPermutations = do
    fixture <- makeFixture 4
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        z = Semantic.TemplateVariable (Semantic.ViewVariableIx 2)
        power t = Semantic.TemplateProvider
            (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        atom index terms = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.fromList terms)
        conclusion = atom 3 [x]
        determined arity rows = do
            skeleton <- expectRight (checkedRuleSkeleton arity
                (Semantic.RulePremiseBundles (Semantic.RulePremiseAtom <$> rows)) conclusion)
            let (result, used) = Reference.determinedVariables 10000 skeleton
            known <- expectRight result
            exact <- expectRight (fst (Reference.determinedVariables used skeleton))
            assertEqual "exact allowance retains the same determination" known exact
            assertEqual "one-short is exhaustion, not missing variables"
                (Left Reference.ReferenceWorkExhausted)
                (fst (Reference.determinedVariables (used - 1) skeleton))
            pure known
        xKnown = Set.singleton (Semantic.ViewVariableIx 0)
        xyKnown = Set.fromList [Semantic.ViewVariableIx 0, Semantic.ViewVariableIx 1]
    forM_ (List.permutations [atom 0 [x,y], atom 1 [power x,y]]) \rows ->
        case NonEmpty.nonEmpty rows of
            Nothing -> assertFailure "empty permutation"
            Just premises -> determined 2 premises >>= assertEqual "F2 determines y in either order" xyKnown
    -- A second output becomes available in a later fixed-point round even if
    -- its row occurs first. A third guard can then be reconstructed from x,z.
    forM_ (List.permutations [atom 0 [x,y], atom 1 [y,z], atom 2 [power x,power z]]) \rows ->
        case NonEmpty.nonEmpty rows of
            Nothing -> assertFailure "empty permutation"
            Just premises -> determined 3 premises >>= assertEqual "anchored closure determines all outputs"
                (Set.fromList [Semantic.ViewVariableIx i | i <- [0..2]])
    let empty = Semantic.TemplateProvider
            (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
    determined 2 (atom 0 [empty] :| [atom 1 [empty,y]]) >>= assertEqual
        "a closed proved guard can anchor a later row" xyKnown
    determined 2 (atom 0 [y] :| []) >>= assertEqual "a predicate head is not an anchor" xKnown
    determined 3 (atom 0 [y,z] :| [atom 1 [z,y]]) >>= assertEqual "an unanchored cycle determines nothing" xKnown

referenceFrozenSupport :: Assertion
referenceFrozenSupport = do
    let leaf i = Semantic.TemplateVariable (Reference.OpaqueSeed i)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        power t = Semantic.TemplateProvider
            (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        empty = Semantic.TemplateProvider
            (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        pair = Semantic.TemplateOrderedPair
        seeds = Set.fromList [leaf 0, leaf 1]
        templates = Set.fromList [power x, pair x x, pair x y, empty]
        (result, used) = Reference.enumerateSupport 10000 seeds templates
    support <- expectRight result
    assertEqual "support preserves the original assignment seeds" seeds (Reference.referenceSeeds support)
    assertEqual "empty substitution admits a closed provider"
        (Set.fromList ([leaf 0,leaf 1,empty,power (leaf 0),power (leaf 1)]
            <> [pair (leaf i) (leaf j) | i <- [0,1], j <- [0,1]]))
        (Reference.referenceUniverse support)
    assertBool "generated values never seed another template layer"
        (power (power (leaf 0)) `Set.notMember` Reference.referenceUniverse support)
    assertEqual "the query skeleton bound is derived from the finite support" 3
        (Reference.referenceMaximumTermSize support)
    exact <- expectRight (fst (Reference.enumerateSupport used seeds templates))
    assertEqual "exact support budget succeeds" support exact
    assertEqual "one-short support construction is explicitly exhausted"
        (Left Reference.ReferenceWorkExhausted)
        (fst (Reference.enumerateSupport (used - 1) seeds templates))
    repeated <- expectRight (fst (Reference.enumerateSupport 10000 seeds (Set.singleton (pair x x))))
    assertBool "repeated variables cannot mix assignments"
        (pair (leaf 0) (leaf 1) `Set.notMember` Reference.referenceUniverse repeated)
    closed <- expectRight (fst (Reference.enumerateSupport 10000 Set.empty (Set.singleton empty)))
    assertEqual "a closed provider does not require an invented seed" (Set.singleton empty)
        (Reference.referenceUniverse closed)
    nested <- expectRight (fst (Reference.enumerateSupport 10000 (Set.singleton (power (leaf 0)))
        (Set.singleton (power x))))
    assertEqual "explicit compound seeds and their safe subterms can be inputs"
        (Set.fromList [leaf 0, power (leaf 0), power (power (leaf 0))])
        (Reference.referenceUniverse nested)

prop_preparedCatalogSupport :: Property
prop_preparedCatalogSupport = property do
    fixture <- evalIO (makeFixture 4)
    descriptions <- forAll (Gen.list (Range.linear 0 7)
        ((,,,,) <$> Gen.integral (Range.linear 0 3) <*> Gen.integral (Range.linear 0 3)
            <*> Gen.integral (Range.linear 0 4) <*> Gen.bool <*> Gen.bool))
    observed <- forAll (Gen.list (Range.linear 0 3)
        ((,) <$> Gen.integral (Range.linear 0 3) <*> Gen.integral (Range.linear 0 2)))
    targetHead <- forAll (Gen.integral (Range.linear 0 3))
    alias <- forAll Gen.bool
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        emptySet :: Semantic.SetTermTemplate variable
        emptySet = Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider Vector.empty
        power :: Semantic.SetTermTemplate variable -> Semantic.SetTermTemplate variable
        power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton value)
        form :: Int -> Semantic.SetTermTemplate variable -> Semantic.SetTermTemplate variable
        form shape value = case shape of
            0 -> value
            1 -> power value
            2 -> Semantic.TemplateOrderedPair value value
            3 -> power emptySet
            _ -> Semantic.TemplateClosed (closedFixtureValue closedFixtureComprehension)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        registration (result,source,shape,closed,view)
            | closed = Reference.ClassificationRule (Reference.ReferenceRule 0 [] (row result (form shape emptySet)) Set.empty)
            | otherwise = (if view && source < result then Reference.DefinitionRule else Reference.ClassificationRule)
                (Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row source x)] (row result (form shape x)) Set.empty)
        registrations = Map.fromList (zip [0..] (registration <$> descriptions))
        facts = [Reference.ReferenceFact (row head' (form shape emptySet)) (referenceSummary ordinal)
            | (ordinal,(head',shape)) <- zip [0..] observed]
        aliases = if alias then Set.singleton (referenceSeed 1) else Set.empty
        target = row targetHead emptySet
        charge = Reference.chargeReferenceWork . fromIntegral
    snapshot <- evalEither (fst (Reference.prepareReferenceSnapshot 10000000 registrations facts aliases target))
    let expected = Reference.referenceSnapshotSupport snapshot
        requests = Set.toAscList (Reference.referenceUniverse expected) <>
            [power (power (power (power emptySet))), Semantic.TemplateOrderedPair (referenceSeed 0) (referenceSeed 1)]
        run allowance entries = Reference.runReference allowance do
            (support,initial,counts) <- Production.prepareProductionSupport entries facts aliases target
            (answers,final) <- foldM (\(answers,current) term -> do
                (present,next) <- Support.symbolicSupportContains charge term current
                pure (present:answers,next)) ([],support) (requests <> reverse requests)
            pure (reverse answers,Support.symbolicSupportMaximumTermSize final,Set.fromList initial,counts)
        (outcome,used) = run 10000000 registrations
    result <- evalEither outcome
    result === ((`Set.member` Reference.referenceUniverse expected) <$> (requests <> reverse requests),
        Reference.referenceMaximumTermSize expected,
        Set.fromList (Reference.referenceWitnessAtom <$> Map.elems
            (Reference.referenceWitnesses (Reference.referenceSnapshotInitial snapshot))),
        Rule.SnapshotCounts (fromIntegral (Map.size (Reference.referenceSnapshotRules snapshot)))
            (fromIntegral (sum (length . Reference.referenceRulePremises <$> Map.elems (Reference.referenceSnapshotRules snapshot))))
            (fromIntegral (length (Reference.referenceSnapshotViews snapshot))))
    run used registrations === (outcome,used)
    fst (run (used - 1) registrations) === Left Reference.ReferenceWorkExhausted
    fst (run 10000000 (Map.fromList (zip [0..] (reverse (Map.elems registrations))))) === outcome

prop_symbolicSupport :: Property
prop_symbolicSupport = property do
    let power :: Semantic.SetTermTemplate variable -> Semantic.SetTermTemplate variable
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton t)
        emptySet :: Semantic.SetTermTemplate variable
        emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        termGen :: Int -> Gen variable -> Gen (Semantic.SetTermTemplate variable)
        termGen depth variable = Gen.choice
            ([Semantic.TemplateVariable <$> variable, pure emptySet,
                pure (Semantic.TemplateClosed (closedFixtureValue (Core.COpaqueInteger 7))),
                pure (Semantic.TemplateClosed (closedFixtureValue closedFixtureComprehension))] <>
                if depth == 0 then [] else
                    [power <$> termGen (depth - 1) variable,
                     Semantic.TemplateOrderedPair <$> termGen (depth - 1) variable <*> termGen (depth - 1) variable])
    seeds <- forAll (Gen.list (Range.linear 0 3)
        (termGen 1 (Reference.OpaqueSeed <$> Gen.integral (Range.linear 0 1))))
    templates <- forAll (Gen.list (Range.linear 0 3)
        (termGen 2 (Semantic.ViewVariableIx <$> Gen.integral (Range.linear 0 1))))
    extra <- forAll (Gen.list (Range.linear 0 4)
        (termGen 3 (Reference.OpaqueSeed <$> Gen.integral (Range.linear 0 2))))
    let patternTerm = termGen 3 (Gen.choice
            [Pattern.Pinned . Reference.OpaqueSeed <$> Gen.integral (Range.linear 0 2),
             Pattern.Output <$> Gen.integral (Range.linear 0 3)])
    requested <- forAll (Semantic.MembershipAtomTemplate <$> patternTerm <*> patternTerm)
    otherPattern <- forAll (Semantic.MembershipAtomTemplate <$> patternTerm <*> patternTerm)
    explicit <- evalEither (fst (Reference.enumerateSupport 10000000 (Set.fromList seeds) (Set.fromList templates)))
    let queries = Set.toList (Reference.referenceUniverse explicit) <> extra
        -- Include repeated positive and negative queries. Interning a rejected
        -- value must neither seed later construction nor change the fixed bound.
        requests = queries <> reverse queries
        expected = (`Set.member` Reference.referenceUniverse explicit) <$> requests
        runWith supplied approved allowance = Reference.runReference allowance do
            let charge = Reference.chargeReferenceWork . fromIntegral
                (first,rest) = splitAt (length approved `div` 2) approved
            -- Incremental catalogue preparation, including repeated syntax,
            -- must preserve the same one-layer domain as the independent
            -- enumerator. Freezing owns only the actual ground seeds.
            prepared <- Support.prepareTemplateSupport charge first >>=
                Support.extendTemplateSupport charge (rest <> first)
            initial <- Support.freezeSupport charge supplied prepared
            (reversed, final) <- foldM (\(answers, support) term -> do
                (present, next) <- Support.symbolicSupportContains charge term support
                pure (present : answers, next)) ([], initial) requests
            pure (reverse reversed, Support.symbolicSupportMaximumTermSize final)
        run = runWith seeds templates
        (outcome, used) = run 10000000
    actual <- evalEither outcome
    actual === (expected, Reference.referenceMaximumTermSize explicit)
    fst (runWith (reverse seeds) (reverse templates) 10000000) === outcome
    run used === (outcome, used)
    fst (run (used - 1)) === Left Reference.ReferenceWorkExhausted
    let toReference = fmap (fmap (\case
            Pattern.Pinned seed -> Reference.Pin seed
            Pattern.Output index -> Reference.Hole index))
        normalize allowance request = Reference.runReference allowance do
            let charge = Reference.chargeReferenceWork . fromIntegral
            support <- Support.buildSymbolicSupport charge seeds templates
            fmap (Pattern.canonicalPatternAtom . fst) <$> Pattern.normalizeFormationPattern charge support request
        (normalized, normalizationWork) = normalize 10000000 requested
    accepted <- evalEither normalized
    expectedPattern <- evalEither (fst (Reference.runReference 10000000
        (Reference.normalizeRequest explicit (toReference requested))))
    case accepted of
        Right canonical -> Just (toReference canonical) === expectedPattern
        Left _ -> case expectedPattern of
            Nothing -> pure ()
            Just _ -> do
                -- The stricter partial filter may reject the old size-only
                -- policy, but only if an argument has no ground completion.
                let compatible (Semantic.TemplateVariable Pattern.Output{}) _ = True
                    compatible (Semantic.TemplateVariable (Pattern.Pinned a)) (Semantic.TemplateVariable b) = a == b
                    compatible (Semantic.TemplateClosed a) (Semantic.TemplateClosed b) = a == b
                    compatible (Semantic.TemplateProvider a xs) (Semantic.TemplateProvider b ys) =
                        a == b && length xs == length ys && and (zipWith compatible (toList xs) (toList ys))
                    compatible (Semantic.TemplateOrderedPair a b) (Semantic.TemplateOrderedPair c d) = compatible a c && compatible b d
                    compatible _ _ = False
                    universe = Set.toList (Reference.referenceUniverse explicit)
                any (\term -> not (any (compatible term) universe)) (toList requested) === True
    normalize normalizationWork requested === (normalized, normalizationWork)
    fst (normalize (normalizationWork - 1) requested) === Left Reference.ReferenceWorkExhausted
    let renamed = fmap (fmap (\case
            Pattern.Pinned seed -> Pattern.Pinned seed
            Pattern.Output index -> Pattern.Output (index + 100))) requested
    fst (normalize 10000000 renamed) === normalized
    case accepted of
        Left _ -> pure ()
        Right canonical -> fst (normalize 10000000 canonical) === normalized
    let interning allowance = Reference.runReference allowance do
            let charge = Reference.chargeReferenceWork . fromIntegral
            support <- Support.buildSymbolicSupport charge seeds templates
            Request.internRequest charge requested (Request.emptyRequestTable support) >>= \case
                Left rejected -> pure (Left rejected)
                Right (identifier, table) -> Request.internRequest charge renamed table >>= \case
                    Left rejected -> pure (Left rejected)
                    Right (same, final) -> pure (Right (identifier == same,
                        (\case Semantic.AtomicLeaf pattern' -> Just (Pattern.canonicalPatternAtom pattern'); Semantic.WholeLeaf{} -> Nothing)
                            =<< Request.lookupRequest identifier final))
        (interned, interningWork) = interning 10000000
    indexed <- evalEither interned
    indexed === fmap (\canonical -> (True, Just canonical)) accepted
    interning interningWork === (interned, interningWork)
    fst (interning (interningWork - 1)) === Left Reference.ReferenceWorkExhausted
    let unifying allowance = Reference.runReference allowance do
            let charge = Reference.chargeReferenceWork . fromIntegral
            Unification.unifyPatterns charge Unification.emptySubstitution requested otherPattern >>= traverse (\substitution ->
                (,) <$> Unification.applyPatternSubstitution charge 1000000 substitution requested
                    <*> Unification.applyPatternSubstitution charge 1000000 substitution otherPattern)
        (unified, unificationWork) = unifying 10000000
    actualUnification <- evalEither unified
    expectedUnification <- evalEither (fst (Reference.runReference 10000000 do
        Reference.unifyAtoms Map.empty (toReference requested) (toReference otherPattern) >>= traverse (\substitution ->
            (,) <$> Reference.applyAtom substitution (toReference requested)
                <*> Reference.applyAtom substitution (toReference otherPattern))))
    fmap (\(left,right) -> (fmap toReference left,fmap toReference right)) actualUnification
        === fmap (\(left,right) -> (Right left,Right right)) expectedUnification
    unifying unificationWork === (unified, unificationWork)
    fst (unifying (unificationWork - 1)) === Left Reference.ReferenceWorkExhausted

formationRuleCompletion :: Assertion
formationRuleCompletion = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        variable = Semantic.TemplateVariable . Semantic.ViewVariableIx
        pin = Semantic.TemplateVariable . Pattern.Pinned . Reference.OpaqueSeed
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        headers = [Semantic.RulePremiseAnd (Semantic.RulePremiseAtom (row 0 [variable 0,variable 1]))
            (Semantic.RulePremiseAtom (row 1 [power (variable 0),variable 1]))]
        conclusion = row 2 [variable 0]
        facts = [Reference.ReferenceFact (row 0 [referenceSeed 0,referenceSeed 1]) (referenceSummary 0),
            Reference.ReferenceFact (row 1 [power (referenceSeed 0),referenceSeed 1]) (referenceSummary 1)]
        charge = Reference.chargeReferenceWork . fromIntegral
        admitted action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        required = maybe (Reference.invalidReferenceInput "expected rule state or completion") pure
        run allowance order = Reference.runReference allowance do
            support <- Support.buildSymbolicSupport charge [referenceSeed 0,referenceSeed 1] [power (variable 0)]
            (target, _) <- admitted (Pattern.normalizeFormationPattern charge support (row 2 [pin 0]))
            rule <- admitted (Rule.compileRule charge 2 headers conclusion)
            initial <- required =<< admitted (Rule.startRule charge 2 rule target)
            pending <- admitted (Rule.finishRule charge 2 initial)
            final <- foldM (\state position -> do
                options <- Rule.ruleOptions charge 2 state
                waiting <- admitted (required (List.lookup position options))
                let Reference.ReferenceFact fact _ = facts !! fromIntegral position
                required =<< admitted (Rule.resumeRule charge Join.SourceRow waiting fact (Reference.WitnessId position))) initial order
            completed <- required =<< admitted (Rule.finishRule charge 2 final)
            pure (isNothing pending, completed)
        registered = Map.singleton 0 (Reference.ReferenceRule 2 headers conclusion Set.empty)
        tree = \case
            Composite.CompositePremiseTruth -> error "atomic reference received neutral premise"
            Composite.CompositePremiseLeaf witness -> Reference.PremiseLeaf witness
            Composite.CompositePremiseAnd left right -> Reference.PremiseConjunction (tree left) (tree right)
    forM_ [[0,1],[1,0]] \order -> do
        let (outcome, used) = run 100000 order
        (pending, completed) <- expectRight outcome
        assertBool "a matching conclusion cannot bypass pending premises" pending
        let instantiated = Rule.completedInstantiation completed
            goal = Production.completedAtom completed
            summary = Reference.WitnessSummary (Set.fromList [0,1]) (Set.singleton 0) Set.empty
            observed = [(Reference.WitnessId index, Reference.ReferenceWitness fact origin (Reference.ObservedRow index))
                | (index, Reference.ReferenceFact fact origin) <- zip [0..] facts]
            derived = Reference.ReferenceWitness goal summary
                (Reference.AppliedRule 0 (Rule.ruleBinderValues instantiated) (tree <$> Rule.completedPremises completed))
            witnesses = Map.fromList (observed <> [(Reference.WitnessId 2,derived)])
            evaluation = Reference.ReferenceEvaluation Set.empty
                (Map.fromList [((Reference.referenceWitnessAtom witness,Reference.referenceWitnessSummary witness),identifier)
                    | (identifier,witness) <- Map.toList witnesses]) witnesses Set.empty
        assertEqual "the selected result is instantiated from acquired rows" (row 2 [referenceSeed 0]) goal
        checkReferenceWitnesses registered facts evaluation
        ReferenceReplay.checkReferenceReplay registered facts evaluation
        assertEqual "rule ownership and completion share the exact allowance" (outcome,used) (run used order)
        assertEqual "one-short completion exhausts" (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1) order))
    let emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        closedGoal = row 2 [emptySet]
        closed :: Natural -> (Either Reference.ReferenceFailure (Either Join.JoinFailure
            (Maybe (Rule.CompletedRule Reference.OpaqueSeed Reference.WitnessId))), Word)
        closed arity = Reference.runReference 10000 do
            support <- Support.buildSymbolicSupport charge ([] :: [Reference.GroundTerm]) [emptySet]
            (target, _) <- admitted (Pattern.normalizeFormationPattern charge support closedGoal)
            Rule.compileRule charge arity [] closedGoal >>= \case
                Left failure -> pure (Left failure)
                Right rule -> do
                    initial <- required =<< admitted (Rule.startRule charge 1 rule target)
                    Rule.finishRule charge 1 initial
    absent <- expectRight (fst (closed (2 ^ (64 :: Int))))
    assertEqual "completion does not allocate an arity-sized range or guess binders"
        (Left (Join.JoinUndeterminedVariable 0)) (fmap (fmap (Rule.ruleBinderValues . Rule.completedInstantiation)) absent)
    completed <- expectJust =<< expectRight =<< expectRight (fst (closed 0))
    assertEqual "zero-binder unconditional rules complete without fabricated premises"
        (Rule.CompletedRule (Rule.RuleInstantiation Map.empty (Semantic.AtomicLeaf closedGoal)) []) completed

formationAnchoredJoins :: Assertion
formationAnchoredJoins = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row index = Semantic.StructureAtomTemplate (fixtureHead fixture index) . Vector.fromList
        variable = Semantic.TemplateVariable . Semantic.ViewVariableIx
        output = Semantic.TemplateVariable . Pattern.Output
        pin = Semantic.TemplateVariable . Pattern.Pinned . Reference.OpaqueSeed
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        charge = Reference.chargeReferenceWork . fromIntegral
        required = maybe (Reference.invalidReferenceInput "expected a legal join") pure
        admitted action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        run allowance swapped = Reference.runReference allowance do
            support <- Support.buildSymbolicSupport charge [referenceSeed 0,referenceSeed 1,referenceSeed 2] [power (variable 0)]
            (target, _) <- admitted (Pattern.normalizeFormationPattern charge support (row 2 [pin 0]))
            initial <- required =<< admitted (Join.startJoin charge 2 3 (row 2 [variable 0]) target)
            missing <- Join.prepareJoinPremise charge 2 initial (row 0 [variable 2])
            invalid <- Join.prepareJoinPremise charge 2 initial (row 0 [variable 3])
            let direct = (row 0 [variable 0,variable 1], row 0 [referenceSeed 0,referenceSeed 1], row 0 [referenceSeed 0,referenceSeed 2])
                constructed = (row 1 [power (variable 0),variable 1], row 1 [power (referenceSeed 0),referenceSeed 1], row 1 [power (referenceSeed 0),referenceSeed 2])
                ((first,firstRow,_),(second,secondRow,wrongRow)) = if swapped then (constructed,direct) else (direct,constructed)
            waiting <- admitted (Join.prepareJoinPremise charge 2 initial first)
            exact <- Join.resumeJoinPremise charge Join.ExactAnswer waiting firstRow
            afterFirst <- required =<< admitted (Join.resumeJoinPremise charge Join.SourceRow waiting firstRow)
            remaining <- admitted (Join.prepareJoinPremise charge 2 afterFirst second)
            wrong <- admitted (Join.resumeJoinPremise charge Join.SourceRow remaining wrongRow)
            final <- required =<< admitted (Join.resumeJoinPremise charge Join.ExactAnswer remaining secondRow)
            bindings <- Unification.applyPatternSubstitution charge 2 (Join.joinSubstitution final)
                (Semantic.MembershipAtomTemplate (output 1) (output 2))
            (partial, _) <- admitted (Pattern.normalizeFormationPattern charge support (row 2 [output 0,pin 0]))
            fresh <- required =<< admitted (Join.startJoin charge 2 2 (row 2 [variable 1,variable 0]) partial)
            freshBindings <- Unification.applyPatternSubstitution charge 2 (Join.joinSubstitution fresh)
                (Semantic.MembershipAtomTemplate (output 1) (output 0))
            pure (bindings, freshBindings, either (== Join.JoinSourceShapeRequired) (const False) exact, isNothing wrong,
                either (const False) (not . Join.joinPremiseIsGround) missing,
                either (== Join.JoinInvalidVariable 3) (const False) invalid)
        expected = (Right (Semantic.MembershipAtomTemplate (pin 1) (output 2)),
            Right (Semantic.MembershipAtomTemplate (output 2) (pin 0)), True,True,True,True)
    forM_ [False,True] \swapped -> do
        let (outcome, used) = run 100000 swapped
        actual <- expectRight outcome
        assertEqual "both F2 orders keep full-row correlations, source eligibility, and fresh namespaces" expected actual
        assertEqual "activation and both joins share an exact account" (outcome,used) (run used swapped)
        assertEqual "one-short anchored join work is exhaustion" (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1) swapped))
    closed <- expectRight (fst (Reference.runReference 100000 do
        let emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        support <- Support.buildSymbolicSupport charge [referenceSeed 1] [emptySet]
        (target, _) <- admitted (Pattern.normalizeFormationPattern charge support (row 2 [emptySet]))
        initial <- required =<< admitted (Join.startJoin charge 1 1 (row 2 [emptySet]) target)
        waiting <- admitted (Join.prepareJoinPremise charge 1 initial (row 0 [emptySet,variable 0]))
        final <- required =<< admitted (Join.resumeJoinPremise charge Join.SourceRow waiting (row 0 [emptySet,referenceSeed 1]))
        Unification.applyPatternSubstitution charge 1 (Join.joinSubstitution final) (row 2 [output 0])))
    assertEqual "a shared nullary provider is an anchor even without a pinned leaf" (Right (row 2 [pin 1])) closed

formationUnificationBoundaries :: Assertion
formationUnificationBoundaries = do
    let output :: Natural -> Semantic.SetTermTemplate (Pattern.PatternVariable Reference.OpaqueSeed)
        output = Semantic.TemplateVariable . Pattern.Output
        pin = Semantic.TemplateVariable . Pattern.Pinned . Reference.OpaqueSeed
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        pair = Semantic.TemplateOrderedPair
        row = Semantic.MembershipAtomTemplate
        charge = Reference.chargeReferenceWork . fromIntegral
        extend substitution left right = Unification.unifyPatterns charge substitution (row left (pin 0)) (row right (pin 0))
        check action = expectRight (fst (Reference.runReference 10000 action))
    cyclic <- check (Unification.unifyPatterns charge Unification.emptySubstitution
        (row (output 0) (output 1)) (row (power (output 1)) (output 0)))
    assertBool "indirect cyclic output constraints are rejected" (isNothing cyclic)
    fresh <- check (Unification.mayUnifyPartialTerm charge (pair (output 0) (pin 0))
        (pair (Just <$> referenceSeed 1) (Semantic.TemplateVariable Nothing)))
    assertBool "support holes are fresh with respect to request outputs" fresh
    repeated <- check (Unification.mayUnifyPartialTerm charge (pair (output 0) (output 0))
        (pair (Just <$> referenceSeed 0) (Just <$> referenceSeed 1)))
    assertBool "a fully specified candidate preserves repeated request slots" (not repeated)
    initial <- expectJust =<< check (extend Unification.emptySubstitution (output 0) (pin 0))
    joined <- expectJust =<< check (Unification.matchCompleteRow charge initial
        (row (output 0) (output 1)) (row (referenceSeed 0) (referenceSeed 1)))
    mismatch <- check (Unification.matchCompleteRow charge joined
        (row (power (output 0)) (output 1)) (row (power (referenceSeed 0)) (referenceSeed 2)))
    assertBool "a later guard cannot replace an already acquired row column" (isNothing mismatch)
    consistent <- expectJust =<< check (Unification.matchCompleteRow charge joined
        (row (power (output 0)) (output 1)) (row (power (referenceSeed 0)) (referenceSeed 1)))
    applied <- check (Unification.applyPatternSubstitution charge 3 consistent (row (output 1) (output 2)))
    assertEqual "complete rows determine their outputs without guessing others" (Right (row (pin 1) (output 2))) applied
    shared <- check do
        chain <- foldM (\pending index -> case pending of
            Nothing -> pure Nothing
            Just substitution -> extend substitution (output index) (pair (output (index + 1)) (output (index + 1))))
            (Just Unification.emptySubstitution) [0..29]
        case chain of
            Nothing -> pure False
            Just substitution -> extend substitution (output 30) (pin 0) >>= \case
                Nothing -> pure False
                Just grounded -> extend grounded (output 31) (output 0) >>= \case
                    Nothing -> pure False
                    Just final -> do
                        expanded <- Unification.applyPatternSubstitution charge 31 final (row (output 31) (pin 0))
                        pure (expanded == Left Pattern.PatternSkeletonExceeded)
    assertBool "binding and occurs checking do not expand a 2^30-node shared substitution" shared

formationRequestIdentity :: Assertion
formationRequestIdentity = do
    fixture <- makeFixture 1
    let pin = Semantic.TemplateVariable . Pattern.Pinned . Reference.OpaqueSeed
        output = Semantic.TemplateVariable . Pattern.Output
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        pair = Semantic.TemplateOrderedPair
        row = Semantic.MembershipAtomTemplate
        requested =
            [row (pin 0) (output 0), row (pin 1) (output 0),
             row (output 0) (output 0), row (output 0) (output 1),
             row (power (pin 0)) (output 0), row (pair (pin 0) (pin 0)) (output 0),
             Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.fromList [pin 0,output 0])]
        action = do
            let charge = Reference.chargeReferenceWork . fromIntegral
            support <- Support.buildSymbolicSupport charge [referenceSeed 0,referenceSeed 1] [power variable,pair variable variable]
            Except.runExceptT do
                (identifiers, table) <- foldM (\(known, current) request -> do
                    (identifier, next) <- Except.ExceptT (Request.internRequest charge request current)
                    pure (identifier : known, next)) ([], Request.emptyRequestTable support) requested
                repeated <- traverse (\request -> fst <$> Except.ExceptT (Request.internRequest charge request table)) requested
                pure (reverse identifiers, repeated)
    (identifiers, repeated) <- expectRight =<< expectRight (fst (Reference.runReference 100000 action))
    assertEqual "different complete constraints receive distinct request IDs" (length requested) (Set.size (Set.fromList identifiers))
    assertEqual "reinterning retains every original identity" identifiers repeated

formationPatternBoundaries :: Assertion
formationPatternBoundaries = do
    fixture <- makeFixture 1
    let variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        pair = Semantic.TemplateOrderedPair
        output = Semantic.TemplateVariable . Pattern.Output
        pin = Semantic.TemplateVariable . Pattern.Pinned . Reference.OpaqueSeed
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        row = Semantic.MembershipAtomTemplate
        normalize seeds templates request = expectRight (fst (Reference.runReference 100000 do
            let charge = Reference.chargeReferenceWork . fromIntegral
            support <- Support.buildSymbolicSupport charge seeds templates
            fmap (Pattern.canonicalPatternAtom . fst) <$> Pattern.normalizeFormationPattern charge support request))
        admitted = normalize [referenceSeed 0] [pair variable variable]
        sparseLabel = 2 ^ (64 :: Int)
    sparse <- admitted (row (pair (output sparseLabel) (output sparseLabel)) (pair (output 7) (output sparseLabel)))
    assertEqual "sparse output labels are canonicalized across the complete atom"
        (Right (row (pair (output 0) (output 0)) (pair (output 1) (output 0)))) sparse
    tooLarge <- admitted (row (power (power (power (output 0)))) (pin 0))
    assertEqual "each output has a one-node lower bound" (Left Pattern.PatternSkeletonExceeded) tooLarge
    outside <- admitted (row (pin 1) (pin 0))
    assertEqual "out-of-support pins remain distinct from oversized syntax" (Left Pattern.PatternOutsideSupport) outside
    let nullary :: Semantic.AtomTemplate (Semantic.SetTermTemplate (Pattern.PatternVariable Reference.OpaqueSeed))
        nullary = Semantic.StructureAtomTemplate (fixtureHead fixture 0) Vector.empty
    closed <- normalize [] [] nullary
    assertEqual "a nullary request does not need an invented support term" (Right nullary) closed

preparedSupportProfiles :: Assertion
preparedSupportProfiles = do
    let power value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton value)
        emptySet = Semantic.TemplateProvider Semantic.FiniteSetLiteralSourceProvider Vector.empty
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        templates = [Semantic.TemplateOrderedPair x x, power (power (power x)),
            Semantic.TemplateOrderedPair x (power emptySet)]
        charge = Reference.chargeReferenceWork . fromIntegral
    for_ [([],[]), ([],templates), ([power emptySet],templates),
            ([power emptySet],[Semantic.TemplateOrderedPair (power emptySet) (power emptySet)])] \(seeds,approved) -> do
        explicit <- expectRight (fst (Reference.enumerateSupport 1000000 (Set.fromList seeds) (Set.fromList approved)))
        prepared <- expectRight (fst (Reference.runReference 1000000
            (Support.prepareTemplateSupport charge approved)))
        let freeze allowance = Reference.runReference allowance do
                support <- Support.freezeSupport charge seeds prepared
                pure (Support.symbolicSupportMaximumTermSize (support :: Support.FrozenSupport Reference.OpaqueSeed))
            (result,used) = freeze 1000000
        result @?= Right (Reference.referenceMaximumTermSize explicit)
        freeze used @?= (result,used)
        fst (freeze (used - 1)) @?= Left Reference.ReferenceWorkExhausted
    -- c and v come from the SAME template; union must not combine the largest
    -- fixed part (3) and occurrence count (2) into the spurious bound 7.
    result <- expectRight (fst (Reference.runReference 1000000 do
        prepared <- Support.prepareTemplateSupport charge templates
        empty <- Support.freezeSupport charge ([] :: [Reference.GroundTerm]) prepared
        populated <- Support.freezeSupport charge [power emptySet :: Reference.GroundTerm] prepared
        pure (Support.symbolicSupportMaximumTermSize empty,Support.symbolicSupportMaximumTermSize populated)))
    result @?= (2,5)
    for_ [[],[x],[power x],templates] \earlier -> do
        (full,incremental,repeated) <- expectRight (fst (Reference.runReference 1000000 do
            (_,prior) <- Support.extendOwnedTemplateSupport charge 0 earlier Support.emptyTemplateSupport
            (_,incoming) <- Support.extendOwnedTemplateSupport charge 1 templates Support.emptyTemplateSupport
            growth <- Support.sizeProfileGrowth charge prior incoming
            full <- Support.unionSizeProfiles charge prior incoming
            incremental <- Support.unionSizeProfiles charge prior growth
            repeated <- Support.sizeProfileGrowth charge full incoming
            pure (full,incremental,repeated)))
        incremental @?= full
        repeated @?= Support.emptySizeProfile

symbolicSupportAvoidsEnumeration :: Assertion
symbolicSupportAvoidsEnumeration = do
    let seeds = referenceSeed <$> [0..63]
        template = foldr1 Semantic.TemplateOrderedPair
            [Semantic.TemplateVariable (Semantic.ViewVariableIx index) | index <- [0..15]]
        value = foldr1 Semantic.TemplateOrderedPair (replicate 16 (referenceSeed 0))
        constructed = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton (referenceSeed 0))
        outside = foldr1 Semantic.TemplateOrderedPair (replicate 16 constructed)
        action = do
            let charge = Reference.chargeReferenceWork . fromIntegral
            initial <- Support.buildSymbolicSupport charge seeds [template]
            (yes, first) <- Support.symbolicSupportContains charge value initial
            (no, second) <- Support.symbolicSupportContains charge constructed first
            (stillNo, third) <- Support.symbolicSupportContains charge outside second
            (cached, fourth) <- Support.symbolicSupportContains charge value third
            (possible, final) <- Support.symbolicSupportMayContain charge
                (foldr1 Semantic.TemplateOrderedPair (replicate 16 (Semantic.TemplateVariable Nothing))) fourth
            pure (yes, no, stillNo, cached, possible, Support.symbolicSupportMaximumTermSize final)
    -- The full template alone has 64^16 instances. This allowance covers only
    -- the supplied syntax and symbolic matching, not even a fraction of them.
    actual <- expectRight (fst (Reference.runReference 100000 action))
    assertEqual "query interning preserves the frozen seed domain and size bound"
        (True, False, False, True, True, 31) actual

partialSupportFeasibility :: Assertion
partialSupportFeasibility = do
    let power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        pair = Semantic.TemplateOrderedPair
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        seed = referenceSeed 0
        pinned = fmap (Just) seed
        hole = Semantic.TemplateVariable Nothing
        -- The long seed raises the size bound: size alone admits nested power
        -- requests, although only one power layer occurs in the support.
        longSeed = foldr1 pair (replicate 8 seed)
        charge = Reference.chargeReferenceWork . fromIntegral
        run allowance = Reference.runReference allowance do
            support <- Support.buildSymbolicSupport charge [longSeed] [power variable]
            (yes, first) <- Support.symbolicSupportMayContain charge (power hole) support
            (no, second) <- Support.symbolicSupportMayContain charge (power (power hole)) first
            (rigid, third) <- Support.symbolicSupportMayContain charge (pair hole pinned) second
            (again, final) <- Support.symbolicSupportMayContain charge (power (power hole)) third
            pure (yes,no,rigid,again,Support.symbolicSupportMaximumTermSize final)
        (result, used) = run 100000
    expectRight result >>= assertEqual "only feasible partial shapes survive" (True,False,True,False,16)
    assertEqual "partial admission exact budget" (result,used) (run used)
    assertEqual "partial admission one-short budget" (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1)))
    empty <- expectRight (fst (Reference.runReference 10000 do
        support <- Support.buildSymbolicSupport charge ([] :: [Reference.GroundTerm]) [power variable]
        fst <$> Support.symbolicSupportMayContain charge (power hole) support))
    assertBool "an assignable template has no instance without a seed" (not empty)

    fixed <- expectRight (fst (Reference.runReference 10000 do
        let other = referenceSeed 1
            slot = Semantic.ViewVariableIx 0
            template = pair (Semantic.TemplateVariable slot) (Semantic.TemplateVariable (Semantic.ViewVariableIx 1))
        support <- Support.freezeSupportWithCaptures charge [([template],Map.singleton slot seed)]
            [other] Support.emptyTemplateSupport
        fst <$> Support.symbolicSupportMayContain charge (pair (fmap Just other) hole) support))
    assertBool "partial shape checks retain rigid captures" (not fixed)

referenceDerivedRows :: Assertion
referenceDerivedRows = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        rule arity rows result = Reference.ReferenceRule arity
            (Semantic.RulePremiseAtom <$> rows) result Set.empty
        producer = rule 2 [row 0 [x,y]] (row 1 [x,y])
        consumer = rule 2 [row 1 [x,y]] (row 2 [x])
        facts = [Reference.ReferenceFact (row 0 [a,b]) (referenceSummary 0)]
        target = row 2 [a]
    (result, _) <- runReferenceCase [producer,consumer] facts target
    assertReferenceAnswer "a producer answers the erased-output request" True target result
    let rowRequest = row 1 [Semantic.TemplateVariable (Reference.Pin (Reference.OpaqueSeed 0)),
            Semantic.TemplateVariable (Reference.Hole 0)]
    assertBool "the intermediate row is requested before b is known"
        (Set.member rowRequest (Reference.referenceRequests result))
    missing <- fst <$> runReferenceCase [consumer] facts target
    assertReferenceAnswer "a seed in U is not evidence for an erased output" False target missing
    let unrelated = rule 2 [row 1 [y]] (row 2 [x])
    unanchored <- runProductionRules (Map.singleton 0 unrelated)
        [Reference.ReferenceFact (row 1 [b]) (referenceSummary 0)] target
    assertReferenceAnswer "a disconnected proved row supplies its own parameters" True target unanchored

    -- The same rule language handles graph-domain rows and nested pair keys.
    let domainReference = Semantic.globalBindingRef
            (Semantic.declarationSlot preludeModuleName (localDeclarationOrdinal 24))
            (Semantic.SemanticExpressionFunction (Raw.TokenCons (Raw.Word "dom") (Raw.HoleCons Raw.End)))
        domain t = Semantic.TemplateProvider (Semantic.GlobalSourceProvider domainReference) (Vector.singleton t)
        graph = Semantic.TemplateVariable (Semantic.ViewVariableIx 2)
        member = Semantic.MembershipAtomTemplate
        pair = Semantic.TemplateOrderedPair
        domainRule = rule 3 [member (pair x y) graph] (member x (domain graph))
        g = referenceSeed 2
        c = referenceSeed 3
        nestedGoal = member a (domain (domain g))
    nested <- fst <$> runReferenceCase [domainRule]
        [Reference.ReferenceFact (member (pair (pair a b) c) g) (referenceSummary 0)] nestedGoal
    assertReferenceAnswer "a derived pair row feeds the next graph-domain request" True nestedGoal nested

referenceCorrelatedJoins :: Assertion
referenceCorrelatedJoins = do
    fixture <- makeFixture 4
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        c = referenceSeed 2
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        target = row 3 [a]
        producer = Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 2 [x,y])]
            (row 1 [power x,y]) Set.empty
        direct value = zipWith Reference.ReferenceFact [row 0 [a,b],row 2 [a,value]]
            [referenceSummary 0, referenceSummary 1]
    forM_ (List.permutations [row 0 [x,y],row 1 [power x,y]]) \premises -> do
        let rule = Reference.ReferenceRule 2 (Semantic.RulePremiseAtom <$> premises) (row 3 [x]) Set.empty
        successful <- fst <$> runReferenceCase [producer,rule] (direct b) target
        assertReferenceAnswer "F2 reconstructs the guard and asks for its derived row" True target successful
        mismatch <- fst <$> runReferenceCase [producer,rule] (direct c) target
        assertReferenceAnswer "different complete rows cannot contribute mixed columns" False target mismatch
    let repeated = Reference.ReferenceRule 2
            [Semantic.RulePremiseAtom (row 1 [x,y,y])]
            (row 3 [x]) Set.empty
    mismatch <- fst <$> runReferenceCase [repeated]
        [Reference.ReferenceFact (row 1 [a,b,c]) (referenceSummary 0)] target
    assertReferenceAnswer "repeated placeholders retain their equality constraint" False target mismatch
    matched <- fst <$> runReferenceCase [repeated]
        [Reference.ReferenceFact (row 1 [a,b,b]) (referenceSummary 0)] target
    assertReferenceAnswer "one complete row supplies a repeated output consistently" True target matched
    assertBool "canonical requests retain the repeated output identity"
        (Set.member (row 1 [Semantic.TemplateVariable (Reference.Pin (Reference.OpaqueSeed 0)),
            Semantic.TemplateVariable (Reference.Hole 0), Semantic.TemplateVariable (Reference.Hole 0)])
            (Reference.referenceRequests matched))

-- This oracle works on a tiny relation of integer triples, independently of
-- templates, support, requests, unification, or witness scheduling. Every edge
-- preserves both columns; the final existential join must use the same y.
prop_referenceRelationalClosure :: Property
prop_referenceRelationalClosure = property do
    edges <- List.nub <$> forAll (Gen.list (Range.linear 0 4)
        ((,) <$> Gen.integral (Range.linear 0 2) <*> Gen.integral (Range.linear 0 2)))
    rows <- List.nub <$> forAll (Gen.list (Range.linear 0 4)
        ((,,) <$> Gen.integral (Range.linear 0 2) <*> Gen.integral (Range.linear 0 1)
            <*> Gen.integral (Range.linear 0 1)))
    depth <- forAll (Gen.int (Range.linear 0 2))
    grouped <- forAll Gen.bool
    fixture <- evalIO (makeFixture 4)
    let closure known =
            let next = known <> Set.fromList
                    [(destination, a, b) | (source, destination) <- edges,
                        (head', a, b) <- Set.toList known, head' == source]
            in if next == known then known else closure next
        complete = closure (Set.fromList rows)
        expected a = any (\b -> Set.member (0,a,b) complete && Set.member (1,a,b) complete) [0,1]
        power :: Semantic.SetTermTemplate variable -> Semantic.SetTermTemplate variable
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton t)
        row :: Natural -> term -> term -> Semantic.AtomTemplate term
        row head' a b = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.fromList [a,b])
        -- One relation uses a nested provider in its first column. Producers
        -- must reconstruct this guard without changing the underlying join.
        encoded :: Natural -> Semantic.SetTermTemplate variable -> Semantic.SetTermTemplate variable
            -> Semantic.AtomTemplate (Semantic.SetTermTemplate variable)
        encoded head' a b = row head' (if head' == 1 then iterate power a !! depth else a) b
        result :: term -> Semantic.AtomTemplate term
        result a = Semantic.StructureAtomTemplate (fixtureHead fixture 3) (Vector.singleton a)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        producers = [Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (encoded source x y)]
            (encoded destination x y) Set.empty | (source,destination) <- edges]
        premises = Semantic.RulePremiseAtom <$> [encoded 0 x y, encoded 1 x y]
        joinRule ordered = Reference.ReferenceRule 2
            (if grouped then [foldr1 Semantic.RulePremiseAnd ordered] else ordered) (result x) Set.empty
        rules = producers <> [joinRule premises]
        reordered = joinRule (reverse premises) : reverse producers
        facts = [Reference.ReferenceFact (encoded head' (referenceSeed a) (referenceSeed b)) (referenceSummary ordinal)
            | (ordinal,(head',a,b)) <- zip [0..] rows]
        -- Rule ordinals name occurrences. Remap the reversed enumeration before
        -- comparing eligibility, rather than accidentally ignoring provenance.
        canonicalSummary reversed summary = summary
            { Reference.witnessOccurrences = if reversed
                then Set.map (fromIntegral (length rules - 1) -) (Reference.witnessOccurrences summary)
                else Reference.witnessOccurrences summary }
        answers target reversed evaluation = Set.fromList
            [canonicalSummary reversed summary
            | ((found,summary),_) <- Map.toList (Reference.referenceAnswers evaluation), found == target]
    classify "successful correlated join" (any expected [0,1])
    classify "completed absence" (any (not . expected) [0,1])
    classify "derived rows" (complete /= Set.fromList rows)
    classify "nested constructor guard" (depth == 2)
    classify "cyclic producers" (any (\(a,b) -> a == b || (b,a) `elem` edges) edges)
    forM_ [0,1] \a -> do
        let target = result (referenceSeed a)
        (forward, _) <- evalIO (runReferenceCase rules facts target)
        (backward, _) <- evalIO (runReferenceCase reordered (reverse facts) target)
        not (Set.null (answers target False forward)) === expected a
        answers target False forward === answers target True backward
        let (scheduled, work) = runRelationalJoin 100000 edges rows a
        production <- evalEither scheduled
        not (Set.null (Relational.relationalRootAnswers production)) === expected a
        -- Every emitted row must belong to the independent closure, including
        -- intermediates that were not themselves requested at the root.
        let allowed = complete <> Set.fromList [(3,subject,0) | subject <- [0,1], expected subject]
        Map.keysSet (Relational.relationalAnswers production) `Set.isSubsetOf` allowed === True
        reorderedProduction <- evalEither (fst (runRelationalJoin 100000 (reverse edges) (reverse rows) a))
        Relational.relationalRootAnswers production === Relational.relationalRootAnswers reorderedProduction
        runRelationalJoin work edges rows a === (scheduled, work)
        fst (runRelationalJoin (work - 1) edges rows a) === Left Reference.ReferenceWorkExhausted

relationalCausalDelivery :: Assertion
relationalCausalDelivery = do
    let evaluator = Relational.RelationalEvaluator
            { Relational.relationalCharge = Reference.chargeReferenceWork 1
            , Relational.relationalRequestBucket = pure
            , Relational.relationalAnswerBuckets = pure . pure
            , Relational.relationalAnswerKey = id
            , Relational.relationalMatches = \request answer -> pure
                (if request == answer then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalObserve = \answer -> pure
                (Relational.RelationalStep [] [] [(Nothing,()) | answer == (2 :: Int)])
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [0] [] [])
            , Relational.relationalExpand = \request -> pure
                (Relational.RelationalStep [] (if request == 0 then [(1,0),(1,1)] else []) [])
            , Relational.relationalResume = \continuation _ -> do
                when (continuation == (1 :: Int)) (Reference.chargeReferenceWork 10000)
                pure (Relational.RelationalStep [2] [] [])
            }
        run allowance = Reference.runReference allowance (Relational.solveRelational evaluator [1] 0)
        observed@(result,used) = run 1000
    solved <- expectRight result
    Relational.relationalRootAnswers solved @?= Set.singleton 0
    run used @?= observed
    fst (run (used-1)) @?= Left Reference.ReferenceWorkExhausted
    fst (Reference.runReference 1000 (Relational.evaluateRelational evaluator [1] 0)) @?=
        Left Reference.ReferenceWorkExhausted
    complete <- expectRight (fst (Reference.runReference 20000 (Relational.evaluateRelational evaluator [1] 0)))
    assertBool "the expensive sibling is retained for saturation" (Relational.relationalSaturated complete)

componentWitnessSharing :: Assertion
componentWitnessSharing = do
    fixture <- makeFixture 3
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        value index = Semantic.TemplateVariable (index :: Natural)
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
            (const (pure ()))
            (\case Diagnostics.Count operation amount -> State.modify' (Diagnostics.countOperation operation amount)
                   _ -> pure ())
            (\_ completed -> pure (Just (Production.completedAtom completed,())))
            (\_ _ -> pure Nothing) pure (const (pure ()))
        drain session = case Evaluation.ruleSessionStatus session of
            Relational.RelationalRunnable -> Evaluation.advanceRuleSession 16 session >>= drain
            _ -> pure session
        run width = Reference.runReference 10000000 (State.runStateT (do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
                [Semantic.RulePremiseAtom (row 0 x),Semantic.RulePremiseAtom (row 1 y)] (row 2 x))
            catalog <- Catalog.insertRule charge () rule Catalog.emptyCatalog
            snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 2 x)) catalog)
            let roots = [Semantic.AtomicLeaf (row 2 (value i)) | i <- [0..width-1]]
                missing = Semantic.AtomicLeaf (row 2 (value (2*width)))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf atom) atom Join.SourceRow ()
                    | atom <- [row 0 (value i) | i <- [0..width-1]] <>
                        [row 1 (value i) | i <- [width..2*width-1]]]
            start <- admit (Evaluation.initializeCatalogLeaves owner catalog snapshot facts (pure [])
                (roots <> [missing]) (Semantic.AtomicLeaf (row 2 (value 0))))
            initial <- case start of
                Evaluation.PreparedAnswer{} -> lift (Reference.invalidReferenceInput "component rule bypassed search")
                Evaluation.StartedRules session -> pure session
            reached <- foldM (\session goal -> do
                focused <- admit (Evaluation.focusRuleSession goal session) >>= drain
                proof <- Evaluation.ruleSessionAnswer focused
                unless (isJust proof) (lift (Reference.invalidReferenceInput "component lost a founded root"))
                pure focused) initial roots
            saturated <- admit (Evaluation.focusRuleSession missing reached) >>= drain
            (result,_) <- Evaluation.finishRuleSession saturated
            pure (Relational.relationalSaturated result && Set.null (Relational.relationalRootAnswers result))) Diagnostics.emptyDiagnostics)
        count operation diagnostics = Map.findWithDefault 0 operation (Diagnostics.operationCounts diagnostics)
    counts <- for [8,32,128] \width -> do
        (miss,diagnostics) <- expectRight (fst (run width))
        assertBool "absence waits for saturation, including old alternative deliveries" miss
        count Diagnostics.ComponentRequest diagnostics @?= width+2
        count Diagnostics.ComponentResult diagnostics @?= width+1
        assertBool "one internal Q witness serves all externally distinct x values"
            (count Diagnostics.GroundInstance diagnostics <= 4*width+8)
        pure (count Diagnostics.CandidatePair diagnostics)
    for_ (zip counts (drop 1 counts)) \(small,large) ->
        assertBool "candidate visits grow with the rows, not their Cartesian product" (large < 6*small)

ruleGroupDomain :: Assertion
ruleGroupDomain = do
    fixture <- makeFixture 5
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row index term = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        value = Semantic.TemplateVariable (0 :: Natural)
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton term)
        pair term = Semantic.TemplateOrderedPair term term
        target = row 3 value
        sibling = row 4 (power value)
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
            (const (pure ())) (const (pure ()))
            (\_ completed -> pure (Just (Production.completedAtom completed,())))
            (\_ _ -> pure Nothing) pure (const (pure ()))
        drain session = case Evaluation.ruleSessionStatus session of
            Relational.RelationalRunnable -> Evaluation.advanceRuleSession 7 session >>= drain
            _ -> pure session
        run roots = Reference.runReference 1000000 do
            rules <- traverse (\(arity,premises,result) -> Rule.RegisteredClassification <$>
                admit (Rule.compileRule charge arity (Semantic.RulePremiseAtom <$> premises) result))
                [(1,[row 0 x],row 1 (power x)),(1,[row 1 x],row 2 (pair x)),(2,[row 2 y],row 3 x)]
            catalog <- Catalog.insertRules charge (zip [0 :: Natural ..] rules) Catalog.emptyCatalog
            snapshot <- admit (Catalog.selectSnapshotHeads charge
                (Semantic.AtomicLeaf . Rule.atomSignature <$> roots) catalog)
            let facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf atom) atom Join.SourceRow ()
                    | atom <- [row 0 value,sibling]]
            initialized <- admit (Evaluation.initializeCatalogLeaves owner catalog snapshot facts (pure [])
                (Semantic.AtomicLeaf <$> roots) (Semantic.AtomicLeaf target))
            case initialized of
                Evaluation.PreparedAnswer{} -> Reference.invalidReferenceInput "derived group root bypassed search"
                Evaluation.StartedRules started -> do
                    finished <- drain started
                    (result,_) <- Evaluation.finishRuleSession finished
                    let solved = not (Set.null (Relational.relationalRootAnswers result))
                    if not solved then pure (False,False) else do
                        focused <- admit (Evaluation.focusRuleSession (Semantic.AtomicLeaf sibling) finished) >>= drain
                        (second,_) <- Evaluation.finishRuleSession focused
                        pure (True,not (Set.null (Relational.relationalRootAnswers second)))
    fst (run [target]) @?= Right (False,False)
    for_ [[target,sibling],[sibling,target],[target,sibling,sibling]] \roots ->
        fst (run roots) @?= Right (True,True)
    let deferredInputs present = Reference.runReference 1000 do
            snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature sibling) Catalog.emptyCatalog)
            let facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf sibling) sibling Join.SourceRow () | present]
            start <- admit (Evaluation.initializeCatalogLeaves owner Catalog.emptyCatalog snapshot facts
                (charge 10000 >> pure [value]) [Semantic.AtomicLeaf sibling] (Semantic.AtomicLeaf sibling))
            pure (case start of Evaluation.PreparedAnswer{} -> True; _ -> False)
    assertEqual "a founded initial answer avoids unused domain materialization" (Right True) (fst (deferredInputs True))
    assertEqual "ordinary search still charges the complete original input action"
        (Left Reference.ReferenceWorkExhausted) (fst (deferredInputs False))

relationalResumption :: Assertion
relationalResumption = do
    let evaluator = Relational.RelationalEvaluator
            { Relational.relationalCharge = State.modify' (+ (1 :: Int))
            , Relational.relationalRequestBucket = pure
            , Relational.relationalAnswerBuckets = pure . pure
            , Relational.relationalAnswerKey = id
            , Relational.relationalMatches = \request answer -> pure
                (if request == answer then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalObserve = const (pure (Relational.RelationalStep [] [] []))
            , Relational.relationalExpand = \request -> pure (Relational.RelationalStep []
                [(request-1,request) | request > (0 :: Int)] [])
            , Relational.relationalResume = \parent _ -> pure (Relational.RelationalStep [parent] [] [])
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [] [] [])
            }
        drain quantum owner session = case Relational.relationalStatus session of
            Relational.RelationalRunnable -> Relational.advanceRelational quantum owner session >>= drain quantum owner
            _ -> pure session
        sliced quantum = State.runState (do
            initial <- Relational.initializeRelational False evaluator [0] 16
            finished <- drain quantum evaluator initial
            Relational.finishRelational evaluator finished) 0
        complete = State.runState (Relational.evaluateRelational evaluator [0] 16) 0
    for_ [1,7,64] \quantum -> sliced quantum @?= complete
    let inspected = State.evalState (do
            first <- Relational.initializeRelational False evaluator [0] 16 >>= drain 7 evaluator
            (pending,second) <- Relational.queryRelational evaluator 18 first
            completed <- drain 7 evaluator second
            (found,retained) <- Relational.queryRelational evaluator 18 completed
            result <- Relational.finishRelational evaluator retained
            pure (pending,found,Relational.relationalRootAnswers result)) 0
    inspected @?= (Nothing,Just 18,Set.singleton 16)
    let focused = State.evalState (do
            first <- Relational.initializeRelational True evaluator [0] 16 >>= drain 7 evaluator
            second <- Relational.focusRelational evaluator 18 first >>= drain 1 evaluator
            Relational.finishRelational evaluator second) 0
    Relational.relationalRootAnswers focused @?= Set.singleton 18
    assertBool "a group retains earlier founded answers when its root changes"
        (Map.member 16 (Relational.relationalAnswers focused))
    let unpublished = State.evalState (do
            first <- Relational.initializeRelational True evaluator [0,1] 0 >>= drain 1 evaluator
            second <- Relational.focusRelational evaluator 1 first >>= drain 1 evaluator
            Relational.finishRelational evaluator second) 0
    Relational.relationalRootAnswers unpublished @?= Set.singleton 1
    let (before,work) = State.runState (do
            initial <- Relational.initializeRelational True evaluator [] 16
            Relational.advanceRelational 0 evaluator initial) 0
    Relational.relationalStatus before @?= Relational.RelationalRunnable
    work @?= 1
    let cyclic = evaluator {Relational.relationalExpand = \request ->
            pure (Relational.RelationalStep [] [(request,request)] [])}
        (idle,_) = State.runState
            (Relational.initializeRelational True cyclic [] 0 >>= drain 1 cyclic) 0
    Relational.relationalStatus idle @?= Relational.RelationalQuiescent
    let (resumed,_) = State.runState (do
            delivered <- Relational.deliverRelational cyclic (Relational.RelationalStep [0] [] []) idle
            final <- drain 1 cyclic delivered
            Relational.finishRelational cyclic final) 0
    Relational.relationalRootAnswers resumed @?= Set.singleton 0
    assertBool "a delivered external proof resumes the same pending obligation"
        (not (Relational.relationalSaturated resumed))
    let quiet = evaluator {Relational.relationalExpand = const (pure (Relational.RelationalStep [] [] []))}
        (burst,_) = State.runState (do
            initial <- Relational.initializeRelational False quiet [] 0
            Relational.deliverRelational quiet
                (Relational.RelationalStep [] [(1,n) | n <- [1..1000]] []) initial) 0
        countSteps session largest = case Relational.relationalStatus session of
            Relational.RelationalRunnable -> do
                start <- State.get
                next <- Relational.advanceRelational 1 quiet session
                end <- State.get
                countSteps next (max largest (end-start))
            _ -> pure largest
        largest = State.evalState (countSteps burst 0) 0
    assertBool "one scheduler turn does not enroll an entire subscriber batch" (largest <= 4)

relationalRootCompletion :: Assertion
relationalRootCompletion = do
    let evaluator = Relational.RelationalEvaluator
            { Relational.relationalCharge = Reference.chargeReferenceWork 1
            , Relational.relationalRequestBucket = pure
            , Relational.relationalAnswerBuckets = pure . pure
            , Relational.relationalAnswerKey = id
            , Relational.relationalMatches = \request answer ->
                pure (if request == answer then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalObserve = const (pure (Relational.RelationalStep [] [] []))
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [] [] [])
            , Relational.relationalExpand = \request -> do
                when (request == (1 :: Int) || request == 2) (Reference.chargeReferenceWork 10000)
                pure (Relational.RelationalStep []
                    (if request == 0 then [(1,()),(2,())] else []) [])
            , Relational.relationalResume = \() answer ->
                pure (Relational.RelationalStep (if answer == 1 then [0] else []) [] [])
            }
        solve root = Reference.runReference 100 (Relational.solveRelational evaluator [1] root)
        ample = Reference.runReference 30000 (Relational.evaluateRelational evaluator [1] 0)
    solved <- expectRight (fst (solve 0))
    saturated <- expectRight (fst ample)
    assertEqual "root solving retains the same checked root answer"
        (Relational.relationalRootAnswers saturated) (Relational.relationalRootAnswers solved)
    assertBool "successful root solving does not claim complete enumeration"
        (not (Relational.relationalSaturated solved))
    assertBool "the parity evaluator still saturates" (Relational.relationalSaturated saturated)
    direct <- expectRight (fst (Reference.runReference 100
        (Relational.solveRelational evaluator [2] 2)))
    assertEqual "direct root evidence bypasses expensive producer expansion"
        (Set.singleton 2) (Relational.relationalRootAnswers direct)
    let work = snd (solve 0)
    exact <- expectRight (fst (Reference.runReference work (Relational.solveRelational evaluator [1] 0)))
    assertEqual "exact budget retains the root witness" solved exact
    assertEqual "one-short solving remains exhaustion"
        (Left Reference.ReferenceWorkExhausted)
        (fst (Reference.runReference (work - 1) (Relational.solveRelational evaluator [1] 0)))
    absent <- expectRight (fst (solve 3))
    assertBool "absence requires completed saturation"
        (Relational.relationalSaturated absent && Set.null (Relational.relationalRootAnswers absent))
    assertEqual "an unsolved expensive request is not reported absent"
        (Left Reference.ReferenceWorkExhausted) (fst (solve 2))

    let sameBucket = evaluator
            { Relational.relationalRequestBucket = const (pure ())
            , Relational.relationalAnswerBuckets = const (pure [()])
            , Relational.relationalMatches = \request answer -> do
                when (answer == 2) (Reference.chargeReferenceWork 10000)
                pure (if request == answer then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalResume = \() _ -> pure (Relational.RelationalStep [0,2] [] [])
            }
    forM_ [[0,2],[1]] \facts -> do
        let earlyRun = Reference.runReference 100 (Relational.solveRelational sameBucket facts 0)
            prefixOnly = sameBucket
                { Relational.relationalResume = \() _ -> pure (Relational.RelationalStep [0] [] []) }
            prefixRun = Reference.runReference 100
                (Relational.solveRelational prefixOnly (List.filter (/= 2) facts) 0)
        early <- expectRight (fst earlyRun)
        assertEqual "unused answer tails charge no work after root acceptance"
            (snd prefixRun) (snd earlyRun)
        assertEqual "a sufficient emitted root skips expensive same-bucket alternatives"
            (Set.singleton 0) (Relational.relationalRootAnswers early)
        assertEqual "exhaustive evaluation still visits the expensive alternative"
            (Left Reference.ReferenceWorkExhausted)
            (fst (Reference.runReference 100 (Relational.evaluateRelational sameBucket facts 0)))
        full <- expectRight (fst (Reference.runReference 100000
            (Relational.evaluateRelational sameBucket facts 0)))
        assertBool "exhaustive evaluation completes with sufficient resources"
            (Relational.relationalSaturated full)
        assertEqual "early completion and saturation agree on the root"
            (Relational.relationalRootAnswers full) (Relational.relationalRootAnswers early)

-- An answer's continuation may need another proof, not merely publish an
-- immediate consequence. Alternate witnesses must not delay that new demand.
relationalWitnessDemand :: Assertion
relationalWitnessDemand = do
    let evaluator = Relational.RelationalEvaluator
            { Relational.relationalCharge = Reference.chargeReferenceWork 1
            , Relational.relationalRequestBucket = pure
            , Relational.relationalAnswerBuckets = \answer -> pure [if answer >= 3 then 1 else answer]
            , Relational.relationalAnswerKey = id
            , Relational.relationalMatches = \request answer -> pure
                (if request == answer || request == 1 && answer >= 3
                    then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalObserve = const (pure (Relational.RelationalStep [] [] []))
            , Relational.relationalExpand = \request -> pure (case request of
                0 -> Relational.RelationalStep [] [(1,1)] []
                2 -> Relational.RelationalStep [2] [] []
                _ -> Relational.RelationalStep [] [] [])
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [] [] [])
            , Relational.relationalResume = \continuation answer -> do
                when (answer >= 3) (Reference.chargeReferenceWork 10000)
                pure (if continuation == (1 :: Int)
                    then Relational.RelationalStep [] [(2,2)] []
                    else Relational.RelationalStep [0] [] [])
            }
        solve allowance owner = Reference.runReference allowance
            (Relational.solveRelational owner [1,3] (0 :: Int))
        observed@(outcome,used) = solve 500 evaluator
    result <- expectRight outcome
    Relational.relationalRootAnswers result @?= Set.singleton 0
    for_ [16,256] \population -> do
        let facts = 1 : [3..population+2]
            (expanded,cost) = Reference.runReference 20000
                (Relational.solveRelational evaluator facts 0)
        successful <- expectRight expanded
        Relational.relationalRootAnswers successful @?= Set.singleton 0
        assertBool "initial rows cost work, alternate proof callbacks do not"
            (cost < 30 * fromIntegral (length facts) + 500)
    solve used evaluator @?= observed
    fst (solve (used-1) evaluator) @?= Left Reference.ReferenceWorkExhausted
    fst (Reference.runReference 500 (Relational.evaluateRelational evaluator [1,3] 0)) @?=
        Left Reference.ReferenceWorkExhausted
    full <- expectRight (fst (Reference.runReference 50000
        (Relational.evaluateRelational evaluator [1,3] 0)))
    assertBool "saturation still delivers alternate witnesses" (Relational.relationalSaturated full)
    let needsLater = evaluator
            { Relational.relationalResume = \_ answer -> pure
                (Relational.RelationalStep [0 | answer == 3] [] []) }
    later <- expectRight (fst (solve 500 needsLater))
    Relational.relationalRootAnswers later @?= Set.singleton 0
    let absent = evaluator {Relational.relationalResume = \_ _ -> pure (Relational.RelationalStep [] [] [])}
    missing <- expectRight (fst (solve 500 absent))
    assertBool "an unanswered root is absent only after saturation"
        (Relational.relationalSaturated missing && Set.null (Relational.relationalRootAnswers missing))

leafIndexScaling :: Assertion
leafIndexScaling = do
    let leaf = Semantic.TemplateVariable (0 :: Int)
        power term = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
            (Vector.singleton term)
        charge = Reference.chargeReferenceWork . fromIntegral
    costs <- forM [0,16,128] \depth -> do
        let term = foldr (const power) leaf (replicate depth ())
        (root, table) <- expectRight (fst (Reference.runReference 1000000 (Terms.intern charge term Terms.emptyNodes)))
        let (lookedUp, cost) = Reference.runReference 10000 (Terms.intern charge leaf table)
        (identifier, _) <- expectRight lookedUp
        assertEqual "constructor insertion preserves the original leaf identity" 0 identifier
        (same, _) <- expectRight (fst (Reference.runReference 1000000 (Terms.intern charge term table)))
        assertEqual "constructor identities are stable" root same
        pure cost
    assertEqual "leaf lookup does not traverse unrelated constructors" 1
        (Set.size (Set.fromList costs))

relationalSchedulerDeliversOnce :: Assertion
relationalSchedulerDeliversOnce = do
    let initial :: (Map Int Int, Map (Int,Int) Int, Map (Int,Int) Int)
        initial = (Map.empty, Map.empty, Map.empty)
        evaluator = Relational.RelationalEvaluator
            { Relational.relationalCharge = lift (Reference.chargeReferenceWork 1)
            , Relational.relationalRequestBucket = const (pure ())
            , Relational.relationalAnswerBuckets = const (pure [()])
            , Relational.relationalAnswerKey = id
            , Relational.relationalMatches = \request answer -> do
                State.modify' (\(expanded,matched,delivered) ->
                    (expanded,Map.insertWith (+) (request,answer) 1 matched,delivered))
                pure (if request == answer then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalObserve = const (pure (Relational.RelationalStep [] [] []))
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [] [] [])
            , Relational.relationalExpand = \request -> do
                State.modify' (\(expanded,matched,delivered) ->
                    (Map.insertWith (+) request 1 expanded,matched,delivered))
                pure (Relational.RelationalStep [] (case request of
                    0 -> [(1,10),(1,10)]
                    -- Answer 1 already matched this request. Subscriber 11
                    -- must see it immediately; request 2 precedes its answer.
                    1 -> [(1,11),(2,20)]
                    _ -> []) [])
            , Relational.relationalResume = \continuation answer -> do
                State.modify' (\(expanded,matched,delivered) ->
                    (expanded,matched,Map.insertWith (+) (continuation,answer) 1 delivered))
                pure (Relational.RelationalStep [if continuation == 20 then 0 else 2] [] [])
            }
    (result, (expanded,matched,delivered)) <- expectRight (fst (Reference.runReference 10000
        (State.runStateT (Relational.evaluateRelational evaluator [1,1] 0) initial)))
    assertEqual "the root receives its derived answer" (Set.singleton 0) (Relational.relationalRootAnswers result)
    assertEqual "each request expands once" (Map.fromList [(i,1) | i <- [0,1,2]]) expanded
    assertEqual "each indexed candidate pair is matched once"
        (Map.fromList [((request,answer),1) | request <- [0,1,2], answer <- [0,1,2]]) matched
    assertEqual "duplicates and late subscriptions neither lose nor repeat delivery"
        (Map.fromList [((10,1),1),((11,1),1),((20,2),1)]) delivered
    prerequisitesBeforeAlternatives

prerequisitesBeforeAlternatives :: Assertion
prerequisitesBeforeAlternatives = do
    let evaluator = Relational.RelationalEvaluator
            { Relational.relationalCharge = Reference.chargeReferenceWork 1
            , Relational.relationalRequestBucket = pure
            , Relational.relationalAnswerBuckets = pure . pure
            , Relational.relationalAnswerKey = id
            , Relational.relationalMatches = \request answer -> pure
                (if request == answer then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalObserve = const (pure (Relational.RelationalStep [] [] []))
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> Reference.chargeReferenceWork 10000 >>
                pure (Relational.RelationalStep [] [] [])
            , Relational.relationalExpand = \request -> pure
                (if request == (2 :: Int) then Relational.RelationalStep [2] [] []
                    else Relational.RelationalStep [] [(request+1,request)] [(Just request,())])
            , Relational.relationalResume = \parent _ -> pure (Relational.RelationalStep [parent] [] [])
            }
        solve allowance = Reference.runReference allowance (Relational.solveRelational evaluator [] 0)
        observed@(outcome,work) = solve 500
    result <- expectRight outcome
    Relational.relationalRootAnswers result @?= Set.singleton 0
    Relational.relationalDeliveryCount result @?= 2
    solve work @?= observed
    fst (solve (work-1)) @?= Left Reference.ReferenceWorkExhausted
    fst (Reference.runReference 500 (Relational.evaluateRelational evaluator [] 0)) @?=
        Left Reference.ReferenceWorkExhausted
    full <- expectRight (fst (Reference.runReference 50000 (Relational.evaluateRelational evaluator [] 0)))
    assertBool "deferred alternatives remain reachable in exhaustive mode" (Relational.relationalSaturated full)
    let siblings = evaluator
            { Relational.relationalExpand = \request -> pure $
                if request == 0 then Relational.RelationalStep [] [(1,0),(2,0)] []
                else if request == 1 then Relational.RelationalStep [1] [] []
                else Relational.RelationalStep [] [(request+1,request)] [] }
    firstSibling <- expectRight (fst (Reference.runReference 500 (Relational.solveRelational siblings [] 0)))
    assertEqual "a later recursive sibling cannot overtake an earlier prerequisite"
        (Set.singleton 0) (Relational.relationalRootAnswers firstSibling)
    let partial = evaluator
            { Relational.relationalAnswerBuckets = \answer -> pure [if answer == 0 then 0 else 1]
            , Relational.relationalMatches = \request answer -> pure
                (if request == 0 && answer == 0 || request == 1 && answer > 0
                    then Relational.DirectMatch else Relational.NoMatch)
            , Relational.relationalExpand = \request -> pure
                (if request == 0 then Relational.RelationalStep [] [(1,0)] []
                    else Relational.RelationalStep [1] [] [(Just request,())])
            , Relational.relationalDiscovery = const False
            , Relational.relationalNeedsMoreAnswers = const (pure True)
            , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [2] [] [])
            , Relational.relationalResume = \_ answer -> pure
                (Relational.RelationalStep [0 | answer == 2] [] [])
            }
    resumed <- expectRight (fst (Reference.runReference 500 (Relational.solveRelational partial [] 0)))
    assertEqual "a first partial answer does not suppress a necessary later alternative"
        (Set.singleton 0) (Relational.relationalRootAnswers resumed)
    let conversion = evaluator
            { Relational.relationalRequestBucket = const (pure 0)
            , Relational.relationalAnswerBuckets = const (pure [0])
            , Relational.relationalMatches = \request answer -> pure
                (if request == answer then Relational.DirectMatch else Relational.DeferredMatch ())
            , Relational.relationalExpand = \request -> pure (Relational.RelationalStep [request] [] [])
            }
    direct <- expectRight (fst (Reference.runReference 500 (Relational.solveRelational conversion [1] 0)))
    assertEqual "a checked direct producer precedes expensive same-head conversion"
        (Set.singleton 0) (Relational.relationalRootAnswers direct)
    sharedJoinSelections

sharedJoinSelections :: Assertion
sharedJoinSelections = do
    fixture <- makeFixture 5
    let row :: Natural -> term -> Semantic.AtomTemplate term
        row head' value = Semantic.StructureAtomTemplate (fixtureHead fixture head') (Vector.singleton value)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        value = Semantic.TemplateVariable (0 :: Natural)
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        run allowance population = Reference.runReference allowance (State.runStateT (do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 1
                [Semantic.RulePremiseAtom (row head' x) | head' <- [0..3]] (row 4 x))
            catalog <- Catalog.insertRule charge () rule Catalog.emptyCatalog
            snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature (row 4 value)) catalog)
            let count (Diagnostics.Count operation amount) = State.modify' (Diagnostics.countOperation operation amount)
                count _ = pure ()
                owner = Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure (const (pure ())) count
                    (\_ _ -> pure (Just (0 :: Natural,()))) (\_ _ -> pure Nothing) pure (const (pure ()))
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf (row head' value)) (head'*population+alternative) Join.SourceRow ()
                    | head' <- [0..3], alternative <- [1..population]]
            void (admit (Evaluation.evaluateCatalogRules owner catalog snapshot facts [] (row 4 value)))) Diagnostics.emptyDiagnostics)
    for_ [1,4,16] \population -> do
        let observed@(outcome,work) = run 1000000 population
        (_,counts) <- expectRight outcome
        Map.lookup Diagnostics.CompletedRule (Diagnostics.operationCounts counts) @?= Just 1
        Map.lookup Diagnostics.GroundInstance (Diagnostics.operationCounts counts) @?= Just 1
        Map.lookup Diagnostics.PreparedGroundPremise (Diagnostics.operationCounts counts) @?= Just 4
        Map.lookup Diagnostics.GroundDelivery (Diagnostics.operationCounts counts) @?= Just (4*population)
        Map.lookup Diagnostics.AnswerTuple (Diagnostics.operationCounts counts) @?= Just 1
        -- The declaration's shared signature index is fixed preparation work;
        -- alternative proofs must add only linear matching and delivery work.
        assertBool ("alternative premise proofs never form a product: " <> show (population,work))
            (work < 500 + 3000*fromIntegral population)
        run work population @?= observed
        fst (run (work-1) population) @?= Left Reference.ReferenceWorkExhausted

type RelationalRow = (Natural, Natural, Natural)
type RelationalRequest = (Natural, Natural, Maybe Natural)

data JoinContinuation
    = CopyTo !Natural
    | SelectSecond !Natural
    | CompleteJoin !Natural
    deriving (Eq, Ord)

-- The production scheduler's callbacks implement this generated fragment
-- directly on scalar rows. In particular, SelectSecond cannot choose y until
-- a complete row arrives, and CompleteJoin subscribes to that exact same y.
runRelationalJoin
    :: Word -> [(Natural, Natural)] -> [RelationalRow] -> Natural
    -> (Either Reference.ReferenceFailure
        (Relational.RelationalResult RelationalRequest RelationalRow RelationalRow), Word)
runRelationalJoin allowance edges rows subject = Reference.runReference allowance
    (Relational.evaluateRelational evaluator rows (3,subject,Just 0))
  where
    evaluator = Relational.RelationalEvaluator
        { Relational.relationalCharge = Reference.chargeReferenceWork 1
        , Relational.relationalRequestBucket = \(head',_,_) -> pure head'
        , Relational.relationalAnswerBuckets = \(head',_,_) -> pure [head']
        , Relational.relationalAnswerKey = id
        , Relational.relationalMatches = \(head',a,pin) (other,b,c) ->
            pure (if head' == other && a == b && maybe True (== c) pin then Relational.DirectMatch else Relational.NoMatch)
        , Relational.relationalObserve = const (pure (Relational.RelationalStep [] [] []))
        , Relational.relationalDiscovery = const False
        , Relational.relationalNeedsMoreAnswers = const (pure True)
        , Relational.relationalContinue = \() -> pure (Relational.RelationalStep [] [] [])
        , Relational.relationalExpand = \(head',a,pin) -> pure
            (Relational.RelationalStep [] (if head' == 3
                then [((0,a,Nothing),SelectSecond a)]
                else [((source,a,pin),CopyTo head') | (source,destination) <- edges, destination == head']) [])
        , Relational.relationalResume = \continuation (_,a,b) -> pure (case continuation of
            CopyTo destination -> Relational.RelationalStep [(destination,a,b)] [] []
            SelectSecond original -> Relational.RelationalStep [] [((1,original,Just b),CompleteJoin original)] []
            CompleteJoin original -> Relational.RelationalStep [(3,original,0)] [] [])
        }

referenceFiniteRequests :: Assertion
referenceFiniteRequests = do
    fixture <- makeFixture 2
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        b = referenceSeed 1
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        grow = Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 0 [x,power y])]
            (row 0 [x,y]) Set.empty
        consumer = Reference.ReferenceRule 2 [Semantic.RulePremiseAtom (row 0 [x,y])]
            (row 1 [x]) Set.empty
        target = row 1 [a]
    (growing, _) <- runReferenceCase [grow,consumer] [] target
    assertReferenceAnswer "a growing ungrounded cycle does not prove its target" False target growing
    assertBool "composed unknown expressions stay inside the finite query vocabulary"
        (Set.size (Reference.referenceRequests growing) <= 3)
    assertBool "a support boundary is distinct from ordinary missing evidence"
        (any (\case Reference.OutsideSupport{} -> True; _ -> False) (Reference.referenceRejections growing))
    let forward = Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 0 [x])]
            (row 1 [x]) Set.empty
        backward = Reference.ReferenceRule 1 [Semantic.RulePremiseAtom (row 1 [x])]
            (row 0 [x]) Set.empty
        seed = Reference.ReferenceFact (row 0 [a]) (referenceSummary 0)
    absent <- fst <$> runReferenceCase [forward,backward] [] target
    assertReferenceAnswer "a pending ordinary cycle is not a proof" False target absent
    founded <- fst <$> runReferenceCase [backward,forward] [seed] target
    assertReferenceAnswer "grounded evidence wakes the cyclic request" True target founded
    let emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        closed = Reference.ReferenceRule 0 [] (row 0 [emptySet]) Set.empty
        closedTarget = row 0 [emptySet]
    direct <- fst <$> runReferenceCase [closed] [] closedTarget
    assertReferenceAnswer "zero-binder, zero-premise producers are ordinary success" True closedTarget direct
    let nullary = Reference.ReferenceRule 0 [] (row 0 []) Set.empty
    zero <- fst <$> runReferenceCase [nullary] [] (row 0 [])
    assertReferenceAnswer "a nullary atom needs no invented support seed" True (row 0 []) zero
    let invented = Reference.ReferenceRule 2 [] (row 0 [x,y]) Set.empty
    instantiated <- runProductionRules (Map.fromList [(0,invented),(1,consumer)])
        [Reference.ReferenceFact (row 1 [b]) (referenceSummary 0)] target
    assertReferenceAnswer "a universally valid producer can instantiate parameters from U" True target instantiated

referenceWitnessAlternatives :: Assertion
referenceWitnessAlternatives = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        conjunction = Semantic.RulePremiseAnd
            (Semantic.RulePremiseAtom (row 0 [x])) (Semantic.RulePremiseAtom (row 1 [x]))
        rule = Reference.ReferenceRule 1 [conjunction] (row 2 [x]) (Set.singleton 0)
        provisional = referenceSummary 0
        actual = (referenceSummary 1) {Reference.witnessSupport = Set.singleton 7}
        facts = [Reference.ReferenceFact (row 0 [a]) provisional,
            Reference.ReferenceFact (row 0 [a]) actual,
            Reference.ReferenceFact (row 1 [a]) (referenceSummary 2)]
        target = row 2 [a]
    (result, _) <- runReferenceCase [rule] facts target
    let summaries = [summary | ((foundRow,summary), _) <- Map.toAscList (Reference.referenceAnswers result), foundRow == target]
    assertEqual "one founded representative is kept for each eligibility summary" 2 (length summaries)
    assertBool "earlier provisional evidence cannot hide actual supported evidence"
        (any (\summary -> Reference.witnessOrigins summary == Set.fromList [1,2]
            && Reference.witnessSupport summary == Set.fromList [0,7]
            && Reference.witnessOccurrences summary == Set.singleton 0) summaries)
    reversed <- fst <$> runReferenceCase [rule] (reverse facts) target
    assertEqual "completed answers do not depend on evidence enumeration"
        (Map.keysSet (Reference.referenceAnswers result)) (Map.keysSet (Reference.referenceAnswers reversed))

referenceCanonicalSnapshot :: Assertion
referenceCanonicalSnapshot = do
    fixture <- makeFixture 6
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        alias = referenceSeed 1
        unrelated = referenceSeed 2
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        raised count term = iterate power term List.!! count
        implication premise conclusion = Reference.ReferenceRule 1
            [Semantic.RulePremiseAtom premise] conclusion Set.empty
        firstView = (implication (row 0 [x]) (row 1 [power x])) {Reference.referenceRuleSupport = Set.singleton 0}
        secondView = (implication (row 1 [x]) (row 2 [power x])) {Reference.referenceRuleSupport = Set.singleton 1}
        consumer = implication (row 2 [raised 2 x]) (row 3 [x])
        irrelevant = implication (row 4 [x]) (row 4 [raised 3 x])
        registrations = Map.fromList [(0,Reference.DefinitionRule firstView),
            (1,Reference.DefinitionRule secondView), (2,Reference.ClassificationRule consumer),
            (9,Reference.ClassificationRule irrelevant)]
        facts = [Reference.ReferenceFact (row 4 [unrelated]) (referenceSummary 10),
            Reference.ReferenceFact (row 0 [a]) (referenceSummary 11)]
        target = row 3 [a]
    (snapshot,result,used) <- runSnapshotCase registrations facts (Set.singleton alias) target
    let support = Reference.referenceSnapshotSupport snapshot
        initial = Reference.referenceSnapshotInitial snapshot
    assertEqual "canonical head closure excludes the unrelated producer" (Set.fromList [0,1,2])
        (Map.keysSet (Reference.referenceSnapshotRules snapshot))
    assertEqual "only direct, forward-view, target, and permitted alias terms seed support"
        (Set.fromList [a,power a,raised 2 a,alias]) (Reference.referenceSeeds support)
    assertEqual "one fixed template layer follows the whole finite E0 view closure"
        (Set.fromList ([raised n a | n <- [0..4]] <> [raised n alias | n <- [0..2]]))
        (Reference.referenceUniverse support)
    assertReferenceAnswer "forward definitions compose before freezing support" True (row 2 [raised 2 a]) initial
    assertReferenceAnswer "the goal's syntax is not an initial hypothesis" False target initial
    assertReferenceAnswer "classification runs against the frozen snapshot" True target result
    let provenance = [summary | ((found,summary),_) <- Map.toAscList (Reference.referenceAnswers initial), found == row 2 [raised 2 a]]
    assertEqual "view composition retains source authority and premise origin"
        [Reference.WitnessSummary (Set.singleton 11) (Set.fromList [0,1]) (Set.fromList [0,1])] provenance
    reversed <- runSnapshotCase registrations (reverse facts) (Set.singleton alias) target
    let (other,otherResult,_) = reversed
    assertEqual "input enumeration does not define support" support (Reference.referenceSnapshotSupport other)
    assertEqual "input enumeration preserves all eligible answers"
        (Map.keysSet (Reference.referenceAnswers result)) (Map.keysSet (Reference.referenceAnswers otherResult))

    let ordinary = Map.insert 1 (Reference.ClassificationRule secondView) registrations
    (later,laterResult,_) <- runSnapshotCase ordinary facts (Set.singleton alias) target
    assertBool "an ordinary implication cannot expand E0 just because it resembles a view"
        (raised 2 a `Set.notMember` Reference.referenceSeeds (Reference.referenceSnapshotSupport later))
    assertBool "its later derived answer never reseeds the template domain"
        (raised 4 a `Set.notMember` Reference.referenceUniverse (Reference.referenceSnapshotSupport later))
    assertReferenceAnswer "the ordinary producer still participates in request search" True target laterResult

    let alternative = Reference.ClassificationRule (implication (row 5 [x]) (row 3 [x]))
        forwardAfterSearch count = Map.insert 4
            (Reference.DefinitionRule (implication (row 2 [x]) (row 5 [raised count x])))
            (Map.insert 3 alternative ordinary)
    (dynamic,dynamicResult,_) <- runSnapshotCase (forwardAfterSearch 1) facts (Set.singleton alias) target
    assertReferenceAnswer "the new row's view was not part of initial evidence" False (row 5 [raised 3 a])
        (Reference.referenceSnapshotInitial dynamic)
    assertReferenceAnswer "derived answers expose forward views even without a matching query" True (row 5 [raised 3 a]) dynamicResult
    (bounded,boundedResult,_) <- runSnapshotCase (forwardAfterSearch 2) facts (Set.singleton alias) target
    assertBool "the requested view result lies outside this frozen domain"
        (raised 4 a `Set.notMember` Reference.referenceUniverse (Reference.referenceSnapshotSupport bounded))
    assertReferenceAnswer "forward views on derived rows cannot enlarge the domain" False (row 5 [raised 4 a]) boundedResult
    assertBool "the excluded view keeps its source association"
        (Set.member (Reference.OutsideSupport (Just 4) (Reference.groundPattern (row 5 [raised 4 a])))
            (Reference.referenceRejections boundedResult))

    let emptySet = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        choice t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.GlobalChoiceProvider) (Vector.singleton t)
        closed = Reference.ReferenceRule 0 [] (row 2 [emptySet]) Set.empty
        guarded = Reference.ReferenceRule 0 [Semantic.RulePremiseAtom (row 0 [emptySet])]
            (row 2 [choice emptySet]) Set.empty
        withClosed = Map.insert 7 (Reference.ClassificationRule guarded)
            (Map.insert 6 (Reference.ClassificationRule closed) registrations)
    (closedSnapshot,_,_) <- runSnapshotCase withClosed facts Set.empty target
    assertBool "an authorized premise-free closed result contributes its seed"
        (emptySet `Set.member` Reference.referenceSeeds (Reference.referenceSnapshotSupport closedSnapshot))
    assertBool "an unresolved closed guard contributes no proved seed"
        (choice emptySet `Set.notMember` Reference.referenceSeeds (Reference.referenceSnapshotSupport closedSnapshot))
    assertReferenceAnswer "closed syntax does not erase an implication premise" False (row 2 [choice emptySet])
        (Reference.referenceSnapshotInitial closedSnapshot)
    let (prepared,preparationUsed) = Reference.prepareReferenceSnapshot used registrations facts (Set.singleton alias) target
    preparedSnapshot <- expectRight prepared
    assertEqual "standalone preparation has the same semantic snapshot" snapshot preparedSnapshot
    assertBool "snapshot construction spends part of the single request account" (preparationUsed > 0 && preparationUsed < used)
    assertEqual "search does not get a fresh allowance after snapshot construction"
        (Left Reference.ReferenceWorkExhausted)
        (fst (Reference.evaluateFormation preparationUsed registrations facts (Set.singleton alias) target))

referenceMembershipHeadClosure :: Assertion
referenceMembershipHeadClosure = do
    fixture <- makeFixture 3
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        a = referenceSeed 0
        b = referenceSeed 1
        other = referenceSeed 2
        hidden = referenceSeed 3
        power t = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton t)
        member = Semantic.MembershipAtomTemplate
        rule premise result = Reference.ClassificationRule (Reference.ReferenceRule 1
            [Semantic.RulePremiseAtom premise] result Set.empty)
        registrations = Map.fromList [(0,rule (row 0 [x]) (member x (power x))),
            (1,rule (row 1 [x]) (member x (power (power x)))),
            (2,rule (row 2 [x]) (row 2 [x]))]
        facts = zipWith Reference.ReferenceFact [row 0 [a],row 1 [other],row 2 [hidden]] (referenceSummary <$> [0..2])
        target = member a b
    (snapshot,result,_) <- runSnapshotCase registrations facts Set.empty target
    assertEqual "membership uses one common semantic head" (Set.fromList [0,1])
        (Map.keysSet (Reference.referenceSnapshotRules snapshot))
    assertBool "a producer's templates remain even when its result cannot match this ground target"
        (power (power other) `Set.member` Reference.referenceUniverse (Reference.referenceSnapshotSupport snapshot))
    assertBool "an unrelated head contributes no seeds"
        (hidden `Set.notMember` Reference.referenceSeeds (Reference.referenceSnapshotSupport snapshot))
    assertReferenceAnswer "head relevance alone does not prove the requested membership" False target result

referenceDefinitionSnapshotBoundaries :: Assertion
referenceDefinitionSnapshotBoundaries = do
    fixture <- makeFixture 2
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row i = Semantic.StructureAtomTemplate (fixtureHead fixture i) . Vector.fromList
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        y = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        a = referenceSeed 0
        rule arity premise result = Reference.ReferenceRule arity [Semantic.RulePremiseAtom premise] result Set.empty
        forward = rule 1 (row 0 [x]) (row 1 [x])
        backward = rule 1 (row 1 [x]) (row 0 [x])
        target = row 1 [a]
        reject label registrations = case fst (Reference.prepareReferenceSnapshot 10000 registrations
                [Reference.ReferenceFact target (referenceSummary 0)] Set.empty target) of
            Left Reference.ReferenceInvalidInput{} -> pure ()
            other -> assertFailure (label <> ": " <> show other)
    reject "an already available target cannot hide invalid cyclic definition data"
        (Map.fromList [(0,Reference.DefinitionRule forward),(1,Reference.DefinitionRule backward)])
    reject "a definition view must determine its result binders from its source"
        (Map.singleton 0 (Reference.DefinitionRule (rule 2 (row 0 [x]) (row 1 [y]))))
    reject "an enormous declared arity is rejected without enumerating its binder range"
        (Map.singleton 0 (Reference.DefinitionRule (rule (2 ^ (64 :: Int)) (row 0 [x]) (row 1 [x]))))
    reject "matching variable count does not admit a sparse binder range"
        (Map.singleton 0 (Reference.DefinitionRule
            (rule 2 (row 0 [x, Semantic.TemplateVariable (Semantic.ViewVariableIx 2)]) (row 1 [x]))))
    reject "a membership theorem is not a predicate-definition association"
        (Map.singleton 0 (Reference.DefinitionRule
            (rule 2 (Semantic.MembershipAtomTemplate x y) (row 1 [x]))))
    (_,result,_) <- runSnapshotCase
        (Map.fromList [(0,Reference.ClassificationRule forward),(1,Reference.ClassificationRule backward)]) [] Set.empty target
    assertReferenceAnswer "ordinary classification cycles remain legal but ungrounded" False target result
    (_,membershipResult,_) <- runSnapshotCase
        (Map.singleton 0 (Reference.ClassificationRule
            (rule 2 (Semantic.MembershipAtomTemplate x y) (row 1 [x]))))
        [Reference.ReferenceFact (Semantic.MembershipAtomTemplate a (referenceSeed 1)) (referenceSummary 0)] Set.empty target
    assertReferenceAnswer "a registered membership classification remains an ordinary producer" True target membershipResult

runSnapshotCase
    :: Map Natural Reference.ReferenceRegistration -> [Reference.ReferenceFact Natural]
    -> Set Reference.GroundTerm -> Reference.GroundAtom
    -> IO (Reference.ReferenceSnapshot Natural, Reference.ReferenceEvaluation Natural, Word)
runSnapshotCase registrations facts aliases target = do
    let run allowance = Reference.evaluateFormation allowance registrations facts aliases target
        (outcome,used) = run 2000000
        rules = Reference.registrationRule <$> registrations
    (snapshot,result) <- expectRight outcome
    exact <- expectRight (fst (run used))
    assertEqual "the exact shared allowance completes the same snapshot and answers" (snapshot,result) exact
    assertEqual "one-short shared work is explicit exhaustion"
        (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1)))
    checkReferenceWitnesses rules facts (Reference.referenceSnapshotInitial snapshot)
    checkReferenceWitnesses rules facts result
    ReferenceReplay.checkReferenceReplay rules facts result
    pure (snapshot,result,used)

referenceSeed :: Natural -> Reference.GroundTerm
referenceSeed = Semantic.TemplateVariable . Reference.OpaqueSeed

referenceSummary :: Natural -> Reference.WitnessSummary Natural
referenceSummary origin = Reference.WitnessSummary (Set.singleton origin) Set.empty Set.empty

runReferenceCase
    :: [Reference.ReferenceRule] -> [Reference.ReferenceFact Natural] -> Reference.GroundAtom
    -> IO (Reference.ReferenceEvaluation Natural, Word)
runReferenceCase rules facts target = do
    let terms = toList
        seeds = Set.fromList (concatMap terms (target : [row | Reference.ReferenceFact row _ <- facts]))
        templates = Set.unions (Reference.referenceRuleTemplates <$> rules)
        registered = Map.fromList (zip [0..] rules)
    support <- expectRight (fst (Reference.enumerateSupport 1000000 seeds templates))
    let run allowance = Reference.evaluateRequests allowance support registered facts target
        (outcome, used) = run 2000000
    result <- expectRight outcome
    exact <- expectRight (fst (run used))
    assertEqual "exact work boundary preserves the completed reference result" result exact
    assertEqual "one-short is exhaustion, never cached absence"
        (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1)))
    checkReferenceWitnesses registered facts result
    ReferenceReplay.checkReferenceReplay registered facts result
    production <- runProductionRules registered facts target
    let hasTarget = any ((== target) . fst) . Map.keys . Reference.referenceAnswers
    assertEqual "production and reference agree on requested truth; selected proofs replay independently"
        (hasTarget result) (hasTarget production)
    pure (result, used)

-- The fixture owner interns atom/eligibility identities independently of proof
-- history and reconstructs the production recipes through the Core replay helper.
runProductionRules
    :: Map Natural Reference.ReferenceRule -> [Reference.ReferenceFact Natural] -> Reference.GroundAtom
    -> IO (Reference.ReferenceEvaluation Natural)
runProductionRules = runProductionWithViews Set.empty

runProductionWithViews
    :: Set Natural -> Map Natural Reference.ReferenceRule -> [Reference.ReferenceFact Natural] -> Reference.GroundAtom
    -> IO (Reference.ReferenceEvaluation Natural)
runProductionWithViews viewOrdinals registered facts target = do
    let registrations = Map.mapWithKey (\ordinal rule ->
            if Set.member ordinal viewOrdinals then Reference.DefinitionRule rule else Reference.ClassificationRule rule) registered
        run allowance = Reference.runReference allowance
            (Production.evaluateProduction (Production.freeTermsMayAgree (Reference.chargeReferenceWork . fromIntegral))
                pure (\a b -> pure (a == b)) registrations facts Set.empty target)
        (outcome,used) = run 2000000
    evaluation <- expectRight outcome
    assertEqual "scheduled rule evaluation shares exact accounting" (outcome,used) (run used)
    assertEqual "one-short scheduled evaluation is exhaustion" (Left Reference.ReferenceWorkExhausted) (fst (run (used - 1)))
    checkReferenceWitnesses registered facts evaluation
    ReferenceReplay.checkReferenceReplay registered facts evaluation
    pure evaluation

assertReferenceAnswer :: String -> Bool -> Reference.GroundAtom -> Reference.ReferenceEvaluation Natural -> Assertion
assertReferenceAnswer label expected row result = assertEqual label expected
    (any ((== row) . fst) (Map.keys (Reference.referenceAnswers result)))

-- Validate the witness relation independently of request scheduling/unification.
-- Checked-kernel reconstruction belongs to the forthcoming scoped adapter.
checkReferenceWitnesses
    :: Map Natural Reference.ReferenceRule -> [Reference.ReferenceFact Natural]
    -> Reference.ReferenceEvaluation Natural -> Assertion
checkReferenceWitnesses rules facts result =
    forM_ (Map.toAscList (Reference.referenceWitnesses result)) \(identifier, witness) -> do
        case Reference.referenceWitnessRecipe witness of
            Reference.ObservedRow ordinal -> case drop (fromIntegral ordinal) facts of
                Reference.ReferenceFact row summary : _ -> do
                    assertEqual "observed statement" row (Reference.referenceWitnessAtom witness)
                    assertEqual "observed eligibility" summary (Reference.referenceWitnessSummary witness)
                [] -> assertFailure "an observation named a nonexistent input"
            Reference.SameDenotation{} ->
                assertFailure "the free-constructor reference invented a denotation equality"
            Reference.AppliedRule ordinal bindings forest -> do
                rule <- maybe (assertFailure "unknown rule" >> fail "unknown rule") pure (Map.lookup ordinal rules)
                let instantiate = \case
                        Semantic.TemplateClosed value -> pure (Semantic.TemplateClosed value)
                        Semantic.TemplateVariable variable -> maybe
                            (assertFailure "missing rule binding" >> fail "missing binding") pure (Map.lookup variable bindings)
                        Semantic.TemplateProvider provider arguments -> Semantic.TemplateProvider provider <$> traverse instantiate arguments
                        Semantic.TemplateOrderedPair left right -> Semantic.TemplateOrderedPair <$> instantiate left <*> instantiate right
                    statement = Semantic.traverseAtomTemplateArguments instantiate
                    checkTree expected actual = case (expected,actual) of
                        (Semantic.RulePremiseAnd left right, Reference.PremiseConjunction a b) ->
                            (<>) <$> checkTree left a <*> checkTree right b
                        (Semantic.RulePremiseAtom row, Reference.PremiseLeaf prior) -> do
                            assertBool "witness prerequisites are strictly earlier" (prior < identifier)
                            found <- maybe (assertFailure "missing prerequisite" >> fail "missing prerequisite") pure
                                (Map.lookup prior (Reference.referenceWitnesses result))
                            required <- statement row
                            assertEqual "the complete premise row is preserved" required (Reference.referenceWitnessAtom found)
                            pure [Reference.referenceWitnessSummary found]
                        _ -> assertFailure "antecedent grouping changed" >> pure []
                instantiated <- statement (Reference.referenceRuleConclusion rule)
                assertEqual "selected result under the same substitution" instantiated (Reference.referenceWitnessAtom witness)
                assertEqual "every original header is retained" (length (Reference.referenceRulePremises rule)) (length forest)
                summaries <- concat <$> sequence (zipWith checkTree (Reference.referenceRulePremises rule) forest)
                assertEqual "exact premise origins" (Set.unions (Reference.witnessOrigins <$> summaries))
                    (Reference.witnessOrigins (Reference.referenceWitnessSummary witness))
                assertEqual "exact source occurrences" (Set.insert ordinal (Set.unions (Reference.witnessOccurrences <$> summaries)))
                    (Reference.witnessOccurrences (Reference.referenceWitnessSummary witness))
                assertEqual "required support survives composition"
                    (Reference.referenceRuleSupport rule <> Set.unions (Reference.witnessSupport <$> summaries))
                    (Reference.witnessSupport (Reference.referenceWitnessSummary witness))

rejectsMalformedRuleProviderApplications :: Assertion
rejectsMalformedRuleProviderApplications = do
    fixture <- makeFixture 1
    let head' = fixtureHead fixture 0
        malformed term =
            checkedRuleSkeleton
                0
                (Semantic.RulePremiseBundles
                    (Semantic.RulePremiseAtom
                        (Semantic.StructureAtomTemplate
                            head' (Vector.singleton term))
                        :| []))
                (Semantic.StructureAtomTemplate
                    head' (Vector.singleton term))
        assertMalformed label result = case result of
            Left{} -> pure ()
            Right{} -> assertFailure (label <> " was accepted")
    assertMalformed "empty finite-set provider"
        (malformed
            (Semantic.TemplateProvider
                Semantic.FiniteSetLiteralSourceProvider Vector.empty))
    assertMalformed "wrong intrinsic arity"
        (malformed
            (Semantic.TemplateProvider
                (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
                Vector.empty))
    assertMalformed "wrong global arity"
        (malformed
            (Semantic.TemplateProvider
                (Semantic.GlobalSourceProvider
                    (binaryProviderReference "binary" 22))
                (Vector.singleton
                    (Semantic.TemplateProvider
                        (Semantic.IntrinsicSourceProvider
                            Semantic.EmptySetProvider)
                        Vector.empty))))

binaryProviderReference :: Text -> Natural -> Semantic.GlobalBindingRef
binaryProviderReference label ordinal =
    Semantic.globalBindingRef
        (Semantic.declarationSlot
            preludeModuleName (localDeclarationOrdinal ordinal))
        (Semantic.SemanticExpressionFunction
            (Raw.HoleCons
                (Raw.TokenCons
                    (Raw.Word label)
                    (Raw.HoleCons Raw.End))))

rejectsMismatchedRichGoalEvidence :: Assertion
rejectsMismatchedRichGoalEvidence = do
    fixture <- makeFixture 2
    evidence <- expectRight
        (findDirectEvidence fixture (directIndex fixture [(0, 0, "source")]) 0)
        >>= maybe
            (assertFailure "the rich-goal fixture had no direct witness"
                >> fail "unreachable")
            pure
    let mismatchedShape = Semantic.StructureAtomTemplate
            (fixtureHead fixture 1)
            (Vector.singleton (Core.CBound 0))
    case Notion.provedRichGoal
            Notion.groundNotionKeyFromTemplate
            mismatchedShape
            evidence of
        Nothing -> pure ()
        Just{} -> assertFailure
            "mismatched rich shape and logical evidence were accepted"

countsArenaAllocations :: Assertion
countsArenaAllocations = do
    fixture <- makeFixture 1
    let term = Core.CBound 0
        head' = fixtureHead fixture 0
        formula = atom fixture head' [term]
        proposition = checkedProposition fixture (Core.CAnd formula formula)
        key = Notion.groundNotionKeyFromTemplate (Semantic.StructureAtomTemplate head' (Vector.singleton term))
        observe :: Bool -> Except.ExceptT () (State.State (Natural, Natural)) ()
        observe projection = State.modify' (\(nodes, projections) ->
            (nodes + 1, projections + if projection then 1 else 0))
        charge stop _ = do
            (nodes, _) <- State.get
            when (stop && nodes > 0) (Except.throwE ())
        run stop = State.runState (Except.runExceptT
            (Notion.withFormationWitnessArena \arena ->
                fst <$> Notion.runFormationConstruction observe (do
                    source <- Notion.prepareFormationHypothesis (charge stop) proposition ("source" :: Text)
                    _ <- Notion.directFormationEvidence (charge stop) key source (Notion.ConjunctionLeft Notion.ConjunctionHere) 0
                    _ <- Notion.directFormationEvidence (charge stop) key source (Notion.ConjunctionLeft Notion.ConjunctionHere) 0
                    pure ()) arena)) (0,0)
    case run False of
        (Right (Right ()), counts) -> counts @?= (2,1)
        _ -> assertFailure "shared projection accounting failed"
    case run True of
        (Left (), counts) -> counts @?= (1,0)
        _ -> assertFailure "the exhausted construction lost its allocated node"

diamondArenaReplay :: Assertion
diamondArenaReplay = do
    fixture <- makeFixture 2
    unusedView <- unaryView fixture 0 0 1
    let term = Core.CBound 0
        notion index = Semantic.StructureAtomTemplate (fixtureHead fixture index) (Vector.singleton term)
        formula = atom fixture (fixtureHead fixture 0) [term]
        target = checkedProposition fixture formula
        step = checkedProposition fixture (Core.CImp formula (Core.CImp formula formula))
        charge = Reference.chargeReferenceWork . fromIntegral
        run size allowance = Reference.runReference allowance (Notion.withFormationWitnessArena \arena ->
            fst <$> Notion.runFormationConstruction (const (pure ())) (do
                root <- Notion.prepareFormationHypothesis charge target "seed"
                first <- Notion.directFormationEvidence charge (Notion.groundNotionKeyFromTemplate (notion 0))
                    root Notion.ConjunctionHere 0
                -- Alternatives must not escape the arena through unused source
                -- slots or imported facts, even when they were allocated first.
                _ <- Notion.prepareFormationHypothesis charge (checkedProposition fixture Core.CFalsum) "unused"
                _ <- Notion.applyFormationRule charge (Notion.FormationViewRule unusedView)
                    (Map.singleton 0 term) [Notion.FormationPremiseEvidenceLeaf first] (Semantic.AtomicLeaf (notion 1))
                last' <- foldM (\parent _ -> Notion.applyUniversalSource charge
                    (Notion.directFormationSourceEvidence (Notion.DirectFormationSource step Notion.ConjunctionHere "step" 1))
                    (replicate 2 (SourceEvidence.EliminateGuard (Notion.FormationPremiseEvidenceLeaf parent)))
                    Notion.ConjunctionHere (notion 0)) first [1..size :: Int]
                Notion.selectFormationEvidence charge Notion.defaultFormationSearchLimits last') arena)
    work <- forM [4,16,32,64,128] \size -> do
        let observed@(outcome, used) = run size 1000000
        evidence <- expectRight =<< expectRight outcome
        let materialized = Notion.materializeFormationEvidence Notion.defaultFormationSearchLimits evidence
        assertEqual "selection retains only the founded source graph" (Set.fromList ["seed", "step"])
            (Set.fromList (Notion.materializedNotionHypothesisOrigin <$> toList (Notion.materializedFormationHypotheses materialized)))
        Notion.materializedFormationImports materialized @?= Vector.empty
        replayed <- measureFormationReplay "diamond" size
            (expectRight =<< replayMaterializedFormationResult fixture materialized target)
        assertEqual "diamond emission grows with distinct nodes" (fromIntegral (7 * size - 2))
            (Derivation.replayedScopedKernelNodeCount replayed)
        void (expectRight =<< expectRight (fst (run size used)))
        case fst (run size (used - 1)) of
            Left Reference.ReferenceWorkExhausted -> pure ()
            _ -> assertFailure "selected-graph traversal escaped the shared work allowance"
        when (size == 4) (assertEmittedLimits fixture evidence target)
        -- Force both results here; measurement does not retain either arena.
        observed `seq` pure used
    case work of
        [_,small,_,_,large] -> assertBool "graph construction and selection do not unfold diamonds" (large < 12 * small)
        _ -> assertFailure "diamond measurement fixture changed"

pairedNotionLeaves :: Assertion
pairedNotionLeaves = do
    fixture <- makeFixture 1
    let formula = atom fixture (fixtureHead fixture 0) [Core.CBound 0]
        exact = Core.CAnd formula formula
        residual = Core.CExists Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1))
        universal = Core.CForall Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0))
        source = Core.CAnd Core.CTruth (Core.CAnd exact (Core.CAnd residual universal))
        opaque = SourceEvidence.SourceResidual Nothing
        evidence = SourceEvidence.SourceAnd opaque
            (SourceEvidence.SourceAnd (SourceEvidence.SourceAtom ("exact" :: Text))
                (SourceEvidence.SourceAnd opaque (SourceEvidence.SourceBind (SourceEvidence.SourceAtom "bound"))))
        charge = Reference.chargeReferenceWork . fromIntegral
        run core tree = Reference.runReference 1000000 (State.evalStateT
            (SourceEvidence.notionLeaves (State.lift (charge 1))
                (Notion.extendConjunctionProjection charge) Notion.rootConjunctionProjection
                (checkedProposition fixture core) tree) Notion.emptyConjunctionProjections)
    leaves <- expectRight (fst (run source evidence))
    fmap (Core.scopedCoreTerm . SourceEvidence.sourceLeafFormula) leaves @?= [exact, residual, universal]
    case fmap SourceEvidence.sourceLeafDescription leaves of
        [SourceEvidence.LeafAtom "exact", SourceEvidence.LeafResidual Nothing,
                SourceEvidence.LeafUniversal (SourceEvidence.UniversalBind (SourceEvidence.UniversalReturn (SourceEvidence.AtomLeaf "bound")))] -> pure ()
        _ -> assertFailure "the paired walk changed an exact atom or exposed a residual body"
    for_ leaves \leaf ->
        Notion.projectConjunctionPath (Notion.conjunctionProjectionPath (SourceEvidence.sourceLeafPath leaf)) source
            @?= Just (Core.scopedCoreTerm (SourceEvidence.sourceLeafFormula leaf))
    neutral <- expectRight (fst (run Core.CTruth (opaque :: SourceEvidence.SourceEvidence () Text)))
    assertBool "neutral truth contributes no request" (null neutral)
    let compile core description = fst (Reference.runReference 10000 (Goal.compileGoal (charge 1) core description))
    atomicPlan <- expectRight (compile exact (SourceEvidence.SourceAtom ("exact" :: Text)))
    case Goal.goalOperation atomicPlan of
        Goal.AtomicGoal "exact" -> pure ()
        _ -> assertFailure "logical inspection opened an exact atomic encoding"
    opaquePlan <- expectRight (compile (Core.CImp formula formula)
        (SourceEvidence.SourceInputs Nothing [] :: SourceEvidence.SourceEvidence () Text))
    assertEqual "opening a complete opaque description does not rediscover child inputs"
        [SourceEvidence.SourceInputs Nothing [],SourceEvidence.SourceInputs Nothing []]
        (Goal.goalEvidence <$> Goal.goalChildren opaquePlan)
    existential <- expectRight (compile (Core.CExists Core.TySet (Core.COr formula Core.CTruth))
        (SourceEvidence.SourceExists (SourceEvidence.SourceOr (SourceEvidence.SourceAtom "witness") opaque)))
    assertBool "a positive disjunctive body admits finite witness search" (Goal.goalPositive existential)
    hypothetical <- expectRight (compile (Core.CExists Core.TySet (Core.CImp formula formula))
        (SourceEvidence.SourceExists (SourceEvidence.SourceRequire (SourceEvidence.SourceAtom "assumption")
            (SourceEvidence.SourceAtom "result"))))
    assertBool "witness search does not open a hypothetical body" (not (Goal.goalPositive hypothetical))
    for_ [(Core.CForall Core.TySet residual, SourceEvidence.SourceBind opaque),
            (Core.CExists Core.TySet residual, SourceEvidence.SourceExists opaque),
            (Core.COr formula formula, SourceEvidence.SourceOr (SourceEvidence.SourceAtom "left") opaque),
            (Core.CEq Core.TyProp formula formula, SourceEvidence.SourceIff (SourceEvidence.SourceAtom "left") opaque),
            (Core.CImp formula formula, SourceEvidence.SourceRequire (SourceEvidence.SourceAtom "guard") opaque)]
        \(core, tree) -> do
            selected <- expectRight (fst (run core tree))
            case fmap SourceEvidence.sourceLeafDescription selected of
                [SourceEvidence.LeafResidual Nothing] -> pure ()
                _ -> assertFailure "an unsupported telescope did not remain one whole leaf"
    costs <- for [16, 32, 64, 128 :: Int] \width -> do
        let core = foldr1 Core.CAnd (replicate width formula)
            tree = foldr1 SourceEvidence.SourceAnd (replicate width (SourceEvidence.SourceAtom "leaf"))
            (result, work) = run core tree
        selected <- expectRight result
        length selected @?= width
        pure (fromIntegral work / (fromIntegral width * log (fromIntegral width + 1)) :: Double)
    for_ (zip costs (drop 1 costs)) \(smaller, larger) ->
        assertBool "scope spine preparation shares prefixes within n log n growth" (larger < 1.1 * smaller)

scopedIntroductionReplay :: Assertion
scopedIntroductionReplay = do
    fixture <- makeFixture 1
    let predicate = atom fixture (fixtureHead fixture 0) [Core.CBound 0]
        captured = atom fixture (fixtureHead fixture 0) [Core.CBound 1]
        pairBody = Core.CAnd predicate captured
        body = Core.CAnd pairBody pairBody
        target = checkedProposition fixture (Core.CForall Core.TySet (Core.CImp predicate body))
        typing = Identity.globalTypingFromClosure (fixtureClosure fixture)
        childTerm term = expectRight (Core.checkScopedCanonicalCore typing [Core.TySet,Core.TySet] term)
        charge = Reference.chargeReferenceWork . fromIntegral
        run :: (forall scope. Notion.FormationConstruction scope Text (Except.ExceptT Reference.ReferenceFailure (State.State Word)) (Notion.FormationEvidence Text))
            -> IO (Notion.FormationEvidence Text)
        run action = expectRight =<< expectRight (fst (Reference.runReference 1000000
            (Notion.withFormationWitnessArena (\arena -> fst <$> Notion.runFormationConstruction (const (pure ())) action arena))))
        limits = Notion.defaultFormationSearchLimits
    guardFormula <- childTerm predicate
    bodyFormula <- childTerm body
    pairFormula <- childTerm pairBody
    capturedFormula <- childTerm captured
    implication <- childTerm (Core.CImp predicate body)
    child <- run do
        local <- Notion.prepareFormationHypothesis charge guardFormula ("temporary" :: Text)
        inherited <- Notion.prepareFormationHypothesis charge capturedFormula "outer"
        parent <- Notion.directFormationEvidence charge (Notion.groundNotionKeyFromFormula guardFormula)
            local Notion.ConjunctionHere 0
        outer <- Notion.directFormationEvidence charge (Notion.groundNotionKeyFromFormula capturedFormula)
            inherited Notion.ConjunctionHere 1
        pair <- Notion.composeFormationEvidence charge pairFormula
            (Notion.FormationPremiseEvidenceAnd (Notion.FormationPremiseEvidenceLeaf parent) (Notion.FormationPremiseEvidenceLeaf outer))
        witness <- Notion.composeFormationEvidence charge bodyFormula
            (Notion.FormationPremiseEvidenceAnd (Notion.FormationPremiseEvidenceLeaf pair) (Notion.FormationPremiseEvidenceLeaf pair))
        Notion.selectFormationEvidence charge limits witness
    guarded <- run do
        witness <- Notion.introduceFormationEvidence charge pure (Notion.FormationAssumptionIntroduction "temporary") implication child
        Notion.selectFormationEvidence charge limits witness
    let alignParent formula = do
                result <- Reference.countedReferenceOperation (\work ->
                    let (outcome,remaining) = Core.countedInstantiateScopedPrefix work 1 Map.empty formula
                    in (Bifunctor.first (\case Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted
                                               failure -> Reference.ReferenceInvalidInput (Text.pack (show failure))) outcome,remaining))
                case result of
                    Core.ScopedInstantiationClosed parent -> pure parent
                    _ -> Reference.invalidReferenceInput "a child hypothesis mentions its fresh binder"
    closed <- run do
        witness <- Notion.introduceFormationEvidence charge alignParent Notion.FormationSetIntroduction target guarded
        Notion.selectFormationEvidence charge limits witness
    let materialized = Notion.materializeFormationEvidence limits closed
    assertEqual "only the inherited hypothesis is exported" ["outer"]
        (Notion.materializedNotionHypothesisOrigin <$> toList (Notion.materializedFormationHypotheses materialized))
    replayed <- expectRight =<< replayMaterializedFormationResult fixture materialized target
    assertEqual "the temporary assumption is discharged" (Set.singleton (Derivation.hypothesisIx 0))
        (Derivation.replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "sharing stays below the fresh binder" target (Derivation.replayedScopedKernelTarget replayed)
    wrongCapture <- replayMaterializedFormation fixture materialized
        (checkedProposition fixture (Core.CForall Core.TySet
            (Core.CImp predicate (atom fixture (fixtureHead fixture 0) [Core.CBound 1]))))
    case wrongCapture of
        Left Declaration.TransientFormationProofTargetMismatch -> pure ()
        _ -> assertFailure "an introduced proof changed its captured argument"
    let parameter index = Semantic.TemplateVariable (Semantic.ViewVariableIx index)
        described index = SourceEvidence.SourceAtom
            (Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.singleton (parameter index)))
        conjunction = SourceEvidence.SourceAnd (described 0) (described 1)
        source = Semantic.describedResidualTemplate (Core.scopedCoreTerm target)
            (SourceEvidence.SourceBind (SourceEvidence.SourceRequire (described 0)
                (SourceEvidence.SourceAnd conjunction conjunction)))
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
    projections <- expectRight (fst (Reference.runReference 100000 do
        base <- admit (Rule.compileConclusionRule charge 1 [] (Semantic.WholeLeaf source))
        admit (Projection.compileWholeEliminations charge base)))
    (plan,projected) <- case [(plan,rule) | (_,plan,rule) <- projections,
            let (_,_,conclusion) = Rule.ruleDescription rule,
            conclusion == Semantic.AtomicLeaf (Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.singleton (parameter 0)))] of
        selected:_ -> pure selected
        [] -> assertFailure "introduced whole lost its captured projection" >> error "unreachable"
    assertBool "projection consumes evidence without requesting a new introduction" (Rule.ruleIsElimination projected)
    let instanceTerm = Core.CIntrinsic Core.Empty
        instanceShape = Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.singleton instanceTerm)
        instanceFormula = checkedProposition fixture (atom fixture (fixtureHead fixture 0) [instanceTerm])
        conclusion = Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.singleton (Core.CBound 0))
        conclusionFormula = checkedProposition fixture predicate
    reused <- run do
        whole <- Notion.introduceFormationEvidence charge alignParent Notion.FormationSetIntroduction target guarded
        input <- Notion.prepareFormationHypothesis charge instanceFormula "instance"
        guardProof <- Notion.directFormationEvidence charge (Notion.groundNotionKeyFromTemplate instanceShape)
            input Notion.ConjunctionHere 0
        witness <- Notion.applyProjectedEvidence charge plan
            (Map.fromList [(0,Core.CBound 0),(1,instanceTerm)])
            [Notion.FormationPremiseEvidenceLeaf whole,Notion.FormationPremiseEvidenceLeaf guardProof]
            (Semantic.AtomicLeaf conclusion)
        Notion.selectFormationEvidence charge limits witness
    let projectedEvidence = Notion.materializeFormationEvidence limits reused
    Notion.materializedFormationImports projectedEvidence @?= Vector.empty
    Set.fromList (Notion.materializedNotionHypothesisOrigin <$> toList (Notion.materializedFormationHypotheses projectedEvidence))
        @?= Set.fromList ["outer","instance"]
    void (expectRight =<< replayMaterializedFormationResult fixture projectedEvidence conclusionFormula)

sharedProjectionReplay :: Assertion
sharedProjectionReplay = do
    fixture <- makeFixture 1
    let head' = fixtureHead fixture 0
        argument = Core.CBound 0
        shape = Semantic.StructureAtomTemplate head' (Vector.singleton argument)
        key = Notion.groundNotionKeyFromTemplate shape
        leaf = atom fixture head' [argument]
        limits = Notion.defaultFormationSearchLimits
    growth <- for [3, 16, 32, 64, 128 :: Int] \width -> do
        let proposition = foldr1 Core.CAnd (replicate width leaf)
            checked = checkedProposition fixture proposition
        let charge = Reference.chargeReferenceWork . fromIntegral
            paths 1 prefix = pure [prefix]
            paths count prefix = do
                left <- Notion.extendConjunctionProjection charge False prefix
                right <- Notion.extendConjunctionProjection charge True prefix
                (left :) <$> paths (count - 1) right
            construct bounded = Reference.runReference 10000000 do
                projections <- State.evalStateT (paths width Notion.rootConjunctionProjection)
                    Notion.emptyConjunctionProjections
                Notion.withFormationWitnessArena \arena ->
                    fst <$> Notion.runFormationConstruction (const (pure ())) (do
                        root <- Notion.prepareFormationHypothesis charge checked "shared source"
                        leaves <- for projections \path -> Notion.FormationPremiseEvidenceLeaf <$>
                            Notion.directPreparedFormationEvidence charge key root path 0
                        let bundle = foldr1 Notion.FormationPremiseEvidenceAnd leaves
                        Notion.materializeFormationPremiseEvidence charge bounded bundle) arena
            materialize bounded = expectRight =<< expectRight (fst (construct bounded))
        materialized <- materialize limits
        replayed <- measureFormationReplay "projection" width
            (expectRight =<< replayMaterializedFormationResult fixture materialized checked)
        assertEqual "one original source survives all shared introductions"
            (Set.singleton (Derivation.hypothesisIx 0))
            (Derivation.replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual "projection nodes and let overhead grow linearly"
            (fromIntegral (7 * width - 9))
            (Derivation.replayedScopedKernelNodeCount replayed)
        assertEqual "the exact target survives hypothesis reindexing" checked
            (Derivation.replayedScopedKernelTarget replayed)
        when (width == 3) do
            let nodes = Derivation.replayedScopedKernelNodeCount replayed
                depth = Derivation.replayedScopedKernelMaximumDepth replayed
            for_ [(nodes, depth, True), (nodes - 1, depth, False), (nodes, depth - 1, False)]
                \(nodeLimit, depthLimit, shouldPass) -> do
                    bounded <- expectJust (Notion.formationSearchLimitsWithEqualityChain
                        64 64 64 1000000 nodeLimit depthLimit 16)
                    selected <- materialize bounded
                    result <- replayMaterializedFormation fixture selected checked
                    case (shouldPass, result) of
                        (True, Right ()) -> pure ()
                        (False, Left (Declaration.TransientFormationProofFailed
                            Notion.FormationProofDerivationLimitExceeded{})) -> pure ()
                        _ -> assertFailure "emitted proof limits did not include shared binding overhead"
        pure (width, snd (construct limits))
    diagnostic <- Environment.lookupEnv "FELIX_NOTION_TEST_COST"
    when (isJust diagnostic) (putStrLn ("projection construction work: " <> show growth))
    let normalized (width, work) = fromIntegral work / (fromIntegral width * log (fromIntegral width + 1)) :: Double
    for_ (zip (drop 1 growth) (drop 2 growth)) \(smaller, larger) ->
        assertBool "shared-prefix preparation and construction stay within n log n growth"
            (normalized larger < 1.1 * normalized smaller)

-- Diagnostic batches exercise the production emitter and fresh kernel replay.
-- The ordinary suite checks deterministic growth; timing is never an assertion.
measureFormationReplay :: String -> Int -> IO value -> IO value
measureFormationReplay label size action = do
    result <- action
    diagnostic <- Environment.lookupEnv "FELIX_NOTION_TEST_COST"
    when (isJust diagnostic) do
        started <- Clock.getMonotonicTimeNSec
        replicateM_ 20 action
        stopped <- Clock.getMonotonicTimeNSec
        putStrLn (label <> ": size=" <> show size <> " replays=20 ns=" <> show (stopped - started))
    pure result

queriesSourceTerminalEvidenceDirectly :: Assertion
queriesSourceTerminalEvidenceDirectly = do
    fixture <- makeFixture 1
    let head' = fixtureHead fixture 0
        argument = Core.CBound 0
        shape = Semantic.StructureAtomTemplate
            head' (Vector.singleton argument)
        key = Notion.groundNotionKeyFromTemplate shape
        target = atom fixture head' [argument]
        projectedSource = Notion.DirectFormationSource
            (checkedProposition fixture (Core.CAnd target target))
            (Notion.ConjunctionLeft Notion.ConjunctionHere)
            ("projected source" :: Text)
            0
        projectedEvidence = expectPureRight
            (selectedDirectEvidence key projectedSource)
        projectedGoal = fromMaybe
            (error "projected direct evidence lost its rich shape")
            (Notion.provedRichGoal
                Notion.groundNotionKeyFromTemplate shape projectedEvidence)
        index = Notion.insertUnarySource
            shape
            (Just (Notion.UnaryStructurePremise head'))
            projectedGoal
            Notion.emptyUnarySourceIndex
        exactLimits = fromMaybe
            (error "valid exact direct-query limits were rejected")
            (Notion.formationSearchLimits 1 1 1 1 2 1)
        shallowLimits = fromMaybe
            (error "valid shallow direct-query limits were rejected")
            (Notion.formationSearchLimits 1 1 1 1 1 1)
    hit <- expectRight
        (Notion.findDirectFormationEvidenceWithLimits exactLimits index key)
    case hit of
        Notion.FormationFound evidence statistics -> do
            let materialized = Notion.materializeFormationEvidence exactLimits evidence
            case toList (Notion.materializedFormationHypotheses materialized) of
                [hypothesis] ->
                    assertEqual "the direct query returns the selected origin"
                        "projected source"
                        (Notion.materializedNotionHypothesisOrigin hypothesis)
                hypotheses -> assertFailure
                    ("the direct query selected " <> show (length hypotheses)
                        <> " hypotheses")
            assertEqual "the direct query reports only one direct atom"
                Notion.emptyFormationSearchStatistics
                    { Notion.formationSearchDirectGroundAtoms = 1 }
                statistics
        Notion.FormationNotFound{} ->
            assertFailure "an indexed direct source was not found"
    case Notion.findDirectFormationEvidenceWithLimits shallowLimits index key of
        Right (Notion.FormationFound evidence _) -> do
            failed <- replayMaterializedFormation fixture
                (Notion.materializeFormationEvidence shallowLimits evidence) (checkedProposition fixture target)
            case failed of
                Left (Declaration.TransientFormationProofFailed Notion.FormationProofDerivationLimitExceeded{}) -> pure ()
                _ -> assertFailure "the direct witness escaped its emitted-node limit"
        _ -> assertFailure "a direct witness was rejected before emission"
    case Notion.findDirectFormationEvidenceWithLimits
            exactLimits
            (Notion.emptyUnarySourceIndex :: TestUnarySourceIndex)
            key of
        Right (Notion.FormationNotFound explanation) -> do
            assertEqual "a terminal miss performs no formation work"
                Notion.emptyFormationSearchStatistics
                (Notion.formationFailureStatistics explanation)
            assertEqual "a terminal miss has no frontier"
                Nothing
                (Notion.formationFailureFrontier explanation)
            assertBool "a terminal miss never considers parameter erasure"
                (not (Notion.formationFailureConsideredParameterErasure explanation))
        Right Notion.FormationFound{} ->
            assertFailure "an absent terminal source was found"
        Left failure -> assertFailure
            ("an absent terminal source exhausted a limit: " <> show failure)


retainsMaterializedHypothesisOrigins :: Assertion
retainsMaterializedHypothesisOrigins = do
    fixture <- makeFixture 1
    evidence <- expectJust =<< expectRight
        (findDirectEvidence fixture (directIndex fixture [(0, 0, "nearest")]) 0)
    let materialized = Notion.materializeFormationEvidence Notion.defaultFormationSearchLimits evidence
    case toList (Notion.materializedFormationHypotheses materialized) of
        [hypothesis] -> do
            assertEqual "selected origin survives materialization"
                "nearest"
                (Notion.materializedNotionHypothesisOrigin hypothesis)
            assertEqual "selected proposition survives materialization"
                (checkedProposition fixture
                    (atom fixture (fixtureHead fixture 0) [Core.CBound 0]))
                (Notion.materializedNotionHypothesisProposition hypothesis)
        hypotheses -> assertFailure
            ("expected one materialized hypothesis, got "
                <> show (length hypotheses))

transportsCheckedNotionEvidence :: Assertion
transportsCheckedNotionEvidence = do
    fixture <- makeFixture 1
    let head' = fixtureHead fixture 0
        left = Core.CBound 0
        right = Core.CIntrinsic Core.Empty
        premiseAtom = Semantic.StructureAtomTemplate
            head' (Vector.singleton left)
        targetAtom = Semantic.StructureAtomTemplate
            head' (Vector.singleton right)
        premiseTerm = atom fixture head' [left]
        equalityTerm = Core.CEq Core.TySet left right
        sourceTerm = Core.CAnd premiseTerm equalityTerm
        source = checkedProposition fixture sourceTerm
        equality = checkedProposition fixture equalityTerm
        premise = checkedProposition fixture premiseTerm
        target = checkedProposition fixture (atom fixture head' [right])
        predicate = checkedProposition fixture
            (Core.CLam Core.TySet
                (atom fixture head' [Core.CBound 0]))
        origin :: Text
        origin = "combined source"
        parentSource = Notion.DirectFormationSource
            source
            (Notion.ConjunctionLeft Notion.ConjunctionHere)
            origin
            0
        equalitySource = Notion.DirectFormationSource
            source
            (Notion.ConjunctionRight Notion.ConjunctionHere)
            origin
            1
    transport <- expectJust
        (Notion.formationEqualityTransport
            equalitySource equality Notion.FormationEqualityLeftToRight)
    assertBool "an unrelated source path cannot certify equality transport"
        (isNothing
            (Notion.formationEqualityTransport
                parentSource equality Notion.FormationEqualityLeftToRight))
    evidence <- buildWitness do
        parent <- directWitness (Notion.groundNotionKeyFromTemplate premiseAtom) parentSource
        Notion.applyEqualityTransportWithLimits (const (pure ())) Notion.defaultFormationSearchLimits
            (transport :| []) predicate premise target parent premiseAtom targetAtom
    assertBool "transported evidence records equality use"
        (Notion.formationEvidenceUsesEquality evidence)
    assertEqual "one selected equality edge"
        1 (Notion.formationEvidenceEqualityTransportSteps evidence)
    let materialized = Notion.materializeFormationEvidence Notion.defaultFormationSearchLimits evidence
    assertEqual "one proof local supplies both projected leaves"
        1
        (Vector.length
            (Notion.materializedFormationHypotheses materialized))
    replayed <- replayMaterializedFormation fixture materialized target
    assertEqual "the public consumer checks the target and exact local authority"
        (Right ()) replayed
    wrongTarget <- expectRight (Core.checkScopedCanonicalCore
        (Identity.globalTypingFromClosure (fixtureClosure fixture))
        [Core.TySet] Core.CFalsum)
    mismatch <- replayMaterializedFormation fixture materialized wrongTarget
    assertEqual "the consumer rejects a different requested target"
        (Left Declaration.TransientFormationProofTargetMismatch) mismatch
    closedTarget <- expectRight (Core.checkScopedCanonicalCore
        (Identity.globalTypingFromClosure (fixtureClosure fixture)) [] Core.CTruth)
    contextFailure <- replayMaterializedFormation fixture materialized closedTarget
    case contextFailure of
        Left (Declaration.TransientFormationProofFailed
                (Notion.FormationProofKernelError KernelProof.ProofStructuralCompositionMismatch{})) ->
            pure ()
        other -> assertFailure
            ("the consumer lost the typed hypothesis-context failure: " <> show other)

suppliedUniversalReplay :: Assertion
suppliedUniversalReplay = do
    fixture <- makeFixture 0
    let bound = Semantic.TemplateVariable (SourceEvidence.UniversalBound 0)
        outer = Semantic.TemplateVariable (SourceEvidence.UniversalOuter (0 :: Natural))
        emptyTerm = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        membership x y = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) y
        a = (Just (Semantic.MembershipAtomTemplate bound outer), membership (Core.CBound 0) (Core.CBound 1))
        b = (Just (Semantic.MembershipAtomTemplate bound emptyTerm), membership (Core.CBound 0) (Core.CIntrinsic Core.Empty))
        leaf = SourceEvidence.AtomLeaf
        both = SourceEvidence.AtomAnd
        bind = SourceEvidence.UniversalBind
        require = SourceEvidence.UniversalRequire
        result = SourceEvidence.UniversalReturn
        supplied = bind (require (both (leaf a) (leaf b)) (result (both (leaf a) (leaf b))))
        target = bind (require (leaf b) (require (leaf a) (result (both (leaf b) (both (leaf a) (leaf b))))))
        charge = Reference.chargeReferenceWork . fromIntegral
        match allowance source demand = Reference.runReference allowance
            (SuppliedUniversal.matchUniversal charge (SuppliedUniversal.sameUniversalAtom charge) source demand)
        outcome = match 100000 supplied target
    adapter <- expectJust =<< expectRight (fst outcome)
    let sourceFormula = checkedProposition fixture (SuppliedUniversal.universalFormula (snd <$> supplied))
        targetFormula = checkedProposition fixture (SuppliedUniversal.universalFormula (snd <$> target))
        unrelated = membership (Core.CBound 0) (Core.CBound 0)
        unrelatedFormula = checkedProposition fixture unrelated
    let materialized certificate = runWitnesses do
            direct <- directWitness
                (Notion.groundNotionKeyFromTemplate (Semantic.MembershipAtomTemplate (Core.CBound 0) (Core.CBound 0)))
                (Notion.DirectFormationSource unrelatedFormula Notion.ConjunctionHere "unrelated" 0)
            Notion.materializeFormationPremiseEvidence (const (pure ())) Notion.defaultFormationSearchLimits
                (Notion.FormationPremiseEvidenceAnd (Notion.FormationPremiseEvidenceLeaf direct)
                    (Notion.FormationPremiseEvidenceSupplied
                        (Notion.directFormationSourceEvidence (Notion.DirectFormationSource sourceFormula Notion.ConjunctionHere "whole source" 1)) certificate))
        joined target' = checkedProposition fixture (Core.CAnd unrelated (Core.scopedCoreTerm target'))
    package <- materialized adapter
    _ <- expectRight =<< replayMaterializedFormationResult fixture package (joined targetFormula)
    -- Additional target assumptions do not strengthen the supplied source.
    -- The existing adapter selects only the guards its source actually needs.
    let extra = (Just (Semantic.MembershipAtomTemplate outer bound), membership (Core.CBound 1) (Core.CBound 0))
        weaker = bind (require (both (leaf a) (leaf b)) (require (leaf extra) (result (leaf b))))
    weakened <- expectJust =<< expectRight (fst (match 100000 supplied weaker))
    weakenedPackage <- materialized weakened
    _ <- expectRight =<< replayMaterializedFormationResult fixture weakenedPackage
        (joined (checkedProposition fixture (SuppliedUniversal.universalFormula (snd <$> weaker))))
    -- Normalize a captured alias in the whole source, then adapt it below
    -- fresh binders and guards. The equality must remain a root dependency.
    subject <- expectRight (Core.checkScopedCanonicalCore
        (Identity.globalTypingFromClosure (fixtureClosure fixture)) [Core.TySet] (Core.CBound 0))
    replacement <- expectRight (Core.checkScopedCanonicalCore
        (Identity.globalTypingFromClosure (fixtureClosure fixture)) [Core.TySet] (Core.CIntrinsic Core.Empty))
    replaced <- expectJust =<< expectRight (Core.replaceScopedCoreOccurrence subject replacement sourceFormula)
    let equality = checkedProposition fixture (Core.CEq Core.TySet (Core.CBound 0) (Core.CIntrinsic Core.Empty))
        equalitySource = Notion.DirectFormationSource equality Notion.ConjunctionHere "alias" 2
        normalize item@(_,formula) = if formula == snd a then b else item
        normalizedSource = normalize <$> supplied
        normalizedTarget = normalize <$> target
    edge <- expectJust (Notion.formationEqualityTransport equalitySource equality Notion.FormationEqualityLeftToRight)
    transported <- expectRight (Notion.transportFormationSourceWithLimits Notion.defaultFormationSearchLimits
        (Notion.DirectFormationSource sourceFormula Notion.ConjunctionHere "whole source" 1)
        ((edge, Core.scopedCoreReplacementAbstraction replaced) :| []) sourceFormula
        (Core.scopedCoreReplacementResult replaced))
    adapted <- expectJust =<< expectRight (fst (match 100000 normalizedSource normalizedTarget))
    transportedPackage <- runWitnesses (Notion.materializeFormationPremiseEvidence (const (pure ())) Notion.defaultFormationSearchLimits
        (Notion.FormationPremiseEvidenceSupplied transported adapted))
    assertEqual "whole-source alias replay retains the original source and equality" 2
        (Vector.length (Notion.materializedFormationHypotheses transportedPackage))
    _ <- expectRight =<< replayMaterializedFormationResult fixture transportedPackage
        (checkedProposition fixture (SuppliedUniversal.universalFormula (snd <$> normalizedTarget)))
    let used = snd outcome
    assertBool "exact matcher allowance succeeds" (maybe False (const True) (either (const Nothing) id (fst (match used supplied target))))
    case fst (match (used - 1) supplied target) of
        Left Reference.ReferenceWorkExhausted -> pure ()
        _ -> assertFailure "one-short universal matching must exhaust"
    for_ [ bind (require (leaf a) (result (leaf b)))
         , bind (require (both (leaf a) (leaf (Just (Semantic.MembershipAtomTemplate outer bound), snd a)))
             (result (leaf b)))
         , bind (bind (require (both (leaf a) (leaf b)) (result (leaf b))))
         ] $ \wrong -> do
            rejected <- expectRight (fst (match 100000 supplied wrong))
            assertBool "different guards, captures, or binder skeletons do not match" (isNothing rejected)
    let forged = fmap (\(key,formula) -> (key, if formula == snd b then Core.CFalsum else formula)) target
    forgedAdapter <- expectJust =<< expectRight (fst (match 100000 supplied forged))
    forgedPackage <- materialized forgedAdapter
    rejected <- replayMaterializedFormation fixture forgedPackage
        (joined (checkedProposition fixture (SuppliedUniversal.universalFormula (snd <$> forged))))
    assertBool "matching keys cannot authorize a forged exact proposition" (case rejected of Left _ -> True; Right _ -> False)
    for_ [16,256] $ \population -> do
        let extra ordinal = (ordinal, fmap (\(key,formula) ->
                (fmap (fmap (fmap (\case SourceEvidence.UniversalOuter _ -> SourceEvidence.UniversalOuter ordinal; x -> x))) key, formula)) supplied)
            sources = (0,supplied) : [extra ordinal | ordinal <- [1..population]]
            indexed = Reference.runReference 1000000 $ do
                index <- SuppliedUniversal.prepareSuppliedIndex charge sources
                candidates <- SuppliedUniversal.suppliedCandidates charge target index
                fmap catMaybes $ for candidates $ \(ordinal,body) ->
                    fmap (ordinal <$) (SuppliedUniversal.matchUniversal charge (SuppliedUniversal.sameUniversalAtom charge) body target)
        found <- expectRight (fst indexed)
        assertEqual "candidate indexing retains exactly the rigid matching source" [0] found
    -- Equal lowered propositions cannot erase different written provider inputs.
    let provider value = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider) (Vector.singleton value)
        left = Semantic.MembershipAtomTemplate (provider bound) outer
        right = Semantic.MembershipAtomTemplate (provider outer) outer
    assertEqual "rich provider arguments remain part of identity" (Right False)
        (fst (Reference.runReference 1000 (SuppliedUniversal.sameUniversalAtom charge left right)))

replaysFormationConversion :: Assertion
replaysFormationConversion = do
    fixture <- makeFixture 1
    let head' = fixtureHead fixture 0
        term = Core.CBound 0
        beta value = Core.CApp (Core.CLam Core.TySet (Core.CBound 0)) value
        notion value = Semantic.StructureAtomTemplate head' (Vector.singleton value)
        source = checkedProposition fixture (atom fixture head' [term])
        middle = checkedProposition fixture (atom fixture head' [beta term])
        target = checkedProposition fixture (atom fixture head' [beta (beta term)])
        limits = Notion.defaultFormationSearchLimits
    let original :: Notion.FormationConstruction scope Text IO (Notion.FormationWitness scope Text)
        original = directEvidence fixture (notion term) source "source" 0
    evidence <- buildWitness do
        parent <- original
        converted <- Notion.convertFormationEvidence (const (pure ())) middle parent (notion (beta term))
        Notion.convertFormationEvidence (const (pure ())) target converted (notion (beta (beta term)))
    assertEqual "conversion records the requested logical atom"
        (Notion.groundNotionKeyFromTemplate (notion (beta (beta term)))) (Notion.formationEvidenceGroundKey evidence)
    assertBool "denotation conversion introduces no local equality dependency"
        (not (Notion.formationEvidenceUsesEquality evidence))
    let materialized = Notion.materializeFormationEvidence limits evidence
    replayed <- expectRight =<< replayMaterializedFormationResult fixture materialized target
    assertEqual "independent replay retains the requested target" target (Derivation.replayedScopedKernelTarget replayed)
    assertBool "conversion node estimate bounds independent replay"
        (Derivation.replayedScopedKernelNodeCount replayed <= Notion.formationEvidenceDerivationNodes evidence)
    assertBool "conversion depth estimate bounds independent replay"
        (Derivation.replayedScopedKernelMaximumDepth replayed <= Notion.formationEvidenceDerivationDepth evidence)
    assertEqual "conversion adds no theorem imports" Vector.empty (Notion.materializedFormationImports materialized)
    assertEqual "conversion retains the original local provenance" ["source"]
        (Notion.materializedNotionHypothesisOrigin <$> toList (Notion.materializedFormationHypotheses materialized))
    assertEmittedLimits fixture evidence target
    let wrong = checkedProposition fixture Core.CFalsum
    wrongEvidence <- buildWitness (original >>= \parent -> Notion.convertFormationEvidence (const (pure ())) wrong parent (notion term))
    let wrongMaterialized = Notion.materializeFormationEvidence limits wrongEvidence
    wrongReplay <- replayMaterializedFormation fixture wrongMaterialized wrong
    case wrongReplay of
        Left (Declaration.TransientFormationProofFailed
            (Notion.FormationProofKernelError KernelProof.ProofConversionNotConvertible)) -> pure ()
        _ -> assertFailure "conversion accepted a different proposition"
    otherScope <- expectRight (Core.checkScopedCanonicalCore
        (Identity.globalTypingFromClosure (fixtureClosure fixture)) [] Core.CTruth)
    scopeEvidence <- buildWitness (original >>= \parent -> Notion.convertFormationEvidence (const (pure ())) otherScope parent (notion term))
    let scopeMaterialized = Notion.materializeFormationEvidence limits scopeEvidence
    scopeReplay <- replayMaterializedFormation fixture scopeMaterialized target
    case scopeReplay of
        Left (Declaration.TransientFormationProofFailed
            (Notion.FormationProofKernelError KernelProof.ProofStructuralCompositionMismatch{})) -> pure ()
        _ -> assertFailure "conversion accepted a target from another scope"

retainsFoundedWitnesses :: Assertion
retainsFoundedWitnesses = do
    fixture <- makeFixture 2
    view <- unaryView fixture 0 0 1
    let baseHead = fixtureHead fixture 0
        head' = fixtureHead fixture 1
        left = Core.CBound 0
        middle = Core.CIntrinsic Core.Empty
        right = Core.canonicalSetInsert middle middle
        notion term = atom fixture head' [term]
        predicate = checkedProposition fixture
            (Core.CLam Core.TySet (notion (Core.CBound 0)))
        premise = checkedProposition fixture (notion left)
        target = checkedProposition fixture (notion right)
        premiseAtom = Semantic.StructureAtomTemplate
            head' (Vector.singleton left)
        targetAtom = Semantic.StructureAtomTemplate
            head' (Vector.singleton right)
        baseTargetAtom = Semantic.StructureAtomTemplate
            baseHead (Vector.singleton right)
        baseTarget = checkedProposition fixture (atom fixture baseHead [right])
        directTargetSource = Notion.DirectFormationSource
            target Notion.ConjunctionHere "direct target" 99
    (oneStep, twoStep, directTarget, viewEvidence) <- runWitnesses do
        parent <- directEvidence fixture premiseAtom premise "parent" 0
        one <- transportEvidence fixture predicate premise target parent premiseAtom targetAtom
            [(left, right, "one step", 8)]
        two <- transportEvidence fixture predicate premise target parent premiseAtom targetAtom
            [(left, middle, "first step", 0), (middle, right, "second step", 1)]
        direct <- directWitness (Notion.groundNotionKeyFromTemplate targetAtom) directTargetSource
        base <- directEvidence fixture baseTargetAtom baseTarget "view source" 100
        derived <- Notion.applyFormationRule (const (pure ())) (Notion.FormationViewRule view)
            (Map.singleton 0 right) [Notion.FormationPremiseEvidenceLeaf base] (Semantic.AtomicLeaf targetAtom)
        (,,,) <$> selectWitness one <*> selectWitness two <*> selectWitness direct <*> selectWitness derived
    assertEqual "an exact direct source precedes searched evidence" 0
        (Notion.formationEvidenceEqualityTransportSteps
            (Notion.preferDirectFormationEvidence oneStep directTarget))
    assertEqual "search retains its first founded witness" 1
        (Notion.formationEvidenceEqualityTransportSteps
            (Notion.preferDirectFormationEvidence oneStep viewEvidence))
    assertEqual "later shorter equality paths do not rerank founded evidence" 2
        (Notion.formationEvidenceEqualityTransportSteps
            (Notion.preferDirectFormationEvidence twoStep oneStep))

boundsEqualityTransportChains :: Assertion
boundsEqualityTransportChains = do
    fixture <- makeFixture 1
    limits <- maybe
        (assertFailure "valid equality-chain limits were rejected"
            >> fail "unreachable")
        pure
        (Notion.formationSearchLimitsWithEqualityChain
            16 16 16 64 256 64 1)
    let head' = fixtureHead fixture 0
        left = Core.CBound 0
        middle = Core.CIntrinsic Core.Empty
        right = Core.canonicalSetInsert middle middle
        notion term = atom fixture head' [term]
        predicate = checkedProposition fixture
            (Core.CLam Core.TySet (notion (Core.CBound 0)))
        premise = checkedProposition fixture (notion left)
        target = checkedProposition fixture (notion right)
        premiseAtom = Semantic.StructureAtomTemplate
            head' (Vector.singleton left)
        targetAtom = Semantic.StructureAtomTemplate
            head' (Vector.singleton right)
    transports <- traverse
        (makeTransport fixture)
        ((left, middle, "first", 0) :| [(middle, right, "second", 1)])
    outcome <- Notion.withFormationWitnessArena \arena -> fmap fst (Notion.runFormationConstruction (const (pure ())) (do
        parent <- directEvidence fixture premiseAtom premise "parent" 0
        void (Notion.applyEqualityTransportWithLimits (const (pure ())) limits transports predicate premise target parent
            premiseAtom targetAtom)) arena)
    case outcome of
        Left (Notion.FormationEqualityChainLimitExceeded 1 2) -> pure ()
        Left failure -> assertFailure ("unexpected equality-chain failure: " <> show failure)
        Right{} -> assertFailure "an overlong equality chain was accepted"

    -- One parent edge and two further substitutions at different positions
    -- share a single cumulative limit. Repeated operands are positional.
    let member a b = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) a) b
        a = Core.CBound 0
        b = Core.CIntrinsic Core.Empty
        originalAtom = Semantic.MembershipAtomTemplate a a
        parentAtom = Semantic.MembershipAtomTemplate b a
        finalAtom = Semantic.MembershipAtomTemplate a b
        original = checkedProposition fixture (member a a)
        parentTarget = checkedProposition fixture (member b a)
        finalTarget = checkedProposition fixture (member a b)
        firstPredicate = checkedProposition fixture
            (Core.CLam Core.TySet (member (Core.CBound 0) (Core.CBound 1)))
        secondPredicate = checkedProposition fixture
            (Core.CLam Core.TySet (member (Core.CBound 1) (Core.CBound 0)))
    forward <- makeTransport fixture (a,b,"forward",0)
    backward <- makeTransport fixture (b,a,"backward",1)
    for_ [2,3] \allowed -> do
        cumulative <- expectJust (Notion.formationSearchLimitsWithEqualityChain 64 64 64 4096 10000 256 allowed)
        let build :: Notion.FormationConstruction scope Text IO (Notion.FormationEvidence Text)
            build = do
                originalWitness <- directEvidence fixture originalAtom original "parent" 100
                parent <- Notion.applyEqualitySubstitutionsWithLimits (const (pure ())) cumulative
                    ((forward,firstPredicate) :| []) original parentTarget originalWitness originalAtom parentAtom
                result <- Notion.applyEqualitySubstitutionsWithLimits (const (pure ())) cumulative
                    ((backward,firstPredicate) :| [(forward,secondPredicate)])
                    parentTarget finalTarget parent parentAtom finalAtom
                selectWitness result
        outcome' <- Notion.withFormationWitnessArena \arena -> fmap fst
            (Notion.runFormationConstruction (const (pure ())) build arena)
        case (allowed,outcome') of
            (2,Left (Notion.FormationEqualityChainLimitExceeded 2 3)) -> pure ()
            (3,Right evidence) -> do
                Notion.formationEvidenceEqualityTransportSteps evidence @?= 3
                _ <- expectRight =<< replayMaterializedFormationResult fixture
                    (Notion.materializeFormationEvidence cumulative evidence) finalTarget
                pure ()
            _ -> assertFailure "argument substitutions did not share the cumulative bound"


replaysGrowingEqualityTransportChains :: Assertion
replaysGrowingEqualityTransportChains = do
    fixture <- makeFixture 1
    limits <- expectJust
        (Notion.formationSearchLimitsWithEqualityChain
            64 64 64 4096 10000 256 16)
    let head' = fixtureHead fixture 0
        notion term = atom fixture head' [term]
        notionAtom term = Semantic.StructureAtomTemplate
            head' (Vector.singleton term)
        beta proposition =
            Core.CApp (Core.CLam Core.TyProp (Core.CBound 0)) proposition
        start = Core.CBound 0
        parentProposition = checkedProposition fixture (notion start)
        premise = checkedProposition fixture (beta (notion start))
        predicate = checkedProposition fixture
            (Core.CLam Core.TySet (beta (notion (Core.CBound 0))))
        makeEdge (ordinal, left, right) = do
            let reversed = odd ordinal
                equality = checkedProposition fixture
                    (if reversed
                        then Core.CEq Core.TySet right left
                        else Core.CEq Core.TySet left right)
                source = Notion.DirectFormationSource equality
                    Notion.ConjunctionHere
                    ("edge " <> Text.pack (show ordinal)) ordinal
                direction = if reversed
                    then Notion.FormationEqualityRightToLeft
                    else Notion.FormationEqualityLeftToRight
            expectJust
                (Notion.formationEqualityTransport source equality direction)
    forM_ [1, 2, 4, 8, 16 :: Natural] $ \size -> do
        let endpoints = start : (Core.COpaqueInteger . toInteger <$> [1 .. size])
            targetTerm = beta (beta (notion (Core.COpaqueInteger (toInteger size))))
            target = checkedProposition fixture targetTerm
            targetAtom = notionAtom (Core.COpaqueInteger (toInteger size))
        edges <- traverse makeEdge
            (zip3 [0 ..] endpoints (drop 1 endpoints))
        transports <- expectJust (NonEmpty.nonEmpty edges)
        let construct :: Notion.FormationSearchLimits -> Core.ScopedCheckedCore Identity.ObjectId
                -> Notion.FormationConstruction scope Text IO (Notion.FormationWitness scope Text)
            construct bounded target' = do
                parent <- directEvidence fixture (notionAtom start) parentProposition "parent" 100
                Notion.applyEqualityTransportWithLimits (const (pure ())) bounded transports predicate premise target' parent
                    (notionAtom start) targetAtom
        evidence <- buildWitness (construct limits target)
        assertEqual "every directed edge survives selection"
            size (Notion.formationEvidenceEqualityTransportSteps evidence)
        let materialized = Notion.materializeFormationEvidence limits evidence
        assertEqual "materialization retains the parent and every edge origin"
            ("parent" : ["edge " <> Text.pack (show ordinal) | ordinal <- [0 .. size - 1]])
            (Notion.materializedNotionHypothesisOrigin
                <$> toList (Notion.materializedFormationHypotheses materialized))
        assertEqual "transport needs no imported theorem"
            Vector.empty (Notion.materializedFormationImports materialized)
        replayed <- expectRight =<< replayMaterializedFormationResult fixture materialized target
        assertEqual "replay retains the beta-written target" target
            (Derivation.replayedScopedKernelTarget replayed)
        assertBool "expanded node estimate bounds actual independent replay"
            (Derivation.replayedScopedKernelNodeCount replayed
                <= Notion.formationEvidenceDerivationNodes evidence)
        assertBool "expanded depth estimate bounds actual independent replay"
            (Derivation.replayedScopedKernelMaximumDepth replayed
                <= Notion.formationEvidenceDerivationDepth evidence)
        assertEmittedLimits fixture evidence target
        -- Search records an exact target but has no conversion authority. The
        -- consumer must reject a nonconvertible endpoint after prior edges.
        let badTarget = checkedProposition fixture Core.CFalsum
        badEvidence <- buildWitness (construct limits badTarget)
        let badMaterialized = Notion.materializeFormationEvidence limits badEvidence
        failed <- replayMaterializedFormation fixture badMaterialized badTarget
        case failed of
            Left (Declaration.TransientFormationProofFailed
                (Notion.FormationProofKernelError KernelProof.ProofConversionNotConvertible)) -> pure ()
            other -> assertFailure ("late endpoint conversion failure lost its cause: " <> show other)
        when (size > 1) $ do
            shortLimits <- expectJust
                (Notion.formationSearchLimitsWithEqualityChain
                    64 64 64 4096 10000 256 (size - 1))
            outcome <- Notion.withFormationWitnessArena \arena -> fmap fst
                (Notion.runFormationConstruction (const (pure ())) (void (construct shortLimits target)) arena)
            case outcome of
                Left failure -> assertEqual
                    "upstream chain exhaustion remains a formation-search failure"
                    (Notion.FormationEqualityChainLimitExceeded (size - 1) size)
                    failure
                Right{} -> assertFailure "an overlong transport chain was accepted"

-- Each builder runs under a fresh nominal arena; only compact selected evidence
-- leaves it. Tests constructing shared proofs keep all their nodes in one run.
runWitnesses
    :: (forall scope. Notion.FormationConstruction scope Text IO value) -> IO value
runWitnesses action = Notion.withFormationWitnessArena \arena ->
    expectRight . fst =<< Notion.runFormationConstruction (const (pure ())) action arena

buildWitness
    :: (forall scope. Notion.FormationConstruction scope Text IO (Notion.FormationWitness scope Text))
    -> IO (Notion.FormationEvidence Text)
buildWitness action = runWitnesses (action >>= selectWitness)

selectWitness
    :: Monad m => Notion.FormationWitness scope Text
    -> Notion.FormationConstruction scope Text m (Notion.FormationEvidence Text)
selectWitness = Notion.selectFormationEvidence (const (pure ())) Notion.defaultFormationSearchLimits

directWitness
    :: Monad m => Notion.GroundNotionKey -> Notion.DirectFormationSource Text
    -> Notion.FormationConstruction scope Text m (Notion.FormationWitness scope Text)
directWitness key source = do
    root <- Notion.prepareFormationHypothesis (const (pure ()))
        (Notion.directSourceProposition source) (Notion.directSourceOrigin source)
    Notion.directFormationEvidence (const (pure ())) key root
        (Notion.directSourcePath source) (Notion.directSourceOrdinal source)

selectedDirectEvidence
    :: Notion.GroundNotionKey -> Notion.DirectFormationSource Text
    -> Either Notion.FormationSearchError (Notion.FormationEvidence Text)
selectedDirectEvidence key source = runIdentity (Notion.withFormationWitnessArena \arena ->
    fst <$> Notion.runFormationConstruction (const (pure ())) (directWitness key source >>= selectWitness) arena)

directEvidence
    :: Monad m => Fixture
    -> Semantic.AtomTemplate (Core.CanonicalTerm Identity.ObjectId)
    -> Core.ScopedCheckedCore Identity.ObjectId -> Text -> Natural
    -> Notion.FormationConstruction scope Text m (Notion.FormationWitness scope Text)
directEvidence _fixture atom' proposition origin ordinal =
    directWitness (Notion.groundNotionKeyFromTemplate atom')
        (Notion.DirectFormationSource proposition Notion.ConjunctionHere origin ordinal)

transportEvidence
    :: Fixture
    -> Core.ScopedCheckedCore Identity.ObjectId
    -> Core.ScopedCheckedCore Identity.ObjectId
    -> Core.ScopedCheckedCore Identity.ObjectId
    -> Notion.FormationWitness scope Text
    -> Semantic.AtomTemplate (Core.CanonicalTerm Identity.ObjectId)
    -> Semantic.AtomTemplate (Core.CanonicalTerm Identity.ObjectId)
    -> [(Core.CanonicalTerm Identity.ObjectId, Core.CanonicalTerm Identity.ObjectId, Text, Natural)]
    -> Notion.FormationConstruction scope Text IO (Notion.FormationWitness scope Text)
transportEvidence fixture predicate premise target parent premiseAtom targetAtom edges = do
    transports <- liftIO (expectJust (NonEmpty.nonEmpty edges) >>= traverse (makeTransport fixture))
    Notion.applyEqualityTransportWithLimits (const (pure ()))
        Notion.defaultFormationSearchLimits transports predicate premise target parent premiseAtom targetAtom

assertEmittedLimits
    :: Fixture -> Notion.FormationEvidence Text -> Core.ScopedCheckedCore Identity.ObjectId -> Assertion
assertEmittedLimits fixture evidence target = do
    checked <- expectRight =<< replayMaterializedFormationResult fixture
        (Notion.materializeFormationEvidence Notion.defaultFormationSearchLimits evidence) target
    let nodes = Derivation.replayedScopedKernelNodeCount checked
        depth = Derivation.replayedScopedKernelMaximumDepth checked
    for_ [(nodes, depth, True), (nodes - 1, depth, False), (nodes, depth - 1, False)]
        \(nodeLimit, depthLimit, shouldPass) -> do
            limits <- expectJust (Notion.formationSearchLimitsWithEqualityChain
                64 64 64 1000000 nodeLimit depthLimit 1024)
            result <- replayMaterializedFormation fixture (Notion.materializeFormationEvidence limits evidence) target
            case (shouldPass, result) of
                (True, Right ()) -> pure ()
                (False, Left (Declaration.TransientFormationProofFailed
                    Notion.FormationProofDerivationLimitExceeded{})) -> pure ()
                _ -> assertFailure "actual emitted proof limits were not enforced"

makeTransport
    :: Fixture
    -> ( Core.CanonicalTerm Identity.ObjectId
       , Core.CanonicalTerm Identity.ObjectId
       , Text
       , Natural
       )
    -> IO (Notion.FormationEqualityTransport Text)
makeTransport fixture (left, right, origin, ordinal) = do
    let equality = checkedProposition fixture
            (Core.CEq Core.TySet left right)
        source = Notion.DirectFormationSource
            equality Notion.ConjunctionHere origin ordinal
    expectJust
        (Notion.formationEqualityTransport
            source equality Notion.FormationEqualityLeftToRight)

sourceTermFixture
    :: ( Semantic.GlobalBindingRef
       , SourceTerm.SourceTermOccurrence Text (Core.CanonicalTerm ())
       )
sourceTermFixture =
    let key = Semantic.SemanticExpressionFunction
            (Raw.HoleCons
                (Raw.TokenCons (Raw.Word "source-provider") Raw.End))
        owner = Semantic.declarationSlot
            preludeModuleName (localDeclarationOrdinal 0)
        reference = Semantic.globalBindingRef owner key
        argument = SourceTerm.sourceTermOccurrence
            (Core.CBound 1) Core.TySet "argument"
        occurrence = fromMaybe
            (error "set-valued global provider fixture was rejected")
            (SourceTerm.sourceGlobalProviderTermOccurrence
                reference
                (Vector.singleton argument)
                (Core.CBound 2)
                "provider")
    in (reference, occurrence)

preservesSourceProvidersThroughCoreTransformations :: Assertion
preservesSourceProvidersThroughCoreTransformations = do
    let (reference, occurrence) = sourceTermFixture
        shifted = SourceTerm.shiftCanonicalSourceTermOccurrence 10 0 occurrence
    assertEqual "root Core is transformed"
        (Core.CBound 12) (SourceTerm.sourceTermOccurrenceCore shifted)
    provider <- case SourceTerm.sourceTermOccurrenceProvider shifted of
        Just provider -> pure provider
        Nothing -> assertFailure "global source provider was erased"
    assertEqual "provider owner is stable"
        (Semantic.GlobalSourceProvider reference)
        (SourceTerm.sourceTermProviderHead provider)
    let arguments = SourceTerm.sourceTermProviderArguments provider
    assertEqual "provider arity is stable" 1 (Vector.length arguments)
    assertEqual "provider arguments are transformed recursively"
        (Core.CBound 11)
        (SourceTerm.sourceTermOccurrenceCore (Vector.head arguments))

describeSourceOccurrence
    :: SourceTerm.SourceTermOccurrence presentation core
    -> [(core, Core.CoreType, presentation, Maybe (Either Semantic.SourceProviderHead ()), Int)]
describeSourceOccurrence occurrence =
    let (tag, children) = case (SourceTerm.sourceTermOccurrenceProvider occurrence,
            SourceTerm.sourceTermOccurrenceOrderedPair occurrence) of
            (Just provider, _) -> (Just (Left (SourceTerm.sourceTermProviderHead provider)),
                toList (SourceTerm.sourceTermProviderArguments provider))
            (_, Just (left, right)) -> (Just (Right ()), [left, right])
            _ -> (Nothing, [])
    in (SourceTerm.sourceTermOccurrenceCore occurrence, SourceTerm.sourceTermOccurrenceType occurrence,
        SourceTerm.sourceTermOccurrencePresentation occurrence, tag, length children) : concatMap describeSourceOccurrence children

replacesScopedSourceAliases :: Assertion
replacesScopedSourceAliases = do
    let typing = fixtureGlobalTyping (globalTypingFixture [])
        context = [Core.TySet, Core.TySet]
        source term = SourceTerm.sourceTermOccurrence term Core.TySet ("source" :: Text)
        seal = expectRight . SourceTerm.sealCanonicalSourceTermOccurrence
            (SourceTerm.SourceTermCheckingContext typing context)
        reference = fst sourceTermFixture
    selected <- seal (source (Core.CBound 0))
    replacement <- expectJust (SourceTerm.sourceIntrinsicProviderTermOccurrence Semantic.PowerSetProvider
        (Vector.singleton (source (Core.CBound 1))) "replacement") >>= seal
    let replace occurrence = do
            ordinary <- expectRight (SourceTerm.replaceScopedSourceTermOccurrence
                (SourceTerm.sourceTermOccurrenceCore selected) replacement occurrence)
            let run allowance = Bifunctor.first (fmap (fmap describeSourceOccurrence))
                    (SourceTerm.countedReplaceScopedSourceTermOccurrence allowance
                        (SourceTerm.sourceTermOccurrenceCore selected) replacement occurrence)
                (answer, remaining) = run 1000000
                used = 1000000 - remaining
            assertEqual "counting preserves every source node, provider, and presentation"
                (Right (fmap describeSourceOccurrence ordinary)) answer
            assertEqual "exact source replacement allowance is sufficient" (answer, 0) (run used)
            assertEqual "one-short source replacement allowance exhausts"
                (Left Core.CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
            expectJust ordinary
        replacedCore = Core.CApp (Core.CIntrinsic Core.PowerSet) (Core.CBound 1)
    whole <- replace selected
    assertBool "an opaque alias inherits its defining source provider"
        (isJust (SourceTerm.sourceTermOccurrenceProvider whole))
    for_ [Core.CBound 0, Core.CBound 1] \denotation -> do
        written <- expectJust (SourceTerm.sourceGlobalProviderTermOccurrence reference
            (Vector.singleton (source (Core.CBound 0))) denotation "written") >>= seal
        viewed <- replace written
        provider <- expectJust (SourceTerm.sourceTermOccurrenceProvider viewed)
        assertEqual "written identity/erasing providers keep their exact owner"
            (Semantic.GlobalSourceProvider reference) (SourceTerm.sourceTermProviderHead provider)
        argument <- expectJust (fst <$> Vector.uncons (SourceTerm.sourceTermProviderArguments provider))
        assertEqual "retained arguments undergo the same source substitution"
            replacedCore (Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore argument))
        assertEqual "source-only changes do not rewrite an erased Core argument"
            (if denotation == Core.CBound 0 then replacedCore else denotation)
            (Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore viewed))
    pair <- expectJust (SourceTerm.sourceOrderedPairTermOccurrence
        (source (Core.CBound 0)) (source (Core.CBound 1))
        (Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (Core.CBound 0)) (Core.CBound 1)) "pair") >>= seal
    viewedPair <- replace pair
    (left, right) <- expectJust (SourceTerm.sourceTermOccurrenceOrderedPair viewedPair)
    assertEqual "pair arguments retain their source structure" replacedCore
        (Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore left))
    assertEqual "an unrelated pair argument is unchanged" (Core.CBound 1)
        (Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore right))
    opaque <- seal (source (Core.CApp (Core.CLogicalSelect Core.TySet)
        (Core.CLam Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1)))))
    viewedOpaque <- replace opaque
    assertBool "an opaque binder-containing term does not acquire source children"
        (isNothing (SourceTerm.sourceTermOccurrenceProvider viewedOpaque)
            && isNothing (SourceTerm.sourceTermOccurrenceOrderedPair viewedOpaque))
    assertEqual "replacement under an opaque binder avoids capture"
        (Core.CApp (Core.CLogicalSelect Core.TySet) (Core.CLam Core.TySet
            (Core.CEq Core.TySet (Core.CBound 0) (Core.CApp (Core.CIntrinsic Core.PowerSet) (Core.CBound 2)))))
        (Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore viewedOpaque))

constructsExactIntrinsicSourceProviders :: Assertion
constructsExactIntrinsicSourceProviders = do
    let argument
            :: SourceTerm.SourceTermOccurrence
                Text (Core.CanonicalTerm Identity.ObjectId)
        argument = SourceTerm.sourceTermOccurrence
            (Core.CBound 0) Core.TySet "argument"
        construct provider =
            SourceTerm.sourceIntrinsicProviderTermOccurrence
                provider (Vector.singleton argument) "provider"
        expected provider = Core.CApp
            (Core.CIntrinsic (Semantic.intrinsicProviderCoreTag provider))
            (Core.CBound 0)
    forM_
        [ Semantic.PowerSetProvider
        , Semantic.GlobalChoiceProvider
        ] \provider -> do
            occurrence <- maybe
                (assertFailure "an admitted intrinsic provider was rejected")
                pure
                (construct provider)
            assertEqual "provider Core is constructed from its identity"
                (expected provider)
                (SourceTerm.sourceTermOccurrenceCore occurrence)
            retained <- maybe
                (assertFailure "intrinsic provider identity was not retained")
                pure
                (SourceTerm.sourceTermOccurrenceProvider occurrence)
            assertEqual "exact intrinsic provider head"
                (Semantic.IntrinsicSourceProvider provider)
                (SourceTerm.sourceTermProviderHead retained)
    emptyOccurrence <- maybe
        (assertFailure "the nullary empty-set provider was rejected")
        pure
        (SourceTerm.sourceIntrinsicProviderTermOccurrence
            Semantic.EmptySetProvider
            (Vector.empty
                :: Vector.Vector
                    (SourceTerm.SourceTermOccurrence
                        Text (Core.CanonicalTerm Identity.ObjectId)))
            "empty provider")
    assertEqual "nullary provider Core is constructed from its identity"
        (Core.CIntrinsic Core.Empty)
        (SourceTerm.sourceTermOccurrenceCore emptyOccurrence)
    emptyProvider <- maybe
        (assertFailure "the empty-set provider identity was not retained")
        pure
        (SourceTerm.sourceTermOccurrenceProvider emptyOccurrence)
    assertEqual "exact nullary intrinsic provider head"
        (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider)
        (SourceTerm.sourceTermProviderHead emptyProvider)
    assertBool "a unary intrinsic rejects no arguments"
        (isNothing
            (SourceTerm.sourceIntrinsicProviderTermOccurrence
                Semantic.PowerSetProvider
                (Vector.empty
                    :: Vector.Vector
                        (SourceTerm.SourceTermOccurrence
                            Text (Core.CanonicalTerm Identity.ObjectId)))
                "provider"))
    assertBool "a nullary intrinsic rejects an argument"
        (isNothing
            (SourceTerm.sourceIntrinsicProviderTermOccurrence
                Semantic.EmptySetProvider
                (Vector.singleton argument)
                "provider"))
    let propositionArgument
            :: SourceTerm.SourceTermOccurrence
                Text (Core.CanonicalTerm Identity.ObjectId)
        propositionArgument = SourceTerm.sourceTermOccurrence
            Core.CTruth Core.TyProp "proposition"
    assertBool "an intrinsic set provider rejects a proposition argument"
        (isNothing
            (SourceTerm.sourceIntrinsicProviderTermOccurrence
                Semantic.PowerSetProvider
                (Vector.singleton propositionArgument)
                "provider"))

prop_finiteSetLiteralProviderRepresentation :: Property
prop_finiteSetLiteralProviderRepresentation = property do
    values <- forAll
        (Gen.list (Range.linear 1 8) (Gen.integral (Range.linear (-8) 8)))
    let elements
            :: [ SourceTerm.SourceTermOccurrence
                    Integer (Core.CanonicalTerm ())
               ]
        elements =
            [ SourceTerm.sourceTermOccurrence
                (Core.COpaqueInteger value)
                Core.TySet
                value
            | value <- values
            ]
        expectedCore = foldr
            Core.canonicalSetInsert
            (Core.CIntrinsic Core.Empty)
            (SourceTerm.sourceTermOccurrenceCore <$> elements)
    nonemptyElements <- evalMaybe (NonEmpty.nonEmpty elements)
    occurrence <- evalMaybe
        (SourceTerm.sourceFiniteSetLiteralTermOccurrence
            nonemptyElements
            0)
    SourceTerm.sourceTermOccurrenceCore occurrence === expectedCore
    SourceTerm.sourceTermOccurrenceType occurrence === Core.TySet
    provider <- evalMaybe
        (SourceTerm.sourceTermOccurrenceProvider occurrence)
    SourceTerm.sourceTermProviderHead provider
        === Semantic.FiniteSetLiteralSourceProvider
    let observe element =
            ( SourceTerm.sourceTermOccurrenceCore element
            , SourceTerm.sourceTermOccurrenceType element
            , SourceTerm.sourceTermOccurrencePresentation element
            )
    (observe <$> toList (SourceTerm.sourceTermProviderArguments provider))
        === (observe <$> elements)

sealsSourceGlobalsInOwnSnapshot :: Assertion
sealsSourceGlobalsInOwnSnapshot = do
    let fixture = globalTypingFixture [Core.TySet]
        missing = case fixtureObjectIds fixture of
            [identity] -> identity
            _ -> error "source sealing fixture arity"
        visible = SourceTerm.SourceTermCheckingContext (fixtureGlobalTyping fixture) []
        absent = SourceTerm.SourceTermCheckingContext
            (fixtureGlobalTyping (globalTypingFixture [])) []
        -- Beta reduction would discard this argument, but sealing must check it.
        term = Core.CApp (Core.CLam Core.TySet Core.CTruth) (Core.CGlobal missing)
        occurrence = SourceTerm.sourceTermOccurrence term Core.TyProp ("source" :: Text)
    checked <- either (assertFailure . show) pure
        (SourceTerm.sealCanonicalSourceTermOccurrence visible occurrence)
    Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore checked) @?= term
    case SourceTerm.sealCanonicalSourceTermOccurrence absent occurrence of
        Left (SourceTerm.SourceTermSealCoreCheckFailed original Core.UnknownCoreGlobal) ->
            original @?= term
        other -> assertFailure (either show (const "missing global was accepted") other)
    -- Inference can stop before a missing global. Retaining the whole failing
    -- input lets elaboration recover all missing identities with its old priority.
    let illTyped = Core.CAnd (Core.COpaqueInteger 7) term
    case SourceTerm.checkCanonicalSourceTerm absent Core.TyProp illTyped of
        Left (SourceTerm.SourceTermSealCoreCheckFailed original _) -> do
            original @?= illTyped
            Core.canonicalTermGlobals original @?= Set.singleton missing
        other -> assertFailure (either show (const "ill-typed source was accepted") other)
    checkedAgain <- either (assertFailure . show) pure
        (SourceTerm.sealCanonicalSourceTermOccurrence visible occurrence)
    SourceTerm.sourceTermOccurrenceCore checkedAgain
        @?= SourceTerm.sourceTermOccurrenceCore checked

indexesReferenceAnswers :: Assertion
indexesReferenceAnswers = do
    let a = Semantic.TemplateVariable (Reference.OpaqueSeed 0)
        b = Semantic.TemplateVariable (Reference.OpaqueSeed 1)
        target = Semantic.MembershipAtomTemplate a b
        summary origins occurrences supportIds = Reference.WitnessSummary
            (Set.fromList (origins :: [Natural])) (Set.fromList occurrences) (Set.fromList supportIds)
        rows = [(target, summary [] [] []), (target, summary [0] [] []),
            (target, summary [0,1] [] []), (target, summary [0] [0] []), (target, summary [0] [] [0]),
            (Semantic.MembershipAtomTemplate b a, summary [1] [] [])]
        support = Reference.ReferenceSupport (Set.fromList [a,b]) (Set.fromList [a,b]) 1
        run input allowance = Reference.evaluateRequests allowance support Map.empty
            [Reference.ReferenceFact row provenance | (row, provenance) <- input] target
    for_ [rows, reverse rows, rows <> rows] \input -> do
        let (answer, used) = run input 1000000
        result <- expectRight answer
        assertEqual "answer keys preserve atom and all three provenance dimensions"
            (Set.fromList rows) (Map.keysSet (Reference.referenceAnswers result))
        assertEqual "duplicate observations retain one witness per key"
            (length rows) (Map.size (Reference.referenceWitnesses result))
        assertEqual "answer bookkeeping shares its exact allowance" (answer, used) (run input used)
        assertEqual "one-short answer bookkeeping exhausts" (Left Reference.ReferenceWorkExhausted)
            (fst (run input (used - 1)))

countsReferenceTermSets :: Assertion
countsReferenceTermSets = do
    let variable index = Semantic.TemplateVariable (Reference.OpaqueSeed index)
        provider = Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider
        term arguments = Semantic.TemplateProvider provider (Vector.fromList arguments)
        terms = [variable 0, variable 1, term [], term [variable 0], term [variable 0, variable 1],
            term [variable 1], Semantic.TemplateOrderedPair (variable 1) (variable 0)]
        run input allowance = Reference.runReference allowance (Reference.referenceTermSet input)
    for_ [terms, reverse terms, terms <> terms] \input -> do
        let (answer, used) = run input 1000000
        assertEqual "metered term sets preserve derived ordering and deduplication"
            (Right (Set.fromList input)) answer
        assertEqual "term-set construction shares an exact allowance" (answer, used) (run input used)
        assertEqual "one-short term-set construction exhausts" (Left Reference.ReferenceWorkExhausted)
            (fst (run input (used - 1)))
    let nested seed = foldr (\_ child -> term [child]) (variable seed) [1..100 :: Int]
    assertEqual "deep comparisons cannot hide behind two set insertions"
        (Left Reference.ReferenceWorkExhausted)
        (fst (run [nested 0, nested 1] 20))

preservesNestedFiniteSetProviders :: Assertion
preservesNestedFiniteSetProviders = do
    let firstElement = SourceTerm.sourceTermOccurrence
            (Core.CBound 0 :: Core.CanonicalTerm Void) Core.TySet "first"
        secondElement = SourceTerm.sourceTermOccurrence
            (Core.CBound 1 :: Core.CanonicalTerm Void) Core.TySet "second"
        inner = fromMaybe
            (error "the nested singleton fixture was rejected")
            (SourceTerm.sourceFiniteSetLiteralTermOccurrence
                (firstElement :| []) "inner")
        outer = fromMaybe
            (error "the nested finite-set fixture was rejected")
            (SourceTerm.sourceFiniteSetLiteralTermOccurrence
                (inner :| [secondElement]) "outer")
        checkingContext = SourceTerm.SourceTermCheckingContext
            GlobalTyping.emptyGlobalTyping [Core.TySet, Core.TySet]
    assertFiniteSetRepresentationLaw outer
    assertFiniteSetRepresentationLaw
        (SourceTerm.shiftCanonicalSourceTermOccurrence 2 0 outer)
    sealed <- either
        (assertFailure . ("finite-set sealing failed: " <>) . show)
        pure
        (SourceTerm.sealCanonicalSourceTermOccurrence checkingContext outer)
    assertFiniteSetRepresentationLaw
        (SourceTerm.forgetScopedSourceTermOccurrence sealed)
    assertFiniteSetRepresentationLaw
        (SourceTerm.forgetScopedSourceTermOccurrence
            (SourceTerm.weakenScopedSourceTermOccurrence Core.TyProp sealed))
    aligned <- either
        (assertFailure . ("finite-set alignment failed: " <>))
        pure
        (maybe
            (Left "checked source alignment failed")
            Right
            (SourceTerm.alignScopedSourceTermOccurrence
                [Core.TySet, Core.TySet]
                sealed))
    assertFiniteSetRepresentationLaw
        (SourceTerm.forgetScopedSourceTermOccurrence aligned)
    for_ [[Core.TySet, Core.TySet], [Core.TyProp, Core.TySet, Core.TySet, Core.TySet],
            [Core.TyProp], [Core.TySet, Core.TyProp]] \target -> do
        let ordinary = describeSourceOccurrence <$> SourceTerm.alignScopedSourceTermOccurrence target sealed
            run allowance = Bifunctor.first (fmap (fmap describeSourceOccurrence))
                (SourceTerm.countedAlignScopedSourceTermOccurrence allowance target sealed)
            (answer, remaining) = run 1000000
            used = 1000000 - remaining
        assertEqual "counted alignment preserves every nested source node and rejection"
            (Right ordinary) answer
        assertEqual "source alignment shares its exact allowance" (answer, 0) (run used)
        assertEqual "one-short source alignment exhausts"
            (Left Core.CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
    let wrongRecordedType = SourceTerm.sourceTermOccurrence
            (SourceTerm.sourceTermOccurrenceCore sealed) Core.TyProp ("wrong" :: Text)
    assertEqual "counted alignment rejects inconsistent recorded source types" (Right Nothing)
        (fmap (fmap describeSourceOccurrence) (fst (SourceTerm.countedAlignScopedSourceTermOccurrence
            1000 [Core.TySet, Core.TySet] wrongRecordedType)))
    assertBool "alignment rejects a non-prefix context"
        (isNothing
            (SourceTerm.alignScopedSourceTermOccurrence
                [Core.TyProp]
                sealed))
    Core.scopedCoreContext (SourceTerm.sourceTermOccurrenceCore sealed)
        @?= [Core.TySet, Core.TySet]
    Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore sealed)
        @?= SourceTerm.sourceTermOccurrenceCore outer
    SourceTerm.sourceTermOccurrencePresentation sealed @?= "outer"
    case SourceTerm.sealCanonicalSourceTermOccurrence
            (SourceTerm.SourceTermCheckingContext GlobalTyping.emptyGlobalTyping [])
            outer of
        Left (SourceTerm.SourceTermSealCoreCheckFailed term (Core.UnboundCoreIndex 0)) ->
            term @?= SourceTerm.sourceTermOccurrenceCore outer
        other -> assertFailure ("wrong-context source sealing: " <> either show (const "accepted") other)
    case SourceTerm.sealCanonicalSourceTermOccurrence checkingContext
            (SourceTerm.sourceTermOccurrence Core.CTruth Core.TySet ()) of
        Left (SourceTerm.SourceTermSealTypeMismatch Core.TySet Core.TyProp) -> pure ()
        other -> assertFailure ("wrong-type source sealing: " <> either show (const "accepted") other)
    -- A failed transaction cannot change a later transaction's binder snapshot.
    resealed <- either (assertFailure . show) pure
        (SourceTerm.sealCanonicalSourceTermOccurrence checkingContext outer)
    Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore resealed)
        @?= SourceTerm.sourceTermOccurrenceCore outer
    let replacementElement = SourceTerm.sourceTermOccurrence
            (Core.CIntrinsic Core.Empty) Core.TySet "replacement element"
        replacement = fromMaybe
            (error "the replacement singleton fixture was rejected")
            (SourceTerm.sourceFiniteSetLiteralTermOccurrence
                (replacementElement :| []) "replacement")
    assertFiniteSetRepresentationLaw
        (SourceTerm.instantiateCanonicalSourceTermOccurrence replacement outer)
    let equalCoreWrapper
            :: SourceTerm.SourceTermOccurrence
                Text (Core.CanonicalTerm Void)
        equalCoreWrapper = SourceTerm.sourceTermOccurrence
            (SourceTerm.sourceTermOccurrenceCore outer)
            Core.TySet
            "equal-Core wrapper"
    assertBool "an equal-Core wrapper does not recover literal identity"
        (isNothing
            (SourceTerm.sourceTermOccurrenceProvider equalCoreWrapper))
    let illTyped
            :: SourceTerm.SourceTermOccurrence
                Text (Core.CanonicalTerm Void)
        illTyped = SourceTerm.sourceTermOccurrence
            Core.CTruth Core.TyProp "ill-typed element"
    assertBool "a finite-set provider rejects a proposition element"
        (isNothing
            (SourceTerm.sourceFiniteSetLiteralTermOccurrence
                (illTyped :| [])
                "invalid literal"))

assertFiniteSetRepresentationLaw
    :: (Eq global, Show global)
    => SourceTerm.SourceTermOccurrence
        Text (Core.CanonicalTerm global)
    -> Assertion
assertFiniteSetRepresentationLaw occurrence = do
    provider <- maybe
        (assertFailure "finite-set provider metadata was erased")
        pure
        (SourceTerm.sourceTermOccurrenceProvider occurrence)
    assertEqual "finite-set provider head"
        Semantic.FiniteSetLiteralSourceProvider
        (SourceTerm.sourceTermProviderHead provider)
    let arguments = SourceTerm.sourceTermProviderArguments provider
        expected = foldr
            Core.canonicalSetInsert
            (Core.CIntrinsic Core.Empty)
            (SourceTerm.sourceTermOccurrenceCore <$> toList arguments)
    assertBool "finite-set provider spine remains nonempty"
        (not (Vector.null arguments))
    assertEqual "finite-set representation law"
        expected
        (SourceTerm.sourceTermOccurrenceCore occurrence)
    for_ arguments \argument ->
        case SourceTerm.sourceTermProviderHead
                <$> SourceTerm.sourceTermOccurrenceProvider argument of
            Just Semantic.FiniteSetLiteralSourceProvider ->
                assertFiniteSetRepresentationLaw argument
            _ -> pure ()

preservesOrderedPairsThroughCoreTransformations :: Assertion
preservesOrderedPairsThroughCoreTransformations = do
    let left :: SourceTerm.SourceTermOccurrence Text (Core.CanonicalTerm ())
        left = SourceTerm.sourceTermOccurrence
            (Core.CBound 1) Core.TySet "left"
        right = SourceTerm.sourceTermOccurrence
            (Core.CBound 2) Core.TySet "right"
        pair = fromMaybe
            (error "set arguments did not construct an ordered pair")
            (SourceTerm.sourceOrderedPairTermOccurrence
                left right (Core.CBound 3) "pair")
        shifted = SourceTerm.shiftCanonicalSourceTermOccurrence 10 0 pair
    assertEqual "pair Core is transformed"
        (Core.CBound 13) (SourceTerm.sourceTermOccurrenceCore shifted)
    (shiftedLeft, shiftedRight) <-
        case SourceTerm.sourceTermOccurrenceOrderedPair shifted of
            Just arguments -> pure arguments
            Nothing -> assertFailure "ordered-pair source identity was erased"
    assertEqual "left pair argument is transformed recursively"
        (Core.CBound 11) (SourceTerm.sourceTermOccurrenceCore shiftedLeft)
    assertEqual "right pair argument is transformed recursively"
        (Core.CBound 12) (SourceTerm.sourceTermOccurrenceCore shiftedRight)
    assertBool "an ordered pair is not a provider occurrence"
        (isNothing (SourceTerm.sourceTermOccurrenceProvider shifted))
    assertBool "ill-typed pair metadata is rejected"
        (isNothing
            (SourceTerm.sourceOrderedPairTermOccurrence
                (SourceTerm.sourceTermOccurrence
                    Core.CTruth Core.TyProp "bad")
                right
                (Core.CBound 5)
                "bad pair"))

substitutesCompleteSourceTermOccurrences :: Assertion
substitutesCompleteSourceTermOccurrences = do
    let (reference, _occurrence) = sourceTermFixture
        argument
            :: SourceTerm.SourceTermOccurrence
                Text (Core.CanonicalTerm ())
        argument = SourceTerm.sourceTermOccurrence
            (Core.CBound 0) Core.TySet "argument"
        occurrence = fromMaybe
            (error "set-valued global provider fixture was rejected")
            (SourceTerm.sourceGlobalProviderTermOccurrence
                reference
                (Vector.singleton argument)
                (Core.CApp (Core.CGlobal ()) (Core.CBound 0))
                "provider")
        replacement = SourceTerm.sourceTermOccurrence
            (Core.COpaqueInteger 99) Core.TySet "replacement"
        substituted = SourceTerm.instantiateCanonicalSourceTermOccurrence
            replacement occurrence
    assertEqual "non-selected root is transformed"
        (Core.CApp (Core.CGlobal ()) (Core.COpaqueInteger 99))
        (SourceTerm.sourceTermOccurrenceCore substituted)
    provider <- case SourceTerm.sourceTermOccurrenceProvider substituted of
        Just provider -> pure provider
        Nothing -> assertFailure "global source provider was erased"
    let substitutedArgument =
            Vector.head (SourceTerm.sourceTermProviderArguments provider)
    assertEqual "selected argument is replaced as one occurrence"
        (Core.COpaqueInteger 99)
        (SourceTerm.sourceTermOccurrenceCore substitutedArgument)
    assertEqual "replacement presentation is retained"
        "replacement"
        (SourceTerm.sourceTermOccurrencePresentation substitutedArgument)
    assertBool "provider-free replacement stays provider-free"
        (isNothing
            (SourceTerm.sourceTermOccurrenceProvider substitutedArgument))

data Fixture = Fixture
    { fixtureTheory :: !Identity.TheoryId
    , fixtureClosure :: !Identity.CheckedObjectClosure
    , fixtureHeads :: !(Map Natural Semantic.SemanticStructureNotionHead)
    , fixturePredicates :: !(Map Identity.StructureId Identity.ObjectId)
    , fixtureProvider :: !Identity.ObjectId
    }

makeFixture :: Natural -> IO Fixture
makeFixture headCount = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        rootOrigin = Identity.StructureOrigin preludeModuleName (localDeclarationOrdinal 0) (structureSlot 0)
        rootWire = Schema.LocalStructureSchemaWire (structureSlot 0) [] [] [] [] []
        provider = Identity.transparentObject theory (Core.TyArrow Core.TySet Core.TySet)
            (Core.CLam Core.TySet (Core.CBound 0))
    initial <- expectRight (Identity.validateObjectClosure theory [provider])
    rootInput <- expectRight (Schema.checkManifestLocalStructureSchema initial rootOrigin Schema.GeneralRecordRoot rootWire
        (presentation (0 :: Natural) rootWire))
    root :| _ <- expectRight (Schema.resolveStructureBatch (const Nothing) (rootInput :| []))
    schemas <- for (take (fromIntegral headCount) [0 ..]) \index -> do
        let input = Schema.LocalStructureSchemaWire (structureSlot 0) [] []
                [Schema.structureApplicationKey (Schema.resolvedSchemaId root) []] []
                [(Schema.LocalLawOrdinal 0, Core.CEq Core.TySet (Core.CBound 0) (Core.COpaqueInteger (toInteger index)))]
            origin = Identity.StructureOrigin preludeModuleName (localDeclarationOrdinal (index + 1)) (structureSlot 0)
        local <- expectRight (Schema.checkLocalStructureSchema initial origin input (presentation (index + 1) input))
        resolved :| _ <- expectRight (Schema.resolveStructureBatch
            (\identity -> if identity == Schema.resolvedSchemaId root then Just root else Nothing) (local :| []))
        pure resolved
    let objects = [Identity.transparentObject theory (Predicate.structurePredicateType schema) (Predicate.structurePredicateBody schema)
            | schema <- schemas]
    closure <- expectRight (Identity.extendObjectClosure initial objects)
    registrations <- traverse (\(schema, object) -> expectRight
        (Predicate.checkPendingStructureRegistration closure schema (Identity.assertedObjectId object))) (zip schemas objects)
    pure (Fixture theory closure
        (Map.fromList (zip [0 ..] (Semantic.pendingStructureNotionHead <$> registrations)))
        (Map.fromList [(Schema.resolvedSchemaId (Predicate.pendingStructureSchema registration), Predicate.pendingStructurePredicate registration)
            | registration <- registrations])
        (Identity.assertedObjectId provider))
  where
    presentation index input = Schema.StructurePresentation
        (Schema.structurePhrase (Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl ((Just ("notion" <> Text.pack (show index)), Just ("notions" <> Text.pack (show index))) :| []))
            (Raw.Marker ("notion_fixture_" <> Text.pack (show index)))))
        Nowhere [] ((Nothing, Nowhere) <$ Schema.localWireParents input) Map.empty Map.empty
        (Map.fromList [(ordinal, (Raw.Marker "law", Nowhere)) | (ordinal, _) <- Schema.localWireLaws input])

fixtureHead :: Fixture -> Natural -> Semantic.SemanticStructureNotionHead
fixtureHead fixture index =
    fromMaybe
        (error ("missing notion fixture head " <> show index))
        (Map.lookup index (fixtureHeads fixture))

atom
    :: Fixture -> Semantic.SemanticStructureNotionHead
    -> [Core.CanonicalTerm Identity.ObjectId] -> Core.CanonicalTerm Identity.ObjectId
atom fixture head' arguments =
    let predicate = fromMaybe (impossible "notion fixture lost its checked predicate")
            (Map.lookup (Semantic.structureNotionHeadId head') (fixturePredicates fixture))
    in foldl' Core.CApp (Core.CGlobal predicate) arguments

unaryView
    :: Fixture
    -> Natural
    -> Natural
    -> Natural
    -> IO Notion.VisibleNotionView
unaryView fixture ordinal premiseIndex conclusionIndex = do
    let premiseHead = fixtureHead fixture premiseIndex
        conclusionHead = fixtureHead fixture conclusionIndex
        variable = Core.CBound 0
        premise = atom fixture premiseHead [variable]
        conclusion = atom fixture conclusionHead [variable]
        theorem = Core.CForall Core.TySet (Core.CImp premise conclusion)
    checked <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            theorem)
    let fingerprint = factFingerprint fixture checked ordinal
        declaration = ((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.NotionViewRule (Semantic.StructureNotionViewPremise
                premiseHead
                (Vector.singleton
                    (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))) (Semantic.AtomicLeaf (Semantic.StructureAtomTemplate
                conclusionHead
                (Vector.singleton
                    (Semantic.TemplateVariable (Semantic.ViewVariableIx 0))))))
    expectRight
        ((uncurry Notion.visibleNotionView)
            declaration checked premise conclusion)

validatesProviderResultRuleInvariants :: Assertion
validatesProviderResultRuleInvariants = do
    fixture <- makeFixture 2
    let variable = Semantic.ViewVariableIx 0
        variableTerm = Semantic.TemplateVariable variable
        premiseHead = fixtureHead fixture 0
        conclusionHead = fixtureHead fixture 1
        premise = atom fixture premiseHead [Core.CBound 0]
        providerValue = Core.CApp
            (Core.CGlobal (fixtureProvider fixture))
            (Core.CBound 0)
        conclusion = atom fixture conclusionHead [providerValue]
        theorem = Core.CForall Core.TySet (Core.CImp premise conclusion)
        unconditionalTheorem = Core.CForall Core.TySet conclusion
        key = Semantic.SemanticExpressionFunction
            (Raw.HoleCons
                (Raw.TokenCons (Raw.Word "provider-rule") Raw.End))
        reference = Semantic.globalBindingRef
            (Semantic.declarationSlot
                preludeModuleName (localDeclarationOrdinal 10))
            key
        prefixReference = Semantic.globalBindingRef
            (Semantic.declarationSlot
                preludeModuleName (localDeclarationOrdinal 11))
            (Semantic.SemanticPrefixPredicate "terminalGuard" 1)
        prefixHead = Semantic.PrefixPredicateNotionHead prefixReference
        provider arguments = Semantic.resultProviderTemplate
            (Semantic.GlobalSourceProvider reference)
            arguments
        premiseTemplate argument = Semantic.StructureAtomTemplate
            premiseHead (Vector.singleton argument)
        premiseBundles premiseAtom = Semantic.ProviderResultGuarded
            (Semantic.RulePremiseBundles
                (Semantic.RulePremiseAtom premiseAtom :| []))
        conclusionTemplate arguments = Semantic.StructureAtomTemplate
            conclusionHead arguments
        orderedPair = Core.CApp
            (Core.CApp (Core.CIntrinsic Core.OrderedPair) (Core.CBound 0))
            (Core.CBound 0)
        terminalPremise = atom fixture premiseHead [orderedPair]
        terminalTheorem = Core.CForall Core.TySet
            (Core.CImp terminalPremise conclusion)
    checked <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            theorem)
    terminalChecked <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            terminalTheorem)
    unconditionalChecked <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            unconditionalTheorem)
    let fingerprint = factFingerprint fixture checked 10
        validRule = ((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) (premiseBundles (premiseTemplate variableTerm)) (conclusionTemplate
                (Vector.singleton Semantic.ResultRuleProviderValue)))
        unconditionalFingerprint =
            factFingerprint fixture unconditionalChecked 11
        unconditionalRule = ((Semantic.SemanticFactBranch unconditionalFingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) Semantic.ProviderResultUnconditional (conclusionTemplate
                (Vector.singleton Semantic.ResultRuleProviderValue)))
        terminalRule = ((Semantic.SemanticFactBranch (factFingerprint fixture terminalChecked 12) Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) (premiseBundles
                (Semantic.GlobalAtomTemplate
                    prefixHead
                    (Vector.singleton
                        (Semantic.TemplateOrderedPair
                            variableTerm variableTerm)))) (conclusionTemplate
                (Vector.singleton Semantic.ResultRuleProviderValue)))
    visible <- expectRight
        ((uncurry Notion.visibleProviderResultRule)
            validRule checked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)

    premiseEvidence <- expectRight
        (findDirectEvidence fixture (directIndex fixture [(0, 0, "source")]) 0)
        >>= maybe
            (assertFailure "the provider premise had no direct witness"
                >> fail "unreachable")
            pure
    let resultKey = Notion.groundNotionKeyFromTemplate
            (Semantic.StructureAtomTemplate
                conclusionHead (Vector.singleton providerValue))
    resultEvidence <- buildWitness do
        parent <- directEvidence fixture
            (Semantic.StructureAtomTemplate premiseHead (Vector.singleton (Core.CBound 0)))
            (checkedProposition fixture premise) "source" 0
        Notion.applyFormationRule (const (pure ())) (Notion.FormationProviderRule visible)
            (Map.singleton 0 (Core.CBound 0)) [Notion.FormationPremiseEvidenceLeaf parent]
            (Semantic.AtomicLeaf (Semantic.StructureAtomTemplate conclusionHead (Vector.singleton providerValue)))
    assertEqual "the provider theorem establishes its exact result atom"
        (Notion.groundNotionKeyFromTemplate
            (Semantic.StructureAtomTemplate
                conclusionHead (Vector.singleton providerValue)))
        resultKey
    assertEqual "selected provider steps belong to the final evidence"
        1 (Notion.formationEvidenceProviderRuleSteps resultEvidence)
    assertEqual "direct evidence is composite level zero"
        0 (Notion.formationEvidenceCompositeLevel premiseEvidence)
    assertEqual "one provider theorem adds one composite level"
        1 (Notion.formationEvidenceCompositeLevel resultEvidence)
    unconditionalVisible <- expectRight
        ((uncurry Notion.visibleProviderResultRule)
            unconditionalRule
            unconditionalChecked
            Notion.MaterializedProviderResultUnconditional
            conclusion)
    unconditionalEvidence <- buildWitness (Notion.applyFormationRule (const (pure ()))
        (Notion.FormationProviderRule unconditionalVisible) (Map.singleton 0 (Core.CBound 0))
        [] (Semantic.AtomicLeaf (Semantic.StructureAtomTemplate conclusionHead (Vector.singleton providerValue))))
    assertEqual "the premise-free provider theorem contributes one step"
        1
        (Notion.formationEvidenceProviderRuleSteps unconditionalEvidence)
    assertEqual "the premise-free imported leaf is composite level one"
        1
        (Notion.formationEvidenceCompositeLevel unconditionalEvidence)
    assertEqual "one universal elimination follows the imported theorem node"
        2
        (Notion.formationEvidenceDerivationNodes unconditionalEvidence)
    assertEqual "the imported specialization has the expected depth"
        2
        (Notion.formationEvidenceDerivationDepth unconditionalEvidence)
    _terminalVisible <- expectRight
        ((uncurry Notion.visibleProviderResultRule)
            terminalRule
            terminalChecked
            (Notion.MaterializedProviderResultGuarded
                (terminalPremise :| []))
            conclusion)
    let materialized = Notion.materializeFormationEvidence Notion.defaultFormationSearchLimits unconditionalEvidence
    assertEqual "the premise-free theorem introduces no local hypothesis"
        0
        (Vector.length (Notion.materializedFormationHypotheses materialized))
    assertEqual "the premise-free theorem retains its exact import"
        (Vector.singleton unconditionalFingerprint)
        (Notion.materializedFormationImports materialized)
    replayed <- replayMaterializedFormation fixture materialized
        (checkedProposition fixture conclusion)
    assertEqual "a selected fingerprint must resolve in the consumer's current builder"
        (Left (Declaration.TransientFormationFactMissing unconditionalFingerprint))
        replayed
    assertRuleLeftContaining "wrong conclusion"
        ((uncurry Notion.visibleProviderResultRule)
            unconditionalRule
            checked
            Notion.MaterializedProviderResultUnconditional
            conclusion)
    assertRuleLeftContaining "too few curried premises"
        ((uncurry Notion.visibleProviderResultRule)
            validRule
            unconditionalChecked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)
    assertRuleLeftContaining "strict provider argument or subterm"
        ((uncurry Notion.visibleProviderResultRule)
            (((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider Vector.empty) (premiseBundles (premiseTemplate variableTerm)) (conclusionTemplate
                    (Vector.singleton Semantic.ResultRuleProviderValue))))
            checked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)
    assertRuleLeftContaining "exactly once at notion focus"
        ((uncurry Notion.visibleProviderResultRule)
            (((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) (premiseBundles (premiseTemplate variableTerm)) (conclusionTemplate
                    (Vector.fromList
                        [ Semantic.ResultRuleTerm variableTerm
                        , Semantic.ResultRuleProviderValue
                        ]))))
            checked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)
    assertRuleLeftContaining "fresh or growing term"
        ((uncurry Notion.visibleProviderResultRule)
            (((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) (premiseBundles
                    (Semantic.StructureAtomTemplate
                        premiseHead
                        (Vector.fromList
                            [ variableTerm
                            , Semantic.TemplateVariable
                                (Semantic.ViewVariableIx 1)
                            ]))) (conclusionTemplate
                    (Vector.singleton Semantic.ResultRuleProviderValue))))
            checked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)
    assertRuleLeftContaining "not determined"
        ((uncurry Notion.visibleProviderResultRule)
            (((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) (premiseBundles
                    (Semantic.GlobalAtomTemplate
                        prefixHead
                        (Vector.singleton
                            (Semantic.TemplateOrderedPair
                                variableTerm
                                (Semantic.TemplateVariable
                                    (Semantic.ViewVariableIx 1)))))) (conclusionTemplate
                    (Vector.singleton Semantic.ResultRuleProviderValue))))
            checked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)
    assertRuleLeftContaining "source-terminal global predicate"
        ((uncurry Notion.visibleProviderResultRule)
            (((Semantic.SemanticFactBranch fingerprint Notion.ConjunctionHere), Semantic.ProviderResultRule (provider (Vector.singleton variableTerm)) (premiseBundles (premiseTemplate variableTerm)) (Semantic.GlobalAtomTemplate
                    prefixHead
                    (Vector.singleton Semantic.ResultRuleProviderValue))))
            checked
            (Notion.MaterializedProviderResultGuarded (premise :| []))
            conclusion)

rejectsSourceTerminalNullaryClassifications :: Assertion
rejectsSourceTerminalNullaryClassifications = do
    fixture <- makeFixture 0
    proposition <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture) Core.CFalsum)
    let key = Semantic.SemanticPrefixPredicate "closedGuard" 0
        head' = Semantic.PrefixPredicateNotionHead
            (Semantic.globalBindingRef
                (Semantic.declarationSlot
                    preludeModuleName (localDeclarationOrdinal 13))
                key)
        classification = ((Semantic.SemanticFactBranch (factFingerprint fixture proposition 13) Notion.ConjunctionHere), Semantic.NullaryProviderRule Semantic.EmptySetProvider head')
    assertRuleLeftContaining "source-terminal global predicate"
        ((uncurry Notion.visibleNullaryProviderClassification)
            classification proposition Core.CFalsum)

assertRuleLeftContaining :: Text -> Either Text value -> Assertion
assertRuleLeftContaining expected = \case
    Left message ->
        assertBool
            ("expected error containing " <> show expected
                <> ", got " <> show message)
            (expected `Text.isInfixOf` message)
    Right _ ->
        assertFailure
            ("semantic rule unexpectedly passed: "
                <> Text.unpack expected)

factFingerprint
    :: Fixture
    -> Identity.CheckedPropositionContent
    -> Natural
    -> Semantic.SemanticFactOccurrenceFingerprint
factFingerprint fixture proposition ordinal =
    Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
        (Semantic.factSlot preludeModuleName (localFactOrdinal ordinal))
        (Authority.factAuthority
            (Identity.theoremRef
                (fixtureTheory fixture)
                (Identity.checkedPropositionId proposition))
            Authority.cleanAuthoritySafety)

type TestUnarySourceIndex =
    Notion.UnarySourceIndex
        (Semantic.AtomTemplate (Core.CanonicalTerm Identity.ObjectId))
        (Core.CanonicalTerm Identity.ObjectId)
        Text

directIndex
    :: Fixture
    -> [(Natural, Natural, Text)]
    -> TestUnarySourceIndex
directIndex fixture =
    directIndexWithArgument fixture (Core.CBound 0)

directIndexWithArgument
    :: Fixture
    -> Core.CanonicalTerm Identity.ObjectId
    -> [(Natural, Natural, Text)]
    -> TestUnarySourceIndex
directIndexWithArgument fixture argument =
    directIndexMixed fixture
        . fmap (\(headIndex, ordinal, origin) ->
            (argument, headIndex, ordinal, origin))

directIndexMixed
    :: Fixture
    -> [(Core.CanonicalTerm Identity.ObjectId, Natural, Natural, Text)]
    -> TestUnarySourceIndex
directIndexMixed fixture =
    foldl' (insertDirectTestSource fixture) Notion.emptyUnarySourceIndex

insertDirectTestSource
    :: Fixture
    -> TestUnarySourceIndex
    -> (Core.CanonicalTerm Identity.ObjectId, Natural, Natural, Text)
    -> TestUnarySourceIndex
insertDirectTestSource fixture index (argument, headIndex, ordinal, origin) =
    let head' = fixtureHead fixture headIndex
        checkedArgument = checkedSet fixture argument
        proposition = checkedProposition fixture (atom fixture head' [argument])
        assertion = Notion.structureSourceNotionAssertion
            head'
            (Vector.singleton checkedArgument)
            proposition
            Notion.ConjunctionHere
            Nowhere
        key = Notion.groundNotionKeyFromAssertion assertion
        shape = Semantic.StructureAtomTemplate
            head' (Vector.singleton argument)
        source = Notion.DirectFormationSource
            proposition Notion.ConjunctionHere origin ordinal
        evidence = expectPureRight
            (selectedDirectEvidence key source)
        proved = fromMaybe
            (error "a direct test source lost its rich shape")
            (Notion.provedRichGoal
                Notion.groundNotionKeyFromTemplate shape evidence)
    in Notion.insertUnarySource
        shape
        (Just (Notion.UnaryStructurePremise head'))
        proved
        index

groundKey :: Fixture -> Natural -> Notion.GroundNotionKey
groundKey fixture headIndex =
    let head' = fixtureHead fixture headIndex
        argument = checkedSet fixture (Core.CBound 0)
        proposition = checkedProposition fixture (atom fixture head' [Core.CBound 0])
        assertion = Notion.structureSourceNotionAssertion
            head'
            (Vector.singleton argument)
            proposition
            Notion.ConjunctionHere
            Nowhere
    in Notion.groundNotionKeyFromAssertion assertion

checkedSet
    :: Fixture
    -> Core.CanonicalTerm Identity.ObjectId
    -> Core.ScopedCheckedCore Identity.ObjectId
checkedSet fixture term =
    expectPureRight
        (Core.checkScopedCanonicalCore
            (Identity.globalTypingFromClosure (fixtureClosure fixture))
            [Core.TySet]
            term)

checkedProposition
    :: Fixture
    -> Core.CanonicalTerm Identity.ObjectId
    -> Core.ScopedCheckedCore Identity.ObjectId
checkedProposition fixture term =
    expectPureRight
        (Core.checkScopedCanonicalCore
            (Identity.globalTypingFromClosure (fixtureClosure fixture))
            [Core.TySet]
            term)

preservesSourceAtomOrdering :: Assertion
preservesSourceAtomOrdering = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        owner = Semantic.declarationSlot preludeModuleName (localDeclarationOrdinal 0)
        origin = Identity.StructureOrigin preludeModuleName (localDeclarationOrdinal 0) (structureSlot 0)
        wire = Schema.LocalStructureSchemaWire (structureSlot 0) [] [] [] [] []
        phrase = Schema.structurePhrase (Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl ((Just "sample", Just "samples") :| [])) (Raw.Marker "sample"))
        presentation = Schema.StructurePresentation phrase Nowhere [] [] Map.empty Map.empty Map.empty
        key = Semantic.SemanticNoun (Raw.TokenCons (Raw.Word "sample") Raw.End)
            (Raw.TokenCons (Raw.Word "samples") Raw.End)
        global = Semantic.NounNotionHead (Semantic.globalBindingRef owner key)
    initial <- expectRight (Identity.validateObjectClosure theory [])
    input <- expectRight (Schema.checkManifestLocalStructureSchema initial origin Schema.GeneralRecordRoot wire presentation)
    root :| _ <- expectRight (Schema.resolveStructureBatch (const Nothing) (input :| []))
    let object = Identity.transparentObject theory (Predicate.structurePredicateType root) (Predicate.structurePredicateBody root)
    closure <- expectRight (Identity.extendObjectClosure initial [object])
    registration <- expectRight (Predicate.checkPendingStructureRegistration closure root (Identity.assertedObjectId object))
    firstLocation <- expectRight (mkLocationChecked anonymousSourceDescriptor 1 1)
    secondLocation <- expectRight (mkLocationChecked anonymousSourceDescriptor 2 1)
    let structure = Semantic.pendingStructureNotionHead registration
        shape = Semantic.semanticRecordShapeKey root
        atoms :: [Semantic.AtomTemplate Integer]
        atoms =
            [ Semantic.GlobalAtomTemplate global (Vector.fromList [1,2])
            , Semantic.GlobalAtomTemplate global (Vector.fromList [2,1])
            , Semantic.StructureAtomTemplate structure (Vector.fromList [1,2])
            , Semantic.StructureAtomTemplate structure (Vector.fromList [2,1])
            , Semantic.MembershipAtomTemplate 1 2
            , Semantic.MembershipAtomTemplate 2 1
            , Semantic.ExactStructureAtomTemplate shape 1
            , Semantic.ExactStructureAtomTemplate shape 2
            ]
        occurrences :: [Notion.SourceNotionOccurrence String Integer Integer]
        occurrences = [Notion.sourceNotionAssertionFromTemplate template formula path location
            | template <- atoms
            , (formula,path,location) <- [(0,Notion.ConjunctionHere,firstLocation), (0,Notion.ConjunctionHere,secondLocation),
                (0,Notion.ConjunctionHere,Nowhere), (0,Notion.ConjunctionLeft Notion.ConjunctionHere,Nowhere),
                (1,Notion.ConjunctionHere,firstLocation)]]
        ordered = map fst (List.sortOn snd (reverse (zip [0 :: Int ..] occurrences)))
        grounds = map (Notion.groundNotionKeyFromTemplate . fmap Core.COpaqueInteger) atoms
        groundOrder = map fst (List.sortOn snd (reverse (zip [0 :: Int ..] grounds)))
        spelled = map (Notion.withSourceNotionOrigin
            (SourceEvidence.WrittenOrigin Nowhere (Just "different spelling") Notion.ConjunctionHere)) occurrences
    assertEqual "family, argument, formula, path and location order" [0..39] ordered
    assertEqual "ground family and argument order" [0..7] groundOrder
    assertEqual "written origin does not affect equality" occurrences spelled
    assertEqual "written origin does not affect ordering" (replicate 40 EQ)
        (zipWith compare occurrences spelled)

instantiatesAtomicTemplateShape :: Assertion
instantiatesAtomicTemplateShape = do
    fixture <- makeFixture 1
    let occurrenceArguments
            :: Vector.Vector (Core.CanonicalTerm Identity.ObjectId)
        occurrenceArguments = Vector.fromList
            [ Core.COpaqueInteger 10
            , Core.COpaqueInteger 20
            , Core.COpaqueInteger 30
            ]
        pattern' word = Raw.TokenCons (Raw.Word word) Raw.End
        key = Semantic.SemanticNoun
            (pattern' "sample") (pattern' "samples")
        owner = Semantic.declarationSlot
            preludeModuleName (localDeclarationOrdinal 0)
        globalHead = Semantic.NounNotionHead
            (Semantic.globalBindingRef owner key)
        structureHead' = fixtureHead fixture 0
        argument index = Semantic.TemplateVariable
            (Semantic.OccurrenceArgumentIx index)
    assertEqual "global arguments retain repetition and source order"
        (Just
            (Semantic.GlobalAtomTemplate
                globalHead
                (Vector.fromList
                    [ Core.COpaqueInteger 30
                    , Core.COpaqueInteger 10
                    , Core.COpaqueInteger 30
                    ])))
        (Notion.instantiateDirectNotionTemplate
            occurrenceArguments
            (Semantic.GlobalAtomTemplate
                globalHead
                (Vector.fromList [argument 2, argument 0, argument 2])))
    assertEqual "structure arguments retain their selected order"
        (Just
            (Semantic.StructureAtomTemplate
                structureHead'
                (Vector.fromList
                    [Core.COpaqueInteger 20, Core.COpaqueInteger 10])))
        (Notion.instantiateDirectNotionTemplate
            occurrenceArguments
            (Semantic.StructureAtomTemplate
                structureHead'
                (Vector.fromList [argument 1, argument 0])))
    assertEqual "membership retains its element/set shape"
        (Just
            (Semantic.MembershipAtomTemplate
                (Core.COpaqueInteger 30)
                (Core.COpaqueInteger 20)))
        (Notion.instantiateDirectNotionTemplate
            occurrenceArguments
            (Semantic.MembershipAtomTemplate (argument 2) (argument 1)))
    assertEqual "an invalid occurrence argument fails atomically"
        Nothing
        (Notion.instantiateDirectNotionTemplate
            occurrenceArguments
            (Semantic.GlobalAtomTemplate
                globalHead (Vector.singleton (argument 3))))

constructsBinaryMembershipAtoms :: Assertion
constructsBinaryMembershipAtoms = do
    fixture <- makeFixture 1
    let element = checkedSet fixture (Core.CBound 0)
        set = checkedSet fixture (Core.CIntrinsic Core.Empty)
        proposition = checkedProposition fixture
            (Core.CApp
                (Core.CApp (Core.CIntrinsic Core.Member) (Core.CBound 0))
                (Core.CIntrinsic Core.Empty))
        assertion = Notion.membershipSourceNotionAssertion
            element set proposition Notion.ConjunctionHere Nowhere
    case Notion.sourceAssertionAtom assertion of
        Semantic.MembershipAtomTemplate actualElement actualSet -> do
            assertEqual "membership preserves its element" element actualElement
            assertEqual "membership preserves its set" set actualSet
        _ -> assertFailure "membership assertion changed atomic family"
    assertEqual "membership ground key has the membership head"
        (Just Notion.MembershipNotionHeadKey)
        (Notion.groundNotionHeadKey
            (Notion.groundNotionKeyFromAssertion assertion))

replayMaterializedFormation
    :: Fixture
    -> Notion.MaterializedFormationEvidence origin
    -> Core.ScopedCheckedCore Identity.ObjectId
    -> IO (Either Declaration.TransientFormationReplayError ())
replayMaterializedFormation fixture evidence target =
    fmap (const ()) <$> replayMaterializedFormationResult fixture evidence target

replayMaterializedFormationResult
    :: Fixture
    -> Notion.MaterializedFormationEvidence origin
    -> Core.ScopedCheckedCore Identity.ObjectId
    -> IO (Either Declaration.TransientFormationReplayError
        (Derivation.ReplayedScopedKernelDerivation Identity.ObjectId))
replayMaterializedFormationResult fixture evidence target = do
    foundation <- expectRight Foundation.checkedFoundation
    importCheck <- Declaration.newImportCheck foundation
    imports <- expectRight =<< Declaration.prepareImports importCheck []
    let action :: Declaration.ModuleDriver Text
            (Either Declaration.TransientFormationReplayError
                (Derivation.ReplayedScopedKernelDerivation Identity.ObjectId))
        action = Declaration.runProspectiveLoweringDriver
            (Declaration.replayTransientFormationLowering
                (fixtureClosure fixture) evidence target)
        noProver = Declaration.vampireResolver
            (\_task -> fail "formation replay requested an external prover")
    result <- expectRight =<< Declaration.runModuleDriverFreshIO
        foundation preludeModuleName imports noProver action
    case result of
        Declaration.DriverSucceeded replayed _interface _prefix -> pure replayed
        Declaration.DriverFailed failure _prefix ->
            assertFailure ("formation driver failed: " <> show failure) >> fail "no replay result"
        Declaration.DriverSealFailed failure _prefix ->
            assertFailure ("formation driver did not seal: " <> show failure) >> fail "no replay result"

findDirectEvidence
    :: Fixture
    -> TestUnarySourceIndex
    -> Natural
    -> Either Notion.FormationSearchError
        (Maybe (Notion.FormationEvidence Text))
findDirectEvidence fixture index goal = do
    outcome <- Notion.findDirectFormationEvidenceWithLimits
        Notion.defaultFormationSearchLimits index (groundKey fixture goal)
    pure case outcome of
        Notion.FormationFound evidence _statistics -> Just evidence
        Notion.FormationNotFound{} -> Nothing

selectsDuplicateDirectWitnessesByOrdinal :: Assertion
selectsDuplicateDirectWitnessesByOrdinal = do
    fixture <- makeFixture 2
    let preferred = (0, 0, "preferred")
        displaced = (0, 10, "displaced")
    for_
        [ directIndex fixture [displaced, preferred]
        , directIndex fixture [preferred, displaced]
        ] \index -> do
            selected <- selectedDirectOrigin fixture index 0
            assertEqual "smaller source ordinal wins" "preferred" selected

selectedDirectOrigin
    :: Fixture
    -> TestUnarySourceIndex
    -> Natural
    -> IO Text
selectedDirectOrigin fixture index headIndex = do
    evidence <- expectJust =<< expectRight
        (findDirectEvidence fixture index headIndex)
    let materialized = Notion.materializeFormationEvidence Notion.defaultFormationSearchLimits evidence
    case toList (Notion.materializedFormationHypotheses materialized) of
        [hypothesis] ->
            pure (Notion.materializedNotionHypothesisOrigin hypothesis)
        hypotheses ->
            assertFailure
                ("expected one selected direct hypothesis, got "
                    <> show (length hypotheses))
                >> fail "unreachable"

rejectsMismatchedTheorem :: Assertion
rejectsMismatchedTheorem = do
    fixture <- makeFixture 3
    let first = fixtureHead fixture 0
        second = fixtureHead fixture 1
        third = fixtureHead fixture 2
        variable = Core.CBound 0
        actualPremise = atom fixture first [variable]
        registeredPremise = atom fixture second [variable]
        conclusion = atom fixture third [variable]
        theorem = Core.CForall Core.TySet
            (Core.CImp actualPremise conclusion)
    checked <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            theorem)
    let declaration = ((Semantic.SemanticFactBranch (factFingerprint fixture checked 0) Notion.ConjunctionHere), Semantic.NotionViewRule (Semantic.StructureNotionViewPremise
                second
                (Vector.singleton
                    (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))) (Semantic.AtomicLeaf (Semantic.StructureAtomTemplate
                third
                (Vector.singleton
                    (Semantic.TemplateVariable (Semantic.ViewVariableIx 0))))))
    case (uncurry Notion.visibleNotionView)
            declaration checked registeredPremise conclusion of
        Left{} -> pure ()
        Right{} -> assertFailure "a mismatched theorem registration was accepted"

rejectsSparseViewVariables :: Assertion
rejectsSparseViewVariables = do
    fixture <- makeFixture 2
    let premiseHead = fixtureHead fixture 0
        conclusionHead = fixtureHead fixture 1
        argument = Core.CIntrinsic Core.Empty
        premise = atom fixture premiseHead [argument]
        conclusion = atom fixture conclusionHead [argument]
        theorem = Core.CImp premise conclusion
        sparseIndex = 1000000000
    checked <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            theorem)
    let declaration = ((Semantic.SemanticFactBranch (factFingerprint fixture checked 0) Notion.ConjunctionHere), Semantic.NotionViewRule (Semantic.StructureNotionViewPremise
                premiseHead
                (Vector.singleton
                    (Semantic.TemplateVariable
                        (Semantic.ViewVariableIx sparseIndex)))) (Semantic.AtomicLeaf (Semantic.StructureAtomTemplate
                conclusionHead
                (Vector.singleton
                    (Semantic.TemplateVariable
                        (Semantic.ViewVariableIx sparseIndex))))))
    case (uncurry Notion.visibleNotionView) declaration checked premise conclusion of
        Left failure ->
            assertEqual "sparse contexts receive the density diagnostic"
                "notion view variables are not a dense premise-determined context"
                failure
        Right{} -> assertFailure "a sparse view-variable context was accepted"

sharesProviderSearchBudget :: Assertion
sharesProviderSearchBudget = do
    let limits = fromMaybe
            (error "valid notion test limits were rejected")
            (Notion.formationSearchLimits 8 8 8 2 64 2)
        providerWork = Notion.emptyFormationSearchStatistics
            { Notion.formationSearchProviderOccurrences = 1
            , Notion.formationSearchProviderRuleInspections = 2
            , Notion.formationSearchProviderPremiseRequests = 2
            , Notion.formationSearchMaximumProviderDepth = 2
            }
    budget <- expectRight
        (Notion.consumeFormationSearchStatistics
            providerWork
            (Notion.initialFormationSearchBudget limits))
    let consumed = Notion.formationSearchBudgetStatistics budget
    assertEqual "provider occurrences are retained"
        1 (Notion.formationSearchProviderOccurrences consumed)
    assertEqual "provider registrations are retained"
        2 (Notion.formationSearchProviderRuleInspections consumed)
    assertEqual "recursive premise requests are retained"
        2 (Notion.formationSearchProviderPremiseRequests consumed)
    assertEqual "maximum provider depth uses maximum, not addition"
        2 (Notion.formationSearchMaximumProviderDepth consumed)
    attributed <- expectRight (Notion.consumeFormationSearchStatistics providerWork
        (Notion.setFormationRegistrationFamily (Just Diagnostics.ProviderFamily)
            (Notion.initialFormationSearchBudget limits)))
    assertEqual "family attribution retains the same generic inspection account"
        consumed (Notion.formationSearchBudgetStatistics attributed)
    assertEqual "family attribution counts actual charged inspections"
        (Map.singleton Diagnostics.ProviderFamily 2)
        (Diagnostics.familyInspections (Notion.formationSearchBudgetDiagnostics attributed))
    assertEqual "phase accounting counts physical inspections once" (Map.singleton Diagnostics.Query 2)
        (Diagnostics.phaseInspections (Notion.formationSearchBudgetDiagnostics attributed))
    let proofPhase = Notion.setFormationSearchPhase Diagnostics.Proof budget
        rejectedDebit = Notion.emptyFormationSearchStatistics {Notion.formationSearchViewInspections = 1}
        recorded = Notion.recordFormationRejectedDebit rejectedDebit proofPhase
    assertEqual "a rejected debit is diagnostic, not performed work" consumed
        (Notion.formationSearchBudgetStatistics recorded)
    assertEqual "the exhausted owner's rejected debit survives" (Just rejectedDebit)
        (Notion.formationSearchRejectedDebit recorded)
    let exhausted = Notion.consumeFormationSearchStatistics
            Notion.emptyFormationSearchStatistics
                { Notion.formationSearchViewInspections = 1 }
            budget
    assertEqual "one later unary inspection shares the provider limit"
        (Left (Notion.FormationInferenceInspectionLimitExceeded 2 3))
        (fmap (const ()) exhausted)
    case exhausted of
        Left failure -> do
            let rendered = Elaboration.renderElaborationError
                    (Elaboration.ElaborationFormationSearchFailed
                        Nowhere failure)
            assertBool "provider-heavy exhaustion names inference inspections"
                ("inference inspections" `Text.isInfixOf` rendered)
            assertBool "provider-heavy exhaustion reports its counts"
                ("observed 3" `Text.isInfixOf` rendered
                    && "configured limit 2" `Text.isInfixOf` rendered)
            assertBool "provider-heavy exhaustion hides constructors"
                (not ("FormationInference" `Text.isInfixOf` rendered))
            assertBool "provider-heavy exhaustion does not call the budget a view limit"
                (not ("view limit" `Text.isInfixOf` rendered))
        Right{} -> assertFailure "the provider-heavy budget unexpectedly remained"
    assertEqual "provider recursion shares the derivation-depth limit"
        (Left (Notion.FormationDerivationDepthLimitExceeded 2 3))
        (fmap (const ())
            (Notion.consumeFormationSearchStatistics
                Notion.emptyFormationSearchStatistics
                    { Notion.formationSearchMaximumProviderDepth = 3 }
                (Notion.initialFormationSearchBudget limits)))

chargesSourceIndexWork :: Assertion
chargesSourceIndexWork = do
    let limits = fromMaybe
            (error "valid source-index test limits were rejected")
            (Notion.formationSearchLimits 8 8 1 1 64 8)
        indexWork = Notion.emptyFormationSearchStatistics
            { Notion.formationSearchSourceIndexInspections = 1
            , Notion.formationSearchIndexedRows = 1
            }
        fresh = Notion.initialFormationSearchBudget limits
    assertEqual "a budget retains its absolute limits"
        limits
        (Notion.formationSearchBudgetLimits fresh)
    first <- expectRight
        (Notion.consumeFormationSearchStatistics indexWork fresh)
    assertEqual "source-index scans are recorded"
        1
        (Notion.formationSearchSourceIndexInspections
            (Notion.formationSearchBudgetStatistics first))
    assertEqual "indexed rows are recorded"
        1
        (Notion.formationSearchIndexedRows
            (Notion.formationSearchBudgetStatistics first))
    assertEqual "the same cached scan cost is charged to a fresh query"
        (Right first)
        (Notion.consumeFormationSearchStatistics indexWork fresh)
    assertEqual "a second source-index scan exhausts inference work"
        (Left (Notion.FormationInferenceInspectionLimitExceeded 1 2))
        (fmap (const ())
            (Notion.consumeFormationSearchStatistics
                Notion.emptyFormationSearchStatistics
                    { Notion.formationSearchSourceIndexInspections = 1 }
                first))
    assertEqual "a second indexed row exhausts the ground-atom budget"
        (Left (Notion.FormationGroundAtomLimitExceeded 1 2))
        (fmap (const ())
            (Notion.consumeFormationSearchStatistics
                Notion.emptyFormationSearchStatistics
                    { Notion.formationSearchIndexedRows = 1 }
                first))

expectPureRight :: Show error => Either error value -> value
expectPureRight = \case
    Left failure -> error ("unexpected fixture failure: " <> show failure)
    Right value -> value

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left failure -> assertFailure ("unexpected failure: " <> show failure)
    Right value -> pure value

expectJust :: Maybe value -> IO value
expectJust = \case
    Nothing -> assertFailure "expected a notion witness"
    Just value -> pure value

-- Build and authorize the imported theorem through the ordinary declaration
-- driver. This explicitly selects a backward registration; the module-level
-- product example instead registers a finite-evidence rule.
replaysBackwardFormationRule :: Assertion
replaysBackwardFormationRule = for_
        [ Notion.ConjunctionHere
        , Notion.ConjunctionLeft (Notion.ConjunctionRight Notion.ConjunctionHere)
        , Notion.ConjunctionRight (Notion.ConjunctionLeft Notion.ConjunctionHere)
        ] \path -> do
    fixture <- makeFixture 0
    foundation <- expectRight Foundation.checkedFoundation
    let member term = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) term) term
        body = member (Core.CBound 0)
        pair = Core.CAnd body body
        wrap Notion.ConjunctionHere value = value
        wrap (Notion.ConjunctionLeft rest) value = Core.CAnd (wrap rest value) value
        wrap (Notion.ConjunctionRight rest) value = Core.CAnd value (wrap rest value)
        theorem = Core.CForall Core.TySet (Core.CImp pair (wrap path body))
        limits = Notion.defaultFormationSearchLimits
        argument = Core.COpaqueInteger 7
        targetTerm = member argument
        targetAtom = Semantic.MembershipAtomTemplate argument argument
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        premiseAtom = Semantic.MembershipAtomTemplate variable variable
        premiseTree = Semantic.RulePremiseAnd
            (Semantic.RulePremiseAtom premiseAtom) (Semantic.RulePremiseAtom premiseAtom)
        checkedTerm context term = Core.checkScopedCanonicalCore
            (Identity.globalTypingFromClosure (fixtureClosure fixture)) context term
    checkedTheorem <- expectRight (Identity.validatePropositionContent
        (fixtureClosure fixture) theorem)
    checkedPremise <- expectRight (checkedTerm [Core.TySet] pair)
    target <- expectRight (checkedTerm [] targetTerm)
    let fingerprint = factFingerprint fixture checkedTheorem 0
        ruleAt selector = ((Semantic.SemanticFactBranch fingerprint selector), Semantic.BackwardNotionRule (Semantic.RulePremiseBundles (premiseTree :| [])) premiseAtom)
        rule = ruleAt path
    visible <- expectRight ((uncurry Notion.visibleBackwardNotionRule) rule checkedTheorem (pair :| []) body)
    assertBool "selectors remain part of registration identity"
        (rule /= ruleAt (Notion.ConjunctionLeft path))
    assertRuleLeftContaining "wrong conclusion"
        ((uncurry Notion.visibleBackwardNotionRule) (ruleAt (foldr (const Notion.ConjunctionLeft) Notion.ConjunctionHere [1..5 :: Int]))
            checkedTheorem (pair :| []) body)
    assertRuleLeftContaining "wrong conclusion"
        ((uncurry Notion.visibleBackwardNotionRule) rule checkedTheorem (pair :| []) Core.CFalsum)
    let construct :: Core.CanonicalTerm Identity.ObjectId
            -> Notion.FormationConstruction scope Text IO (Notion.FormationWitness scope Text)
        construct argument' = do
            left <- directEvidence fixture targetAtom target "left origin" 0
            right <- directEvidence fixture targetAtom target "right origin" 1
            Notion.applyFormationRule (const (pure ())) (Notion.FormationBackwardRule visible)
                (Map.singleton 0 argument')
                [Notion.FormationPremiseEvidenceAnd (Notion.FormationPremiseEvidenceLeaf left)
                    (Notion.FormationPremiseEvidenceLeaf right)] (Semantic.AtomicLeaf targetAtom)
    evidence <- buildWitness (construct argument)
    let materialized = Notion.materializeFormationEvidence limits evidence
    assertEqual "equal statements retain distinct exact origins"
        ["left origin", "right origin"]
        (Notion.materializedNotionHypothesisOrigin
            <$> toList (Notion.materializedFormationHypotheses materialized))
    assertEqual "one exact theorem fingerprint" (Vector.singleton fingerprint)
        (Notion.materializedFormationImports materialized)
    let erasedArgument = Core.CApp
            (Core.CLam (Core.TyArrow Core.TySet Core.TySet) argument)
            (Core.CGlobal (fixtureProvider fixture))
    rawEvidence <- buildWitness (construct erasedArgument)
    let rawMaterialized = Notion.materializeFormationEvidence limits rawEvidence
    olderClosure <- expectRight (Identity.validateObjectClosure (fixtureTheory fixture) [])
    importCheck <- Declaration.newImportCheck foundation
    imports <- expectRight =<< Declaration.prepareImports importCheck []
    let wrapProof Notion.ConjunctionHere value = value
        wrapProof (Notion.ConjunctionLeft rest) value =
            Derivation.conjunctionIntroductionDerivation (wrapProof rest value) value
        wrapProof (Notion.ConjunctionRight rest) value =
            Derivation.conjunctionIntroductionDerivation value (wrapProof rest value)
        proof = Derivation.forallIntroductionDerivation Core.TySet
            (Derivation.implicationIntroductionDerivation checkedPremise
                (wrapProof path (Derivation.conjunctionLeftEliminationDerivation
                    (Derivation.localHypothesisDerivation (Derivation.hypothesisIx 0)))))
        action :: Declaration.ModuleDriver Text
            ( Either Declaration.TransientFormationReplayError
                (Derivation.ReplayedScopedKernelDerivation Identity.ObjectId)
            , Either Declaration.TransientFormationReplayError ()
            )
        action = do
            void (DeclTest.admitCompiled
                (Semantic.declarationSyntaxId "backward-formation-consumer") [] []
                [Declaration.checkedCandidate (Declaration.candidateSpec checkedTheorem Semantic.SearchEligible [])
                    (Declaration.checkedNoExternalSourceProofPlanning []) :| []] \case
                [candidate :| []] -> Declaration.authorizeKernelProofCandidate candidate (pure proof)
                _ -> error "backward formation fixture shape")
            replayed <- Declaration.runProspectiveLoweringDriver
                (Declaration.replayTransientFormationLowering
                    (fixtureClosure fixture) materialized target)
            rejected <- Declaration.runProspectiveLoweringDriver
                (Declaration.replayTransientFormationLowering
                    olderClosure rawMaterialized target)
            case replayed of
                Left _ -> pure ()
                Right checked -> do
                    let nodes = Derivation.replayedScopedKernelNodeCount checked
                        depth = Derivation.replayedScopedKernelMaximumDepth checked
                    for_ [(nodes, depth, True), (nodes - 1, depth, False), (nodes, depth - 1, False)]
                        \(nodeLimit, depthLimit, shouldPass) -> do
                            bounded <- liftIO (expectJust (Notion.formationSearchLimitsWithEqualityChain
                                64 64 64 1000000 nodeLimit depthLimit 16))
                            outcome <- Declaration.runProspectiveLoweringDriver
                                (Declaration.replayTransientFormationLowering (fixtureClosure fixture)
                                    (Notion.materializeFormationEvidence bounded evidence) target)
                            liftIO case (shouldPass, outcome) of
                                (True, Right _) -> pure ()
                                (False, Left (Declaration.TransientFormationProofFailed
                                    Notion.FormationProofDerivationLimitExceeded{})) -> pure ()
                                _ -> assertFailure "projected theorem emission escaped its limits"
            pure (replayed, const () <$> rejected)
        noProver = Declaration.vampireResolver
            (\_ -> fail "backward formation requested an external prover")
    result <- expectRight =<< Declaration.runModuleDriverFreshIO foundation
        preludeModuleName imports noProver action
    case result of
        Declaration.DriverSucceeded (replayed, rejected) _ _ -> do
            assertEqual "consumer checks even a raw beta-erased argument under its own snapshot"
                (Left (Declaration.TransientFormationProofFailed
                    (Notion.FormationProofKernelError
                        (KernelProof.ProofTermIllTyped Core.UnknownCoreGlobal)))) rejected
            checked <- expectRight replayed
            assertEqual "consumer exact target" target
                (Derivation.replayedScopedKernelTarget checked)
            assertEqual "actual expanded theorem application nodes"
                (Notion.formationEvidenceDerivationNodes evidence)
                (Derivation.replayedScopedKernelNodeCount checked)
            assertEqual "formation counts depth from one; replay counts edges from zero"
                (Notion.formationEvidenceDerivationDepth evidence)
                (1 + Derivation.replayedScopedKernelMaximumDepth checked)
        Declaration.DriverFailed failure _ -> assertFailure (show failure)
        Declaration.DriverSealFailed failure _ -> assertFailure (show failure)

projectionPrefixSharing :: Assertion
projectionPrefixSharing = do
    fixture <- makeFixture 1
    let x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        empty = Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.EmptySetProvider) Vector.empty
        guardAtom = Semantic.MembershipAtomTemplate x empty
        guardFormula = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) (Core.CBound 0)) (Core.CIntrinsic Core.Empty)
        resultAtom = Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.singleton x)
        resultFormula = atom fixture (fixtureHead fixture 0) [Core.CBound 0]
        charge = Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (Reference.invalidReferenceInput . Text.pack . show) pure
        compile width = Reference.runReference 10000000 do
            let formula = Core.CForall Core.TySet (foldr Core.CImp
                    (foldr1 Core.CAnd (replicate width resultFormula)) (replicate width guardFormula))
                evidence = SourceEvidence.SourceBind (foldr SourceEvidence.SourceRequire
                    (foldr1 SourceEvidence.SourceAnd (replicate width (SourceEvidence.SourceAtom resultAtom)))
                    (replicate width (SourceEvidence.SourceAtom guardAtom)))
            base <- admit (Rule.compileConclusionRule charge 0 []
                (Semantic.WholeLeaf (Semantic.describedResidualTemplate formula evidence)))
            admit (Projection.compileProjections charge base)
    costs <- for [8,32,128] \width -> do
        let (result,work) = compile width
        projections <- expectRight result
        length projections @?= width
        for_ projections \(_,rule) -> Rule.rulePremiseCount rule @?= width
        pure work
    for_ (zip costs (drop 1 costs)) \(small,large) ->
        assertBool "quadrupling a shared guard prefix and its conclusions avoids product work" (large < 6 * small)

wholeRootInputs :: Assertion
wholeRootInputs = do
    let typing = fixtureGlobalTyping (globalTypingFixture [])
        context = [Core.TySet,Core.TySet]
        inner = Core.TySet:context
        pair a b = Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) a) b
        member a b = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) a) b
        body = member (pair (Core.CBound 0) (Core.CBound 1)) (Core.CBound 2)
        checked term = expectRight (Core.checkScopedCanonicalCore typing inner term)
        source term = (\value -> SourceTerm.sourceTermOccurrence value Core.TySet ()) <$> checked term
        run allowance formula evidence = ScopedSource.scopedSourceInputs typing allowance context context formula evidence (Leaves.emptyOpaqueLeaves context)
        values (terms,leaves) = Set.fromList <$> traverse (traverse (\identifier ->
            Core.scopedCoreTerm <$> maybe (assertFailure "missing whole input" >> error "unreachable") pure
                (Leaves.lookupOpaqueLeaf identifier leaves))) terms
        residual = SourceEvidence.SourceResidual Nothing
    opaque <- expectRight (fst (run 10000 (Core.CExists Core.TySet body) residual)) >>= values
    opaque @?= Set.singleton (Semantic.TemplateVariable (Core.CBound 1))
    left <- source (Core.CBound 0)
    right <- source (Core.CBound 1)
    pairCore <- checked (pair (Core.CBound 0) (Core.CBound 1))
    writtenPair <- maybe (assertFailure "invalid written pair" >> error "unreachable") pure
        (SourceTerm.sourceOrderedPairTermOccurrence left right pairCore ())
    container <- source (Core.CBound 2)
    checkedBody <- checked body
    let atom = Notion.sourceNotionAssertionFromTemplate
            (Semantic.MembershipAtomTemplate writtenPair container) checkedBody Notion.ConjunctionHere Nowhere
        evidence = SourceEvidence.SourceBind (SourceEvidence.SourceAtom atom)
        formula = Core.CForall Core.TySet body
        (result,remaining) = run 10000 formula evidence
    collected <- expectRight result >>= values
    collected @?= Set.fromList [Semantic.TemplateVariable (Core.CBound 0),Semantic.TemplateVariable (Core.CBound 1)]
    let supportEvidence = SourceEvidence.SourceInputs Nothing
            [SourceEvidence.SourceInput [Core.TySet] (SourceTerm.sourceSupportTemplate Core.scopedCoreTerm term)
            | term <- [writtenPair,container]]
    retained <- expectRight (fst (run 10000 (Core.CExists Core.TySet body) supportEvidence)) >>= values
    assertEqual "existential opacity preserves independent written children" collected retained
    hidden <- expectRight (fst (run 10000 (Core.CNot (Core.CExists Core.TySet body)) supportEvidence)) >>= values
    assertEqual "compound negation preserves support without exposing evidence" collected hidden
    let rich = Semantic.TemplateOrderedPair (Semantic.TemplateVariable (Core.CBound 0)) (Semantic.TemplateVariable (Core.CBound 1))
        equation = Core.CEq Core.TySet (pair (Core.CBound 0) (Core.CBound 1)) (pair (Core.CBound 0) (Core.CBound 1))
        written = SourceEvidence.SourceInputs Nothing [SourceEvidence.SourceInput [] rich]
    onlyWritten <- expectRight (fst (run 10000 equation written)) >>= values
    assertEqual "retained rich operands do not acquire an extra opaque view" (Set.singleton rich) onlyWritten
    let completeEmpty = SourceEvidence.SourceInputs Nothing []
        extra = SourceEvidence.SourceInput [] (Semantic.TemplateVariable (Core.CBound 0))
        annotated = SourceEvidence.withSourceInputs [extra] written
    emptyInputs <- expectRight (fst (run 10000 equation completeEmpty)) >>= values
    assertEqual "an empty complete description suppresses residual discovery" Set.empty emptyInputs
    assertBool "an empty additive wrapper keeps the complete empty description"
        (case SourceEvidence.withSourceInputs [] completeEmpty of
            SourceEvidence.SourceInputs Nothing [] -> True
            _ -> False)
    added <- expectRight (fst (run 10000 equation annotated)) >>= values
    assertEqual "annotations add views without mining omitted Core operands"
        (Set.fromList [rich,Semantic.TemplateVariable (Core.CBound 0)]) added
    opaqueInputs <- expectRight (fst (run 10000 equation (SourceEvidence.withSourceInputs [extra] residual))) >>= values
    assertEqual "an annotated residual still discovers its complete opaque operand"
        (Set.fromList [Semantic.TemplateVariable (pair (Core.CBound 0) (Core.CBound 1)),
            Semantic.TemplateVariable (Core.CBound 0)]) opaqueInputs
    let underBinder = SourceEvidence.SourceWithInputs
            [SourceEvidence.SourceInput [Core.TySet] (SourceTerm.sourceSupportTemplate Core.scopedCoreTerm writtenPair)] evidence
    scoped <- expectRight (fst (run 10000 formula underBinder)) >>= values
    assertEqual "annotations preserve binder independence" collected scoped
    let view = SourceEvidence.sourceViews . fmap (fmap SourceTerm.sourceTermOccurrenceCore . Notion.sourceAssertionAtom)
    assertEqual "annotations leave the universal view unchanged" (view evidence) (view underBinder)
    let innerInput = SourceEvidence.SourceInput [] (0 :: Int)
        outerInput = SourceEvidence.SourceInput [] 1
        twice = SourceEvidence.withSourceInputs [outerInput]
            (SourceEvidence.withSourceInputs [innerInput] (SourceEvidence.SourceAtom (2 :: Int)))
    assertEqual "nested annotations retain inner-before-outer operand order"
        [SourceEvidence.SourceInput [] 2,innerInput,outerInput]
        (SourceEvidence.sourceInputsAtDepth pure twice)
    assertEqual "annotations retain direct atomic identity and paths"
        [(Notion.ConjunctionHere,2)] (SourceEvidence.directAtoms twice)
    let shifted = runIdentity (SourceEvidence.traverseSourceAtDepth
            (\depth term -> pure (term + fromIntegral depth)) (const pure)
            (SourceEvidence.SourceBind (SourceEvidence.withSourceInputs [innerInput]
                (SourceEvidence.SourceInputs Nothing [] :: SourceEvidence.SourceEvidence Int Int))))
    assertEqual "input traversal counts enclosing binders"
        [SourceEvidence.SourceInput [Core.TySet] 1]
        (SourceEvidence.sourceInputsAtDepth pure shifted)
    let substitute = Semantic.instantiateSupportPrefixWith (pure ()) 1
            (\depth _ -> pure
                (Semantic.TemplateOrderedPair (Semantic.TemplateVariable (Core.CBound depth))
                    (Semantic.TemplateVariable (Core.CBound depth)), pair (Core.CBound depth) (Core.CBound depth))) 1
    assertEqual "a whole operand substitution retains the complete actual view"
        (Semantic.TemplateOrderedPair (Semantic.TemplateVariable (Core.CBound 1)) (Semantic.TemplateVariable (Core.CBound 1)))
        (runIdentity (substitute (Semantic.TemplateVariable (Core.CBound 1))))
    assertEqual "substitution does not open an opaque operand"
        (Semantic.TemplateVariable (pair (pair (Core.CBound 1) (Core.CBound 1)) (Core.CBound 0)))
        (runIdentity (substitute (Semantic.TemplateVariable (pair (Core.CBound 1) (Core.CBound 0)))))
    let used = 10000-remaining
    (exact,_) <- expectRight (fst (run used formula evidence))
    length exact @?= 2
    case fst (run (used-1) formula evidence) of
        Left Core.CountedCoreStructuralWorkExhausted -> pure ()
        _ -> assertFailure "one-short whole-input preparation must exhaust"

wholeTemplateSupport :: Assertion
wholeTemplateSupport = do
    let typing = fixtureGlobalTyping (globalTypingFixture [])
        context = [Core.TySet,Core.TySet]
        a = Core.CBound 0 :: Core.CanonicalTerm Identity.ObjectId
        b = Core.CBound 1
        pair x y = Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) x) y
        value = Semantic.TemplateVariable
        charge = Reference.chargeReferenceWork . fromIntegral
        tick = charge 1
        counted :: (Word -> (Either (Core.CountedCoreFailure failure) result,Word)) -> Reference.Reference result
        counted operation = Reference.countedReferenceOperation \work ->
            let (result,remaining) = operation work
            in (Bifunctor.first (\case
                    Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted
                    _ -> Reference.ReferenceInvalidInput "invalid opaque support fixture") result,remaining)
        denote term = tick >> case term of
            Semantic.TemplateVariable core -> pure core
            Semantic.TemplateClosed closed -> pure (Semantic.closedSetValueTerm closed)
            Semantic.TemplateOrderedPair x y -> pair <$> denote x <*> denote y
            _ -> Reference.invalidReferenceInput "unexpected provider in opaque support fixture"
        interpreter = Support.OpaqueInterpreter denote
            (\arity template target -> do
                _ <- counted (\work -> Core.countedCheckScopedCanonicalCore typing work
                    (replicate (fromIntegral arity) Core.TySet <> context) template)
                _ <- counted (\work -> Core.countedCheckScopedCanonicalCore typing work context target)
                let match known pattern' actual = tick >> case (pattern',actual) of
                        (Core.CBound index,_) | index < arity -> do
                            let slot = Semantic.ViewVariableIx index
                            pure (case Map.lookup slot known of
                                Just previous | previous /= actual -> Nothing
                                _ -> Just (Map.insert slot actual known))
                        (Core.CBound index,Core.CBound other) -> pure (if index-arity == other then Just known else Nothing)
                        (Core.CApp f x,Core.CApp g y) -> match known f g >>= \case
                            Nothing -> pure Nothing
                            Just next -> match next x y
                        (Core.CIntrinsic x,Core.CIntrinsic y) -> pure (if x == y then Just known else Nothing)
                        _ -> pure Nothing
                match Map.empty template target)
            (\arity template arguments -> do
                actual <- traverse denote arguments
                result <- Core.instantiateCanonicalPrefixWith tick arity
                    (\depth index -> Core.shiftCanonicalWith tick depth 0 (actual Map.! Semantic.ViewVariableIx index)) 0 template
                checked <- counted (\work -> Core.countedCheckScopedCanonicalCore typing work context result)
                pure (maybe (value result) Semantic.TemplateClosed (Semantic.closedSetValue checked)))
        cursorValues = filteredValues Nothing
        filteredValues predicate support = go (Support.supportCursor support)
          where
            go cursor = Support.nextMatchingSupportTerm (Just interpreter) charge predicate cursor >>= \case
                Nothing -> pure []
                Just (found,next) -> (maybe id (:) found) <$> go next
        build seeds groups = Support.freezeSupport charge seeds Support.emptyTemplateSupport
            >>= Support.extendWholeSupport charge interpreter groups
        diagonal = value (pair a a)
        rich = Semantic.TemplateOrderedPair (value a) diagonal
        groups = [(1,[diagonal,rich],Map.empty)]
        expected = Set.fromList ([value a,value b]
            <> [value (pair x x) | x <- [a,b]]
            <> [Semantic.TemplateOrderedPair (value x) (value (pair x x)) | x <- [a,b]])
        rejected = [value (pair a b), Semantic.TemplateOrderedPair (value a) (value (pair b b)),
            value (pair (pair a a) (pair a a))]
    (actual,answers) <- expectRight (fst (Reference.runReference 100000 do
        support <- build [value a,value b] groups
        terms <- Set.fromList <$> cursorValues support
        answers <- for (Set.toList expected <> rejected) \candidate ->
            fst <$> Support.symbolicSupportContainsWith (Just interpreter) charge candidate support
        pure (terms,answers)))
    assertEqual "cursor agrees with explicit one-layer instantiation and subtemplates" expected actual
    assertEqual "membership preserves repeated slots, written views, and the frozen seed boundary"
        (replicate (Set.size expected) True <> replicate (length rejected) False) answers
    for_ (Set.toList expected <> rejected) \target -> do
        (wanted,filtered) <- expectRight (fst (Reference.runReference 100000 do
            actualTarget <- denote target
            support <- build [value a,value b] groups
            wanted <- filterM (fmap (== actualTarget) . denote) (Set.toList expected)
            found <- filteredValues (Just (\partial -> do
                actual <- denote (fromMaybe (Core.CBound 2) <$> partial)
                WholePattern.mayEqualOperands charge 2 actual actualTarget)) support
            pure (Set.fromList wanted,Set.fromList found)))
        assertEqual "cursor pruning preserves every explicitly supported denotation" wanted filtered
    captured <- expectRight (fst (Reference.runReference 100000 do
        support <- build [value a,value b]
            [(2,[value (pair a b)],Map.singleton (Semantic.ViewVariableIx 1) (value b))]
        Set.fromList <$> cursorValues support))
    assertEqual "fixed captures never become assignable slots"
        (Set.fromList [value a,value b,value (pair a b),value (pair b b)]) captured
    closed <- expectRight (fst (Reference.runReference 100000 do
        support <- build [] [(0,[value (Core.CIntrinsic Core.Empty)],Map.empty)]
        cursorValues support))
    assertBool "closed whole templates instantiate even when B is empty"
        (case closed of [Semantic.TemplateClosed{}] -> True; _ -> False)
    -- Prepare a complete query description, including an operand template
    -- appearing only beneath its witness binder. The expected domain is written
    -- independently; neither selected clauses nor generated answers define it.
    for_ [False,True] \reverseBranches -> for_ [False,True] \reverseCatalogue -> do
        let reflexive = Core.CEq Core.TySet a a
            paired = Core.CEq Core.TySet a (pair a a)
            operands terms = SourceEvidence.SourceInputs Nothing
                [SourceEvidence.SourceInput [] term | term <- terms]
            first = (reflexive,operands [value a])
            second = (paired,operands [value a,Semantic.TemplateOrderedPair (value a) (value a)])
            ((left,leftEvidence),(right,rightEvidence)) = if reverseBranches then (second,first) else (first,second)
            query = Core.CExists Core.TySet (Core.COr left right)
            description :: SourceEvidence.SourceEvidence Semantic.SupportTermTemplate Void
            description = SourceEvidence.SourceExists (SourceEvidence.SourceOr leftEvidence rightEvidence)
            rooted = SourceEvidence.SourceWithInputs [SourceEvidence.SourceInput [] (value a)] description
            requiredTemplate = Semantic.TemplateOrderedPair (value a) (value a)
            admit result = either (Reference.invalidReferenceInput . Text.pack . show) pure result
        (seeds,templates,universe,selected) <- expectRight (fst (Reference.runReference 1000000 do
            seeds <- counted (\work -> ScopedSource.sourceTemplateInputs typing work context query (fmap absurd rooted))
            original <- Rule.compileRuleFromPrefixWithInputs charge Set.empty (Just Set.empty) 0
                (Rule.scopedRulePrefix context) (Semantic.WholeLeaf (Semantic.describedResidualTemplate query (fmap absurd description))) >>= admit
            introductions <- Introduction.compileIntroductions charge original >>= admit
            irrelevant <- Rule.compileConclusionRule charge 1
                [Semantic.RulePremiseAtom (Semantic.MembershipAtomTemplate
                    (Semantic.TemplateOrderedPair
                        (Semantic.TemplateOrderedPair (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)) (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))
                        (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))
                    (Semantic.TemplateVariable (Semantic.ViewVariableIx 0)))]
                (Semantic.WholeLeaf (Semantic.ResidualTemplate Core.CFalsum)) >>= admit
            let entries = zip [0 :: Int ..] (Rule.RegisteredClassification . Introduction.introductionRule <$> introductions)
                    <> [(99,Rule.RegisteredClassification irrelevant)]
            catalog <- Catalog.insertRules charge (if reverseCatalogue then reverse entries else entries) Catalog.emptyCatalog
            shape <- Formulas.residualShape tick context query
            snapshot <- Catalog.selectWholeSnapshot charge shape catalog >>= admit
            groups <- fmap concat $ for (Map.elems (Rule.snapshotRules snapshot)) \entry ->
                for (Rule.ruleSupportSources (Rule.registeredRule entry)) \(arity,source) -> do
                    let portable = fmap (fmap (fmap (\(Semantic.ViewVariableIx slot) -> Core.CBound slot)))
                            (fromMaybe (SourceEvidence.SourceResidual Nothing) (Semantic.residualTemplateEvidence source))
                    terms <- counted (\work -> ScopedSource.sourceTemplateInputs typing work
                        (replicate (fromIntegral arity) Core.TySet <> context) (Semantic.residualTemplateFormula source) portable)
                    pure (arity,List.filter (\case Semantic.TemplateVariable (Core.CBound slot) -> slot >= arity; _ -> True) terms,Map.empty)
            support <- build seeds groups
            universe <- Set.fromList <$> cursorValues support
            pure (Set.fromList seeds,Set.fromList [term | (_,terms,_) <- groups,term <- terms],universe,
                [source | ordinal <- Map.keys (Rule.snapshotRules snapshot), Just source <- [Catalog.lookupSource ordinal catalog]])))
        assertEqual "only the written independent operand supplies B" (Set.singleton (value a)) seeds
        assertEqual "the binder contributes exactly its written pair template to T" (Set.singleton requiredTemplate) templates
        assertEqual "query templates extend the original seeds once" (Set.fromList [value a,requiredTemplate]) universe
        assertBool "the complete query closure selects each introduction and no unrelated producer"
            (Set.fromList selected == Set.fromList [0,1,2])

wholeHeadInputs :: Assertion
wholeHeadInputs = do
    let member x set = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) set
        inhabited set = Core.CExists Core.TySet (member (Core.CBound 0) set)
        head' = inhabited (Core.CBound 1)
        input = Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (Core.CBound 0)) (Core.CBound 0)
        shiftedInput = Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) (Core.CBound 1)) (Core.CBound 1)
        charge = Reference.chargeReferenceWork . fromIntegral
        compatible left right = fst (Reference.runReference 10000
            (WholePattern.mayEqualOperands charge 2 left right))
        pair a b = Core.CApp (Core.CApp (Core.CIntrinsic Core.OrderedPair) a) b
        choice term = Core.CApp (Core.CLogicalSelect Core.TySet) (Core.CLam Core.TySet term)
        match source target = fst (Reference.runReference 10000 do
            pattern' <- WholePattern.compileWholePattern charge 1 source
            WholePattern.matchWholePattern charge pattern' target)
    compatible (pair (Core.CBound 0) (Core.CBound 2))
        (pair (Core.CBound 1) (Core.CBound 0)) @?= Right False
    compatible (choice (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 3)))
        (choice (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 2))) @?= Right True
    compatible (choice (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 1)))
        (choice (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 2))) @?= Right False
    match head' (inhabited shiftedInput) @?= Right (Just (Map.singleton (Semantic.ViewVariableIx 0) input))
    match head' (inhabited (Core.CBound 0)) @?= Right Nothing
    match (Core.CAnd head' head') (Core.CAnd (inhabited (Core.CBound 1)) (inhabited (Core.CIntrinsic Core.Empty)))
        @?= Right Nothing
    match (inhabited shiftedInput) (inhabited (Core.CBound 1)) @?= Right Nothing
    match (inhabited shiftedInput) (inhabited shiftedInput) @?= Right (Just Map.empty)
    match (Core.CApp (Core.CLam Core.TySet Core.CTruth) (Core.CBound 0))
        (Core.CApp (Core.CLam Core.TyProp Core.CTruth) Core.CTruth) @?= Right (Just Map.empty)

    let compile arity premises residual = Rule.compileConclusionRule (const (pure ())) arity premises
            (Semantic.WholeLeaf residual)
        nested = Semantic.ResidualTemplate (Core.CEq Core.TySet input input)
        written = Semantic.describedResidualTemplate Core.CTruth
            (SourceEvidence.SourceInputs Nothing [SourceEvidence.SourceInput []
                (Semantic.TemplateVariable (Core.CBound 0))])
        slot = Semantic.ViewVariableIx 0
    for_ [nested,written] \residual -> do
        admitted <- expectRight =<< compile 1 [] residual
        state <- expectRight =<< Rule.startWholeRule (const (pure ())) Rule.OpenRuleInputs admitted
        needsInput <- expectRight =<< Rule.ruleNeedsInputEnumeration (const (pure ())) 100 state
        assertBool "nested and erased head parameters retain finite input discovery" needsInput
        pattern' <- WholePattern.compileWholePattern (const (pure ())) 1 (Semantic.residualTemplateFormula residual)
        inverse <- WholePattern.wholePatternParameters (const (pure ())) pattern'
        assertBool "occurrence does not expose an opaque or erased parameter" (Set.null inverse)
    uncovered <- compile 1 [] (Semantic.ResidualTemplate Core.CTruth)
    assertBool "a genuinely uncovered parameter still fails admission"
        (case uncovered of Left Join.JoinWholeConclusionUndetermined -> True; _ -> False)
    fixture <- makeFixture 2
    let premise index variable = Semantic.RulePremiseAtom
            (Semantic.StructureAtomTemplate (fixtureHead fixture index)
                (Vector.singleton (Semantic.TemplateVariable (Semantic.ViewVariableIx variable))))
    componentRule <- expectRight =<< compile 2 [premise 0 0,premise 1 1] written
    componentState <- expectRight =<< Rule.startWholeRule (const (pure ())) Rule.OpenRuleInputs componentRule
    assertEqual "source-retained parameters remain component outputs"
        [Set.singleton slot,Set.empty] (Rule.componentOutputs <$> Rule.pendingRuleComponents componentState)

equalityArgumentLocality :: Assertion
equalityArgumentLocality = do
    fixture <- makeFixture 2
    let row :: Natural -> [term] -> Semantic.AtomTemplate term
        row headIndex terms = Semantic.StructureAtomTemplate (fixtureHead fixture headIndex) (Vector.fromList terms)
        variable :: value -> Semantic.SetTermTemplate value
        variable value = Semantic.TemplateVariable value
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        run classSize width population present filtered = Reference.runReference 10000000 $ State.runStateT (do
            let x = variable (Semantic.ViewVariableIx 0)
                y = variable (Semantic.ViewVariableIx 1)
                target = row 1 [variable (0 :: Natural)]
                classOf value = if value < classSize then 0 else value
                keys = fmap (fmap classOf)
                count (Diagnostics.Count operation amount) = State.modify' (Diagnostics.countOperation operation amount)
                count _ = pure ()
                owner = (Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge (pure . keys)
                    (const (pure ())) count (\_ completed -> pure (Just (Production.completedAtom completed,())))
                    (\wanted answer -> pure (if keys wanted == keys (Production.atomicAnswer answer)
                        then Just (wanted,()) else Nothing)) (pure . classOf) (const (pure ())))
                    { Evaluation.ruleArgumentClass = \value -> pure (classOf value,value < classSize)
                    , Evaluation.ruleArgumentValue = \case Semantic.TemplateVariable value -> pure (Just value); _ -> pure Nothing
                    , Evaluation.ruleOpaqueIsRigid = \case Semantic.TemplateVariable value -> pure (value >= classSize); _ -> pure False
                    , Evaluation.ruleTermsMayAgree = \left right -> if filtered
                        then Production.freeTermsMayAgree charge (fmap (fmap classOf) left) (fmap (fmap classOf) right)
                        else pure True
                    }
                relevant = row 0 (variable (classSize+population+1) : replicate (width-1) (variable (classSize-1)))
                unrelated = [row 0 (replicate width (variable (classSize+index))) | index <- [1..population]]
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf atom') atom' Join.SourceRow ()
                    | atom' <- [relevant | present] <> unrelated]
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
                [Semantic.RulePremiseAtom (row 0 (y : replicate (width-1) x))] (row 1 [x]))
            snapshot <- admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature target) (Map.singleton 0 rule))
            result <- admit (Evaluation.solveRules owner snapshot facts (variable <$> [0..classSize-1]) target)
            pure (case result of Evaluation.FoundAnswer{} -> True;
                                 Evaluation.SearchAnswers answers _ -> not (Set.null (Relational.relationalRootAnswers answers)))) Diagnostics.emptyDiagnostics
    for_ [(2,2,8),(8,2,8),(32,2,8),(2,4,8),(2,8,8),(2,2,32),(2,2,128)] \(classSize,width,population) ->
        for_ [(present,filtered) | present <- [False,True],filtered <- [False,True]] \(present,filtered) -> do
            (found,counts) <- expectRight (fst (run classSize width population present filtered))
            assertEqual "class lookup retains completed answers and misses" present found
            let count operation = Map.findWithDefault 0 operation (Diagnostics.operationCounts counts)
            assertBool ("equality locality counters: " <> show (classSize,width,population,present,counts))
                (not filtered || count Diagnostics.CandidatePair <= 8 && count Diagnostics.GroundInstance <= 2
                    && count Diagnostics.UniqueRequest <= 5)

partialArgumentBuckets :: Assertion
partialArgumentBuckets = do
    fixture <- makeFixture 1
    let result :: term -> Semantic.AtomTemplate term
        result term = Semantic.StructureAtomTemplate (fixtureHead fixture 0) (Vector.singleton term)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        set = Semantic.TemplateVariable (Semantic.ViewVariableIx 1)
        value = Semantic.TemplateVariable :: Natural -> Semantic.SetTermTemplate Natural
        goal = result (value 0)
        charge = lift . Reference.chargeReferenceWork . fromIntegral
        admit action = action >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
        run population = Reference.runReference 10000000 $ State.runStateT (do
            rule <- Rule.RegisteredClassification <$> admit (Rule.compileRule charge 2
                [Semantic.RulePremiseAtom (Semantic.MembershipAtomTemplate x set)] (result set))
            snapshot <- admit (Rule.prepareRuleSnapshot charge (Rule.atomSignature goal) (Map.singleton 0 rule))
            let count (Diagnostics.Count operation amount) = State.modify' (Diagnostics.countOperation operation amount)
                count _ = pure ()
                owner = (Production.atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge pure
                    (const (pure ())) count (\_ _ -> pure (Just (population,())))
                    (\_ _ -> pure Nothing) pure (const (pure ())))
                    { Evaluation.ruleArgumentValue = \case
                        Semantic.TemplateVariable argument -> pure (Just argument)
                        _ -> pure Nothing }
                facts = [Evaluation.RuleAnswer (Semantic.AtomicLeaf
                    (Semantic.MembershipAtomTemplate (value (population+index)) (value index))) index Join.SourceRow ()
                    | index <- [0..population-1]]
            outcome <- admit (Evaluation.solveRules owner snapshot facts [] goal)
            case outcome of
                Evaluation.FoundAnswer{} -> pure ()
                Evaluation.SearchAnswers answers _ -> unless (not (Set.null (Relational.relationalRootAnswers answers)))
                    (lift (Reference.invalidReferenceInput "a selective membership join lost its witness"))) Diagnostics.emptyDiagnostics
    pairs <- for [8,32,128] \population -> do
        (_,counts) <- expectRight (fst (run population))
        pure (Map.findWithDefault 0 Diagnostics.CandidatePair (Diagnostics.operationCounts counts))
    assertBool "one bound membership argument avoids unrelated members and sets" (all (<= 4) pairs)
