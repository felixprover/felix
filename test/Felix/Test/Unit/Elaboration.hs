{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Felix.Test.Unit.Elaboration (unitTests) where

import Base hiding (Empty)
import Control.Monad (foldM, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Module (preludeModuleName, localDeclarationOrdinal)
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.Diagnostics qualified as Diagnostics
import Felix.Checking.Notion.LeafIndex qualified as Leaves
import Felix.Checking.Notion.FormulaIndex qualified as Formulas
import Felix.Checking.Notion.SourceRows qualified as SourceRows
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Report.Location (pattern Nowhere)
import Felix.Syntax.Abstract qualified as Raw
import Felix.Test.Support.GlobalTyping
import Felix.Test.Support.FormationReference qualified as Reference
import Felix.Test.Support.FormationReferenceScope qualified as ReferenceScope
import Felix.Test.Support.FormationReferenceReplay (checkScopedReferenceReplay)
import Felix.Test.Support.FormationReferenceImports qualified as ReferenceImports
import Felix.Test.Unit.Module.Support (runModuleDriver, unusedResolver, TestValidationPolicy(..))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector

import Data.Text qualified as Text
import Numeric.Natural (Natural)
import Test.Tasty hiding (after)
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "Elaboration"
        [ testCase "abstracts only scoped source terms for the formation reference" scopesReferenceInputs
        , testCase "bounds Core-only abbreviation expansion at its actual use" boundsCoreAbbreviationExpansion
        , testCase "weakens complete structure parameter occurrences" weakensStructureParameters
        , testCase "production source templates preserve scope and written structure" encodesScopedSourceTemplates
        , testCase "interns opaque leaves with bounded exact syntax comparisons" internsOpaqueLeaves
        , testCase "whole formula identities survive weakening and exact hash collisions" internsWholeFormulas
        , testCase "whole notion facts replay exactly through compound goals and scoped sources" replaysWholeFormation
        , testCase "positive query execution agrees with independent finite closure" finiteQueriesAgree
        , testCase "compound query plans execute and replay at increasing widths" compoundQueryScaling
        , testCase "aligns formation observations by nominal scope" alignsFormationObservations
        , testCase "direct queries reuse scoped evidence and ignore unrelated rows" indexesDirectFormation
        , testCase "bounds observation snapshots and checks their retained projections" boundsFormationObservations
        , testCase "keeps provisional formation origins out of proof queries" filtersFormationOrigins
        , testCase "unrelated alias populations do not multiply term traversal" aliasOccurrenceScaling
        , testCase "views aliases inside source arguments with their definition dependencies" viewsSourceAliases
        , testCase "replays formation reference aliases on facts and goals" replaysReferenceAliases
        , testCase "replays live formation equality chains through aliases" replaysLiveEqualities
        , testCase
            "admits and normalizes local aliases in dependency order"
            normalizesFormationAliases
        , testCase
            "rejects ineligible and nonmonotone local aliases atomically"
            rejectsInvalidFormationAliases
        ]

boundsCoreAbbreviationExpansion :: Assertion
boundsCoreAbbreviationExpansion = do
    foundation <- expectRight Foundation.checkedFoundation
    let symbol = Raw.mkMixfixItem [Just (Raw.Command "boundedExpansion"), Nothing]
            (Raw.Marker "bounded_expansion") Raw.NonAssoc
        key = Semantic.SemanticExpressionFunction (Raw.mixfixPattern symbol)
        pair term = CApp (CApp (CIntrinsic OrderedPair) term) term
        rawPair term = Raw.ExprPair Nowhere term term
        argument depth = iterate rawPair (Raw.ExprVar (Raw.NamedVar "X")) !! depth
        statement depth = Raw.StmtFormula (Raw.FormulaChain
            (Raw.ChainBase (Raw.ExprOp Nowhere symbol [argument depth] :| []) Raw.Positive
                (Raw.Relation Nowhere Raw.EqSymbol []) (Raw.ExprVar (Raw.NamedVar "X") :| [])))
        run depth = do
            let body = CLam TySet (iterate pair (CBound 0) !! depth)
                object = Identity.transparentObject (Identity.theoryId foundation) (TyArrow TySet TySet) body
            driven <- expectRight =<< runModuleDriver foundation preludeModuleName []
                unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver
                    (Elaboration.elaborateClaimEnvelopeWithLocalTransparentObject
                        Nowhere key object [] (statement depth)))
            case driven of
                Declaration.DriverSucceeded result _ _ -> pure result
                _ -> assertFailure "Core-only expansion failed outside elaboration" >> fail "unreachable"
    small <- expectRight =<< run 2
    assertEqual "ordinary substitution preserves the surrounding binder"
        (CForall TySet (CEq TySet (iterate pair (CBound 0) !! 4) (CBound 0)))
        (scopedCoreTerm (Elaboration.elaboratedClaimTarget small))
    run 8 >>= \case
        Left (Elaboration.ElaborationExpansionFailed _ actual failure)
            | Just _ <- Semantic.expansionRejectedDebit failure ->
            actual @?= key
        Left failure -> assertFailure ("expansion failed differently: " <> show failure)
        Right _ -> assertFailure "duplicating a large actual bypassed the expansion allowance"

weakensStructureParameters :: Assertion
weakensStructureParameters = do
    original <- expectRight (Elaboration.extendElaborationContext
        ((Elaboration.localId 0, Raw.NamedVar "X") :|
            [(Elaboration.localId 1, Raw.NamedVar "Y")]) Elaboration.emptyElaborationContext)
    let phrase = Schema.structurePhrase (Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl ((Just "record", Just "records") :| [])) (Raw.Marker "record"))
        reference = Semantic.globalBindingRef
            (Semantic.declarationSlot preludeModuleName (localDeclarationOrdinal 0))
            (Semantic.SemanticExpressionFunction (Raw.HoleCons (Raw.HoleCons Raw.End)))
        leaf index = SourceTerm.sourceTermOccurrence (CBound index) TySet (Elaboration.LocatedSourceTerm Nowhere)
    provider <- maybe (fail "invalid provider fixture") pure
        (SourceTerm.sourceGlobalProviderTermOccurrence reference (Vector.fromList [leaf 1, leaf 0])
            (CBound 1) (Elaboration.LocatedSourceTerm Nowhere))
    nested <- maybe (fail "invalid pair fixture") pure
        (SourceTerm.sourceOrderedPairTermOccurrence provider (leaf 0)
            (CApp (CApp (CIntrinsic OrderedPair) (CBound 1)) (CBound 0))
            (Elaboration.LocatedSourceTerm Nowhere))
    let annotated = Elaboration.annotateBinderContext
            (Map.singleton 0 (Elaboration.ResolvedStructureApplication phrase Map.empty [nested, leaf 1])) original
    named <- expectRight (Elaboration.extendTypedElaborationContext
        ((Elaboration.localId 2, Raw.NamedVar "p", TyProp) :| []) annotated)
    anonymous <- expectRight (Elaboration.extendTypedAnonymousElaborationContext TySet (Elaboration.localId 3) named)
    for_ [(annotated, 0), (named, 1), (anonymous, 2)] \(context, shift) -> do
        case Map.toList (Elaboration.binderStructures context) of
            [(receiver, Elaboration.ResolvedStructureApplication _ _ [pair, opaque])] -> do
                receiver @?= shift
                (left, right) <- maybe (fail "pair was erased by weakening") pure
                    (SourceTerm.sourceTermOccurrenceOrderedPair pair)
                SourceTerm.sourceTermOccurrenceCore left @?= CBound (1 + shift)
                SourceTerm.sourceTermOccurrenceCore right @?= CBound shift
                retained <- maybe (fail "provider was erased by weakening") pure
                    (SourceTerm.sourceTermOccurrenceProvider left)
                SourceTerm.sourceTermProviderHead retained @?= Semantic.GlobalSourceProvider reference
                (SourceTerm.sourceTermOccurrenceCore <$> toList (SourceTerm.sourceTermProviderArguments retained))
                    @?= [CBound (1 + shift), CBound shift]
                SourceTerm.sourceTermOccurrenceCore opaque @?= CBound (1 + shift)
                assertBool "synthetic leaves remain opaque" (isNothing (SourceTerm.sourceTermOccurrenceProvider opaque))
                SourceTerm.sourceTermOccurrencePresentation left @?= Elaboration.LocatedSourceTerm Nowhere
            _ -> fail "structure annotation moved to the wrong receiver"

aliasOccurrenceScaling :: Assertion
aliasOccurrenceScaling = do
    let sample count depth = do
            initial <- extendBinder 0 "A" Elaboration.emptyElaborationContext
            context <- foldM (\prior index -> addAlias (index + 1)
                ("alias" <> Text.pack (show index)) index index prior) initial [0 .. count - 1]
            let aliases = Elaboration.alignFormationAliases context
                types = replicate (fromIntegral count + 1) TySet
                term = iterate (CApp (CIntrinsic PowerSet)) (CBound count) !! depth
                original = checked types term
                source = sourceTerm types term
                (logical, afterLogical) = Elaboration.countedNormalizeFormationAliases 1000000 aliases original
                (viewed, afterSource) = Elaboration.countedViewFormationAliases 1000000 aliases source
            result <- expectRight logical
            assertEqual "irrelevant aliases leave the checked term unchanged" original
                (Elaboration.formationAliasNormalizationResult result)
            (value, dependencies) <- expectRight viewed
            assertEqual "irrelevant aliases leave source denotation unchanged" original
                (SourceTerm.sourceTermOccurrenceCore value)
            assertBool "no invented alias dependencies" (null dependencies)
            checkCountedAliases aliases original
            pure (1000000 - afterLogical, 1000000 - afterSource)
        growth (smallLogical, smallSource) (largeLogical, largeSource) =
            (largeLogical - smallLogical, largeSource - smallSource)
    small <- sample 8 0
    smallDeep <- sample 8 128
    many <- sample 32 0
    manyDeep <- sample 32 128
    assertEqual "the cost of traversing the term is independent of unrelated alias count"
        (growth small smallDeep) (growth many manyDeep)

testGlobalType :: GlobalTyping ObjectId
testGlobalType = fixtureGlobalTyping (globalTypingFixture [])

normalizesFormationAliases :: Assertion
normalizesFormationAliases = do
    contextA <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    contextP <- addAlias 1 "P" 0 0 contextA
    for_ [Elaboration.emptyElaborationContext, contextA, contextP] checkCountedAliasScope

    let oneStepProposition = checked [TySet, TySet]
            (CEq TySet (CBound 0) (CBound 0))
    oneStep <- expectRight
        (Elaboration.normalizeFormationAliases
            (Elaboration.alignFormationAliases contextP)
            oneStepProposition)
    assertEqual "one-step alias normal form"
        (CEq TySet (CBound 1) (CBound 1))
        (scopedCoreTerm
            (Elaboration.formationAliasNormalizationResult oneStep))
    assertEqual "one-step replay ordinal"
        [0]
        ( Elaboration.formationAliasReplayStepOrdinal
            <$> Elaboration.formationAliasNormalizationReplaySteps oneStep
        )

    contextR <- addAlias 2 "R" 0 1 contextP
    let multiStepProposition = checked [TySet, TySet, TySet]
            (CEq TySet (CBound 0) (CBound 1))
    multiStep <- expectRight
        (Elaboration.normalizeFormationAliases
            (Elaboration.alignFormationAliases contextR)
            multiStepProposition)
    assertEqual "dependent aliases reach the oldest source root"
        (CEq TySet (CBound 2) (CBound 2))
        (scopedCoreTerm
            (Elaboration.formationAliasNormalizationResult multiStep))
    for_ [(contextA, checked [TySet] CTruth), (contextP, oneStepProposition),
            (contextP, checked [TySet, TySet] (CForall TySet (CEq TySet (CBound 0) (CBound 1)))),
            (contextR, multiStepProposition),
            (contextR, checked [TySet, TySet, TySet] CTruth)] \(context, proposition) ->
        checkCountedAliases (Elaboration.alignFormationAliases context) proposition
    let aliases = Elaboration.alignFormationAliases contextP
        outside = checked [TySet] CTruth
    case (Elaboration.normalizeFormationAliases aliases outside,
            Elaboration.countedNormalizeFormationAliases 1000000 aliases outside) of
        (Left ordinary, (Left (CountedCoreOperationFailed counted), remaining)) -> do
            assertEqual "scope failures retain their original classification" ordinary counted
            assertBool "a failed checked operation retains its work debit" (remaining < 1000000)
        _ -> assertFailure "counted alias normalization hid an invalid source scope"
    assertEqual "replay steps retain newest-to-oldest definition order"
        [1, 0]
        ( Elaboration.formationAliasReplayStepOrdinal
            <$> Elaboration.formationAliasNormalizationReplaySteps multiStep
        )

-- The counted operation must preserve the proof-relevant replay recipe, not
-- merely arrive at an equal final proposition.
checkCountedAliases :: Elaboration.AlignedFormationAliases -> ScopedCheckedCore ObjectId -> Assertion
checkCountedAliases aliases original = do
    ordinary <- expectRight (Elaboration.normalizeFormationAliases aliases original)
    let run = (\(result, after) -> (fmap observe result, after))
            . (\allowance -> Elaboration.countedNormalizeFormationAliases allowance aliases original)
        observe normalization =
            (Elaboration.formationAliasNormalizationOriginal normalization,
                Elaboration.formationAliasNormalizationResult normalization,
                [(Elaboration.formationAliasReplayStepOrdinal step,
                    Elaboration.formationAliasReplayStepAbstraction step,
                    Notion.materializedNotionHypothesisOrigin (Elaboration.formationAliasReplayStepDefinition step))
                | step <- Elaboration.formationAliasNormalizationReplaySteps normalization])
        (result, after) = run 1000000
        used = 1000000 - after
    assertEqual "counting preserves normalization and replay provenance" (Right (observe ordinary)) result
    assertEqual "exact alias allowance leaves no unused work" (result, 0) (run used)
    when (used > 0) do
        assertEqual "one-short alias work exhausts without changing its error class"
            (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))

checkCountedAliasScope :: Elaboration.ElaborationContext -> Assertion
checkCountedAliasScope context =
    for_ [Elaboration.FormationNotionQuery, Elaboration.ProofNotionQuery,
            Elaboration.DefinitionResultNotionQuery] \consumer -> do
        let observe aliases =
                (SourceTerm.sourceTermOccurrenceCore <$> Elaboration.formationAliasTerms aliases,
                    [(Notion.materializedNotionHypothesisOrigin definition,
                        Notion.materializedNotionHypothesisProposition definition)
                    | definition <- Elaboration.formationAliasDefinitions aliases])
            ordinary = observe (Elaboration.formationAliasesFor consumer (Elaboration.alignFormationAliases context))
            run allowance = case Elaboration.countedFormationAliasesFor allowance consumer context of
                (result, after) -> (fmap observe result, after)
            (answer, remaining) = run 1000000
            used = 1000000 - remaining
        assertEqual "counted alignment preserves alias endpoints, definition order, and consumer policy"
            (Right ordinary) answer
        assertEqual "alias alignment and filtering share an exact allowance" (answer, 0) (run used)
        when (used > 0) do
            assertEqual "one-short alias alignment exhausts"
                (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))

replaysReferenceAliases :: Assertion
replaysReferenceAliases = do
    foundation <- expectRight Foundation.checkedFoundation
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    importCheck <- Declaration.newImportCheck foundation
    imports <- expectRight =<< Declaration.prepareImports importCheck []
    let noProver = Declaration.vampireResolver (\_ -> fail "alias formation requested an external prover")
    contextA <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    contextX <- extendBinder 1 "x" contextA
    contextP <- addAlias 2 "P" 1 0 contextX
    contextY <- addAlias 3 "y" 1 1 contextP
    contextR <- addAlias 4 "R" 1 2 contextY
    nested <- extendBinder 5 "unused" contextR
    for_ [(0, contextR), (1, nested)] \(offset, context) -> do
        checkCountedAliasScope context
        let ambient = snd <$> toList (Elaboration.elaborationContextSupport context)
            assertion (element, set) = Notion.membershipSourceNotionAssertion
                (sourceTerm ambient (CBound (element + offset))) (sourceTerm ambient (CBound (set + offset)))
                (checked ambient (CApp (CApp (CIntrinsic Member) (CBound (element + offset))) (CBound (set + offset))))
                Notion.ConjunctionHere Nowhere
            base = (3,4) -- x in A
            aliased = (1,0) -- y in R, with y=x and R=P=A
            origin = Elaboration.FormationFromProofLocal 42 Elaboration.FormationProofAssumption
        for_ [(base, base), (base, aliased), (aliased, base), (aliased, (3,2))] \(factTerms, goalTerms) -> do
            let fact = assertion factTerms
                goal = assertion goalTerms
                parent = Notion.sourceAssertionFormula fact
                source = Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport context)
                    parent (SourceEvidence.SourceAtom fact) 42 Elaboration.FormationProofAssumption
                active = admitFormationSource source context
            let live = Declaration.runProspectiveLoweringDriver do
                    query <- Elaboration.elaborateProofNotionEvidenceWithBudget
                        (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits) active Nowhere goal
                    case query of
                        Right (Elaboration.NotionQueryFound evidence, budget) -> do
                            replayed <- Declaration.replayTransientFormationLowering closure evidence (Notion.sourceAssertionFormula goal)
                            pure (Just (evidence, budget, replayed))
                        _ -> pure Nothing
            driven <- expectRight =<< Declaration.runModuleDriverFreshIO foundation preludeModuleName imports noProver live
            case driven of
                Declaration.DriverSucceeded (Just (evidence, budget, Right _)) _ _ -> do
                    assertEqual "live aliases bypass the legacy controller" 0
                        (Notion.formationSearchCompositePremiseRequests (Notion.formationSearchBudgetStatistics budget))
                    when (factTerms /= base || goalTerms /= base)
                        (assertBool "live alias replay retains its defining hypotheses"
                            (Vector.length (Notion.materializedFormationHypotheses evidence) > 1))
                _ -> assertFailure "the live alias query or its checked replay failed"
            (inputs, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
                Elaboration.ProofNotionQuery active goal)
            let facts = ReferenceScope.scopedReferenceFacts inputs
                target = ReferenceScope.scopedReferenceGoal inputs
                aliases = ReferenceScope.scopedReferenceAliases inputs
                locals = Notion.materializedNotionHypothesis parent origin : ReferenceScope.scopedReferenceAliasDefinitions inputs
                term = \case
                    Semantic.TemplateVariable seed -> Right (scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
                    _ -> Left "the membership alias fixture has no providers"
            (_, result) <- expectRight (fst (Reference.evaluateFormation 10000 Map.empty facts aliases target))
            meanings <- expectRight =<< checkScopedReferenceReplay closure Map.empty ambient term (ReferenceImports.importedReferenceAtom [] term) locals inputs result
            assertEqual "both alias families normalize to the same checked membership"
                (Just (Notion.sourceAssertionFormula (assertion base))) (Map.lookup target meanings)
            assertBool "all eligible alias endpoints enter fixed support independently of lookup"
                (Set.size aliases >= 5)
            (_, absent) <- expectRight (fst (Reference.evaluateFormation 10000 Map.empty
                ([] :: [Reference.ReferenceFact Elaboration.FormationSourceOrigin]) aliases target))
            assertBool "alias endpoints supply syntax, not membership evidence"
                (all ((/= target) . fst) (Map.keys (Reference.referenceAnswers absent)))
            checkScopedReferenceReplay closure Map.empty ambient term (ReferenceImports.importedReferenceAtom [] term) (take 1 locals) inputs result >>= \case
                Left{} -> pure ()
                Right{} -> assertFailure "alias support was accepted without actual definition locals"
            let wrongLocals = Notion.materializedNotionHypothesis (Notion.sourceAssertionFormula (assertion (4,3))) origin
                    : drop 1 locals
            checkScopedReferenceReplay closure Map.empty ambient term (ReferenceImports.importedReferenceAtom [] term) wrongLocals inputs result >>= \case
                Left{} -> pure ()
                Right{} -> assertFailure "alias normalization hid a changed local proposition"
            (restricted, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
                Elaboration.DefinitionResultNotionQuery active goal)
            assertBool "declaration results do not borrow proof-local alias endpoints"
                (Set.null (ReferenceScope.scopedReferenceAliases restricted)
                    && null (ReferenceScope.scopedReferenceAliasDefinitions restricted))

replaysLiveEqualities :: Assertion
replaysLiveEqualities = do
    foundation <- expectRight Foundation.checkedFoundation
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    importCheck <- Declaration.newImportCheck foundation
    imports <- expectRight =<< Declaration.prepareImports importCheck []
    let noProver = Declaration.vampireResolver (\_ -> fail "formation equality requested an external prover")
    contextA <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    contextX <- extendBinder 1 "x" contextA
    contextY <- extendBinder 2 "y" contextX
    contextZ <- extendBinder 3 "z" contextY
    contextP <- addAlias 4 "P" 0 0 contextZ
    nested <- extendBinder 5 "unused" contextP
    for_ [(0, contextP), (1, nested)] \(offset, context) -> do
        let ambient = snd <$> toList (Elaboration.elaborationContextSupport context)
            term index = CBound (index + offset)
            occurrence = sourceTerm ambient . term
            membership index = Notion.membershipSourceNotionAssertion
                (occurrence index) (occurrence 4)
                (checked ambient (CApp (CApp (CIntrinsic Member) (term index)) (term 4)))
                Notion.ConjunctionHere Nowhere
            equality ordinal left right =
                let proposition = checked ambient (CEq TySet (term left) (term right))
                    occurrence' = Notion.setSourceEqualityOccurrence
                        (occurrence left) (occurrence right) proposition Notion.ConjunctionHere Nowhere
                in Elaboration.formationEqualitySource (Elaboration.elaborationContextSupport context)
                    proposition (occurrence' :| []) ordinal Elaboration.FormationProofAssumption
            fact = membership 3
            source = Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport context)
                (Notion.sourceAssertionFormula fact) (SourceEvidence.SourceAtom fact) 42 Elaboration.FormationProofAssumption
            -- x=y and z=y, with the compiler-owned alias P=z. A cycle
            -- exercises visited endpoints without creating new proof paths.
            active = admitFormationEqualitySource (equality 43 3 2)
                (admitFormationEqualitySource (equality 44 1 2)
                    (admitFormationEqualitySource (equality 45 2 3)
                        (admitFormationSource source context)))
        for_ [3, 2, 1, 0] \goalIndex -> do
            let goal = membership goalIndex
                live = Declaration.runProspectiveLoweringDriver do
                    query <- Elaboration.elaborateProofNotionEvidenceWithBudget
                        (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits) active Nowhere goal
                    case query of
                        Right (Elaboration.NotionQueryFound evidence, budget) -> do
                            replayed <- Declaration.replayTransientFormationLowering closure evidence (Notion.sourceAssertionFormula goal)
                            pure (Just (evidence, budget, replayed))
                        _ -> pure Nothing
            driven <- expectRight =<< Declaration.runModuleDriverFreshIO foundation preludeModuleName imports noProver live
            case driven of
                Declaration.DriverSucceeded (Just (evidence, budget, Right _)) _ _ -> do
                    assertEqual "ordinary equality bypasses the legacy controller" 0
                        (Notion.formationSearchCompositePremiseRequests (Notion.formationSearchBudgetStatistics budget))
                    if Notion.sourceAssertionFormula goal == Notion.sourceAssertionFormula fact
                        then do
                            assertEqual "direct evidence retains only its original hypothesis" 1
                                (Vector.length (Notion.materializedFormationHypotheses evidence))
                            assertEqual "direct evidence does not prepare the equality index" 0
                                (Notion.formationSearchEqualitySourceInspections
                                    (Notion.formationSearchBudgetStatistics budget))
                            assertEqual "direct evidence does not transport through unused aliases" 0
                                (Notion.formationSearchEqualityTransportSteps
                                    (Notion.formationSearchBudgetStatistics budget))
                        else do
                            assertBool "replay retains the actual equality hypotheses"
                                (Vector.length (Notion.materializedFormationHypotheses evidence) >= 2)
                            let origins = Notion.materializedNotionHypothesisOrigin
                                    <$> toList (Notion.materializedFormationHypotheses evidence)
                            assertBool "parallel equalities retain source-order predecessor selection"
                                (Elaboration.FormationFromProofLocal 43 Elaboration.FormationProofAssumption `elem` origins
                                    && Elaboration.FormationFromProofLocal 45 Elaboration.FormationProofAssumption `notElem` origins)
                _ -> assertFailure "live equality transport or checked replay failed"

viewsSourceAliases :: Assertion
viewsSourceAliases = do
    contextA <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    freshP <- extendBinder 1 "P" contextA
    body <- power (sourceTerm [TySet] (CBound 0))
    contextP <- expectRight (Elaboration.extendElaborationContextWithFormationAlias
        (Elaboration.localId 1) body
        (checked [TySet,TySet] (CEq TySet (CBound 0) (CApp (CIntrinsic PowerSet) (CBound 1))))
        0 Nowhere freshP) >>= maybe (fail "the checked alias was rejected") pure
    contextR <- addAlias 2 "R" 0 1 contextP
    input <- power (sourceTerm [TySet,TySet,TySet] (CBound 0))
    let aliases = Elaboration.alignFormationAliases contextR
        expected = CApp (CIntrinsic PowerSet) (CApp (CIntrinsic PowerSet) (CBound 2))
    (viewed, definitions) <- expectRight (Elaboration.viewFormationAliases aliases input)
    assertEqual "nested aliases preserve the constructed set term" expected
        (scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore viewed))
    assertEqual "the exact original definitions are retained once in declaration order"
        [Elaboration.FormationFromProofLocal ordinal Elaboration.FormationProofLocalDefinition | ordinal <- [0,1]]
        (Notion.materializedNotionHypothesisOrigin <$> definitions)
    let nestedProvider = do
            outer <- SourceTerm.sourceTermOccurrenceProvider viewed
            (argument, _) <- Vector.uncons (SourceTerm.sourceTermProviderArguments outer)
            SourceTerm.sourceTermProviderHead <$> SourceTerm.sourceTermOccurrenceProvider argument
    assertEqual "the defining source sidecar supplies the inner provider"
        (Just (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)) nestedProvider
    normalized <- expectRight (Elaboration.normalizeFormationAliases aliases (SourceTerm.sourceTermOccurrenceCore input))
    assertEqual "source viewing and checked Core substitution agree"
        (Elaboration.formationAliasNormalizationResult normalized) (SourceTerm.sourceTermOccurrenceCore viewed)
    for_ [input, viewed] \candidate -> do
        let seal allowance =
                let (sealResult, sealRemaining) = SourceTerm.countedSealCanonicalSourceTermOccurrence allowance
                        (SourceTerm.SourceTermCheckingContext testGlobalType [TySet, TySet, TySet])
                        (SourceTerm.forgetScopedSourceTermOccurrence candidate)
                in (SourceTerm.sourceTermOccurrenceCore <$> sealResult, sealRemaining)
            (sealed, sealingRemaining) = seal 1000000
            used = 1000000 - sealingRemaining
        assertEqual "bounded sealing preserves the original scoped Core"
            (Right (SourceTerm.sourceTermOccurrenceCore candidate)) sealed
        assertEqual "source sealing shares its exact allowance" (sealed, 0) (seal used)
        assertEqual "one-short source sealing exhausts"
            (Left CountedCoreStructuralWorkExhausted, 0) (seal (used - 1))
        (ordinary, dependencies) <- expectRight (Elaboration.viewFormationAliases aliases candidate)
        let observe (term, definitions') =
                (SourceTerm.sourceTermOccurrenceCore term,
                    Notion.materializedNotionHypothesisOrigin <$> definitions')
            run allowance = case Elaboration.countedViewFormationAliases allowance aliases candidate of
                (result, remaining) -> (fmap observe result, remaining)
            (result, remaining) = run 1000000
            usedWork = 1000000 - remaining
        assertEqual "counted source views preserve denotation and ordered dependencies"
            (Right (observe (ordinary, dependencies))) result
        assertEqual "source alias viewing shares its exact work allowance" (result, 0) (run usedWork)
        assertEqual "one-short source alias viewing exhausts"
            (Left CountedCoreStructuralWorkExhausted, 0) (run (usedWork - 1))
    (again, unused) <- expectRight (Elaboration.viewFormationAliases aliases viewed)
    assertEqual "an already viewed term is stable"
        (SourceTerm.sourceTermOccurrenceCore viewed) (SourceTerm.sourceTermOccurrenceCore again)
    assertBool "an already viewed term needs no additional definition dependencies" (null unused)
    case Elaboration.viewFormationAliases aliases (sourceTerm [TySet] (CBound 0)) of
        Left Elaboration.FormationAliasReplacementInvariantFailed{} -> pure ()
        _ -> assertFailure "alias viewing crossed a mismatched checked scope"
    foundation <- expectRight Foundation.checkedFoundation
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    explicitSet <- power (sourceTerm [TySet,TySet,TySet] (CBound 2))
    let aliasSet = sourceTerm [TySet,TySet,TySet] (CBound 0)
        membership set = Notion.membershipSourceNotionAssertion
            (sourceTerm [TySet,TySet,TySet] (CBound 2)) set
            (checked [TySet,TySet,TySet] (CApp (CApp (CIntrinsic Member) (CBound 2))
                (scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore set)))) Notion.ConjunctionHere Nowhere
        origin = Elaboration.FormationFromProofLocal 42 Elaboration.FormationProofAssumption
    for_ [(aliasSet, explicitSet), (explicitSet, aliasSet)] \(given, requested) -> do
        let fact = membership given
            parent = Notion.sourceAssertionFormula fact
            context = admitFormationSource
                (Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport contextR)
                    parent (SourceEvidence.SourceAtom fact) 42 Elaboration.FormationProofAssumption) contextR
        (inputs, _) <- expectRight (ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
            Elaboration.ProofNotionQuery context (membership requested))
        let target = ReferenceScope.scopedReferenceGoal inputs
            interpret = ReferenceImports.importedReferenceTerm closure []
                (\seed -> scopedCoreTerm (ReferenceScope.scopedReferenceLeaves inputs Map.! seed))
            locals = Notion.materializedNotionHypothesis parent origin : ReferenceScope.scopedReferenceAliasDefinitions inputs
        (_, result) <- expectRight (fst (Reference.evaluateFormation 10000 Map.empty
            (ReferenceScope.scopedReferenceFacts inputs) (ReferenceScope.scopedReferenceAliases inputs) target))
        let prepare allowance = Reference.runReference allowance do
                (prepared, _) <- ReferenceScope.prepareScopedReferenceInputs Notion.defaultFormationSearchLimits
                    Elaboration.ProofNotionQuery context (membership requested)
                pure (ReferenceScope.scopedReferenceGoal prepared, ReferenceScope.scopedReferenceFacts prepared,
                    ReferenceScope.scopedReferenceLeaves prepared, ReferenceScope.scopedReferenceAliases prepared,
                    Notion.materializedNotionHypothesisOrigin <$> ReferenceScope.scopedReferenceAliasDefinitions prepared)
            (preparedResult, work) = prepare 1000000
        assertEqual "metered alias preparation preserves rows, leaves, support, and definition ownership"
            (Right (target, ReferenceScope.scopedReferenceFacts inputs, ReferenceScope.scopedReferenceLeaves inputs,
                ReferenceScope.scopedReferenceAliases inputs,
                Notion.materializedNotionHypothesisOrigin <$> ReferenceScope.scopedReferenceAliasDefinitions inputs)) preparedResult
        assertEqual "alias preparation consumes its exact combined allowance" (preparedResult, work) (prepare work)
        assertEqual "one-short alias preparation exhausts"
            (Left Reference.ReferenceWorkExhausted) (fst (prepare (work - 1)))
        meanings <- expectRight =<< checkScopedReferenceReplay closure Map.empty [TySet,TySet,TySet]
            interpret (ReferenceImports.importedReferenceAtom [] interpret) locals inputs result
        assertEqual "provider aliases match and replay in both directions"
            (Just (Notion.sourceAssertionFormula (membership explicitSet))) (Map.lookup target meanings)
  where
    power argument = do
        raw <- maybe (fail "power-set source fixture failed") pure
            (SourceTerm.sourceIntrinsicProviderTermOccurrence Semantic.PowerSetProvider
                (Vector.singleton (SourceTerm.forgetScopedSourceTermOccurrence argument))
                (Elaboration.LocatedSourceTerm Nowhere))
        expectRight (SourceTerm.sealCanonicalSourceTermOccurrence
            (SourceTerm.SourceTermCheckingContext testGlobalType
                (scopedCoreContext (SourceTerm.sourceTermOccurrenceCore argument))) raw)

rejectsInvalidFormationAliases :: Assertion
rejectsInvalidFormationAliases = do
    contextA <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    contextP <- addAlias 1 "P" 0 0 contextA
    contextR <- extendBinder 2 "R" contextP
    let outerTypes = [TySet, TySet]
        currentTypes = TySet : outerTypes
        body = sourceTerm outerTypes (CBound 0)
        ineligible = checked currentTypes
            (CEq TySet (CBound 1) (CBound 1))
        valid = checked currentTypes
            (CEq TySet (CBound 0) (CBound 1))
    case Elaboration.extendElaborationContextWithFormationAlias
            (Elaboration.localId 2) body ineligible 1 Nowhere contextR of
        Right Nothing -> pure ()
        Left failure ->
            assertFailure
                ("ineligible equality was rejected as malformed: "
                    <> Text.unpack failure)
        Right Just{} ->
            assertFailure "an ineligible equality was admitted as an alias"
    case Elaboration.extendElaborationContextWithFormationAlias
            (Elaboration.localId 2) body valid 0 Nowhere contextR of
        Left{} -> pure ()
        Right{} ->
            assertFailure
                "a nonmonotone alias definition ordinal was accepted"

addAlias
    :: Natural
    -> Text
    -> Natural
    -> Natural
    -> Elaboration.ElaborationContext
    -> IO Elaboration.ElaborationContext
addAlias identityValue name bodyIndex ordinal outer = do
    extended <- extendBinder identityValue name outer
    let outerTypes = snd <$> toList (Elaboration.elaborationContextSupport outer)
        currentTypes = TySet : outerTypes
        body = sourceTerm outerTypes (CBound bodyIndex)
        equality = checked currentTypes
            (CEq TySet (CBound 0) (CBound (bodyIndex + 1)))
    admitted <- expectRight
        (Elaboration.extendElaborationContextWithFormationAlias
            (Elaboration.localId identityValue)
            body equality ordinal Nowhere extended)
    maybe
        (assertFailure "the generated local definition was ineligible"
            >> fail "unreachable")
        pure
        admitted

extendBinder
    :: Natural
    -> Text
    -> Elaboration.ElaborationContext
    -> IO Elaboration.ElaborationContext
extendBinder identityValue name =
    expectRight
        . Elaboration.extendElaborationContext
            ((Elaboration.localId identityValue, Raw.NamedVar name) :| [])

sourceTerm
    :: [CoreType]
    -> CanonicalTerm ObjectId
    -> Elaboration.ScopedSourceTerm
sourceTerm context term =
    SourceTerm.sourceTermOccurrence
        (checked context term)
        TySet
        (Elaboration.LocatedSourceTerm Nowhere)

checked
    :: [CoreType]
    -> CanonicalTerm ObjectId
    -> ScopedCheckedCore ObjectId
checked context =
    either (error . show) id
        . checkScopedCanonicalCore testGlobalType context

expectRight :: Show failure => Either failure value -> IO value
expectRight (Left failure) =
    assertFailure (show failure) >> fail "unreachable"
expectRight (Right value) = pure value

-- Same Core types are insufficient to move evidence between sibling binders.
alignsFormationObservations :: Assertion
alignsFormationObservations = do
    outer <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    original <- extendBinder 1 "x" outer
    let withSource = observedMembership original
        snapshot context = Elaboration.formationObservationsFor Notion.defaultFormationSearchLimits
            Elaboration.ProofNotionQuery context
    nested <- extendBinder 2 "z" withSource
    (observations, _) <- expectRight (snapshot nested)
    (counted, _) <- expectRight (fst (Elaboration.countedFormationObservationsFor 10000
        Notion.defaultFormationSearchLimits Elaboration.ProofNotionQuery nested))
    assertEqual "counted nominal alignment retains the same weakened parents"
        (Elaboration.formationObservationSource <$> observations)
        (Elaboration.formationObservationSource <$> counted)
    observation <- case observations of
        [one] -> pure one
        _ -> assertFailure "one retained membership observation expected" >> fail "unreachable"
    let assertion = Elaboration.formationObservationAssertion observation
    assertEqual "the source proposition weakens under the new binder"
        (CApp (CApp (CIntrinsic Member) (CBound 1)) (CBound 2))
        (scopedCoreTerm (Elaboration.formationObservationSource observation))
    assertEqual "the projected formula has the same rebasing"
        (Elaboration.formationObservationSource observation)
        (Notion.sourceAssertionFormula assertion)
    assertEqual "proof-local kind and original ordinal survive"
        (Elaboration.FormationFromProofLocal 42 Elaboration.FormationProofDerivedClaim)
        (Elaboration.formationObservationOrigin observation)
    sibling <- extendBinder 3 "y" outer
    let source = membershipSource original Notion.ConjunctionHere
        equality = checked [TySet, TySet] (CEq TySet (CBound 0) (CBound 1))
        equalitySource = Elaboration.formationEqualitySource (Elaboration.elaborationContextSupport original)
            equality (Notion.setSourceEqualityOccurrence
                (sourceTerm [TySet, TySet] (CBound 0)) (sourceTerm [TySet, TySet] (CBound 1))
                equality Notion.ConjunctionHere Nowhere :| []) 43 Elaboration.FormationProofAssumption
    for_ [sibling, outer] \context -> do
        case Elaboration.addFormationPremiseSource source context of
            Left Elaboration.FormationObservationScopeError{} -> pure ()
            _ -> assertFailure "scope insertion admitted an expired or sibling source"
        case Elaboration.addFormationEqualitySource equalitySource context of
            Left Elaboration.FormationObservationScopeError{} -> pure ()
            _ -> assertFailure "equality insertion admitted an expired or sibling source"

boundsFormationObservations :: Assertion
boundsFormationObservations = do
    outer <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    context <- extendBinder 1 "x" outer
    let measured path = Elaboration.runFormationScopePreparation
            (Elaboration.prepareFormationPremiseSource (membershipSource context path) context)
        (_, insertion) = measured Notion.ConjunctionHere
        (rejected, failedInsertion) = measured (Notion.ConjunctionLeft Notion.ConjunctionHere)
    assertEqual "scope insertion is counted even when no query is run" (Just 1)
        (Map.lookup Diagnostics.ScopeInsertion (Diagnostics.operationCounts (Diagnostics.measuredDiagnostics insertion)))
    assertBool "successful source preparation retains its physical work"
        (sum (Diagnostics.phaseInspections (Diagnostics.measuredDiagnostics insertion)) > 0)
    case rejected of
        Left Elaboration.FormationObservationScopeError{} -> pure ()
        _ -> assertFailure "invalid projection escaped the measured scope boundary"
    assertBool "failed preparation retains completed physical work"
        (sum (Diagnostics.phaseInspections (Diagnostics.measuredDiagnostics failedInsertion)) > 0)
    let wideCore = checked [TySet, TySet] (foldr1 CAnd (replicate 8192 membershipFormula))
        wideEvidence = foldr1 SourceEvidence.SourceAnd
            (replicate 8192 (SourceEvidence.SourceAtom (membershipAssertion Notion.ConjunctionHere)))
        wideSource = Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport context)
            wideCore wideEvidence 99 Elaboration.FormationProofAssumption
        (wideResult, wideWork) = Elaboration.runFormationScopePreparation
            (Elaboration.prepareFormationPremiseSource wideSource context)
    case wideResult of
        Left (Elaboration.FormationScopePreparationLimitExceeded cap) -> do
            assertBool "scope insertion refuses the next debit without publishing a partial index"
                (Diagnostics.hasRejectedDebit wideWork)
            assertBool "accepted scope work stays within the independent cap"
                (sum (Diagnostics.phaseInspections (Diagnostics.measuredDiagnostics wideWork)) <= cap)
        _ -> assertFailure "an oversized source escaped the scope preparation allowance"
    let source = membershipSource context Notion.ConjunctionHere
        repeated = admitFormationSource source (observedMembership context)
        limits count = fromMaybe (error "invalid test formation limits")
            (Notion.formationSearchLimits 8 8 8 count 32 16)
        snapshot allowance target = Elaboration.formationObservationsFor (limits allowance)
            Elaboration.FormationNotionQuery target
        checkCounted count target = do
            let summarize (rows, statistics') =
                    ([(Elaboration.formationObservationSource row,
                        Notion.sourceAssertionFormula (Elaboration.formationObservationAssertion row),
                        Notion.sourceAssertionPath (Elaboration.formationObservationAssertion row),
                        Elaboration.formationObservationOrigin row, Elaboration.formationObservationOrdinal row)
                        | row <- rows], statistics')
                run allowance = case Elaboration.countedFormationObservationsFor allowance (limits count)
                        Elaboration.FormationNotionQuery target of
                    (result, after) -> (fmap summarize result, after)
                (answer, remaining) = run 1000000
                used = 1000000 - remaining
                expected = either (Left . CountedCoreOperationFailed) (Right . summarize) (snapshot count target)
            assertEqual "counted observations preserve sources, projections, order, and failures" expected answer
            assertEqual "observation work shares its exact allowance" (answer, 0) (run used)
            assertEqual "one-short observation work remains exhaustion"
                (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
    checkCounted 2 repeated
    checkCounted 1 repeated
    (observations, statistics) <- expectRight (snapshot 2 repeated)
    assertEqual "snapshot retains both evidence occurrences" [0,1]
        (Elaboration.formationObservationOrdinal <$> observations)
    assertEqual "every source inspection is charged" 2
        (Notion.formationSearchSourceIndexInspections statistics)
    case snapshot 1 repeated of
        Left Elaboration.FormationObservationExhausted{} -> pure ()
        _ -> assertFailure "one-short source budget did not exhaust"
    let prepared = Reference.runReference 10000
            (ReferenceScope.prepareScopedReferenceInputs (limits 1) Elaboration.FormationNotionQuery
                repeated (membershipAssertion Notion.ConjunctionHere))
    case fst prepared of
        Left Reference.ReferenceWorkExhausted -> pure ()
        _ -> assertFailure "scoped preparation reclassified observation exhaustion"
    let projection = Notion.ConjunctionRight (Notion.ConjunctionLeft Notion.ConjunctionHere)
        conjunction = checked [TySet,TySet]
            (CAnd (CNot membershipFormula) (CAnd membershipFormula (CNot membershipFormula)))
        projected = Elaboration.formationEvidenceSource
            (Elaboration.elaborationContextSupport context) conjunction
            (SourceEvidence.SourceAnd (SourceEvidence.SourceResidual Nothing)
                (SourceEvidence.SourceAnd (SourceEvidence.SourceAtom (membershipAssertion Notion.ConjunctionHere))
                    (SourceEvidence.SourceResidual Nothing))) 42 Elaboration.FormationProofDerivedClaim
    checkCounted 1 (admitFormationSource projected context)
    (projectedObservations, _) <- expectRight
        (snapshot 1 (admitFormationSource projected context))
    assertEqual "positive projection retains its whole source" [conjunction]
        (Elaboration.formationObservationSource <$> projectedObservations)
    assertEqual "nested conjunction recipe survives" [projection]
        (Notion.sourceAssertionPath . Elaboration.formationObservationAssertion <$> projectedObservations)
    case Elaboration.addFormationPremiseSource
            (membershipSource context (Notion.ConjunctionLeft Notion.ConjunctionHere)) context of
        Left Elaboration.FormationObservationScopeError{} -> pure ()
        _ -> assertFailure "scope insertion accepted an invalid projection"
    for_ [CNot membershipFormula, COr membershipFormula membershipFormula,
            CImp membershipFormula membershipFormula, CForall TySet membershipFormula] \formula -> do
        let hidden = Elaboration.formationEvidenceSource
                (Elaboration.elaborationContextSupport context) (checked [TySet,TySet] formula)
                (SourceEvidence.SourceAtom (membershipAssertion Notion.ConjunctionHere)) 42 Elaboration.FormationProofDerivedClaim
        case Elaboration.addFormationPremiseSource hidden context of
            Left Elaboration.FormationObservationScopeError{} -> pure ()
            _ -> assertFailure "a non-positive or unopened body leaked into the observations"
    let wrongSupport = Elaboration.formationEvidenceSource
            (Elaboration.elaborationContextSupport outer)
            (checked [TySet,TySet] membershipFormula)
            (SourceEvidence.SourceAtom (membershipAssertion Notion.ConjunctionHere)) 42 Elaboration.FormationProofDerivedClaim
    case Elaboration.addFormationPremiseSource wrongSupport context of
        Left Elaboration.FormationObservationScopeError{} -> pure ()
        _ -> assertFailure "a source with inconsistent nominal and checked supports was accepted"

filtersFormationOrigins :: Assertion
filtersFormationOrigins = do
    let actual = Elaboration.FormationFromProofLocal 4 Elaboration.FormationProofAssumption
        header = Elaboration.FormationFromDefinitionHeader 0 Nothing Nowhere
    assertBool "formation can use an active provisional observation"
        (Elaboration.notionQueryAdmitsOrigin Elaboration.FormationNotionQuery header)
    assertBool "a provisional observation is not a proof local"
        (not (Elaboration.notionQueryAdmitsOrigin Elaboration.ProofNotionQuery header))
    assertBool "proof queries retain actual local evidence"
        (Elaboration.notionQueryAdmitsOrigin Elaboration.ProofNotionQuery actual)
    assertBool "definition results use their own headers"
        (Elaboration.notionQueryAdmitsOrigin Elaboration.DefinitionResultNotionQuery header)
    assertBool "definition results do not capture proof-local evidence"
        (not (Elaboration.notionQueryAdmitsOrigin Elaboration.DefinitionResultNotionQuery actual))

indexesDirectFormation :: Assertion
indexesDirectFormation = do
    foundation <- expectRight Foundation.checkedFoundation
    outer <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    initial <- extendBinder 1 "x" outer
    costs <- for [0, 128, 1024 :: Natural] \count -> do
        let withTarget = observedMembership initial
            insert prior index = do
                let element = COpaqueInteger (fromIntegral index)
                    proposition = checked [TySet, TySet]
                        (CApp (CApp (CIntrinsic Member) element) (CBound 1))
                    assertion = Notion.membershipSourceNotionAssertion
                        (sourceTerm [TySet, TySet] element) (sourceTerm [TySet, TySet] (CBound 1))
                        proposition Notion.ConjunctionHere Nowhere
                expectRight (Elaboration.addFormationPremiseSource
                    (Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport initial)
                        proposition (SourceEvidence.SourceAtom assertion) index Elaboration.FormationProofAssumption) prior)
        context <- foldM insert withTarget (take (fromIntegral count) [0..])
        nested <- extendBinder 2 "fresh" context
        let types = [TySet, TySet, TySet]
            align :: Elaboration.ScopedSourceTerm -> Either Text Elaboration.ScopedSourceTerm
            align = maybe (Left "source term could not weaken") Right
                . SourceTerm.alignScopedSourceTermOccurrence types
        target <- expectRight (Notion.traverseSourceNotionAssertionParts align
            (Right . weakenCheckedScopedCore TySet) (membershipAssertion Notion.ConjunctionHere))
        result <- expectRight =<< runModuleDriver foundation preludeModuleName []
            unusedResolver AlwaysMissValidation
            (Declaration.runProspectiveLoweringDriver do
                query <- Elaboration.elaborateProofNotionEvidenceWithBudget
                    (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits)
                    nested Nowhere target
                closure <- Declaration.checkedObjectClosureLowering
                replay <- case query of
                    Right (Elaboration.NotionQueryFound evidence, _) ->
                        Just <$> Declaration.replayTransientFormationLowering closure evidence
                            (Notion.sourceAssertionFormula target)
                    _ -> pure Nothing
                pure (query, replay))
        case result of
            Declaration.DriverSucceeded
                    (Right (Elaboration.NotionQueryFound evidence, budget), Just (Right _)) _ _ -> do
                assertEqual "only the exact posting is inspected" 1
                    (Notion.formationSearchSourceIndexInspections (Notion.formationSearchBudgetStatistics budget))
                assertEqual "an exact hit does not select any catalogue producer" Nothing
                    (Map.lookup Diagnostics.SelectedProducer
                        (Diagnostics.operationCounts (Notion.formationSearchBudgetDiagnostics budget)))
                assertEqual "direct success remains explicit in completion accounting" (Map.singleton Diagnostics.ExactDirect 1)
                    (Diagnostics.outcomeCounts (Notion.formationSearchBudgetDiagnostics budget))
                assertEqual "selected evidence keeps its original local origin"
                    [Elaboration.FormationFromProofLocal 42 Elaboration.FormationProofDerivedClaim]
                    (Notion.materializedNotionHypothesisOrigin <$> toList (Notion.materializedFormationHypotheses evidence))
                pure (Notion.formationInferenceWorkUsed budget)
            _ -> assertFailure "indexed direct query failed to replay under weakening" >> pure 0
    case costs of
        [small, medium, large] -> assertBool ("direct-query work grew with unrelated rows: " <> show costs)
            (small <= medium && medium <= large && large < 2 * medium)
        _ -> assertFailure "missing direct-query samples"

-- The oracle receives complete eligible inputs and an independently enumerated
-- one-layer domain. The live owner must select, compile, search, and replay its
-- own source descriptions; no production rule or answer enters the oracle.
compoundQueryScaling :: Assertion
compoundQueryScaling = do
    foundation <- expectRight Foundation.checkedFoundation
    context <- extendBinder 0 "a" Elaboration.emptyElaborationContext
    for_ [False,True] \skewed -> do
        costs <- for [4,8,16] \width -> do
            let atom ordinal = Semantic.MembershipAtomTemplate (CBound 0) (COpaqueInteger ordinal)
                describe types ordinal =
                    let terms = atom ordinal
                        proposition = checked types (CApp (CApp (CIntrinsic Member) (CBound 0)) (COpaqueInteger ordinal))
                    in Notion.sourceNotionAssertionFromTemplate (sourceTerm types <$> terms)
                        proposition Notion.ConjunctionHere Nowhere
                facts = describe [TySet] <$> [0..width-1]
                supplied = foldl' (\active (ordinal,assertion) -> admitFormationSource
                    (Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport context)
                        (Notion.sourceAssertionFormula assertion) (SourceEvidence.SourceAtom assertion)
                        ordinal Elaboration.FormationProofAssumption) active) context (zip [1..] facts)
                combine (left,a) (right,b) = (CAnd left right,SourceEvidence.SourceAnd a b)
                balance [value] = value
                balance values = let (left,right) = splitAt (length values `div` 2) values
                    in combine (balance left) (balance right)
                parts = [(scopedCoreTerm (Notion.sourceAssertionFormula fact),SourceEvidence.SourceAtom fact)
                    | ordinal <- [0..width-1], let fact = describe [TySet,TySet] ordinal]
                (body,description) = if skewed then foldr1 combine parts else balance parts
                target = checked [TySet] (CExists TySet body)
                evidence = SourceEvidence.SourceExists description
            result <- expectRight =<< runModuleDriver foundation preludeModuleName [] unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    queried <- Elaboration.prepareProofNotionGoalWithBudget
                        (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits)
                        supplied Nowhere target evidence
                    case queried of
                        Right (Elaboration.NotionQueryFound proof,budget,_) -> do
                            closure <- Declaration.checkedObjectClosureLowering
                            replayed <- Declaration.replayTransientFormationLowering closure proof target
                            either (error . show) (const (pure (Notion.formationInferenceWorkUsed budget))) replayed
                        Left failure -> error ("compound query failed at width " <> show width <> ": " <> show failure)
                        Right _ -> error ("compound query unavailable at width " <> show width))
            case result of
                Declaration.DriverSucceeded work _ _ -> pure work
                _ -> assertFailure "compound query driver failed" >> pure 0
        case costs of
            [small,medium,large] -> assertBool ("compound query costs: " <> show (skewed,costs))
                (small < medium && medium < large && large < 4 * medium)
            _ -> assertFailure "missing compound query samples"

finiteQueriesAgree :: Assertion
finiteQueriesAgree = do
    foundation <- expectRight Foundation.checkedFoundation
    outer <- extendBinder 0 "b" Elaboration.emptyElaborationContext
    context <- extendBinder 1 "a" outer
    let a = Semantic.TemplateVariable (Reference.OpaqueSeed 0)
        b = Semantic.TemplateVariable (Reference.OpaqueSeed 1)
        x = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        bound = Semantic.TemplateVariable Nothing
        pair value = Semantic.TemplateOrderedPair value value
        constant n = Semantic.TemplateClosed (fromMaybe (error "closed reference constant")
            (Semantic.closedSetValue (checked [] (COpaqueInteger n))))
        predicate n value = Reference.FiniteAtom (Semantic.MembershipAtomTemplate value (constant n))
        base = [a,b,constant 0,constant 1,constant 2]
        exists = Reference.FiniteExists
        joined = exists (Reference.FiniteAnd (Reference.FiniteOr (predicate 0 bound) (predicate 1 bound)) (predicate 2 bound))
        nested = exists (Reference.FiniteAnd (predicate 0 bound)
            (exists (Reference.FiniteEquality bound (pair (Semantic.TemplateVariable (Just Nothing))))))
        opaqueWitness = exists (Reference.FiniteImplies (predicate 0 bound) (predicate 1 bound))
        seedValue (Reference.OpaqueSeed value) = CBound value
        formal (Semantic.ViewVariableIx value) = CBound value
        run label inputs templates equalities rules facts goals queryInputs = do
            universe <- expectRight (fst (Reference.enumerateSupport 1000000 (Set.fromList inputs) (Set.fromList templates)))
            expected <- expectRight (fst (Reference.runReference 1000000
                (Reference.evaluateFiniteQueries (Set.toList (Reference.referenceUniverse universe)) equalities rules facts goals)))
            let source ordinal (formula,evidence) active = admitFormationSource
                    (Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport context)
                        formula evidence ordinal Elaboration.FormationProofAssumption) active
                initialInputs = [SourceEvidence.SourceInput [] (fmap seedValue term) | term <- inputs]
                withFacts = foldl' (\active (ordinal,fact) -> source ordinal (describe True [TySet,TySet] seedValue fact) active)
                    context (zip [1..] facts)
                withRules = foldl' (\active (ordinal,Reference.FiniteClause arity premises conclusion) ->
                    let body = foldr Reference.FiniteImplies conclusion premises
                        (formula,evidence) = describe True (replicate (fromIntegral arity) TySet <> [TySet,TySet]) formal body
                        quantified = iterate (CForall TySet) (scopedCoreTerm formula) !! fromIntegral arity
                        description = iterate SourceEvidence.SourceBind evidence !! fromIntegral arity
                    in source ordinal (checked [TySet,TySet] quantified,description) active)
                    withFacts (zip [100..] rules)
                withEqualities = foldl' (\active (ordinal,(left,right)) ->
                    let leftCore = denote seedValue left
                        rightCore = denote seedValue right
                        equality = checked [TySet,TySet] (CEq TySet leftCore rightCore)
                        occurrence = Notion.setSourceEqualityOccurrence (rich [TySet,TySet] leftCore)
                            (rich [TySet,TySet] rightCore) equality Notion.ConjunctionHere Nowhere
                    in admitFormationEqualitySource (Elaboration.formationEqualitySource
                        (Elaboration.elaborationContextSupport context) equality (occurrence :| [])
                        ordinal Elaboration.FormationProofAssumption) active)
                    withRules (zip [200..] equalities)
            actual <- for goals \goal -> do
                let (formula,evidence) = describe queryInputs [TySet,TySet] seedValue goal
                result <- expectRight =<< runModuleDriver foundation preludeModuleName [] unusedResolver AlwaysMissValidation
                    (Declaration.runProspectiveLoweringDriver do
                        queried <- Elaboration.prepareProofNotionEvidence withEqualities Nowhere formula
                            (SourceEvidence.SourceWithInputs initialInputs evidence)
                        case queried of
                            Left failure -> error ("finite query failed: " <> show failure)
                            Right (Elaboration.NotionQueryUnavailable{},_) -> pure False
                            Right (Elaboration.NotionQueryUnsupported,_) -> error "finite query was unsupported"
                            Right (Elaboration.NotionQueryFound proof,_) -> do
                                closure <- Declaration.checkedObjectClosureLowering
                                replayed <- Declaration.replayTransientFormationLowering closure proof formula
                                either (error . show) (const (pure True)) replayed)
                case result of
                    Declaration.DriverSucceeded answer _ _ -> pure answer
                    _ -> assertFailure (label <> " driver failed") >> fail "unreachable"
            assertEqual label expected actual
    run "a later union row can satisfy the join" base [] [] []
        [predicate 0 a,predicate 1 b,predicate 2 b] [joined] True
    run "an unknown disjunct remains exact evidence" base [] [] []
        [Reference.FiniteOr (predicate 0 a) (predicate 1 a),predicate 2 a] [joined,predicate 0 a] True
    run "a union without a join partner completes its miss" base [] [] []
        [predicate 0 a] [joined] True
    run "query templates open nested witnesses" base [pair x] [] [] [predicate 0 a] [nested] True
    run "complete empty operand metadata cannot restore a template" base [] [] [] [predicate 0 a] [nested] False
    run "positive premises discover parameters" base [] []
        [Reference.FiniteClause 1 [Reference.FiniteOr (predicate 0 x) (predicate 1 x)] (predicate 2 x)]
        [predicate 0 a,predicate 1 b] [predicate 2 a,predicate 2 b] True
    run "concrete assignments survive class lookup" (base <> [pair b]) [pair x] [(a,b)]
        [Reference.FiniteClause 1 [predicate 0 x] (predicate 2 (pair x))]
        [predicate 0 a] [predicate 2 (pair b)] True
    run "complete arguments do not grant congruence" (base <> [pair a,pair b]) [] [(a,b)] []
        [predicate 0 (pair a)] [predicate 0 (pair b)] True
    for_ [[(a,b),(constant 0,constant 1)],[(constant 1,constant 0),(b,a)]] \equations ->
        for_ [[predicate 0 a,predicate 2 b],[predicate 2 b,predicate 0 a]] \facts ->
            run "both argument classes preserve exact answers under source and equation order" base [] equations []
                facts [predicate 1 b,predicate 2 a] True
    run "derived equations remain guards rather than class edges" base [] []
        [Reference.FiniteClause 2 [predicate 0 x,predicate 1 (Semantic.TemplateVariable (Semantic.ViewVariableIx 1))]
            (Reference.FiniteEquality x (Semantic.TemplateVariable (Semantic.ViewVariableIx 1)))]
        [predicate 0 a,predicate 1 b] [Reference.FiniteEquality a b,predicate 0 b] True
    run "non-positive existential evidence stays whole" base [] [] [] [opaqueWitness]
        [opaqueWitness,predicate 0 a] True
    run "iff elimination remains guarded" base [] [] []
        [Reference.FiniteIff (predicate 0 a) (predicate 1 a)] [predicate 1 a] True
    run "vacuous binders require an admitted term" [] [] [] [] [] [exists Reference.FiniteTruth] True
    run "explicit initial inputs supply a vacuous witness" [a] [] [] [] [] [exists Reference.FiniteTruth] True
  where
    denote variable = \case
        Semantic.TemplateVariable value -> variable value
        Semantic.TemplateClosed value -> Semantic.closedSetValueTerm value
        Semantic.TemplateOrderedPair a b -> CApp (CApp (CIntrinsic OrderedPair) (denote variable a)) (denote variable b)
        Semantic.TemplateProvider{} -> error "unexpected provider in the finite query fixture"
    rich types term = case term of
        CApp (CApp (CIntrinsic OrderedPair) a) b -> fromMaybe (error "ill-typed reference pair")
            (SourceTerm.sourceOrderedPairTermOccurrence (rich types a) (rich types b)
                (checked types term) (Elaboration.LocatedSourceTerm Nowhere))
        _ -> sourceTerm types term
    describe :: Bool -> [CoreType] -> (variable -> CanonicalTerm ObjectId) -> Reference.FiniteFormula variable
        -> (ScopedCheckedCore ObjectId,SourceEvidence.SourceEvidence Semantic.SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence)
    describe retainInputs types variable formula = case formula of
        Reference.FiniteAtom atom ->
            let terms = denote variable <$> atom
                proposition = checked types (atomCore terms)
                assertion = Notion.sourceNotionAssertionFromTemplate (rich types <$> terms) proposition Notion.ConjunctionHere Nowhere
            in (proposition,SourceEvidence.SourceAtom assertion)
        Reference.FiniteTruth -> (checked types CTruth,SourceEvidence.SourceResidual Nothing)
        Reference.FiniteEquality a b ->
            (checked types (CEq TySet (denote variable a) (denote variable b)),
                SourceEvidence.SourceInputs Nothing
                    [SourceEvidence.SourceInput [] (fmap variable term) | retainInputs, term <- [a,b]])
        Reference.FiniteAnd a b -> binary CAnd SourceEvidence.SourceAnd a b
        Reference.FiniteOr a b -> binary COr SourceEvidence.SourceOr a b
        Reference.FiniteImplies a b -> binary CImp SourceEvidence.SourceRequire a b
        Reference.FiniteIff a b -> binary (CEq TyProp) SourceEvidence.SourceIff a b
        Reference.FiniteExists body -> binder CExists SourceEvidence.SourceExists body
        Reference.FiniteForall body -> binder CForall SourceEvidence.SourceBind body
        Reference.FiniteOpaque{} -> error "unexpected opaque proposition in the finite query fixture"
      where
        binary constructor evidence a b =
            let (left,leftEvidence) = describe retainInputs types variable a
                (right,rightEvidence) = describe retainInputs types variable b
            in (checked types (constructor (scopedCoreTerm left) (scopedCoreTerm right)),evidence leftEvidence rightEvidence)
        binder constructor evidence body =
            let under = \case Nothing -> CBound 0; Just outer -> shiftCanonical 1 0 (variable outer)
                (nested,description) = describe retainInputs (TySet:types) under body
            in (checked types (constructor TySet (scopedCoreTerm nested)),evidence description)
    atomCore = \case
        Semantic.MembershipAtomTemplate a b -> CApp (CApp (CIntrinsic Member) a) b
        Semantic.NegativeAtomTemplate body -> CNot (atomCore body)
        _ -> error "unexpected predicate in the finite query fixture"

replaysWholeFormation :: Assertion
replaysWholeFormation = do
    foundation <- expectRight Foundation.checkedFoundation
    outer <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    initial <- extendBinder 1 "x" outer
    let residual = SourceEvidence.SourceResidual Nothing
        equality = CEq TySet (CBound 0) (CBound 1)
        formulas = [CNot membershipFormula, equality,
            COr membershipFormula equality,
            -- A non-positive witness body keeps only its exact-evidence route.
            CExists TySet (CImp (CEq TySet (CBound 0) (CBound 1)) CFalsum),
            CForall TySet (CEq TySet (CBound 0) (CBound 1)),
            CImp equality membershipFormula]
        supply formula evidence = admitFormationSource
            (Elaboration.formationEvidenceSource (Elaboration.elaborationContextSupport initial)
                (checked [TySet, TySet] formula) evidence 42 Elaboration.FormationProofAssumption)
            initial
        query context goal evidence = do
            driven <- expectRight =<< runModuleDriver foundation preludeModuleName []
                unusedResolver AlwaysMissValidation
                (Declaration.runProspectiveLoweringDriver do
                    result <- Elaboration.prepareProofNotionEvidence context Nowhere goal evidence
                    closure <- Declaration.checkedObjectClosureLowering
                    for result \(outcome, _) -> case outcome of
                        Elaboration.NotionQueryFound proof -> do
                            replayed <- Declaration.replayTransientFormationLowering closure proof goal
                            pure (Just (proof, replayed))
                        Elaboration.NotionQueryUnavailable{} -> pure Nothing
                        Elaboration.NotionQueryUnsupported -> pure Nothing)
            case driven of
                Declaration.DriverSucceeded result _ _ -> expectRight result
                _ -> assertFailure "whole notion query failed to run" >> fail "unreachable"
        succeeds result = case result of
            Just (proof, replayed) -> do
                void (expectRight replayed)
                assertEqual "one checked local supplies the selected projection" 1
                    (Vector.length (Notion.materializedFormationHypotheses proof))
            Nothing -> assertFailure "an exact whole notion source failed"
        misses result = assertBool "no whole evidence may be invented" (isNothing result)
    for_ formulas \formula -> do
        let goal = checked [TySet, TySet] formula
            active = supply formula residual
        succeeds =<< query active goal residual
        nested <- extendBinder 2 "unused" active
        succeeds =<< query nested (weakenCheckedScopedCore TySet goal) residual
        misses =<< query initial goal residual
        misses =<< query active (checked [TySet, TySet] (CNot formula)) residual
    let compound = CAnd membershipFormula (CAnd CTruth (CNot equality))
        evidence = SourceEvidence.SourceAnd (SourceEvidence.SourceAtom (membershipAssertion Notion.ConjunctionHere))
            (SourceEvidence.SourceAnd residual residual)
        active = supply compound evidence
    succeeds =<< query active (checked [TySet, TySet] compound) evidence
    succeeds =<< query active (checked [TySet, TySet] (CNot equality)) residual
    query initial (checked [TySet, TySet] CTruth) residual >>= \case
        Just (proof,replayed) -> do
            void (expectRight replayed)
            assertBool "truth introduction needs no local hypothesis"
                (Vector.null (Notion.materializedFormationHypotheses proof))
        Nothing -> assertFailure "truth introduction was unavailable"

    -- Iff contributes no supplied-universal posting, and this scope has no
    -- catalogue yet: producer publication is the last nonzero debit.
    let member left right = CApp (CApp (CIntrinsic Member) left) right
        atom left right = SourceEvidence.SourceAtom (Notion.membershipSourceNotionAssertion
            (sourceTerm [TySet,TySet] left) (sourceTerm [TySet,TySet] right)
            (checked [TySet,TySet] (member left right)) Notion.ConjunctionHere Nowhere)
        x = CBound 0
        a = CBound 1
        p = member x a
        q = member a x
        r = member x x
        source ordinal formula description = Elaboration.formationEvidenceSource
            (Elaboration.elaborationContextSupport initial) (checked [TySet,TySet] formula)
            description ordinal Elaboration.FormationProofAssumption
        mixed = source 43 (CEq TyProp (CAnd p q) r)
            (SourceEvidence.SourceIff (SourceEvidence.SourceAnd (atom x a) (atom a x)) (atom x x))
        projectionOnly = source 43 (CEq TyProp p r) (SourceEvidence.SourceIff (atom x a) (atom x x))
        count operation = Map.findWithDefault 0 operation . Diagnostics.operationCounts . Diagnostics.measuredDiagnostics
        used = sum . Diagnostics.phaseInspections . Diagnostics.measuredDiagnostics
    for_ [(mixed,4),(projectionOnly,2)] \(selected,producers) -> do
        -- (P & Q) iff R yields P & Q -> R, R -> P, R -> Q and
        -- P,Q -> P & Q. P iff R has just its two projections.
        let action = Elaboration.prepareFormationPremiseSource selected initial
            (result,measured) = Elaboration.runFormationScopePreparation action
            work = used measured
            publication = 1 + producers
            run allowance = Elaboration.runFormationScopePreparationWithWork (fromIntegral allowance) action
        prepared <- expectRight result
        assertEqual "every compiled projection and introduction is counted" producers
            (count Diagnostics.ProducerCompilation measured)
        let (exact,exactWork) = run work
            (short,shortWork) = run (work-1)
        void (expectRight exact)
        used exactWork @?= work
        assertEqual "compilation completes before publication refuses its debit"
            (Diagnostics.operationCounts (Diagnostics.measuredDiagnostics measured))
            (Diagnostics.operationCounts (Diagnostics.measuredDiagnostics shortWork))
        assertEqual "publication refusal retains all compiler work"
            (Diagnostics.coreInspections (Diagnostics.measuredDiagnostics measured))
            (Diagnostics.coreInspections (Diagnostics.measuredDiagnostics shortWork))
        used shortWork @?= work - publication
        Map.lookup "scope-preparation.rejected" (Diagnostics.limitHighWater shortWork) @?= Just publication
        Map.lookup "scope-preparation.cap" (Diagnostics.limitHighWater shortWork) @?= Just (work-1)
        case short of
            Left (Elaboration.FormationScopePreparationLimitExceeded cap) -> cap @?= work-1
            _ -> assertFailure "one-short publication returned a partial scope"
        -- The ordinary, unmeasured entry point uses the same preparation.
        unmeasured <- expectRight (Elaboration.addFormationPremiseSource selected initial)
        for_ [prepared,unmeasured] \context -> do
            let withPremise = admitFormationSource (source 44 r (atom x x)) context
            result <- query withPremise (checked [TySet,TySet] p) (atom x a)
            case result of
                Just (_,replayed) -> void (expectRight replayed)
                Nothing -> assertFailure "prepared scoped projection failed to replay"

membershipFormula :: CanonicalTerm ObjectId
membershipFormula = CApp (CApp (CIntrinsic Member) (CBound 0)) (CBound 1)

membershipAssertion :: Notion.ConjunctionPath -> Elaboration.ScopedSourceNotionOccurrence
membershipAssertion path = Notion.membershipSourceNotionAssertion
    (sourceTerm [TySet,TySet] (CBound 0)) (sourceTerm [TySet,TySet] (CBound 1))
    (checked [TySet,TySet] membershipFormula) path Nowhere

membershipSource :: Elaboration.ElaborationContext -> Notion.ConjunctionPath -> Elaboration.FormationPremiseSource
membershipSource context path = Elaboration.formationEvidenceSource
    (Elaboration.elaborationContextSupport context) (checked [TySet,TySet] membershipFormula)
    (SourceEvidence.SourceAtom (membershipAssertion path)) 42 Elaboration.FormationProofDerivedClaim

admitFormationSource
    :: Elaboration.FormationPremiseSource -> Elaboration.ElaborationContext
    -> Elaboration.ElaborationContext
admitFormationSource source context = either (error . show) id
    (Elaboration.addFormationPremiseSource source context)

admitFormationEqualitySource
    :: Elaboration.FormationEqualitySource -> Elaboration.ElaborationContext
    -> Elaboration.ElaborationContext
admitFormationEqualitySource source context = either (error . show) id
    (Elaboration.addFormationEqualitySource source context)

observedMembership :: Elaboration.ElaborationContext -> Elaboration.ElaborationContext
observedMembership context = admitFormationSource
    (membershipSource context Notion.ConjunctionHere) context

internsWholeFormulas :: Assertion
internsWholeFormulas = do
    let context = [TySet]
        member x set = CApp (CApp (CIntrinsic Member) x) set
        formulas =
            [ CNot (member (CBound 0) (CIntrinsic Empty))
            , CExists TySet (member (CBound 0) (CBound 1))
            , CForall TySet (CEq TySet (CBound 0) (CBound 1))
            , COr CTruth CFalsum
            , CEq TyProp (member (CBound 0) (CIntrinsic Empty)) CTruth
            , CForall (TyArrow TySet TyProp) (CApp (CBound 0) (CBound 1))
            , CEq TySet (CBound 0) (CBound 0)
            , CEq TySet (CApp (CLam TySet (CBound 0)) (CBound 0)) (CBound 0)
            ]
        intern term table = fst (Formulas.internFormula 100000 (checked context term) table)
    for_ [id, const 0] \bucket -> do
        (identifiers, table) <- foldM (\(ids, previous) term -> do
            (identifier, next) <- expectRight (intern term previous)
            pure (ids <> [identifier], next)) ([], Formulas.emptyFormulasWithHash bucket context) formulas
        assertEqual "collisions and convertible syntax remain distinct" (length formulas) (Set.size (Set.fromList identifiers))
        prepared <- foldM (\previous (identifier, term) -> do
            (again, _) <- expectRight (intern term previous)
            identifier @?= again
            let (initialShape, firstRemaining) = Formulas.prepareFormulaShape 100000 identifier previous
            (shape, next) <- expectRight initialShape
            let (cachedShape, cachedRemaining) = Formulas.prepareFormulaShape 100000 identifier next
            (againShape, _) <- expectRight cachedShape
            shape @?= againShape
            assertBool "shape preparation is charged once" (cachedRemaining > firstRemaining)
            instantiated <- expectRight (fst (countedInstantiateCanonicalPrefix 100000
                (Vector.singleton (CApp (CIntrinsic PowerSet) (CIntrinsic Empty))) term))
            instantiatedShape <- Formulas.residualShape (pure ()) [] instantiated
            assertEqual "outer set substitution preserves the producer shape" shape (Just instantiatedShape)
            pure next) table (zip identifiers formulas)
        extended <- expectRight (fst (Formulas.extendFormulas 100000 [TySet,TySet] prepared))
        for_ (zip identifiers formulas) \(identifier, term) -> do
            let weakened = checked [TySet,TySet] (shiftCanonical 1 0 term)
            (again, _) <- expectRight (fst (Formulas.internFormula 100000 weakened extended))
            identifier @?= again
            aligned <- expectRight (fst (Formulas.lookupFormula 100000 identifier extended))
            aligned @?= Just weakened
            (originalShape, _) <- expectRight (fst (Formulas.prepareFormulaShape 100000 identifier prepared))
            (extendedShape, _) <- expectRight (fst (Formulas.prepareFormulaShape 100000 identifier extended))
            assertEqual "scope extension retains the prepared producer shape" originalShape extendedShape
        case fst (Formulas.internFormula 100000 (checked context (CBound 0)) table) of
            Left Formulas.FormulaNotProposition -> pure ()
            _ -> assertFailure "whole identity admitted a set-valued term"
    for_ [id,const 0] \bucket -> for_ [8,32,128] \width -> do
        let source = checked [TySet,TySet] (foldr1 CAnd
                [member (CBound 0) (COpaqueInteger ordinal) | ordinal <- [1..width]])
            value = checked context (CBound 0)
            irrelevant = checked context (COpaqueInteger 999)
        (leaf,leaves) <- expectRight (fst (Leaves.internOpaqueLeaf 100000 value (Leaves.emptyOpaqueLeaves context)))
        (other,_) <- expectRight (fst (Leaves.internOpaqueLeaf 100000 irrelevant leaves))
        (node,prepared) <- expectRight (fst (Formulas.prepareFormulaTemplate 10000000 1 source
            (Formulas.emptyFormulasWithHash bucket context)))
        let bindings = Map.singleton 0 (leaf,value)
            (result,remaining) = Formulas.instantiateFormulaTemplate 10000000 node bindings prepared
        (identifier,instantiated) <- expectRight result
        let (repeated,reusedRemaining) = Formulas.instantiateFormulaTemplate 10000000 node
                (Map.insert 1 (other,irrelevant) bindings) instantiated
        (again,_) <- expectRight repeated
        identifier @?= again
        assertBool "repeated compound instances use only their relevant input key"
            (10000000-reusedRemaining < 100 && reusedRemaining > remaining)
        let target = checked context (foldr1 CAnd
                [member (CBound 0) (COpaqueInteger ordinal) | ordinal <- [1..width]])
        (supplied,_) <- expectRight (fst (Formulas.internFormula 10000000 target instantiated))
        assertEqual "instantiated and supplied compounds meet at the exact index" identifier supplied
        actual <- expectRight (fst (Formulas.lookupFormula 100000 identifier instantiated))
        actual @?= Just target
    let initial = Formulas.emptyFormulas context
        formula = checked context (CExists TySet (member (CBound 0) (CBound 1)))
        (measured, remaining) = Formulas.internFormula 100000 formula initial
        used = 100000 - remaining
    (expected, _) <- expectRight measured
    (exact, _) <- expectRight (fst (Formulas.internFormula used formula initial))
    exact @?= expected
    case fst (Formulas.internFormula (used - 1) formula initial) of
        Left Formulas.FormulaWorkExhausted{} -> pure ()
        _ -> assertFailure "one-short formula preparation published an identity"

internsOpaqueLeaves :: Assertion
internsOpaqueLeaves = do
    let context = [TySet]
        terms = [CBound 0, CIntrinsic Empty, CApp (CIntrinsic PowerSet) (CBound 0),
            CApp (CLam TySet (CBound 0)) (CBound 0),
            CApp (CLam TySet (CBound 1)) (CBound 0)] <> [COpaqueInteger index | index <- [1..64]]
        run term table = Leaves.internOpaqueLeaf 100000 (checked context term) table
    for_ [terms, reverse terms] \ordered -> do
        (identifiers, table) <- foldM (\(ids, table) term -> do
            let (result, remaining) = run term table
                used = 100000 - remaining
            (identifier, next) <- expectRight result
            (same, _) <- expectRight (fst (Leaves.internOpaqueLeaf used (checked context term) table))
            assertEqual "exact allowance preserves the leaf key" identifier same
            case fst (Leaves.internOpaqueLeaf (used - 1) (checked context term) table) of
                Left Leaves.OpaqueLeafWorkExhausted -> pure ()
                _ -> assertFailure "one-short opaque insertion returned an index"
            pure (ids <> [identifier], next)) ([], Leaves.emptyOpaqueLeaves context) ordered
        assertEqual "different syntax keeps distinct opaque keys" (length terms) (Set.size (Set.fromList identifiers))
        for_ (zip ordered identifiers) \(term, identifier) -> do
            (again, _) <- expectRight (fst (run term table))
            assertEqual "repeated syntax keeps its key" identifier again
            assertEqual "the original scoped term is retained" (Just (checked context term)) (Leaves.lookupOpaqueLeaf identifier table)
        case fst (Leaves.internOpaqueLeaf 100000 (checked [] (CIntrinsic Empty)) table) of
            Left Leaves.OpaqueLeafScopeMismatch -> pure ()
            _ -> assertFailure "opaque leaf crossed its binder context"
        case fst (Leaves.internOpaqueLeaf 100000 (checked context CTruth) table) of
            Left Leaves.OpaqueLeafNotSet -> pure ()
            _ -> assertFailure "opaque leaf admitted a proposition"
        let extendedContext = TySet : context
        extended <- expectRight (fst (Leaves.extendOpaqueLeaves 100000 extendedContext table))
        for_ (zip ordered identifiers) \(term, identifier) -> do
            let weakened = checked extendedContext (shiftCanonical 1 0 term)
            (again, _) <- expectRight (fst (Leaves.internOpaqueLeaf 100000 weakened extended))
            assertEqual "scope extension preserves level keys beneath internal binders" identifier again
            aligned <- expectRight (fst (Leaves.countedLookupOpaqueLeaf 100000 identifier extended))
            assertEqual "selected leaves align to the extended context" (Just weakened) aligned
        (fresh, _) <- expectRight (fst (Leaves.internOpaqueLeaf 100000
            (checked extendedContext (CBound 0)) extended))
        assertBool "a fresh binder is distinct from all older levels" (fresh `notElem` identifiers)

encodesScopedSourceTemplates :: Assertion
encodesScopedSourceTemplates = do
    let context = [TySet,TySet]
        leaf = sourceTerm context (CBound 0)
        providerCore = CApp (CIntrinsic PowerSet) (CBound 0)
        opaqueCore = CApp (CLogicalSelect TySet) (CLam TySet (CEq TySet (CBound 0) (CBound 2)))
        charge = Reference.chargeReferenceWork . fromIntegral
        equalContexts left right = Reference.countedReferenceOperation (\allowance ->
            let (result,remaining) = countedCoreTypeListIdentity allowance left right
            in (case result of
                Left CountedCoreStructuralWorkExhausted -> Left Reference.ReferenceWorkExhausted
                Right same -> Right same,remaining))
        encode allowance current term = Reference.runReference allowance do
            let intern core = do
                    table <- State.get
                    (identifier, next) <- lift (Reference.countedReferenceOperation (\available ->
                        let (result, remaining) = Leaves.internOpaqueLeaf available core table
                        in (case result of
                            Left Leaves.OpaqueLeafWorkExhausted -> Left Reference.ReferenceWorkExhausted
                            Left failure -> Left (Reference.ReferenceInvalidInput (Text.pack (show failure)))
                            Right value -> Right value, remaining)))
                    State.put next
                    pure identifier
            (result, table) <- State.runStateT
                (SourceTerm.encodeScopedSourceTemplate (lift . charge)
                    (\left right -> lift (equalContexts left right)) current intern term)
                (Leaves.emptyOpaqueLeaves current)
            pure (fmap (fmap (scopedCoreTerm . fromMaybe (error "missing encoded opaque leaf")
                . (`Leaves.lookupOpaqueLeaf` table))) result)
    let assertion formula = Notion.membershipSourceNotionAssertion leaf leaf formula Notion.ConjunctionHere Nowhere
        wrongScope = assertion (checked [TySet] CTruth)
    case fst (SourceRows.encodeSourceRow 10000 context wrongScope (Leaves.emptyOpaqueLeaves context)) of
        Left (CountedCoreOperationFailed SourceTerm.SourceTemplateScopeMismatch) -> pure ()
        _ -> assertFailure "row encoding ignored the enclosing formula scope"
    written <- maybe (assertFailure "invalid provider fixture" >> fail "invalid fixture") pure
        (SourceTerm.sourceIntrinsicProviderTermOccurrence Semantic.PowerSetProvider
            (Vector.singleton (SourceTerm.forgetScopedSourceTermOccurrence leaf))
            (Elaboration.LocatedSourceTerm Nowhere))
    sealed <- expectRight (SourceTerm.sealCanonicalSourceTermOccurrence
        (SourceTerm.SourceTermCheckingContext testGlobalType context) written)
    let pairCore = CApp (CApp (CIntrinsic OrderedPair) providerCore) (CBound 0)
        pair right = maybe (assertFailure "invalid pair fixture" >> fail "invalid fixture") pure
            (SourceTerm.sourceOrderedPairTermOccurrence sealed right (checked context pairCore)
                (Elaboration.LocatedSourceTerm Nowhere))
    paired <- pair leaf
    wrongChild <- pair (sourceTerm [TySet] (CBound 0))
    forM_ [(paired,Semantic.TemplateOrderedPair
                    (Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
                        (Vector.singleton (Semantic.TemplateVariable (CBound 0)))) (Semantic.TemplateVariable (CBound 0))),
            (sealed,Semantic.TemplateProvider (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
                    (Vector.singleton (Semantic.TemplateVariable (CBound 0)))),
            (sourceTerm context providerCore,Semantic.TemplateVariable providerCore),
            (sourceTerm context opaqueCore,Semantic.TemplateVariable opaqueCore)] \(input,expected) -> do
        let (outcome,used) = encode 10000 context input
        assertEqual "only retained written structure is decomposed" (Right (Right expected)) outcome
        assertEqual "source encoding shares exact accounting" (outcome,used) (encode used context input)
        assertEqual "one-short source encoding exhausts" (Left Reference.ReferenceWorkExhausted)
            (fst (encode (used - 1) context input))
    assertEqual "a different binder context is rejected" (Right (Left SourceTerm.SourceTemplateScopeMismatch))
        (fst (encode 10000 [TySet] leaf))
    assertEqual "nested source arguments must share the same context" (Right (Left SourceTerm.SourceTemplateScopeMismatch))
        (fst (encode 10000 context wrongChild))
    let nonSet = SourceTerm.sourceTermOccurrence (checked context (CLam TySet (CBound 0))) TySet
            (Elaboration.LocatedSourceTerm Nowhere)
    assertEqual "declared set metadata cannot override the checked type" (Right (Left SourceTerm.SourceTemplateNotSet))
        (fst (encode 10000 context nonSet))

scopesReferenceInputs :: Assertion
scopesReferenceInputs = do
    outer <- extendBinder 0 "A" Elaboration.emptyElaborationContext
    context <- extendBinder 1 "x" outer
    let target = membershipAssertion Notion.ConjunctionHere
        prepare = ReferenceScope.scopedReferenceInputs Notion.defaultFormationSearchLimits
            Elaboration.ProofNotionQuery
    (inputs, _) <- expectRight (prepare (observedMembership context) target)
    assertEqual "the snapshot retains exactly the two scoped set leaves" 2
        (Map.size (ReferenceScope.scopedReferenceLeaves inputs))
    let evaluate scope = expectRight (fst (Reference.evaluateFormation 10000 Map.empty
            (ReferenceScope.scopedReferenceFacts scope) (ReferenceScope.scopedReferenceAliases scope) (ReferenceScope.scopedReferenceGoal scope)))
    (_, direct) <- evaluate inputs
    assertBool "an admitted scoped observation supplies the direct answer"
        (any ((== ReferenceScope.scopedReferenceGoal inputs) . fst) (Map.keys (Reference.referenceAnswers direct)))
    (syntaxOnly, _) <- expectRight (prepare context target)
    (_, absent) <- evaluate syntaxOnly
    assertEqual "goal syntax alone is not evidence" 0 (Map.size (Reference.referenceAnswers absent))
    let opaque = CApp (CLogicalSelect TySet) (CLam TySet (CEq TySet (CBound 0) (CBound 2)))
        opaqueTarget = Notion.membershipSourceNotionAssertion
            (sourceTerm [TySet,TySet] opaque) (sourceTerm [TySet,TySet] (CBound 1))
            (checked [TySet,TySet] (CApp (CApp (CIntrinsic Member) opaque) (CBound 1)))
            Notion.ConjunctionHere Nowhere
    (withOpaque, _) <- expectRight (prepare context opaqueTarget)
    assertEqual "the binder-containing term remains a whole opaque seed"
        (Set.fromList [opaque, CBound 1])
        (Set.fromList (scopedCoreTerm <$> Map.elems (ReferenceScope.scopedReferenceLeaves withOpaque)))
    assertEqual "leaf IDs retain canonical Core order rather than source traversal order"
        [(Reference.OpaqueSeed 0, CBound 1), (Reference.OpaqueSeed 1, opaque)]
        [(seed, scopedCoreTerm core) | (seed, core) <- Map.toAscList (ReferenceScope.scopedReferenceLeaves withOpaque)]
    case prepare outer target of
        Left Elaboration.FormationObservationScopeError{} -> pure ()
        _ -> assertFailure "reference input retained a dangling outer-scope index"
