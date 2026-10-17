{-# LANGUAGE NoImplicitPrelude #-}

-- Opaque leaves are scoped checked terms. Only the source occurrence's retained
-- provider/pair syntax is decomposed; Core syntax under a binder is never mined
-- for additional seeds or used to invent a written provider association.
module Felix.Test.Support.FormationReferenceScope
    ( ScopedReferenceInputs(..)
    , ScopedReferenceView(..)
    , scopedReferenceInputs
    , prepareScopedReferenceInputs
    , prepareObservedReferenceInputs
    , productionScopedRows
    ) where

import Base
import Control.Monad (foldM, unless)
import Control.Monad.State.Strict qualified as State
import Data.Bifunctor (first)
import Data.Word (Word)
import Data.Text qualified as Text
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Felix.Checking.Core qualified as Core
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.LeafIndex qualified as Leaves
import Felix.Checking.Notion.SourceRows qualified as SourceRows
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Test.Support.FormationReference qualified as Reference
import Felix.Test.Support.FormationReferenceImports qualified as Imports

-- Keeping observations alongside rows preserves the enclosing source and its
-- projection recipe. A consumer must still resolve every origin to actual
-- authorized premises before turning a reference witness into a proof.
data ScopedReferenceInputs = ScopedReferenceInputs
    { scopedReferenceGoal :: !Reference.GroundAtom
    , scopedReferenceFacts :: ![Reference.ReferenceFact Elaboration.FormationSourceOrigin]
    , scopedReferenceLeaves :: !(Map Reference.OpaqueSeed (Core.ScopedCheckedCore ObjectId))
    , scopedReferenceObservations :: ![(Elaboration.FormationObservation, ScopedReferenceView)]
    , scopedReferenceTarget :: !ScopedReferenceView
    , scopedReferenceAliases :: !(Set Reference.GroundTerm)
    , scopedReferenceAliasDefinitions :: ![Notion.MaterializedNotionHypothesis Elaboration.FormationSourceOrigin]
    }

-- The normalized row is paired with its original checked formula and exact
-- transport steps. Source dependencies additionally cover erased arguments.
data ScopedReferenceView = ScopedReferenceView
    { scopedViewAssertion :: !Elaboration.ScopedSourceNotionOccurrence
    , scopedViewNormalization :: !Elaboration.FormationAliasNormalization
    , scopedViewDefinitions :: ![Notion.MaterializedNotionHypothesis Elaboration.FormationSourceOrigin]
    }

scopedReferenceInputs
    :: Notion.FormationSearchLimits
    -> Elaboration.NotionQueryConsumer
    -> Elaboration.ElaborationContext
    -> Elaboration.ScopedSourceNotionOccurrence
    -> Either Elaboration.FormationObservationError
        (ScopedReferenceInputs, Notion.FormationSearchStatistics)
scopedReferenceInputs limits consumer context target = do
    (observations, statistics) <- Elaboration.formationObservationsFor limits consumer context
    let aliases = Elaboration.formationAliasesFor consumer (Elaboration.alignFormationAliases context)
        aliasResult = first (Elaboration.FormationObservationScopeError . Text.pack . show)
        normalize = normalizeScopedView (pure ())
            (aliasResult . Elaboration.normalizeFormationAliases aliases)
            (aliasResult . Elaboration.viewFormationAliases aliases)
        check condition message = unless condition (Left (Elaboration.FormationObservationScopeError message))
    inputs <- assembleScopedInputs (pure ()) check (\left right -> pure (left == right))
        (\left right -> pure (compare left right)) normalize (pure . Set.fromList)
        (snd <$> toList (Elaboration.elaborationContextSupport context)) aliases observations target
    pure (inputs, statistics)

-- Normalization and source-tree traversal join the evaluator's work account.
-- Support-container operations and inventory preparation are still outside
-- this accounting; this is not yet an end-to-end bounded request adapter.
prepareScopedReferenceInputs
    :: Notion.FormationSearchLimits
    -> Elaboration.NotionQueryConsumer
    -> Elaboration.ElaborationContext
    -> Elaboration.ScopedSourceNotionOccurrence
    -> Reference.Reference (ScopedReferenceInputs, Notion.FormationSearchStatistics)
prepareScopedReferenceInputs limits consumer context target = do
    (observations, statistics) <- Reference.countedReferenceOperation (\allowance ->
        first (first (\case
            Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted
            Core.CountedCoreOperationFailed failure -> observationFailure failure))
            (Elaboration.countedFormationObservationsFor allowance limits consumer context))
    aliases <- Reference.countedReferenceOperation (\allowance ->
        first (first (\case
            Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted
            Core.CountedCoreOperationFailed failure -> Reference.ReferenceInvalidInput failure))
            (Elaboration.countedFormationAliasesFor allowance consumer context))
    inputs <- prepareObservedReferenceInputs (snd <$> toList (Elaboration.elaborationContextSupport context))
        aliases observations target
    pure (inputs, statistics)
  where
    observationFailure = \case
        Elaboration.FormationObservationExhausted{} -> Reference.ReferenceWorkExhausted
        Elaboration.FormationScopePreparationLimitExceeded{} -> Reference.ReferenceWorkExhausted
        Elaboration.FormationObservationScopeError message -> Reference.ReferenceInvalidInput message

-- The observations come from the checked scope owner; this adapter grants no
-- proof authority. It is also usable for genuine provisional definition scopes,
-- which have checked binder types but no nominal proof-local context.
prepareObservedReferenceInputs
    :: [Core.CoreType] -> Elaboration.AlignedFormationAliases
    -> [Elaboration.FormationObservation] -> Elaboration.ScopedSourceNotionOccurrence
    -> Reference.Reference ScopedReferenceInputs
prepareObservedReferenceInputs currentTypes aliases observations target = do
    let charge = Reference.chargeReferenceWork 1
        counted :: (Word -> (Either (Core.CountedCoreFailure Elaboration.FormationAliasNormalizationError) value, Word))
            -> Reference.Reference value
        counted operation = Reference.countedReferenceOperation (\allowance ->
            first (first aliasFailure) (operation allowance))
        normalize = normalizeScopedView charge
            (\formula -> counted (\allowance -> Elaboration.countedNormalizeFormationAliases allowance aliases formula))
            (\term -> counted (\allowance -> Elaboration.countedViewFormationAliases allowance aliases term))
        check condition message = unless condition (Reference.invalidReferenceInput message)
        coreOperation :: (Word -> (Either (Core.CountedCoreFailure Void) value, Word)) -> Reference.Reference value
        coreOperation operation = Reference.countedReferenceOperation (\allowance ->
            first (first (\case
                Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted)) (operation allowance))
        equalContexts left right = coreOperation (\allowance -> Core.countedCoreTypeListIdentity allowance left right)
        compareTerms left right = coreOperation (\allowance -> Core.countedCanonicalOrdering allowance left right)
    assembleScopedInputs charge check equalContexts compareTerms normalize Reference.referenceTermSet currentTypes aliases observations target
  where
    aliasFailure = \case
        Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted
        Core.CountedCoreOperationFailed failure -> Reference.ReferenceInvalidInput (Text.pack (show failure))

normalizeScopedView
    :: Monad m
    => m ()
    -> (Core.ScopedCheckedCore ObjectId -> m Elaboration.FormationAliasNormalization)
    -> (Elaboration.ScopedSourceTerm -> m (Elaboration.ScopedSourceTerm,
        [Notion.MaterializedNotionHypothesis Elaboration.FormationSourceOrigin]))
    -> Elaboration.ScopedSourceNotionOccurrence -> m ScopedReferenceView
normalizeScopedView charge normalizeFormula viewSource assertion = do
    charge
    normalization <- normalizeFormula (Notion.sourceAssertionFormula assertion)
    let viewTerm occurrence = do
            (viewed, definitions) <- State.lift (viewSource occurrence)
            State.modify' (definitions <>)
            pure viewed
    (viewed, definitions) <- State.runStateT
        (Notion.traverseSourceNotionAssertionParts viewTerm
            (const (pure (Elaboration.formationAliasNormalizationResult normalization))) assertion) []
    let allDefinitions = definitions <>
            (Elaboration.formationAliasReplayStepDefinition <$> Elaboration.formationAliasNormalizationReplaySteps normalization)
    unique <- foldM (\entries definition -> charge >> pure
        (Map.insert (Notion.materializedNotionHypothesisOrigin definition) definition entries)) Map.empty allDefinitions
    pure (ScopedReferenceView viewed normalization (Map.elems unique))

assembleScopedInputs
    :: Monad m
    => m () -> (Bool -> Text -> m ())
    -> ([Core.CoreType] -> [Core.CoreType] -> m Bool)
    -> (Core.CanonicalTerm ObjectId -> Core.CanonicalTerm ObjectId -> m Ordering)
    -> (Elaboration.ScopedSourceNotionOccurrence -> m ScopedReferenceView)
    -> ([Reference.GroundTerm] -> m (Set Reference.GroundTerm))
    -> [Core.CoreType] -> Elaboration.AlignedFormationAliases
    -> [Elaboration.FormationObservation] -> Elaboration.ScopedSourceNotionOccurrence
    -> m ScopedReferenceInputs
assembleScopedInputs charge check equalContexts compareTerms normalize makeTermSet currentTypes aliases observations target = do
    let endpoints = Elaboration.formationAliasTerms aliases
    targetView <- normalize target
    observedViews <- traverse (normalize . Elaboration.formationObservationAssertion) observations
    let assertions = scopedViewAssertion <$> targetView : observedViews
        validateCore proposition = do
            matches <- equalContexts (Core.scopedCoreContext proposition) currentTypes
            check matches "reference input is outside its lexical context"
        collect term = do
            charge
            let core = SourceTerm.sourceTermOccurrenceCore term
            validateCore core
            check (Core.scopedCoreType core == Core.TySet)
                "reference input contains a non-set argument"
            case (SourceTerm.sourceTermOccurrenceProvider term, SourceTerm.sourceTermOccurrenceOrderedPair term) of
                (Just provider, _) -> concat <$> traverse collect (toList (SourceTerm.sourceTermProviderArguments provider))
                (_, Just (left,right)) -> (<>) <$> collect left <*> collect right
                _ -> pure [core]
    assertionLeaves <- for assertions (\assertion -> do
        validateCore (Notion.sourceAssertionFormula assertion)
        concat <$> traverse collect (atomTerms (Notion.sourceAssertionAtom assertion)))
    endpointLeaves <- traverse collect endpoints
    -- A simple ordered list makes every deep comparison explicit in this
    -- finite oracle. Preserve the ordinary map's first-occurrence ownership.
    let insertLeaf candidate [] = charge >> pure [candidate]
        insertLeaf candidate entries@(existing : rest) = do
            charge
            compareTerms (Core.scopedCoreTerm candidate) (Core.scopedCoreTerm existing) >>= \case
                LT -> pure (candidate : entries)
                EQ -> pure entries
                GT -> (existing :) <$> insertLeaf candidate rest
    leaves <- foldM (flip insertLeaf) [] (concat (assertionLeaves <> endpointLeaves))
    let indexed = zip (Reference.OpaqueSeed <$> [0..]) leaves
        bySeed = Map.fromDistinctAscList indexed
        lookupLeaf _ [] = error "a collected reference leaf disappeared during template construction"
        lookupLeaf core ((seed, candidate) : rest) = do
            charge
            compareTerms core (Core.scopedCoreTerm candidate) >>= \case
                EQ -> pure seed
                _ -> lookupLeaf core rest
        term occurrence = do
            charge
            case (SourceTerm.sourceTermOccurrenceProvider occurrence,
                    SourceTerm.sourceTermOccurrenceOrderedPair occurrence) of
                (Just provider, _) -> Semantic.TemplateProvider (SourceTerm.sourceTermProviderHead provider)
                    <$> traverse term (SourceTerm.sourceTermProviderArguments provider)
                (_, Just (left,right)) -> Semantic.TemplateOrderedPair <$> term left <*> term right
                _ -> Semantic.closedSetValueWith charge (SourceTerm.sourceTermOccurrenceCore occurrence) >>= \case
                    Just value -> pure (Semantic.TemplateClosed value)
                    Nothing -> Semantic.TemplateVariable <$> lookupLeaf
                        (Core.scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore occurrence)) indexed
    facts <- for (zip observations observedViews) \(observation, viewed) -> do
        charge
        row <- Semantic.traverseAtomTemplateArguments term (Notion.sourceAssertionAtom (scopedViewAssertion viewed))
        pure (Reference.ReferenceFact row
            (Reference.WitnessSummary
                (Set.fromList (Elaboration.formationObservationOrigin observation
                    : (Notion.materializedNotionHypothesisOrigin <$> scopedViewDefinitions viewed)))
                Set.empty Set.empty))
    goal <- Semantic.traverseAtomTemplateArguments term (Notion.sourceAssertionAtom (scopedViewAssertion targetView))
    endpointTerms <- traverse term endpoints >>= makeTermSet
    pure (ScopedReferenceInputs goal facts bySeed
        (zip observations observedViews) targetView endpointTerms
        (Elaboration.formationAliasDefinitions aliases))

atomTerms :: Semantic.AtomTemplate term -> [term]
atomTerms = toList

-- Exercise production source encoding against the independently prepared leaf
-- identities and normalized views. Nominal eligibility still belongs to the
-- checked observation owner, and is tested separately from term abstraction.
productionScopedRows :: ScopedReferenceInputs -> Reference.Reference (Reference.GroundAtom, [Reference.GroundAtom])
productionScopedRows inputs = do
    ((target, observed), leaves) <- State.runStateT
        ((,) <$> row (scopedReferenceTarget inputs)
            <*> traverse (row . snd) (scopedReferenceObservations inputs))
        (Leaves.emptyOpaqueLeaves context)
    (,) <$> relabelRow leaves target <*> traverse (relabelRow leaves) observed
  where
    context = Core.scopedCoreContext (Notion.sourceAssertionFormula (scopedViewAssertion (scopedReferenceTarget inputs)))
    row view = do
        leaves <- State.get
        (encoded, next) <- State.lift (Reference.countedReferenceOperation (\allowance ->
            let (result, remaining) = SourceRows.encodeSourceRow allowance context (scopedViewAssertion view) leaves
            in (first (\case
                Core.CountedCoreStructuralWorkExhausted -> Reference.ReferenceWorkExhausted
                Core.CountedCoreOperationFailed failure -> Reference.ReferenceInvalidInput (Text.pack (show failure))) result, remaining)))
        State.put next
        pure encoded
    -- Relabel only for comparison with the independently collected oracle
    -- leaves. Production rows retain their own query-local opaque identities.
    relabelRow leaves value = Reference.chargeReferenceWork 1 >> traverse (term leaves) value
    term leaves value = Reference.chargeReferenceWork 1 >> case value of
        Semantic.TemplateClosed closed -> pure (Semantic.TemplateClosed closed)
        Semantic.TemplateVariable identifier -> do
            core <- maybe (Reference.invalidReferenceInput "production row has a missing opaque leaf") pure
                (Leaves.lookupOpaqueLeaf identifier leaves)
            Semantic.TemplateVariable <$> findLeaf core (Map.toAscList (scopedReferenceLeaves inputs))
        Semantic.TemplateProvider provider arguments -> Semantic.TemplateProvider provider <$> traverse (term leaves) arguments
        Semantic.TemplateOrderedPair left right -> Semantic.TemplateOrderedPair <$> term leaves left <*> term leaves right
    findLeaf _ [] = Reference.invalidReferenceInput "production source introduced an uncollected opaque leaf"
    findLeaf core ((identifier,known):rest) = do
        same <- Imports.equalReferenceCore (Core.scopedCoreTerm core) (Core.scopedCoreTerm known)
        if same then pure identifier else findLeaf core rest
