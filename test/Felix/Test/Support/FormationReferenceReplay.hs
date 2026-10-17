{-# LANGUAGE NoImplicitPrelude #-}

-- | Independently interpret the reference's first-order signature in checked
-- Core and replay its witnesses relative to the supplied premises. This checks
-- logical construction, not permission to promote a provisional observation to
-- a proof-local hypothesis; the scoped production adapter must check that too.
module Felix.Test.Support.FormationReferenceReplay
    ( checkReferenceReplay, checkImportedReferenceReplay, checkScopedReferenceReplay
    ) where

import Base
import Data.Bifunctor (first)
import Control.Monad (foldM, unless, when)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Felix.Checking.Core qualified as Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Test.Support.FormationReferenceScope qualified as Scope
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Identity qualified as Identity
import Felix.Test.Support.FormationReferenceImports qualified as Imports
import Felix.Checking.Kernel.Derivation qualified as Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Semantic qualified as Semantic
import Felix.Test.Support.FormationReference qualified as Reference
import Felix.Test.Support.GlobalTyping
import Numeric.Natural (Natural)
import Test.Tasty.HUnit

checkReferenceReplay
    :: Map Natural Reference.ReferenceRule
    -> [Reference.ReferenceFact Natural]
    -> Reference.ReferenceEvaluation Natural
    -> Assertion
checkReferenceReplay rules facts result = do
    foundation <- expectRight Foundation.checkedFoundation
    let ruleAtoms = concatMap (\rule -> Reference.referenceRuleConclusion rule
            : concatMap leaves (Reference.referenceRulePremises rule)) (Map.elems rules)
        factAtoms = [row | Reference.ReferenceFact row _ <- facts]
        heads = Set.fromList (fmap (const ()) <$> ruleAtoms)
            <> Set.fromList (fmap (const ()) <$> factAtoms)
        providers = Set.unions (termProviders <$> concatMap atomTerms ruleAtoms)
            <> Set.unions (termProviders <$> concatMap atomTerms factAtoms)
        signatures = [(Left head', foldr (const (Core.TyArrow Core.TySet)) Core.TyProp (atomTerms head'))
                | head' <- Set.toAscList heads]
            <> [(Right (provider,arity), foldr (const (Core.TyArrow Core.TySet)) Core.TySet [1..arity])
                | (provider,arity) <- Set.toAscList providers]
        fixture = globalTypingFixture (snd <$> signatures)
        globals = Map.fromList (zip (fst <$> signatures) (fixtureObjectIds fixture))
        typing = fixtureGlobalTyping fixture
        -- Uninterpreted globals give an injective interpretation of the finite
        -- provider/atom signature. Pair construction retains its Core meaning.
        term :: (variable -> Core.CanonicalTerm ObjectId) -> Semantic.SetTermTemplate variable -> Core.CanonicalTerm ObjectId
        term variable = \case
            Semantic.TemplateClosed value -> Semantic.closedSetValueTerm value
            Semantic.TemplateVariable index -> variable index
            Semantic.TemplateProvider provider arguments ->
                List.foldl' Core.CApp (Core.CGlobal (globals Map.! Right (provider,Vector.length arguments)))
                    (term variable <$> toList arguments)
            Semantic.TemplateOrderedPair left right -> Core.CApp
                (Core.CApp (Core.CIntrinsic Core.OrderedPair) (term variable left)) (term variable right)
        atom :: (variable -> Core.CanonicalTerm ObjectId) -> Semantic.AtomTemplate (Semantic.SetTermTemplate variable) -> Core.CanonicalTerm ObjectId
        atom variable row = List.foldl' Core.CApp
            (Core.CGlobal (globals Map.! Left (fmap (const ()) row)))
            (term variable <$> atomTerms row)
        tree variable = \case
            Semantic.RulePremiseAtom row -> atom variable row
            Semantic.RulePremiseUniversal _ -> error "atomic reference received a whole premise"
            Semantic.RulePremiseResidual _ -> error "atomic reference received a whole premise"
            Semantic.RulePremiseAnd left right -> Core.CAnd (tree variable left) (tree variable right)
        source rule = foldr (const (Core.CForall Core.TySet))
            (foldr Core.CImp (atom binder (Reference.referenceRuleConclusion rule))
                (tree binder <$> Reference.referenceRulePremises rule))
            [1 .. Reference.referenceRuleArity rule]
        binder (Semantic.ViewVariableIx index) = Core.CBound index
    imports <- traverse (expectRight . Core.checkCanonicalCore typing . source) rules
    judgements <- traverse (expectRight . Derivation.derivationImportJudgement) (Map.elems imports)
    -- Exercise binder rebasing as well as the closed case. Opaque seed zero
    -- denotes the ambient variable in the second interpretation.
    forM_ [[], [Core.TySet]] \ambient -> do
        let seed (Reference.OpaqueSeed index)
                | index == 0, not (null ambient) = Core.CBound 0
                | otherwise = Core.COpaqueInteger (fromIntegral index)
            checked = expectRight . Core.checkScopedCanonicalCore typing ambient
        hypotheses <- traverse (checked . atom seed) factAtoms
        context <- expectRight (Proof.scopedProofContext foundation typing ambient hypotheses)
        let build retained (identifier, witness) = do
                (proof, expectedHypotheses) <- case Reference.referenceWitnessRecipe witness of
                    Reference.ObservedRow ordinal -> do
                        proof <- expectRight (Proof.indexedHypothesisProof context (Derivation.hypothesisIx ordinal))
                        pure (proof, Set.singleton (Derivation.hypothesisIx ordinal))
                    Reference.SameDenotation prior -> do
                        let (priorProof, used) = retained Map.! prior
                        target <- checked (atom seed (Reference.referenceWitnessAtom witness))
                        proof <- expectRight (Proof.conversionProof context priorProof target)
                        pure (proof, used)
                    Reference.AppliedRule ordinal bindings forest -> do
                        let dense = fromIntegral (Map.size (fst (Map.split ordinal rules)))
                        initial <- expectRight (Proof.importedProof context (Derivation.importIx dense) (imports Map.! ordinal))
                        arguments <- traverse (checked . term seed . snd) (Map.toDescList bindings)
                        specialized <- foldM (\proof argument -> expectRight (Proof.forallEliminationProof context proof argument)) initial arguments
                        let premise = \case
                                Reference.PremiseLeaf prior -> pure (retained Map.! prior)
                                Reference.PremiseConjunction left right -> do
                                    (a,usedA) <- premise left
                                    (b,usedB) <- premise right
                                    proof <- expectRight (Proof.conjunctionIntroductionProof context a b)
                                    pure (proof, usedA <> usedB)
                        premises <- traverse premise forest
                        applied <- foldM (\proof (given,_) -> expectRight (Proof.implicationEliminationProof context proof given)) specialized premises
                        pure (applied, Set.unions (snd <$> premises))
                target <- checked (atom seed (Reference.referenceWitnessAtom witness))
                replayed <- expectRight (Derivation.replayScopedKernelDerivation foundation
                    Derivation.defaultKernelReplayLimits typing (Vector.fromList judgements)
                    (Vector.fromList hypotheses) target (Proof.builtProofDerivation proof))
                let expectedImports = Set.map (\ordinal -> Derivation.importIx
                        (fromIntegral (Map.size (fst (Map.split ordinal rules)))))
                        (Reference.witnessOccurrences (Reference.referenceWitnessSummary witness))
                assertEqual "reference witness consumes its exact imports" expectedImports
                    (Derivation.replayedScopedKernelImportUses replayed)
                assertEqual "reference witness consumes its exact premise slots" expectedHypotheses
                    (Derivation.replayedScopedKernelExternalHypothesisUses replayed)
                pure (Map.insert identifier (proof,expectedHypotheses) retained)
        void (foldM build Map.empty (Map.toAscList (Reference.referenceWitnesses result)))
  where
    leaves (Semantic.RulePremiseAtom atom) = [atom]
    leaves (Semantic.RulePremiseUniversal _) = error "atomic reference received a whole premise"
    leaves (Semantic.RulePremiseResidual _) = error "atomic reference received a whole premise"
    leaves (Semantic.RulePremiseAnd left right) = leaves left <> leaves right

atomTerms :: Semantic.AtomTemplate term -> [term]
atomTerms = toList

termProviders :: Semantic.SetTermTemplate variable -> Set (Semantic.SourceProviderHead, Int)
termProviders = \case
    Semantic.TemplateClosed{} -> Set.empty
    Semantic.TemplateVariable{} -> Set.empty
    Semantic.TemplateProvider provider arguments -> Set.insert (provider,Vector.length arguments)
        (Set.unions (termProviders <$> toList arguments))
    Semantic.TemplateOrderedPair left right -> termProviders left <> termProviders right

expectRight :: Show failure => Either failure value -> IO value
expectRight = either (\failure -> assertFailure (show failure) >> fail "reference replay failed") pure

-- Replay against actual sealed theorem statements. A semantic row must have
-- the same checked denotation through every witness, and each application must
-- consume the exact antecedents of its real source. The caller supplies actual
-- hypotheses from one test scope, never provisional formation observations.
checkImportedReferenceReplay
    :: Identity.CheckedObjectClosure
    -> Map Natural Imports.ImportedReferenceRule
    -> [Core.CoreType]
    -> (Reference.GroundTerm -> Either Text (Core.CanonicalTerm ObjectId))
    -> (Reference.GroundAtom -> Either Text (Core.CanonicalTerm ObjectId))
    -> [(Reference.ReferenceFact Natural, Core.ScopedCheckedCore ObjectId)]
    -> Reference.ReferenceEvaluation Natural
    -> IO (Map Reference.GroundAtom (Core.ScopedCheckedCore ObjectId))
checkImportedReferenceReplay closure rules ambient term atom facts =
    replayImportedReference closure rules ambient term atom (snd <$> facts)
        [ReplayObservation fact ordinal Notion.ConjunctionHere proposition []
        | (ordinal, (fact, proposition)) <- zip [0..] facts] Nothing

-- A scoped observation is reconstructed from its original proof-local slot,
-- not installed as a fresh atomic hypothesis. Resolve the nominal origin and
-- exact enclosing proposition before allowing any proof construction.
checkScopedReferenceReplay
    :: Identity.CheckedObjectClosure
    -> Map Natural Imports.ImportedReferenceRule
    -> [Core.CoreType]
    -> (Reference.GroundTerm -> Either Text (Core.CanonicalTerm ObjectId))
    -> (Reference.GroundAtom -> Either Text (Core.CanonicalTerm ObjectId))
    -> [Notion.MaterializedNotionHypothesis Elaboration.FormationSourceOrigin]
    -> Scope.ScopedReferenceInputs
    -> Reference.ReferenceEvaluation Elaboration.FormationSourceOrigin
    -> IO (Either Text (Map Reference.GroundAtom (Core.ScopedCheckedCore ObjectId)))
checkScopedReferenceReplay closure rules ambient term atom locals inputs result =
    case resolve of
        Left failure -> pure (Left failure)
        Right (observations, goal) -> Right <$> replayImportedReference closure rules ambient term atom
            (Notion.materializedNotionHypothesisProposition <$> locals) observations (Just goal) result
  where
    typing = Identity.globalTypingFromClosure closure
    leaves = Map.fromList
        [(Core.scopedCoreTerm core, seed) | (seed, core) <- Map.toList (Scope.scopedReferenceLeaves inputs)]
    checkMeaning row expected = do
        value <- atom row
        actual <- first (const "reference atom interpretation is not well typed in this scope")
            (Core.checkScopedCanonicalCore typing ambient value)
        unless (actual == expected)
            (Left "reference atom disagrees with its checked source formula")
    -- Check every construction, including children whose denotation is erased
    -- by an enclosing transparent provider. Whole-formula agreement is weaker.
    sourceTerm occurrence = do
        let expected = SourceTerm.sourceTermOccurrenceCore occurrence
        syntax <- case (SourceTerm.sourceTermOccurrenceProvider occurrence,
                SourceTerm.sourceTermOccurrenceOrderedPair occurrence) of
            (Just provider, _) -> Semantic.TemplateProvider (SourceTerm.sourceTermProviderHead provider)
                <$> traverse sourceTerm (SourceTerm.sourceTermProviderArguments provider)
            (_, Just (left, right)) -> Semantic.TemplateOrderedPair <$> sourceTerm left <*> sourceTerm right
            _ -> case Semantic.closedSetValue expected of
                Just value -> pure (Semantic.TemplateClosed value)
                Nothing -> Semantic.TemplateVariable <$> maybe (Left "reference source leaf is absent from the frozen inputs") Right
                    (Map.lookup (Core.scopedCoreTerm expected) leaves)
        value <- term syntax
        actual <- first (const "reference source interpretation is not well typed in this scope")
            (Core.checkScopedCanonicalCore typing ambient value)
        unless (actual == expected && Core.scopedCoreType actual == Core.TySet
                && SourceTerm.sourceTermOccurrenceType occurrence == Core.TySet)
            (Left "reference provider metadata disagrees with its checked source term")
        pure syntax
    resolve = do
        indexed <- for (zip [0..] locals) \(index, local) -> do
            let proposition = Notion.materializedNotionHypothesisProposition local
            unless (Core.scopedCoreContext proposition == ambient)
                (Left "a reference proof local is outside the current scope")
            case Notion.materializedNotionHypothesisOrigin local of
                Elaboration.FormationFromProofLocal ordinal kind -> pure (ordinal, (kind, index, proposition))
                _ -> Left "a provisional observation is not an actual reference proof local"
        let byOrdinal = Map.fromList indexed
            observations = Scope.scopedReferenceObservations inputs
            facts = Scope.scopedReferenceFacts inputs
        unless (Map.size byOrdinal == length indexed)
            (Left "duplicate reference proof-local ordinals")
        unless (length observations == length facts)
            (Left "the reference rows lost their scoped observations")
        let resolveLocal origin expected = do
                (ordinal, kind) <- case origin of
                    Elaboration.FormationFromProofLocal ordinal kind -> pure (ordinal, kind)
                    _ -> Left "a provisional reference observation has no proof-local authority"
                (actualKind, index, proposition) <- maybe (Left "a reference proof local is missing") Right
                    (Map.lookup ordinal byOrdinal)
                unless (kind == actualKind && proposition == expected)
                    (Left "a reference observation does not match its actual proof local")
                pure index
            resolveView viewed = do
                void (Notion.traverseSourceNotionAssertionParts
                    (\occurrence -> sourceTerm occurrence >> pure occurrence) pure
                    (Scope.scopedViewAssertion viewed))
                let normalization = Scope.scopedViewNormalization viewed
                    steps = Elaboration.formationAliasNormalizationReplaySteps normalization
                    origins = Set.fromList (Notion.materializedNotionHypothesisOrigin <$> Scope.scopedViewDefinitions viewed)
                    required = Set.fromList (Notion.materializedNotionHypothesisOrigin
                        . Elaboration.formationAliasReplayStepDefinition <$> steps)
                unless (Elaboration.formationAliasNormalizationResult normalization
                        == Notion.sourceAssertionFormula (Scope.scopedViewAssertion viewed)
                        && required `Set.isSubsetOf` origins)
                    (Left "a reference view lost its checked normalization or dependencies")
                -- Metadata dependencies include erased arguments and therefore
                -- are not necessarily used by the resulting logical proof.
                for_ (Scope.scopedViewDefinitions viewed) \definition ->
                    void (resolveLocal (Notion.materializedNotionHypothesisOrigin definition)
                        (Notion.materializedNotionHypothesisProposition definition))
                for steps \step -> do
                    let definition = Elaboration.formationAliasReplayStepDefinition step
                    slot <- resolveLocal (Notion.materializedNotionHypothesisOrigin definition)
                        (Notion.materializedNotionHypothesisProposition definition)
                    pure (ReplayAlias slot step)
        -- Even an unused alias may contribute a support endpoint. Validate that
        -- capability against the actual scope before trusting the frozen U.
        for_ (Scope.scopedReferenceAliasDefinitions inputs) \definition ->
            void (resolveLocal (Notion.materializedNotionHypothesisOrigin definition)
                (Notion.materializedNotionHypothesisProposition definition))
        replayObservations <- for (zip facts observations) \(fact@(Reference.ReferenceFact row summary), (observation, viewed)) -> do
            index <- resolveLocal (Elaboration.formationObservationOrigin observation)
                (Elaboration.formationObservationSource observation)
            aliases <- resolveView viewed
            let expectedOrigins = Set.fromList (Elaboration.formationObservationOrigin observation
                    : (Notion.materializedNotionHypothesisOrigin <$> Scope.scopedViewDefinitions viewed))
                assertion = Elaboration.formationObservationAssertion observation
                normalization = Scope.scopedViewNormalization viewed
            unless (Reference.witnessOrigins summary == expectedOrigins && Set.null (Reference.witnessOccurrences summary))
                (Left "a reference observation lost its actual source dependencies")
            unless (Elaboration.formationAliasNormalizationOriginal normalization == Notion.sourceAssertionFormula assertion)
                (Left "a reference observation lost its alias transport endpoints")
            checkMeaning row (Elaboration.formationAliasNormalizationResult normalization)
            pure (ReplayObservation fact index (Notion.sourceAssertionPath assertion)
                (Elaboration.formationAliasNormalizationResult normalization) aliases)
        let target = Scope.scopedReferenceTarget inputs
        goalAliases <- resolveView target
        checkMeaning (Scope.scopedReferenceGoal inputs)
            (Elaboration.formationAliasNormalizationResult (Scope.scopedViewNormalization target))
        pure (replayObservations, (Scope.scopedReferenceGoal inputs,
            Elaboration.formationAliasNormalizationOriginal (Scope.scopedViewNormalization target), reverse goalAliases))

data ReplayObservation origin = ReplayObservation
    !(Reference.ReferenceFact origin) !Natural !Notion.ConjunctionPath !(Core.ScopedCheckedCore ObjectId) ![ReplayAlias]

data ReplayAlias = ReplayAlias !Natural !Elaboration.FormationAliasReplayStep

data AliasDirection = ExpandAlias | RestoreAlias

replayAliases :: Proof.ProofContext ObjectId -> AliasDirection -> [ReplayAlias]
    -> Proof.BuiltProof ObjectId -> IO (Proof.BuiltProof ObjectId)
replayAliases context direction aliases initial = foldM step initial aliases
  where
    step current (ReplayAlias slot alias) = do
        definition <- expectRight (Proof.indexedHypothesisProof context (Derivation.hypothesisIx slot))
        assertEqual "alias replay resolves the exact compiler definition"
            (Notion.materializedNotionHypothesisProposition (Elaboration.formationAliasReplayStepDefinition alias))
            (Proof.builtProofStatement definition)
        equality <- case direction of
            ExpandAlias -> pure definition
            RestoreAlias -> expectRight (Proof.equalityReverseProof context definition)
        expectRight (Proof.equalityTransportProof context equality (Elaboration.formationAliasReplayStepAbstraction alias) current)

aliasHypotheses :: [ReplayAlias] -> Set Derivation.HypothesisIx
aliasHypotheses aliases = Set.fromList [Derivation.hypothesisIx slot | ReplayAlias slot _ <- aliases]

replayImportedReference
    :: (Ord origin, Show origin)
    => Identity.CheckedObjectClosure
    -> Map Natural Imports.ImportedReferenceRule
    -> [Core.CoreType]
    -> (Reference.GroundTerm -> Either Text (Core.CanonicalTerm ObjectId))
    -> (Reference.GroundAtom -> Either Text (Core.CanonicalTerm ObjectId))
    -> [Core.ScopedCheckedCore ObjectId]
    -> [ReplayObservation origin]
    -> Maybe (Reference.GroundAtom, Core.ScopedCheckedCore ObjectId, [ReplayAlias])
    -> Reference.ReferenceEvaluation origin
    -> IO (Map Reference.GroundAtom (Core.ScopedCheckedCore ObjectId))
replayImportedReference closure rules ambient term atom hypotheses observations requested result = do
    foundation <- expectRight Foundation.checkedFoundation
    let typing = Identity.globalTypingFromClosure closure
        imports = Identity.checkedPropositionTerm . Imports.importedReferenceProposition <$> rules
        observed = Map.fromList (zip [0..] observations)
        importIndex ordinal = Derivation.importIx (fromIntegral (Map.size (fst (Map.split ordinal rules))))
        checked value = expectRight (Core.checkScopedCanonicalCore typing ambient value)
    judgements <- traverse (expectRight . Derivation.derivationImportJudgement) (Map.elems imports)
    context <- expectRight (Proof.scopedProofContext foundation typing ambient hypotheses)
    let build (retained, meanings) (identifier, witness) = do
            (proof, expectedHypotheses, expectedOrigins) <- case Reference.referenceWitnessRecipe witness of
                Reference.ObservedRow ordinal -> do
                    let ReplayObservation (Reference.ReferenceFact row summary) slot path proposition aliases = observed Map.! ordinal
                        project Notion.ConjunctionHere proof = pure proof
                        project (Notion.ConjunctionLeft rest) proof =
                            expectRight (Proof.conjunctionLeftProof context proof) >>= project rest
                        project (Notion.ConjunctionRight rest) proof =
                            expectRight (Proof.conjunctionRightProof context proof) >>= project rest
                    initial <- expectRight (Proof.indexedHypothesisProof context (Derivation.hypothesisIx slot))
                    projected <- project path initial
                    transported <- replayAliases context ExpandAlias aliases projected
                    proof <- expectRight (Proof.conversionProof context transported proposition)
                    assertEqual "the observation recipe proves its retained formula" proposition (Proof.builtProofStatement proof)
                    assertEqual "the witness retains its observed atom" row (Reference.referenceWitnessAtom witness)
                    pure (proof, Set.singleton (Derivation.hypothesisIx slot) <> aliasHypotheses aliases, Reference.witnessOrigins summary)
                Reference.SameDenotation prior -> do
                    let sourceWitness = Reference.referenceWitnesses result Map.! prior
                        sourceRow = Reference.referenceWitnessAtom sourceWitness
                        targetRow = Reference.referenceWitnessAtom witness
                        denote value = do
                            core <- expectRight (term value) >>= checked
                            assertEqual "interpreted formation arguments are sets" Core.TySet (Core.scopedCoreType core)
                            pure core
                    assertBool "denotation witnesses depend on an earlier proof" (prior < identifier)
                    assertEqual "denotation equality preserves the exact predicate and arity"
                        (fmap (const ()) sourceRow) (fmap (const ()) targetRow)
                    sourceTerms <- traverse denote (atomTerms sourceRow)
                    targetTerms <- traverse denote (atomTerms targetRow)
                    assertEqual "denotation equality is independently checked in Core" sourceTerms targetTerms
                    pure (retained Map.! prior)
                Reference.AppliedRule ordinal bindings forest -> do
                    initial <- expectRight (Proof.importedProof context (importIndex ordinal) (imports Map.! ordinal))
                    arguments <- traverse (\value -> expectRight (term value) >>= checked) (snd <$> Map.toDescList bindings)
                    specialized <- foldM (\proof argument -> expectRight (Proof.forallEliminationProof context proof argument)) initial arguments
                    let premise = \case
                            Reference.PremiseLeaf prior -> pure (retained Map.! prior)
                            Reference.PremiseConjunction left right -> do
                                (a,usedA,originsA) <- premise left
                                (b,usedB,originsB) <- premise right
                                proof <- expectRight (Proof.conjunctionIntroductionProof context a b)
                                pure (proof, usedA <> usedB, originsA <> originsB)
                    premises <- traverse premise forest
                    applied <- foldM (\proof (given,_,_) -> expectRight (Proof.implicationEliminationProof context proof given)) specialized premises
                    let project Notion.ConjunctionHere proof = pure proof
                        project (Notion.ConjunctionLeft rest) proof =
                            expectRight (Proof.conjunctionLeftProof context proof) >>= project rest
                        project (Notion.ConjunctionRight rest) proof =
                            expectRight (Proof.conjunctionRightProof context proof) >>= project rest
                    projected <- project (Imports.importedReferencePath (rules Map.! ordinal)) applied
                    pure (projected, Set.unions [used | (_,used,_) <- premises], Set.unions [origins | (_,_,origins) <- premises])
            let target = Proof.builtProofStatement proof
                row = Reference.referenceWitnessAtom witness
            denotation <- expectRight (atom row) >>= checked
            assertEqual "each reference witness proves its independently interpreted atom" denotation target
            for_ (Map.lookup row meanings) (assertEqual "one reference row has one actual Core denotation" target)
            replayed <- expectRight (Derivation.replayScopedKernelDerivation foundation
                Derivation.defaultKernelReplayLimits typing (Vector.fromList judgements)
                (Vector.fromList hypotheses) target (Proof.builtProofDerivation proof))
            assertEqual "real reference witness consumes its exact source occurrences"
                (Set.map importIndex (Reference.witnessOccurrences (Reference.referenceWitnessSummary witness)))
                (Derivation.replayedScopedKernelImportUses replayed)
            assertEqual "real reference witness consumes its exact local hypotheses" expectedHypotheses
                (Derivation.replayedScopedKernelExternalHypothesisUses replayed)
            assertEqual "real reference witness retains its premise origins" expectedOrigins
                (Reference.witnessOrigins (Reference.referenceWitnessSummary witness))
            for_ requested \(goal, original, aliases) -> when (row == goal) do
                transported <- replayAliases context RestoreAlias aliases proof
                restored <- expectRight (Proof.conversionProof context transported original)
                restoredReplay <- expectRight (Derivation.replayScopedKernelDerivation foundation
                    Derivation.defaultKernelReplayLimits typing (Vector.fromList judgements)
                    (Vector.fromList hypotheses) original (Proof.builtProofDerivation restored))
                assertEqual "restored goal retains its exact imports"
                    (Derivation.replayedScopedKernelImportUses replayed) (Derivation.replayedScopedKernelImportUses restoredReplay)
                assertEqual "restored goal adds only its used alias definitions"
                    (expectedHypotheses <> aliasHypotheses aliases) (Derivation.replayedScopedKernelExternalHypothesisUses restoredReplay)
            pure (Map.insert identifier (proof,expectedHypotheses,expectedOrigins) retained, Map.insert row target meanings)
        insertMeaning meanings (ReplayObservation (Reference.ReferenceFact row _) _ _ proposition _) = do
            denotation <- expectRight (atom row) >>= checked
            assertEqual "each observed row denotes its supplied formula" denotation proposition
            for_ (Map.lookup row meanings) (assertEqual "observed rows have one Core denotation" proposition)
            pure (Map.insert row proposition meanings)
    initialMeanings <- foldM insertMeaning Map.empty observations
    snd <$> foldM build (Map.empty, initialMeanings) (Map.toAscList (Reference.referenceWitnesses result))
