{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Shared checked lowering for closed instances and construction families.
--
-- Each realization is one atomic declaration with staged checked facts:
--
-- * a hidden transparent definition equation for the named object;
-- * a hidden source proof of the flattened mathematical parameter, inherited,
--   field, and law obligations on the aggregate body;
-- * a hidden kernel specialization of the aggregate schema's exact-shape law;
-- * one hidden definitional proof per aggregate projection;
-- * the public structure theorem for the named object, derived from the
--   definition, mathematical proof, exact-shape specialization, and ordinary
--   transparent structure definitions;
-- * a public named-object exact-shape theorem derived from the definition and
--   hidden exact-shape proof;
-- * public named-object projection equations, each derived from the
--   definition and its corresponding aggregate equation.
--
-- During source-proof elaboration the new name expands transparently to its
-- body.  It therefore reads naturally in proof steps without making the
-- definition equation available to unrelated proof search.
-- Constructions additionally register the proved public structure result,
-- retaining their complete parameter and hypothesis envelope at every stage.
module Felix.Checking.Instance
    ( PreparedInstance
    , prepareInstance
    , CheckedInstanceAuthorization
    , lowerPreparedInstance
    , authorizeCheckedInstance
    , InstanceError(..)
    , instanceErrorDisposition
    , instanceErrorLocation
    , renderInstanceError
    ) where

import Base
import Felix.Checking.Planning qualified as Planning
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Obligation qualified as Obligation
import Felix.Cache.Codec
import Felix.Checking.Core
import Felix.Checking.Binding qualified as Binding
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Foundation (CheckedFoundation)
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation
    (KernelDerivation, importIx, implicationIntroductionDerivation, forallIntroductionDerivation)
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.ProviderResult qualified as ProviderResult
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic
import Felix.Checking.Structure.Predicate qualified as StructurePredicate
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface (CanonicalLexicalEntry)

import Control.Monad.Except qualified as Except
import Control.Monad (foldM, unless)
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


data PreparedInstance = PreparedInstance
    !Location
    !SemanticName
    !Binding.PreparedBinding
    !(CanonicalTerm ObjectId)
    !(ScopedCheckedCore ObjectId)
    !Proof.PreparedProof
    !PreparedAggregateExactness
    ![(Raw.StructSymbol, Proof.PreparedProof)]
    ![PreparedStructureDefinition]
    !InstanceScope
    !(Registration Planning.PlannedCandidatePosition)

-- The same envelope is retained for every public consequence. An ordinary
-- instance is the empty-scope case; a construction closes set parameters and
-- all ordered hypotheses around its checked local record obligations.
data InstanceScope = InstanceScope !Natural ![ScopedCheckedCore ObjectId]

data PreparedAggregateExactness = PreparedAggregateExactness
    !SemanticFactOccurrenceFingerprint
    !(FrozenCheckedCore ObjectId)
    ![CanonicalTerm ObjectId]
    !(ScopedCheckedCore ObjectId)

data PreparedStructureDefinition = PreparedStructureDefinition
    !ObjectId
    !SemanticFactOccurrenceFingerprint
    !(FrozenCheckedCore ObjectId)
    deriving stock (Show, Eq, Ord)

data InstanceError
    = InstanceUnsupported !Location
    | InstanceExpectedAggregate !Location
    | InstanceParameterRequiresExpression !Location
    | InstanceObligationModelMismatch !Location
    | InstanceStructureDefinitionUnavailable !Location
    | InstanceAggregateExactnessUnavailable !Location
    | InstanceCompileFailed !Elaboration.ElaborationError
    | InstanceProofFailed !Proof.ProofError
    | InstanceProofOmitted !Location
    | ConstructionInvalid !Location !Text
    deriving stock (Show, Eq)

instanceErrorDisposition
    :: InstanceError
    -> Proof.ProofErrorDisposition
instanceErrorDisposition = \case
    InstanceUnsupported{} -> Proof.ProofSourceRejection
    InstanceExpectedAggregate{} -> Proof.ProofSourceRejection
    InstanceParameterRequiresExpression{} -> Proof.ProofSourceRejection
    InstanceObligationModelMismatch{} -> Proof.ProofSourceRejection
    InstanceStructureDefinitionUnavailable{} -> Proof.ProofSourceRejection
    InstanceAggregateExactnessUnavailable{} -> Proof.ProofSourceRejection
    InstanceCompileFailed{} -> Proof.ProofSourceRejection
    InstanceProofFailed failure -> Proof.proofErrorDisposition failure
    InstanceProofOmitted{} -> Proof.ProofSourceRejection
    ConstructionInvalid{} -> Proof.ProofSourceRejection

instanceErrorLocation :: InstanceError -> Location
instanceErrorLocation = \case
    InstanceUnsupported location -> location
    InstanceExpectedAggregate location -> location
    InstanceParameterRequiresExpression location -> location
    InstanceObligationModelMismatch location -> location
    InstanceStructureDefinitionUnavailable location -> location
    InstanceAggregateExactnessUnavailable location -> location
    InstanceCompileFailed failure ->
        Elaboration.elaborationErrorLocation failure
    InstanceProofFailed failure ->
        Proof.proofErrorLocation failure
    InstanceProofOmitted location -> location
    ConstructionInvalid location _ -> location

renderInstanceError :: InstanceError -> Text
renderInstanceError = \case
    InstanceUnsupported location ->
        at location <> "unsupported named instance declaration"
    InstanceExpectedAggregate location ->
        at location <> "a named instance must be defined by a structure aggregate or reconstruction"
    InstanceParameterRequiresExpression location ->
        at location
            <> "an instance schema parameter must be a symbolic set expression"
    InstanceObligationModelMismatch location ->
        at location
            <> "the checked structure predicate does not match its descriptor obligation model"

    InstanceStructureDefinitionUnavailable location ->
        at location
            <> "the checked structure predicate definition is not available as a proved fact"
    InstanceAggregateExactnessUnavailable location ->
        at location
            <> "the checked aggregate exactness theorem is not available as a proved fact"
    InstanceCompileFailed failure ->
        Elaboration.renderElaborationError failure
    InstanceProofFailed failure ->
        Proof.renderProofError failure
    InstanceProofOmitted location ->
        at location <> "a named instance proof may not be omitted"
    ConstructionInvalid location message ->
        at location <> "invalid instance or construction: " <> message
  where
    at location = locationToText location <> ": "

prepareInstance
    :: Raw.Block
    -> Maybe Raw.Proof
    -> [CanonicalLexicalEntry]
    -> Declaration.LoweringDriver
        (Either InstanceError PreparedInstance)
prepareInstance block explicitProof entries = Except.runExceptT do
    (location, title, marker@(Raw.Marker markerText), assumptions,
        application, nameExpression, rawValue, parameters, isConstruction) <-
        case block of
            Raw.BlockInstance pos heading label instanceDefn ->
                pure (pos, heading, label, [], Raw.instanceApplication instanceDefn,
                    Raw.ExprTypedConstant (Raw.instanceNameLocation instanceDefn)
                        (Raw.instanceNameToken instanceDefn) Raw.ConcreteSet,
                    Raw.instanceValue instanceDefn, [], False)
            Raw.BlockConstruction pos heading label construction -> do
                let Raw.SymbolPattern symbol params = Raw.constructionHead construction
                unless (not (null params))
                    (Except.throwError (ConstructionInvalid pos
                        "use an instance for a declaration without parameters"))
                unless (length params == length (nubOrd params))
                    (Except.throwError (ConstructionInvalid pos
                        "each explicit set parameter must occur exactly once in the symbolic head"))
                unless (isJust explicitProof)
                    (Except.throwError (ConstructionInvalid pos
                        "an explicit proof must immediately follow the declaration"))
                pure (pos, heading, label, Raw.constructionAssumptions construction,
                    Raw.constructionApplication construction,
                    Raw.ExprOp pos symbol (Raw.ExprVar <$> params),
                    Raw.constructionValue construction, params, True)
            _ -> Except.throwError (InstanceUnsupported (locate block))
    headStructure <- resolveInstanceStructure location application
    annotatedValue <- annotateInstanceValue application rawValue
    let structureStatement expression = Raw.StmtStruct (Raw.TermExpr expression)
            (Raw.StructNounPhrase [] application [] Nothing)
    (fullEnvelope, aggregateContext) <- Trans.lift
        (Elaboration.elaborateClaimEnvelopeWithFormationObservation id
            assumptions (structureStatement annotatedValue))
        >>= either (Except.throwError . InstanceCompileFailed) pure
    unless (Elaboration.elaboratedClaimVariables fullEnvelope == parameters)
        (Except.throwError (ConstructionInvalid location
            "the symbolic head must list every set parameter once, in header order; implicit parameters are not supported"))
    aggregate <- Trans.lift (Elaboration.elaborateRecordAggregate aggregateContext annotatedValue)
        >>= either (Except.throwError . InstanceCompileFailed) pure
    let aggregateStructure = Elaboration.elaboratedAggregateStructure aggregate
        scope = InstanceScope (fromIntegral (length parameters))
            (Elaboration.compiledHeaderCore <$> Elaboration.elaboratedClaimAntecedents fullEnvelope)
        fullTarget = Elaboration.elaboratedClaimTarget fullEnvelope
        body = scopedCoreTerm (Elaboration.elaboratedAggregateCore aggregate)
        localTarget = openInstanceTarget scope (scopedCoreTerm fullTarget)
    unless (scopedCoreContext (Elaboration.elaboratedAggregateCore aggregate) == instanceScopeTypes scope)
        (Except.throwError (ConstructionInvalid location "every explicit parameter must have type Set"))
    whenStrictTarget isConstruction annotatedValue $
        unless (localTarget == scopedCoreTerm (Elaboration.elaboratedAggregatePredicate aggregate))
            (Except.throwError (ConstructionInvalid location
                "the body annotation must agree with the complete result schema and its parameters"))
    let definitionBlock = case block of
            Raw.BlockConstruction pos heading label construction ->
                Raw.BlockConstruction pos heading label
                    construction{Raw.constructionValue = annotatedValue}
            Raw.BlockInstance{} -> case nameExpression of
                Raw.ExprTypedConstant pos token coreType ->
                    Raw.BlockDefn location title marker
                        (Raw.DefnTypedConstant pos token coreType (Raw.TypedExpressionExpr annotatedValue))
                _ -> impossible "an instance lost its atomic name"
            _ -> impossible "a record realization lost its declaration"
    definition <- Trans.lift (Binding.prepareBinding definitionBlock entries)
        >>= either (Except.throwError . InstanceCompileFailed) pure
    transparentView <- Except.liftEither
        (first InstanceCompileFailed (Binding.preparedBindingTransparentView definition))
    unless (stripDefinitionBinders parameters (Binding.transparentBindingBody transparentView) == body)
        (Except.throwError (InstanceObligationModelMismatch location))
    resultRule <- prepareRealizationResult location definition fullEnvelope
    let theoremBlock = Raw.BlockClaim Raw.PlainClaim location title marker
            (Raw.Claim assumptions (structureStatement nameExpression))
    (shapeTarget, mathematicalTarget, structureDefinitions, requirements) <-
        prepareInstanceObligationTargets location scope headStructure aggregateStructure fullTarget
    let fieldOrigins = Map.fromList
            [(Schema.resolvedFieldIdentity (Elaboration.elaboratedRecordField field),
                case Elaboration.elaboratedRecordOrigin field of
                    Elaboration.WrittenRecordField here -> (here, "written field clause")
                    Elaboration.CopiedRecordField here -> (here, "copied field base"))
            | field <- Elaboration.elaboratedAggregateFields aggregate]
        obligations =
            [Obligation.RecordObligation (instanceScopeTypes scope) formula origins
                (locate rawValue) fieldOrigins
            | (formula, origins) <- requirements]
    proof <- Trans.lift
        (Proof.prepareProofWithTransparentDefinitionTarget
            definition mathematicalTarget obligations theoremBlock explicitProof)
        >>= either (Except.throwError . InstanceProofFailed) pure
    traverse_ (Except.throwError . InstanceProofOmitted) (Proof.preparedProofFirstOmission proof)
    aggregateExactness <- prepareAggregateExactness location scope aggregateStructure
        (scopedCoreTerm . Elaboration.elaboratedRecordValue <$> Elaboration.elaboratedAggregateFields aggregate) shapeTarget
    projectionProofs <- prepareProjectionProofs location scope definition theoremBlock aggregate
    pure (PreparedInstance location (semanticName markerText) definition body fullTarget
        proof aggregateExactness projectionProofs structureDefinitions scope resultRule)
  where
    whenStrictTarget True _ action = action
    whenStrictTarget False Raw.ExprStructReconstruction{} action = action
    whenStrictTarget False _ _ = pure ()

    stripDefinitionBinders [] body = body
    stripDefinitionBinders (_ : remaining) (CLam TySet body) =
        stripDefinitionBinders remaining body
    stripDefinitionBinders _ _ = impossible "a set provider lost its explicit lambda binders"

-- Both closed instances and construction families publish their complete
-- declared structure result, never the possibly richer aggregate annotation.
-- The pending rule selects the public theorem after its kernel authorization.
prepareRealizationResult
    :: Location -> Binding.PreparedBinding -> Elaboration.ElaboratedClaimEnvelope
    -> Except.ExceptT InstanceError Declaration.LoweringDriver (Registration Planning.PlannedCandidatePosition)
prepareRealizationResult location definition envelope = do
    let arity = fromIntegral (length (Elaboration.elaboratedClaimVariables envelope))
        provider = resultProviderTemplate
            (GlobalSourceProvider (Binding.preparedBindingReference definition))
            (Vector.fromList [TemplateVariable (ViewVariableIx (index - 1)) | index <- reverse [1 .. arity]])
        headers = [(Elaboration.compiledHeaderCore header, Elaboration.compiledHeaderEvidence header)
            | header <- Elaboration.elaboratedClaimAntecedents envelope]
    assertion <- case Elaboration.elaboratedClaimConclusionAssertions envelope of
        [single] -> pure single
        _ -> Except.throwError (ConstructionInvalid location
            "the result must be one checked structure assertion")
    subject <- maybe (Except.throwError (InstanceObligationModelMismatch location)) pure
        (case Notion.sourceAssertionAtom assertion of
            StructureAtomTemplate _head arguments -> arguments Vector.!? 0
            _ -> Nothing)
    (checkedProvider, premises, conclusion) <- Except.liftEither
        (first registrationFailure
            (ProviderResult.prepareWrittenProviderResultRuleTemplates arity headers assertion
                (ProviderResult.definitionProviderResultSubject provider subject)))
    pure (Registration (Planning.plannedEarlierCandidate 1 0) Notion.ConjunctionHere
        (RegisterProviderResult (ProviderResultRule checkedProvider premises conclusion)))
  where
    registrationFailure failure = ConstructionInvalid (failureLocation failure)
        ("provider-result registration: " <> ProviderResult.providerResultErrorReason failure
            <> "; the complete declared structure must have a checked formation representation")
    failureLocation failure = case ProviderResult.providerResultErrorPremise failure of
        Nothing -> location
        Just ordinal -> case drop (fromIntegral ordinal) (Elaboration.elaboratedClaimAntecedents envelope) of
            header : _ -> Elaboration.compiledHeaderLocation header
            [] -> impossible "provider-result error names a nonexistent logical header"

instanceScopeTypes :: InstanceScope -> [CoreType]
instanceScopeTypes (InstanceScope arity _) = replicate (fromIntegral arity) TySet

closeInstanceTarget :: InstanceScope -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
closeInstanceTarget (InstanceScope arity headers) target =
    foldr (const (CForall TySet)) (foldr (CImp . scopedCoreTerm) target headers)
        [1 .. arity]

openInstanceTarget :: InstanceScope -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
openInstanceTarget (InstanceScope arity headers) = dropHeaders headers . dropBinders arity
  where
    dropBinders 0 term = term
    dropBinders remaining (CForall TySet body) = dropBinders (remaining - 1) body
    dropBinders _ _ = impossible "a record consequence lost its explicit parameters"
    dropHeaders [] term = term
    dropHeaders (header : remaining) (CImp premise conclusion)
        | premise == scopedCoreTerm header = dropHeaders remaining conclusion
    dropHeaders _ _ = impossible "a record consequence changed its ordered hypotheses"

resolveInstanceStructure
    :: Location
    -> Raw.StructApplication Raw.Term
    -> Except.ExceptT
        InstanceError
        Declaration.LoweringDriver
        Declaration.ResolvedStructure
resolveInstanceStructure location application = do
    let phrase = Schema.structurePhrase
            (Raw.structApplicationPhrase application)
    Trans.lift
        (Declaration.resolveVisibleStructureLowering phrase)
        >>= maybe
            (Except.throwError (InstanceUnsupported location))
            pure


prepareInstanceObligationTargets
    :: Location
    -> InstanceScope
    -> Declaration.ResolvedStructure
    -> Declaration.ResolvedStructure
    -> ScopedCheckedCore ObjectId
    -> Except.ExceptT
        InstanceError
        Declaration.LoweringDriver
        ( ScopedCheckedCore ObjectId
        , ScopedCheckedCore ObjectId
        , [PreparedStructureDefinition]
        , [(CanonicalTerm ObjectId, Map Schema.RequirementProvenanceKey Schema.RequirementOccurrence)]
        )
prepareInstanceObligationTargets
        location scope structure aggregateStructure fullTarget = do
    let predicate = Declaration.resolvedStructurePredicate structure
    let (headTerm, applicationArguments) =
            canonicalApplicationSpine (openInstanceTarget scope (scopedCoreTerm fullTarget))
        descriptor = Declaration.resolvedStructureSchema structure
        expectedArity =
            fromIntegral
                (Schema.resolvedSchemaParameterCount descriptor)
                + 1
    unless
        ( null (scopedCoreContext fullTarget)
          && scopedCoreType fullTarget == TyProp
          && headTerm == CGlobal predicate
          && length applicationArguments == expectedArity
        )
        (Except.throwError
            (InstanceObligationModelMismatch location))
    (subject, parameters) <- case applicationArguments of
        candidateSubject : candidateParameters ->
            pure (candidateSubject, candidateParameters)
        [] ->
            impossible "a checked structure application has no subject"
    (_openShape, requirements, definitions) <-
        decomposeStructureObligations
            location structure subject parameters
    selectors <- structureSelectors location aggregateStructure
    let mathematical =
            canonicalConjunction (nubOrd (fst <$> requirements))
        exactShape = Record.recordExactShape selectors subject
    shapeTarget <- checkInstanceProposition location (closeInstanceTarget scope exactShape)
    mathematicalTarget <- checkInstanceProposition location (closeInstanceTarget scope mathematical)
    pure
        ( shapeTarget
        , mathematicalTarget
        , nubOrd definitions
        , Map.toAscList (Map.fromListWith Map.union requirements)
        )

-- | Reuse the schema-level aggregate exactness theorem by checked universal
-- elimination.  A concrete structure aggregate is precisely the finite graph
-- obtained by instantiating that theorem with its field values, so invoking an
-- ATP here would only ask it to rediscover a deterministic specialization.
prepareAggregateExactness
    :: Location
    -> InstanceScope
    -> Declaration.ResolvedStructure
    -> [CanonicalTerm ObjectId]
    -> ScopedCheckedCore ObjectId
    -> Except.ExceptT
        InstanceError
        Declaration.LoweringDriver
        PreparedAggregateExactness
prepareAggregateExactness location scope structure values shapeTarget = do
    selectors <- structureSelectors location structure
    genericTarget <-
        checkInstanceProposition location
            (Record.recordSchemaAggregateExactLaw selectors)
    let frozenGeneric =
            fromMaybe
                (impossible
                    "a checked aggregate exactness theorem did not freeze")
                (closeScopedCore genericTarget)
    (fingerprint, indexed) <- Trans.lift
        (Declaration.lookupStructureFactLowering
            (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema structure))
            (Schema.StructureLawFact (Schema.RecordSchemaLaw Record.RecordAggregateExactLaw)))
        >>= maybe (Except.throwError (InstanceAggregateExactnessUnavailable location)) pure
    unless (checkedPropositionTerm indexed == frozenGeneric)
        (Except.throwError (InstanceObligationModelMismatch location))
    specialized <-
        foldM specialize
            (scopedCoreTerm genericTarget)
            values
    unless (specialized == openInstanceTarget scope (scopedCoreTerm shapeTarget))
        (Except.throwError
            (InstanceObligationModelMismatch location))
    pure
        (PreparedAggregateExactness
            fingerprint frozenGeneric values shapeTarget)
  where
    specialize term value =
        case term of
            CForall TySet body ->
                pure (instantiateCanonical value body)
            _ ->
                Except.throwError
                    (InstanceObligationModelMismatch location)


decomposeStructureObligations
    :: Location -> Declaration.ResolvedStructure -> CanonicalTerm ObjectId -> [CanonicalTerm ObjectId]
    -> Except.ExceptT InstanceError Declaration.LoweringDriver
        (CanonicalTerm ObjectId,
            [(CanonicalTerm ObjectId, Map Schema.RequirementProvenanceKey Schema.RequirementOccurrence)],
            [PreparedStructureDefinition])
decomposeStructureObligations location structure subject parameters = do
    let registration = Declaration.resolvedStructureRegistration structure
    application <- maybe (Except.throwError (InstanceObligationModelMismatch location)) pure
        (StructurePredicate.applyStructurePredicate registration subject parameters)
    definition <- resolveStructureDefinitionFact location registration
    pure (StructurePredicate.appliedStructureShape application,
        StructurePredicate.appliedStructureRequirementOccurrences application, [definition])

structureSelectors
    :: Location
    -> Declaration.ResolvedStructure
    -> Except.ExceptT
        InstanceError
        Declaration.LoweringDriver
        [CanonicalTerm ObjectId]
structureSelectors _location structure = pure
    [CGlobal (Schema.resolvedFieldSelector field)
    | field <- Map.elems (Schema.resolvedSchemaFields (Declaration.resolvedStructureSchema structure))]

resolveStructureDefinitionFact
    :: Location -> StructurePredicate.PendingStructureRegistration
    -> Except.ExceptT InstanceError Declaration.LoweringDriver PreparedStructureDefinition
resolveStructureDefinitionFact location registration = do
    let owner = Schema.resolvedSchemaId (StructurePredicate.pendingStructureSchema registration)
        expected = checkedPropositionTerm (StructurePredicate.structurePredicateDefinitionProposition registration)
    (fingerprint, proposition) <- Trans.lift
        (Declaration.lookupStructureFactLowering owner (Schema.StructureResourceFact Schema.PredicateDefinitionResource))
        >>= maybe (Except.throwError (InstanceStructureDefinitionUnavailable location)) pure
    unless (checkedPropositionTerm proposition == expected)
        (Except.throwError (InstanceObligationModelMismatch location))
    pure (PreparedStructureDefinition (StructurePredicate.pendingStructurePredicate registration) fingerprint expected)

checkInstanceProposition
    :: Location
    -> CanonicalTerm ObjectId
    -> Except.ExceptT
        InstanceError
        Declaration.LoweringDriver
        (ScopedCheckedCore ObjectId)
checkInstanceProposition location term = do
    closure <- Trans.lift Declaration.checkedObjectClosureLowering
    let globalTyping = globalTypingFromClosure closure
    checked <-
        either
            (const
                (Except.throwError
                    (InstanceObligationModelMismatch location)))
            pure
            (checkScopedCanonicalCore
                globalTyping
                []
                term)
    unless (scopedCoreType checked == TyProp)
        (Except.throwError
            (InstanceObligationModelMismatch location))
    pure checked

prepareProjectionProofs
    :: Location
    -> InstanceScope
    -> Binding.PreparedBinding
    -> Raw.Block
    -> Elaboration.ElaboratedRecordAggregate
    -> Except.ExceptT InstanceError Declaration.LoweringDriver
        [(Raw.StructSymbol, Proof.PreparedProof)]
prepareProjectionProofs location scope definition source aggregate = do
    let body = scopedCoreTerm (Elaboration.elaboratedAggregateCore aggregate)
    for (Elaboration.elaboratedAggregateFields aggregate) \entry -> do
        let field = Elaboration.elaboratedRecordField entry
            value = Elaboration.elaboratedRecordValue entry
            symbol = Schema.resolvedFieldSymbol field
            projection = CApp (CGlobal (Schema.resolvedFieldProjection field)) body
        target <- checkInstanceProposition location
            (closeInstanceTarget scope (CEq TySet projection (scopedCoreTerm value)))
        prepared <- Trans.lift
            (Proof.prepareGeneratedProofWithTransparentDefinitionTarget
                definition target source)
            >>= either (Except.throwError . InstanceProofFailed) pure
        pure (symbol, prepared)

annotateInstanceValue
    :: Raw.StructApplication Raw.Term
    -> Raw.Expr
    -> Except.ExceptT
        InstanceError
        Declaration.LoweringDriver
        Raw.Expr
annotateInstanceValue application = \case
    Raw.ExprStructAggregate location Nothing entries -> do
        annotation <-
            traverseStructureApplication termExpression application
        pure (Raw.ExprStructAggregate location (Just annotation) entries)
    aggregate@Raw.ExprStructAggregate{} ->
        pure aggregate
    reconstruction@Raw.ExprStructReconstruction{} ->
        pure reconstruction
    expression ->
        Except.throwError
            (InstanceExpectedAggregate (locate expression))
  where
    termExpression = \case
        Raw.TermExpr expression -> pure expression
        term ->
            Except.throwError
                (InstanceParameterRequiresExpression (locate term))

traverseStructureApplication
    :: Applicative f
    => (left -> f right)
    -> Raw.StructApplication left
    -> f (Raw.StructApplication right)
traverseStructureApplication transform
        (Raw.StructApplication phrase arguments) =
    Raw.StructApplication phrase <$> traverse transform arguments

data PreparedInstanceKernelProofs = PreparedInstanceKernelProofs
    !(KernelDerivation ObjectId)
    !(KernelDerivation ObjectId)
    !(KernelDerivation ObjectId)
    ![KernelDerivation ObjectId]

prepareInstanceKernelProofs
    :: CheckedFoundation
    -> GlobalTyping ObjectId
    -> InstanceScope
    -> ObjectId
    -> CanonicalTerm ObjectId
    -> FrozenCheckedCore ObjectId
    -> FrozenCheckedCore ObjectId
    -> FrozenCheckedCore ObjectId
    -> FrozenCheckedCore ObjectId
    -> [CanonicalTerm ObjectId]
    -> [PreparedStructureDefinition]
    -> FrozenCheckedCore ObjectId
    -> FrozenCheckedCore ObjectId
    -> FrozenCheckedCore ObjectId
    -> FrozenCheckedCore ObjectId
    -> [FrozenCheckedCore ObjectId]
    -> [FrozenCheckedCore ObjectId]
    -> Either KernelProof.KernelProofBuildError PreparedInstanceKernelProofs
prepareInstanceKernelProofs
        foundation globalType scope@(InstanceScope arity headers) identity body
        equation mathematical shape aggregateExactness values definitions
        sourceStructure finalStructure sourceExact finalExact
        sourceProjections finalProjections = do
    unless (length sourceProjections == length finalProjections)
        (Left (KernelProof.ProofStructuralCompositionMismatch
            "instance projection targets changed arity"))
    context <- KernelProof.scopedProofContext foundation globalType
        (instanceScopeTypes scope) (reverse headers)
    structure <- prepareStructureDerivation context
    aggregateShape <- prepareAggregateShapeDerivation context
    exactness <- prepareTransportDerivation context sourceExact finalExact
    projections <- traverse (uncurry (prepareTransportDerivation context))
        (zip sourceProjections finalProjections)
    pure (PreparedInstanceKernelProofs structure aggregateShape exactness projections)
  where
    arguments = if arity == 0 then [] else
        [CBound (arity - index - 1) | index <- [0 .. arity - 1]]
    namedValue = foldl' CApp (CGlobal identity) arguments

    closeProof = closeInstanceDerivation scope . KernelProof.builtProofDerivation

    specialize context proof terms = foldM
        (\current value -> KernelProof.scopedTerm context value
            >>= KernelProof.forallEliminationProof context current)
        proof terms

    openImported context index target = do
        imported <- KernelProof.importedProof context (importIx index) target
        specialize context imported arguments

    openConsequence context index target = do
        specialized <- openImported context index target
        foldM (\current header -> KernelProof.hypothesisProof context header
            >>= KernelProof.implicationEliminationProof context current)
            specialized headers

    checkedTarget context target =
        KernelProof.scopedTerm context (openInstanceTarget scope (frozenCoreTerm target))

    prepareAggregateShapeDerivation context = do
        genericProof <- KernelProof.importedProof context (importIx 0) aggregateExactness
        specialized <- specialize context genericProof values
        target <- checkedTarget context shape
        closeProof <$> KernelProof.conversionProof context specialized target

    prepareStructureDerivation context = do
        equationProof <- openImported context 0 equation
        mathematicalProof <- openConsequence context 1 mathematical
        shapeProof <- openConsequence context 2 shape
        definitionProofs <- for (zip [3 :: Natural ..] definitions)
            \(index, PreparedStructureDefinition predicate _fingerprint target) -> do
                proof <- KernelProof.importedProof context (importIx index) target
                pure (predicate, proof)
        sourceTarget <- checkedTarget context sourceStructure
        sourceProof <- KernelProof.transparentPredicateIntroductionProof context
            (Map.fromList definitionProofs) [mathematicalProof, shapeProof] Set.empty sourceTarget
        finalTarget <- checkedTarget context finalStructure
        closeProof <$> transportAcrossInstanceEquation context namedValue body equationProof
            sourceProof finalTarget

    prepareTransportDerivation context source final = do
        equationProof <- openImported context 0 equation
        sourceProof <- openConsequence context 1 source
        finalTarget <- checkedTarget context final
        closeProof <$> transportAcrossInstanceEquation context namedValue body equationProof
            sourceProof finalTarget

closeInstanceDerivation :: InstanceScope -> KernelDerivation ObjectId -> KernelDerivation ObjectId
closeInstanceDerivation (InstanceScope arity headers) derivation =
    closeBinders arity
        (foldl' (flip implicationIntroductionDerivation) derivation (reverse headers))
  where
    closeBinders 0 proof = proof
    closeBinders remaining proof =
        closeBinders (remaining - 1) (forallIntroductionDerivation TySet proof)

transportAcrossInstanceEquation
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> ScopedCheckedCore ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
transportAcrossInstanceEquation
        context identity body equation source finalTarget = do
    reversed <-
        case scopedCoreTerm
                (KernelProof.builtProofStatement equation) of
            CEq TySet actualIdentity actualBody
                | actualIdentity == identity
                , actualBody == body ->
                    KernelProof.equalityReverseProof context equation
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "instance equation does not identify its name with its aggregate")
    abstraction <-
        maybe
            (Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "instance consequence is not the checked name transport of its aggregate proof"))
            pure
            (abstractSetTransport
                body
                identity
                (scopedCoreTerm
                    (KernelProof.builtProofStatement source))
                (scopedCoreTerm finalTarget))
    function <- KernelProof.scopedTerm context abstraction
    functionEquality <-
        KernelProof.equalityReflexivityProof context function
    transportedEquality <-
        KernelProof.equalityCongruenceApplicationProof
            context functionEquality reversed
    sourceApplication <-
        KernelProof.scopedTerm context
            (CApp abstraction body)
    convertedSource <-
        KernelProof.conversionProof
            context source sourceApplication
    transported <-
        KernelProof.equalityModusPonensProof
            context transportedEquality convertedSource
    KernelProof.conversionProof context transported finalTarget

abstractSetTransport
    :: Eq global
    => CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Maybe (CanonicalTerm global)
abstractSetTransport sourceSet targetSet sourceTarget targetTarget = do
    (changed, body) <- go 0 sourceTarget targetTarget
    guard changed
    pure (CLam TySet body)
  where
    go depth source target
        | source == shiftCanonical depth 0 sourceSet
        , target == shiftCanonical depth 0 targetSet =
            Just (True, CBound depth)
        | source == target =
            Just (False, shiftCanonical 1 depth source)
        | otherwise =
            case (source, target) of
                (CApp leftFunction leftArgument,
                    CApp rightFunction rightArgument) ->
                        combine CApp
                            (go depth leftFunction rightFunction)
                            (go depth leftArgument rightArgument)
                (CLam leftType leftBody, CLam rightType rightBody)
                    | leftType == rightType -> do
                        (changed, result) <-
                            go (depth + 1) leftBody rightBody
                        pure (changed, CLam leftType result)
                (CNot leftProposition, CNot rightProposition) -> do
                    (changed, result) <-
                        go depth leftProposition rightProposition
                    pure (changed, CNot result)
                (CAnd leftFirst leftSecond,
                    CAnd rightFirst rightSecond) ->
                        combine CAnd
                            (go depth leftFirst rightFirst)
                            (go depth leftSecond rightSecond)
                (COr leftFirst leftSecond,
                    COr rightFirst rightSecond) ->
                        combine COr
                            (go depth leftFirst rightFirst)
                            (go depth leftSecond rightSecond)
                (CImp leftPremise leftConclusion,
                    CImp rightPremise rightConclusion) ->
                        combine CImp
                            (go depth leftPremise rightPremise)
                            (go depth leftConclusion rightConclusion)
                (CEq leftType leftLeft leftRight,
                    CEq rightType rightLeft rightRight)
                    | leftType == rightType ->
                        combine (CEq leftType)
                            (go depth leftLeft rightLeft)
                            (go depth leftRight rightRight)
                (CForall leftType leftBody,
                    CForall rightType rightBody)
                    | leftType == rightType -> do
                        (changed, result) <-
                            go (depth + 1) leftBody rightBody
                        pure (changed, CForall leftType result)
                (CExists leftType leftBody,
                    CExists rightType rightBody)
                    | leftType == rightType -> do
                        (changed, result) <-
                            go (depth + 1) leftBody rightBody
                        pure (changed, CExists leftType result)
                _ -> Nothing

    combine constructor left right = do
        (leftChanged, checkedLeft) <- left
        (rightChanged, checkedRight) <- right
        pure
            ( leftChanged || rightChanged
            , constructor checkedLeft checkedRight
            )

data CheckedInstanceAuthorization = CheckedInstanceAuthorization
    !ObjectId
    !Proof.CheckedProofAuthorization
    !SemanticFactOccurrenceFingerprint
    ![Proof.CheckedProofAuthorization]
    ![SemanticFactOccurrenceFingerprint]
    !PreparedInstanceKernelProofs

lowerPreparedInstance
    :: PreparedInstance
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration
                CheckedInstanceAuthorization))
lowerPreparedInstance
        (PreparedInstance
            location alias definition body fullTarget proof aggregateExactness
            projectionProofs structureDefinitions scope resultRule) =
    Except.runExceptT do
        let PreparedAggregateExactness
                aggregateExactnessFingerprint
                aggregateExactnessTarget
                aggregateValues
                shapeTarget = aggregateExactness
        let identity = Binding.preparedBindingObjectId definition
            objects = maybeToList (Binding.preparedBindingObject definition)
        baseClosure <-
            Trans.lift Declaration.checkedObjectClosureLowering
        localClosure <-
            Except.liftEither
                (first
                    Declaration.DeclarationObjectValidationFailed
                    (extendObjectClosure baseClosure objects))
        let globalTyping = globalTypingFromClosure localClosure
        equationSpec <-
            Trans.lift
                (Declaration.prepareDefinitionEquationSpecWithEligibilityLowering
                    objects identity SearchIneligible [])
                >>= Except.liftEither
        (proofSpec, proofCandidate, proofAuthorization) <-
            Trans.lift
                (Proof.lowerPreparedProofCandidate
                    objects SearchIneligible [] proof)
                >>= Except.liftEither
        shapeSpec <-
            Trans.lift
                (Declaration.prepareCandidateSpecLowering
                    objects shapeTarget SearchIneligible [])
                >>= Except.liftEither
        loweredProjections <-
            for projectionProofs \(_fieldRole, projectionProof) ->
                Trans.lift
                    (Proof.lowerPreparedProofCandidate
                        objects SearchIneligible [] projectionProof)
                    >>= Except.liftEither
        let projectionSpecs =
                [ spec
                | (spec, _candidate, _authorization) <- loweredProjections
                ]
            projectionCandidates =
                [ candidate
                | (_spec, candidate, _authorization) <- loweredProjections
                ]
            projectionAuthorizations =
                [ authorization
                | (_spec, _candidate, authorization) <- loweredProjections
                ]
        finalTarget <- rebindInstanceTarget scope definition body fullTarget
        finalStructureSpec <-
            Trans.lift
                (Declaration.prepareCandidateSpecLowering
                    objects finalTarget SearchEligible [alias])
                >>= Except.liftEither
        finalProjectionTargets <-
            traverse (rebindProjectionTarget scope definition body . snd) projectionProofs
        finalProjectionSpecs <-
            for (zip (fst <$> projectionProofs) finalProjectionTargets) \(symbol, target) ->
                Trans.lift
                    (Declaration.prepareCandidateSpecLowering
                        objects target SearchEligible
                        [ instanceConsequenceAlias alias ("projection_" <> Raw.unStructSymbol symbol)
                        ])
                    >>= Except.liftEither
        finalExactTarget <-
            rebindTransparentTarget scope definition body
                shapeTarget
        finalExactSpec <-
            Trans.lift
                (Declaration.prepareCandidateSpecLowering
                    objects finalExactTarget SearchEligible
                    [instanceConsequenceAlias alias "shape"])
                >>= Except.liftEither
        let sourceStructureTarget =
                fromMaybe
                    (impossible "a closed instance target did not freeze")
                    (closeScopedCore fullTarget)
        foundation <-
            Trans.lift Declaration.currentFoundationLowering
        kernelProofs <-
            Except.liftEither
                (first
                    (Declaration.ProofObligationFailedAt location
                        . Declaration.KernelProofBuildFailed)
                    (prepareInstanceKernelProofs
                        foundation
                        globalTyping
                        scope
                        identity
                        body
                        (Declaration.candidateSpecTarget equationSpec)
                        (Declaration.candidateSpecTarget proofSpec)
                        (Declaration.candidateSpecTarget shapeSpec)
                        aggregateExactnessTarget
                        aggregateValues
                        structureDefinitions
                        sourceStructureTarget
                        (Declaration.candidateSpecTarget finalStructureSpec)
                        (Declaration.candidateSpecTarget shapeSpec)
                        (Declaration.candidateSpecTarget finalExactSpec)
                        (Declaration.candidateSpecTarget
                            <$> projectionSpecs)
                        (Declaration.candidateSpecTarget
                            <$> finalProjectionSpecs)))
        let equationCandidate =
                Declaration.checkedCandidate
                    equationSpec
                    (Declaration.checkedDefinitionEquationPlanning identity)
            shapeCandidate =
                Declaration.checkedCandidate
                    shapeSpec
                    (Declaration.checkedNoExternalSourceProofPlanningWithFacts
                        [aggregateExactnessFingerprint] [])
            finalStructureCandidate =
                Declaration.checkedCandidate
                    finalStructureSpec
                    (Declaration.checkedNoExternalSourceProofPlanningWithFacts
                        (preparedStructureDefinitionFingerprint
                            <$> structureDefinitions)
                        [ Planning.plannedEarlierCandidate 0 0
                        , Planning.plannedEarlierCandidate 0 1
                        , Planning.plannedEarlierCandidate 0 2
                        ])
            finalProjectionCandidates =
                [ Declaration.checkedCandidate
                    spec
                    (Declaration.checkedNoExternalSourceProofPlanning
                        [ Planning.plannedEarlierCandidate 0 0
                        , Planning.plannedEarlierCandidate
                            0 (fromIntegral (index + 3))
                        ])
                | (index, spec) <-
                    zip [0 :: Int ..] finalProjectionSpecs
                ]
            finalExactCandidate =
                Declaration.checkedCandidate
                    finalExactSpec
                    (Declaration.checkedNoExternalSourceProofPlanning
                        [ Planning.plannedEarlierCandidate 0 0
                        , Planning.plannedEarlierCandidate 0 2
                        ])
            syntax = instanceSyntaxId definition proof finalTarget
        pure
            (Declaration.checkedCompiledDeclarationWithRegistrations
                syntax
                objects
                []
                [Binding.preparedBindingDeclaration definition]
                Nothing
                [resultRule]
                [ equationCandidate
                    :| (proofCandidate : shapeCandidate : projectionCandidates)
                , finalStructureCandidate
                    :| (finalExactCandidate : finalProjectionCandidates)
                ]
                (CheckedInstanceAuthorization
                    identity
                    proofAuthorization
                    aggregateExactnessFingerprint
                    projectionAuthorizations
                    (preparedStructureDefinitionFingerprint
                        <$> structureDefinitions)
                    kernelProofs))

preparedStructureDefinitionFingerprint
    :: PreparedStructureDefinition
    -> SemanticFactOccurrenceFingerprint
preparedStructureDefinitionFingerprint
        (PreparedStructureDefinition _predicate fingerprint _target) =
    fingerprint

-- Public consequences of a named instance need stable source names now that
-- ATP use is premise-explicit.  Concatenated suffixes follow the existing
-- generated structure-fact convention (for example @fooshape@ and
-- @fooprojection0@).
instanceConsequenceAlias :: SemanticName -> Text -> SemanticName
instanceConsequenceAlias alias suffix =
    semanticName (semanticNameText alias <> suffix)

rebindTransparentTarget
    :: InstanceScope
    -> Binding.PreparedBinding
    -> CanonicalTerm ObjectId
    -> ScopedCheckedCore ObjectId
    -> Except.ExceptT
        Declaration.DeclarationError
        Declaration.LoweringDriver
        (ScopedCheckedCore ObjectId)
rebindTransparentTarget scope definition body sourceTarget = do
    let identity = instanceNamedValue scope definition
        (changed, finalTerm) =
            replaceTransparentBody identity body 0
                (openInstanceTarget scope (scopedCoreTerm sourceTarget))
    unless changed
        (impossible "an instance consequence lost its transparent body")
    checkReboundTarget
        definition
        (scopedCoreContext sourceTarget)
        (closeInstanceTarget scope finalTerm)

replaceTransparentBody
    :: Eq global
    => CanonicalTerm global
    -> CanonicalTerm global
    -> Natural
    -> CanonicalTerm global
    -> (Bool, CanonicalTerm global)
replaceTransparentBody identity body depth term
    | term == shiftCanonical depth 0 body =
        (True, shiftCanonical depth 0 identity)
    | otherwise =
        case term of
            CBound index -> (False, CBound index)
            CGlobal global -> (False, CGlobal global)
            CIntrinsic intrinsic -> (False, CIntrinsic intrinsic)
            CLogicalSelect coreType -> (False, CLogicalSelect coreType)
            COpaqueInteger integer -> (False, COpaqueInteger integer)
            CApp function argument ->
                combine CApp
                    (replaceTransparentBody identity body depth function)
                    (replaceTransparentBody identity body depth argument)
            CLam binderType lambdaBody ->
                let (changed, rebound) =
                        replaceTransparentBody
                            identity body (depth + 1) lambdaBody
                in (changed, CLam binderType rebound)
            CFalsum -> (False, CFalsum)
            CTruth -> (False, CTruth)
            CNot proposition ->
                let (changed, rebound) =
                        replaceTransparentBody
                            identity body depth proposition
                in (changed, CNot rebound)
            CAnd left right ->
                combine CAnd
                    (replaceTransparentBody identity body depth left)
                    (replaceTransparentBody identity body depth right)
            COr left right ->
                combine COr
                    (replaceTransparentBody identity body depth left)
                    (replaceTransparentBody identity body depth right)
            CImp premise conclusion ->
                combine CImp
                    (replaceTransparentBody identity body depth premise)
                    (replaceTransparentBody identity body depth conclusion)
            CEq operandType left right ->
                combine (CEq operandType)
                    (replaceTransparentBody identity body depth left)
                    (replaceTransparentBody identity body depth right)
            CForall binderType quantifiedBody ->
                let (changed, rebound) =
                        replaceTransparentBody
                            identity body (depth + 1) quantifiedBody
                in (changed, CForall binderType rebound)
            CExists binderType quantifiedBody ->
                let (changed, rebound) =
                        replaceTransparentBody
                            identity body (depth + 1) quantifiedBody
                in (changed, CExists binderType rebound)
  where
    combine constructor (leftChanged, left) (rightChanged, right) =
        (leftChanged || rightChanged, constructor left right)

rebindInstanceTarget
    :: InstanceScope
    -> Binding.PreparedBinding
    -> CanonicalTerm ObjectId
    -> ScopedCheckedCore ObjectId
    -> Except.ExceptT
        Declaration.DeclarationError
        Declaration.LoweringDriver
        (ScopedCheckedCore ObjectId)
rebindInstanceTarget scope definition body sourceTarget = do
    let identity = instanceNamedValue scope definition
        sourceTerm = openInstanceTarget scope (scopedCoreTerm sourceTarget)
        (headTerm, arguments) = canonicalApplicationSpine sourceTerm
        finalTerm = case arguments of
            subject : parameters
                | subject == body ->
                    foldl' CApp headTerm (identity : parameters)
                | otherwise ->
                    impossible
                        "an instance proof target lost its transparent subject"
            [] ->
                impossible "an instance proof target is not an application"
        context = scopedCoreContext sourceTarget
    checkReboundTarget definition context (closeInstanceTarget scope finalTerm)

instanceNamedValue :: InstanceScope -> Binding.PreparedBinding -> CanonicalTerm ObjectId
instanceNamedValue (InstanceScope arity _) definition =
    foldl' CApp (CGlobal (Binding.preparedBindingObjectId definition))
        (if arity == 0 then [] else [CBound (arity - index - 1) | index <- [0 .. arity - 1]])

rebindProjectionTarget
    :: InstanceScope
    -> Binding.PreparedBinding
    -> CanonicalTerm ObjectId
    -> Proof.PreparedProof
    -> Except.ExceptT
        Declaration.DeclarationError
        Declaration.LoweringDriver
        (ScopedCheckedCore ObjectId)
rebindProjectionTarget scope definition body proof = do
    let identity = instanceNamedValue scope definition
        sourceTarget = Proof.preparedProofTarget proof
        sourceTerm = openInstanceTarget scope (scopedCoreTerm sourceTarget)
        finalTerm = case sourceTerm of
            CEq operandType left right ->
                let (headTerm, arguments) = canonicalApplicationSpine left
                    reboundLeft = case arguments of
                        subject : parameters
                            | subject == body ->
                                foldl' CApp headTerm
                                    (identity : parameters)
                            | otherwise ->
                                impossible
                                    "an instance projection proof lost its transparent subject"
                        [] ->
                            impossible
                                "an instance projection target is not an application"
                in CEq operandType reboundLeft right
            _ ->
                impossible "an instance projection target is not an equality"
    checkReboundTarget
        definition
        (scopedCoreContext sourceTarget)
        (closeInstanceTarget scope finalTerm)

checkReboundTarget
    :: Binding.PreparedBinding
    -> [CoreType]
    -> CanonicalTerm ObjectId
    -> Except.ExceptT
        Declaration.DeclarationError
        Declaration.LoweringDriver
        (ScopedCheckedCore ObjectId)
checkReboundTarget definition context finalTerm = do
    unless (null context)
        (impossible "a closed named instance acquired local binders")
    baseClosure <- Trans.lift Declaration.checkedObjectClosureLowering
    closure <-
        Except.liftEither
            (first
                Declaration.DeclarationObjectValidationFailed
                (extendObjectClosure
                    baseClosure
                    (maybeToList (Binding.preparedBindingObject definition))))
    let globalTyping = globalTypingFromClosure closure
    pure
        (either
            (impossible
                . ("a type-preserving instance target rewrite failed: " <>)
                . show)
            id
            (checkScopedCanonicalCore
                globalTyping
                context
                finalTerm))

instanceSyntaxId
    :: Binding.PreparedBinding
    -> Proof.PreparedProof
    -> ScopedCheckedCore ObjectId
    -> DeclarationSyntaxId
instanceSyntaxId definition proof target =
    declarationSyntaxId
        (encodeCache do
            putCacheTag 0x00
            putSemanticGlobalKeyCache
                (Binding.preparedBindingGlobalKey definition)
            putObjectIdCache (Binding.preparedBindingObjectId definition)
            putCanonicalTermCache putObjectIdCache
                (scopedCoreTerm target)
            putCacheDigest
                (proofSyntaxIdDigest
                    (Proof.preparedProofSyntaxId proof)))

authorizeCheckedInstance
    :: CheckedInstanceAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedInstance
        (CheckedInstanceAuthorization
            identity proofAuthorization aggregateExactnessFingerprint
            projectionAuthorizations
            definitionFingerprints
            (PreparedInstanceKernelProofs
                structureDerivation aggregateShapeDerivation
                exactnessDerivation
                projectionDerivations)) = \case
    [ equation :| (proof : shape : projectionProofs)
      , theorem :| (exactness : projectionTheorems)
      ]
        | length projectionProofs == length projectionAuthorizations
            && length projectionTheorems == length projectionAuthorizations
            && length projectionDerivations
                == length projectionAuthorizations -> do
            Declaration.authorizeDefinitionEquationCandidate identity equation
            Proof.authorizeCheckedProofCandidate
                proofAuthorization proof
            Declaration.authorizeKernelProofCandidate shape do
                void
                    (Declaration.useAuthorizedFact
                        aggregateExactnessFingerprint)
                pure aggregateShapeDerivation
            sequence_
                [ Proof.authorizeCheckedProofCandidate
                    authorization candidate
                | (authorization, candidate) <-
                    zip projectionAuthorizations projectionProofs
                ]
            Declaration.authorizeKernelProofCandidate theorem do
                void (Declaration.useStagedCandidate equation)
                void (Declaration.useStagedCandidate proof)
                void (Declaration.useStagedCandidate shape)
                traverse_
                    (void . Declaration.useAuthorizedFact)
                    definitionFingerprints
                pure structureDerivation
            Declaration.authorizeKernelProofCandidate exactness do
                void (Declaration.useStagedCandidate equation)
                void (Declaration.useStagedCandidate shape)
                pure exactnessDerivation
            sequence_
                [ Declaration.authorizeKernelProofCandidate theoremCandidate do
                    void (Declaration.useStagedCandidate equation)
                    void (Declaration.useStagedCandidate proofCandidate)
                    pure derivation
                | (theoremCandidate, proofCandidate, derivation) <-
                    zip3
                        projectionTheorems
                        projectionProofs
                        projectionDerivations
                ]
    stages ->
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                2 (length stages))
