{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Preparation, lowering, and authorization of source-level bindings.
module Felix.Checking.Binding
    ( PreparedBinding
    , preparedBindingLocation
    , preparedBindingGlobalKey
    , preparedBindingReference
    , preparedBindingLabel
    , preparedBindingGlobalTarget
    , preparedBindingDeclaration
    , preparedBindingObjectId
    , preparedBindingObject
    , preparedBindingObjectContent
    , TransparentBindingView
    , transparentBindingBody
    , preparedBindingTransparentView
    , elaborateClaimEnvelopeWithTransparentBinding
    , preparedBindingSyntaxId
    , preparedBindingIsDefinition
    , prepareBinding
    , lowerPreparedBinding
    , CheckedBindingAuthorization
    , authorizeCheckedBinding
    ) where

import Base hiding (Empty)
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Planning qualified as Planning
import Felix.Cache.Codec
import Felix.Checking.Core
import Felix.Checking.Authority (KernelConstructionDescriptor(..))
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration
import Felix.Checking.Elaboration.Vocabulary
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation
    ( ImportIx
    , KernelDerivation
    , derivationImportJudgement
    , conjunctionLeftEliminationDerivation
    , conjunctionRightEliminationDerivation
    , equalityModusPonensDerivation
    , forallIntroductionDerivation
    , forallEliminationDerivation
    , implicationIntroductionDerivation
    , importedFactDerivation
    , localHypothesisDerivation
    , hypothesisIx
    , hypothesisIxValue
    , importIx
    , importIxValue
    , remapDerivationExternalHypotheses
    , remapKernelDerivationImports
    )
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Notion.Diagnostics qualified as FormationDiagnostics
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.SourceTemplate qualified as SourceTemplate
import Felix.Checking.Semantic
import Felix.Checking.SetConstruction
import Felix.Module
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface (CanonicalLexicalEntry(..))

import Data.Functor.Identity (runIdentity)
import Data.Bifunctor (first)
import Control.Monad.Except (ExceptT)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Except qualified as Except
import Control.Monad (unless, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class qualified as Trans
import Data.ByteString (ByteString)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


data BindingHead = BindingHead
    !SemanticGlobalKey
    ![Raw.VarSymbol]
    !CoreType

data PreparedBindingBody
    = OpaqueBody
    | TransparentBody
        !(CanonicalTerm ObjectId)
        !(Maybe ElaboratedSetConstruction)
    | ContextualTransparentBody
        !(Map.Map Raw.StructSymbol (FieldId, ObjectId))
        !(CanonicalTerm ObjectId)

data BindingFamily
    = SignatureBinding
    | AbbreviationBinding
    | DefinitionBinding
    deriving stock (Show, Eq, Ord)

data PreparedBindingPayload
    = PreparedSignaturePayload
    | PreparedAbbreviationPayload !AbbreviationExpansion
    | PreparedDefinitionPayload
        { preparedDefinitionPayloadAlias :: !SemanticName
        , preparedDefinitionPayloadConstruction
            :: !(Maybe ElaboratedSetConstruction)
        , preparedDefinitionPayloadContract :: !(Maybe FormationContract)
        , preparedDefinitionPayloadBaseProjections
            :: ![DefinitionBaseProjection]
        , preparedDefinitionPayloadResults
            :: !(Maybe PreparedDefinitionResults)
        }

data PreparedBinding = PreparedBinding
    { preparedBindingLocation :: !Location
    , preparedBindingGlobalKey :: !SemanticGlobalKey
    , preparedBindingLabel :: !SemanticBindingLabel
    , preparedBindingGlobalTarget :: !SemanticGlobalTarget
    , preparedBindingObjectContent :: !ObjectContent
    , preparedBindingAssertedObject :: !AssertedObject
    , preparedBindingObject :: !(Maybe AssertedObject)
    , preparedBindingDeclarationSlot :: !DeclarationSlot
    , preparedBindingSyntaxId :: !DeclarationSyntaxId
    , preparedBindingPayload :: !PreparedBindingPayload
    }

preparedBindingObjectId :: PreparedBinding -> ObjectId
preparedBindingObjectId =
    semanticGlobalTargetObject . preparedBindingGlobalTarget

-- All publishers retain the metadata admitted with the binding. Elaboration
-- distinguishes definition contracts from construction result hypotheses.
preparedBindingDeclaration :: PreparedBinding -> SemanticGlobalBinding
preparedBindingDeclaration prepared = semanticGlobalBindingWithMetadata
    (preparedBindingGlobalKey prepared)
    (preparedBindingLabel prepared)
    (preparedBindingGlobalTarget prepared)
    (case preparedBindingPayload prepared of
        PreparedDefinitionPayload{preparedDefinitionPayloadContract = contract} -> contract
        _ -> Nothing)
    (case preparedBindingPayload prepared of
        PreparedAbbreviationPayload expansion -> Just expansion
        _ -> Nothing)

data TransparentBindingView = TransparentBindingView
    { transparentBindingLocation :: !Location
    , transparentBindingGlobalKey :: !SemanticGlobalKey
    , transparentBindingAssertedObject :: !AssertedObject
    , transparentBindingBody :: !(CanonicalTerm ObjectId)
    }

preparedBindingTransparentView
    :: PreparedBinding
    -> Either ElaborationError TransparentBindingView
preparedBindingTransparentView prepared =
    case preparedBindingObjectContent prepared of
        TransparentObjectContent _theory _coreType body -> do
            let asserted = preparedBindingAssertedObject prepared
            unless
                ( assertedObjectId asserted == preparedBindingObjectId prepared
                  && assertedObjectContent asserted
                        == preparedBindingObjectContent prepared
                )
                (Left
                    (ElaborationUnsupportedDeclaration
                        (preparedBindingLocation prepared)))
            pure
                TransparentBindingView
                    { transparentBindingLocation =
                        preparedBindingLocation prepared
                    , transparentBindingGlobalKey =
                        preparedBindingGlobalKey prepared
                    , transparentBindingAssertedObject = asserted
                    , transparentBindingBody = body
                    }
        _ ->
            Left
                (ElaborationUnsupportedDeclaration
                    (preparedBindingLocation prepared))

elaborateClaimEnvelopeWithTransparentBinding
    :: TransparentBindingView
    -> [Raw.Asm]
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedClaimEnvelope)
elaborateClaimEnvelopeWithTransparentBinding view =
    elaborateClaimEnvelopeWithLocalTransparentObject
        (transparentBindingLocation view)
        (transparentBindingGlobalKey view)
        (transparentBindingAssertedObject view)

preparedBindingIsDefinition :: PreparedBinding -> Bool
preparedBindingIsDefinition prepared =
    case preparedBindingPayload prepared of
        PreparedDefinitionPayload{} -> True
        _ -> False

preparedBindingReference :: PreparedBinding -> GlobalBindingRef
preparedBindingReference prepared =
    globalBindingRef (preparedBindingDeclarationSlot prepared)
        (preparedBindingGlobalKey prepared)

prepareBinding
    :: Raw.Block
    -> [CanonicalLexicalEntry]
    -> Declaration.LoweringDriver
        (Either ElaborationError PreparedBinding)
prepareBinding block entries =
    Except.runExceptT do
        entry <-
            case entries of
                [] -> Except.throwError
                    (ElaborationDeclarationOccurrenceMissing (locate block))
                [single] -> pure single
                _ -> Except.throwError
                    (ElaborationDeclarationOccurrenceAmbiguous (locate block))
        surfaceKey <-
            maybe
                (Except.throwError
                    (ElaborationUnsupportedDeclaration (locate block)))
                pure
                (semanticGlobalKeyFromLexicalEntry entry)
        key <- classifyBindingKey block surfaceKey
        (head', family, rawBody) <-
            prepareHead block key
        let BindingHead preparedKey _parameters _coreType = head'
        when
            (isJust (fixedSemanticMeaning preparedKey))
            (Except.throwError
                (ElaborationFixedSemanticCollision
                    (locate block) preparedKey))
        visible <- Trans.lift
            (Declaration.resolveVisibleGlobalLowering preparedKey)
        when
            (isJust visible)
            (Except.throwError
                (ElaborationGlobalAlreadyVisible
                    (locate block) preparedKey))
        slot <- Trans.lift Declaration.nextDeclarationSlotLowering
        theory <- Trans.lift Declaration.currentTheoryLowering
        baseClosure <-
            Trans.lift Declaration.checkedObjectClosureLowering
        let baseGlobalTyping = globalTypingFromClosure baseClosure
        (body, contract, baseProjections, preparedResults,
            bodySource, expansionAllowance) <-
            case rawBody of
                Nothing ->
                    pure (OpaqueBody, Nothing, [], Nothing, Nothing, formationMaximumExpansionWork)
                Just buildBody -> do
                    initialElaboration <- Trans.lift
                        (initialElaborationStateLowering
                            baseClosure emptyElaborationContext)
                    (CompiledBody canonical rawConstruction rawProposition,
                        finalElaboration) <-
                        State.runStateT
                            ( setElaborationDefinitionProvider
                                (globalBindingRef slot preparedKey)
                              >> when (family == AbbreviationBinding) beginAbbreviationExpansion
                              >> buildBody
                            )
                            initialElaboration
                    let BindingHead _semanticKey parameters _coreType = head'
                    construction <-
                        Except.liftEither
                            (traverse
                                (checkElaboratedNamedSetConstruction
                                    finalElaboration
                                    (replicate (length parameters) TySet))
                                rawConstruction)
                    traverse_
                        (\checkedConstruction ->
                            unless
                                (frozenCoreTerm
                                    (preparedSetConstructionClosedBody
                                        checkedConstruction)
                                    == canonical)
                                (impossible
                                    "exact named construction disagrees with its transparent body"))
                        construction
                    let requirements =
                            elaborationRequiredContextualFields finalElaboration
                        body
                            | Map.null requirements =
                                TransparentBody canonical construction
                            | family == AbbreviationBinding =
                                ContextualTransparentBody
                                    requirements
                                    (CLam TySet canonical)
                            | otherwise =
                                impossible
                                    "a non-abbreviation acquired contextual requirements"
                    pure
                        ( body
                        , elaborationFormationContract finalElaboration
                        , elaborationDefinitionBaseProjections finalElaboration
                        , elaborationDefinitionResults finalElaboration
                        , rawProposition
                        , fromMaybe formationMaximumExpansionWork (elaborationExpansionAllowance finalElaboration)
                        )
        let BindingHead semanticKey _parameters coreType = head'
        unless (semanticKey == preparedKey)
            (Except.throwError
                (ElaborationDeclarationHeadMismatch (locate block)))
        let alias = definitionAlias block
            -- The same object checks and identity format serve ordinary
            -- definitions and bounded abbreviation preparation.
            prepareObject
                :: Monad m
                => (CanonicalTerm ObjectId -> m (Either ElaborationError (ScopedCheckedCore ObjectId)))
                -> (CoreType -> CanonicalTerm ObjectId -> m AssertedObject)
                -> m (Either ElaborationError (SemanticGlobalTarget, AssertedObject))
            prepareObject check make = Except.runExceptT $ case body of
                OpaqueBody -> do
                    let seed = opaqueDeclarationSeed (declarationSlotModule slot)
                            (declarationSlotOrdinal slot) SignatureDeclaration (generatedObjectSlot 0)
                        object = opaqueObject theory seed coreType
                    pure (GlobalReference (assertedObjectId object), object)
                TransparentBody canonical _ -> transparent
                    (if family == AbbreviationBinding then TransparentExpansion else GlobalReference)
                    coreType canonical
                ContextualTransparentBody requirements canonical -> transparent
                    (\identity -> ContextualTransparentExpansion identity requirements)
                    (TyArrow TySet coreType) canonical
              where
                transparent target expected canonical = do
                    checked <- Except.ExceptT (check canonical)
                    unless (scopedCoreType checked == expected)
                        (Except.throwError (ElaborationObjectTypeMismatch (locate block) expected (scopedCoreType checked)))
                    object <- Trans.lift (make expected canonical)
                    pure (target (assertedObjectId object), object)
        (target, freshObject, payload, syntax) <- case family of
            AbbreviationBinding -> do
                source <- maybe (impossible "an abbreviation discarded its compiled body") pure bodySource
                let contextual = case body of ContextualTransparentBody{} -> True; _ -> False
                    finish = Except.runExceptT do
                        (target, object) <- Except.ExceptT (prepareObject
                            (\canonical -> Right <$> atExpansionPath "body/type" (expansionCoreWork (\work ->
                                countedCheckScopedCanonicalCore baseGlobalTyping work [] canonical)))
                            (\ty canonical -> atExpansionPath "body/identity" (transparentObjectWith (chargeExpansion 1) theory ty canonical)))
                        expansion <- Trans.lift (atExpansionPath "body/evidence" (prepareExpansion head' contextual source))
                        bytes <- Trans.lift (atExpansionPath "body/encoding" (encodePreparedSyntaxWith (chargeExpansion 1)
                            family head' body alias preparedResults (Just expansion)))
                        let syntax = declarationSyntaxId bytes
                        syntax `seq` pure (target, object, PreparedAbbreviationPayload expansion, syntax)
                (result, remaining) <- Trans.lift (Declaration.withFormationPhaseLowering
                    FormationDiagnostics.DeclarationPreparation (runExpansionWork expansionAllowance finish))
                recorder <- Trans.lift Declaration.formationRecorderLowering
                let used = fromIntegral (expansionAllowance - remaining)
                    total = fromIntegral (formationMaximumExpansionWork - remaining)
                    rejected = case result of Left failure | Just amount <- expansionRejectedDebit failure -> [("expansion.rejected", amount)]; _ -> []
                liftIO (FormationDiagnostics.recordMeasurement recorder FormationDiagnostics.emptyMeasurement
                    { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countPhaseWork
                        FormationDiagnostics.DeclarationPreparation used FormationDiagnostics.emptyDiagnostics
                    , FormationDiagnostics.limitHighWater = Map.fromList
                        ([("expansion.cap", fromIntegral formationMaximumExpansionWork), ("expansion.used", total)] <> rejected) })
                either (Except.throwError . ElaborationExpansionFailed (locate block) preparedKey)
                    Except.liftEither result
            _ -> do
                (target, object) <- Except.liftEither (runIdentity (prepareObject
                    (pure . first (ElaborationCoreCheckFailed (locate block)) . checkScopedCanonicalCore baseGlobalTyping [])
                    (\ty canonical -> pure (transparentObject theory ty canonical))))
                let payload = case family of
                        SignatureBinding -> PreparedSignaturePayload
                        DefinitionBinding -> PreparedDefinitionPayload
                            { preparedDefinitionPayloadAlias = fromMaybe (impossible "a definition has no semantic alias") alias
                            , preparedDefinitionPayloadConstruction = case body of
                                TransparentBody _ construction -> construction
                                _ -> Nothing
                            , preparedDefinitionPayloadContract = contract
                            , preparedDefinitionPayloadBaseProjections = baseProjections
                            , preparedDefinitionPayloadResults = preparedResults
                            }
                pure (target, object, payload, declarationSyntaxId
                    (encodePreparedSyntax family head' body alias preparedResults Nothing))
        let targetObject = semanticGlobalTargetObject target
            content = assertedObjectContent freshObject
        available <- Trans.lift (Declaration.objectAvailableLowering targetObject)
        let asserted = if available then Nothing else Just freshObject
        pure
            PreparedBinding
                { preparedBindingLocation = locate block
                , preparedBindingGlobalKey = preparedKey
                , preparedBindingLabel = declarationBindingLabel block
                , preparedBindingGlobalTarget = target
                , preparedBindingObjectContent = content
                , preparedBindingAssertedObject = freshObject
                , preparedBindingObject = asserted
                , preparedBindingDeclarationSlot = slot
                , preparedBindingSyntaxId = syntax
                , preparedBindingPayload = payload
                }

prepareExpansion
    :: Monad m => BindingHead -> Bool -> CompiledBodySource
    -> ExpansionWork m AbbreviationExpansion
prepareExpansion (BindingHead _ parameters _) contextual = \case
    CompiledTermBody term -> TermExpansion <$> SourceTemplate.abstractSourceTerm layout 0 term
    CompiledPropositionBody proposition -> SourceTemplate.abstractSourceProposition layout
        (compiledPropositionEvidence proposition) (compiledPropositionEqualities proposition)
  where
    arity = fromIntegral (length parameters)
    layout = Vector.fromList (reverse (take (length parameters) [0..]) <> [arity | contextual])

classifyBindingKey
    :: Raw.Block
    -> SemanticGlobalKey
    -> ExceptT
        ElaborationError
        Declaration.LoweringDriver
        SemanticGlobalKey
classifyBindingKey block surfaceKey =
    case block of
        Raw.BlockDefn _location _title _marker
                (Raw.Defn assumptions
                    (Raw.DefnAdj subject (Raw.Adj _ item _arguments))
                    _statement) -> do
            let matchingStructures =
                    [ ()
                    | Raw.AsmLetStruct variables _structurePhrase <- assumptions
                    , variable <- toList variables
                    , variable == subject
                    ]
            when (length matchingStructures > 1)
                (Except.throwError
                    (ElaborationGuardedTransparentDefinition (locate subject)))
            pure
                (semanticAdjectiveKey
                    (if null matchingStructures
                        then OrdinaryAdjectiveReading
                        else StructureAdjectiveReading)
                    (Raw.adjectiveLexicalSide item)
                    (Raw.adjectiveLexicalPattern item))
        _ -> pure surfaceKey

data PreparedBindingProjection = PreparedBindingProjection
    !Declaration.CandidateSpec
    !(Registration Planning.PlannedCandidatePosition)
    !KernelConstructionDescriptor
    !(ImportIx -> KernelDerivation ObjectId)

data PreparedBindingResultCandidate = PreparedBindingResultCandidate
    !Declaration.CandidateSpec
    !(Registration Planning.PlannedCandidatePosition)
    !CheckedBindingResultAuthorization

data CheckedBindingResultAuthorization = CheckedBindingResultAuthorization
    !(Vector SemanticFactOccurrenceFingerprint)
    !(Vector ImportIx -> ImportIx -> KernelDerivation ObjectId)

lowerPreparedBinding
    :: PreparedBinding
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration CheckedBindingAuthorization))
lowerPreparedBinding prepared = do
    baseClosure <- Declaration.checkedObjectClosureLowering
    case extendObjectClosure baseClosure objects of
        Left failure ->
            pure (Left (Declaration.DeclarationObjectValidationFailed failure))
        Right closure ->
            lowerPreparedBindingWith
                (globalTypingFromClosure closure)
                prepared
  where
    objects = maybeToList (preparedBindingObject prepared)

lowerPreparedBindingWith
    :: GlobalTyping ObjectId
    -> PreparedBinding
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration CheckedBindingAuthorization))
lowerPreparedBindingWith globalTyping prepared =
    case preparedBindingPayload prepared of
        PreparedSignaturePayload ->
            pure
                (Right
                    (checked binding [] [] []
                        (CheckedBindingAuthorization
                            CheckedBindingNone Nothing)))
        PreparedAbbreviationPayload _ ->
            pure
                (Right
                    (checked binding [] [] []
                        (CheckedBindingAuthorization
                            CheckedBindingNone Nothing)))
        PreparedDefinitionPayload
                { preparedDefinitionPayloadAlias = alias
                , preparedDefinitionPayloadConstruction = preparedConstruction
                , preparedDefinitionPayloadBaseProjections = baseProjections
                , preparedDefinitionPayloadResults = preparedResults
                } -> case preparedConstruction of
            Nothing ->
                Except.runExceptT do
                    equation <-
                        Trans.lift
                            (Declaration.prepareDefinitionEquationSpecLowering
                                objects identity alias)
                            >>= Except.liftEither
                    projections <-
                        traverse prepareDefinitionProjection
                            (zip [0 :: Natural ..]
                                baseProjections)
                    let equationStage =
                            Declaration.checkedCandidate
                                equation
                                (Declaration.checkedDefinitionEquationPlanning
                                    identity)
                                :| []
                        projectionStage =
                            NonEmpty.nonEmpty
                                [ Declaration.checkedCandidate
                                    spec
                                    (Declaration.checkedKernelPlanningWithStaged descriptor []
                                        [Planning.plannedEarlierCandidate 0 0])
                                | PreparedBindingProjection
                                    spec _pending descriptor _derivation <- projections
                                ]
                        baseStages = equationStage : maybeToList projectionStage
                        pendingViews =
                            [ pending
                            | PreparedBindingProjection
                                _spec pending _descriptor _derivation <- projections
                            ]
                        derivations =
                            [ (descriptor, buildDerivation)
                            | PreparedBindingProjection
                                _spec _pending descriptor buildDerivation <- projections
                            ]
                    results <- traverse
                        (prepareDefinitionResultCandidates
                            (fromIntegral (length baseStages)))
                        preparedResults
                    pure
                        (checked
                            binding
                            pendingViews
                            (maybe [] preparedResultsPending results)
                            (baseStages <> maybeToList
                                (preparedResultsStage <$> results))
                            (CheckedBindingAuthorization
                                (CheckedBindingDefinition identity derivations)
                                (preparedResultsAuthorization <$> results)))
            -- Named constructions already carry a kernel-derived
            -- extensional presentation.  Keep the transparent-body
            -- definition equation internal and bind the source marker to
            -- that public view.
            Just (ElaboratedUnconditionalSetConstruction construction) ->
                Except.runExceptT do
                    equation <-
                        Trans.lift
                            (Declaration.prepareDefinitionEquationSpecWithEligibilityLowering
                                objects identity SearchIneligible [])
                            >>= Except.liftEither
                    (extensional, descriptor) <-
                        Trans.lift
                            (Declaration.prepareNamedSetConstructionSpecLowering
                                objects identity construction alias)
                            >>= Except.liftEither
                    let baseStages =
                            [ Declaration.checkedCandidate
                                equation
                                (Declaration.checkedDefinitionEquationPlanning
                                    identity)
                                :| [ Declaration.checkedCandidate
                                        extensional
                                        (Declaration.checkedKernelPlanning
                                            descriptor [])
                                   ]
                            ]
                    results <- traverse
                        (prepareDefinitionResultCandidates
                            (fromIntegral (length baseStages)))
                        preparedResults
                    pure
                        (checked binding []
                            (maybe [] preparedResultsPending results)
                            (baseStages <> maybeToList
                                (preparedResultsStage <$> results))
                            (CheckedBindingAuthorization
                                (CheckedBindingConstruction
                                    identity construction)
                                (preparedResultsAuthorization <$> results)))
            Just (ElaboratedRelationalSetConstruction construction) ->
                Except.runExceptT do
                    equation <-
                        Trans.lift
                            (Declaration.prepareDefinitionEquationSpecWithEligibilityLowering
                                objects identity SearchIneligible [])
                            >>= Except.liftEither
                    let functionality =
                            relationalSetConstructionClosedFunctionality
                                construction
                        functionalityScoped =
                            embedClosedCore [] functionality
                    functionalitySpec <-
                        Trans.lift
                            (Declaration.prepareFrozenCandidateSpecLowering
                                objects functionality SearchIneligible [])
                            >>= Except.liftEither
                    obligation <-
                        Trans.lift
                            (Declaration.prepareScopedVampireObligationLowering
                                Vector.empty
                                functionalityScoped
                                []
                                []
                                Declaration.internalVampirePremisePolicy)
                            >>= either
                                (Except.throwError
                                    . Declaration.ProofObligationFailedAt location
                                    . Declaration.CurrentCandidateVampirePreparationFailed)
                                pure
                    (extensional, descriptor) <-
                        Trans.lift
                            (Declaration.prepareRelationalSetConstructionSpecLowering
                                objects identity construction
                                functionality alias)
                            >>= Except.liftEither
                    let baseStages =
                            [ Declaration.checkedCandidate
                                equation
                                (Declaration.checkedDefinitionEquationPlanning
                                    identity)
                                :| [ Declaration.checkedCandidate
                                        functionalitySpec
                                        (Declaration.checkedExternalSourceProofPlanning
                                            (Declaration.checkedPlannedVampireRequest
                                                location obligation :| [])
                                            [])
                                   ]
                            , Declaration.checkedCandidate
                                extensional
                                (Declaration.checkedStagedKernelPlanning
                                    descriptor
                                    [Planning.plannedEarlierCandidate 0 1])
                                :| []
                            ]
                    results <- traverse
                        (prepareDefinitionResultCandidates
                            (fromIntegral (length baseStages)))
                        preparedResults
                    pure
                        (checked binding []
                            (maybe [] preparedResultsPending results)
                            (baseStages <> maybeToList
                                (preparedResultsStage <$> results))
                            (CheckedBindingAuthorization
                                (CheckedBindingRelationalConstruction
                                    identity construction obligation)
                                (preparedResultsAuthorization <$> results)))
  where
    identity = preparedBindingObjectId prepared
    objects = maybeToList (preparedBindingObject prepared)
    location = preparedBindingLocation prepared
    binding = preparedBindingDeclaration prepared
    checked declaration notionViews providerRules stages body =
        Declaration.checkedCompiledDeclarationWithRegistrations
            (preparedBindingSyntaxId prepared)
            objects
            []
            [declaration]
            Nothing
            (notionViews <> providerRules)
            stages
            body

    prepareDefinitionProjection (ordinal, projection) = do
        let key = preparedBindingGlobalKey prepared
            owner = preparedBindingDeclarationSlot prepared
            arity = notionArity key
            formula = definitionBaseProjectionFormula projection
            argumentTerms =
                [ CBound (arity - argument - 1)
                | argument <-
                    if arity == 0 then [] else [0 .. arity - 1]
                ]
            predicate = foldl' CApp (CGlobal identity) argumentTerms
            targetTerm = closeSetBinders arity (CImp predicate formula)
            context = replicate (fromIntegral arity) TySet
        target <-
            either
                (Except.throwError
                    . Declaration.DeclarationPropositionValidationFailed
                    . PropositionCoreCheckError)
                pure
                (checkCanonicalCore globalTyping targetTerm)
        spec <-
            Trans.lift
                (Declaration.prepareFrozenCandidateSpecLowering
                    objects target SearchIneligible [])
                >>= Except.liftEither
        premiseScoped <-
            either
                (Except.throwError
                    . Declaration.DeclarationPropositionValidationFailed
                    . PropositionCoreCheckError)
                pure
                (checkScopedCanonicalCore
                    globalTyping
                    context
                    predicate)
        arguments <-
            traverse
                (\term ->
                    either
                        (Except.throwError
                            . Declaration.DeclarationPropositionValidationFailed
                            . PropositionCoreCheckError)
                        pure
                        (checkScopedCanonicalCore
                            globalTyping
                            context
                            term))
                argumentTerms
        let premiseHead = case key of
                SemanticNoun{} ->
                    NounNotionHead (globalBindingRef owner key)
                SemanticPrefixPredicate{} ->
                    PrefixPredicateNotionHead (globalBindingRef owner key)
                SemanticLeftAdjective{} ->
                    AdjectiveNotionHead (globalBindingRef owner key)
                SemanticRightAdjective{} ->
                    AdjectiveNotionHead (globalBindingRef owner key)
                SemanticVerb{} ->
                    VerbNotionHead (globalBindingRef owner key)
                SemanticRelation{} ->
                    RelationNotionHead (globalBindingRef owner key)
                _ -> impossible
                    "a definition projection has an incompatible predicate family"
            premise =
                GlobalNotionViewPremise
                    premiseHead
                    (fromMaybe
                        (impossible "a definition projection has malformed predicate arguments")
                        (globalNotionOccurrenceArguments key
                            (Vector.fromList
                                [ TemplateVariable
                                    (ViewVariableIx (arity - argument - 1))
                                | argument <-
                                    if arity == 0 then [] else [0 .. arity - 1]
                                ])))
            conclusion = case definitionBaseProjectionTemplate projection of
                AtomicLeaf atom -> AtomicLeaf (occurrenceTemplateToView arity atom)
                WholeLeaf residual -> WholeLeaf residual
            pending = Registration (Planning.plannedEarlierCandidate 1 ordinal) Notion.ConjunctionHere
                (RegisterNotionView (NotionViewRule premise conclusion))
            buildDerivation selectedImport =
                let equation = foldl'
                        forallEliminationDerivation
                        (importedFactDerivation selectedImport)
                        arguments
                    expanded = equalityModusPonensDerivation
                        equation
                        (localHypothesisDerivation (hypothesisIx 0))
                    projected = projectBase
                        (definitionBaseProjectionPath projection)
                        expanded
                in closeDerivationBinders arity
                    (implicationIntroductionDerivation premiseScoped projected)
        pure (PreparedBindingProjection spec pending
            (CheckedDefinitionProjection identity (definitionBaseProjectionPath projection)) buildDerivation)

    prepareDefinitionResultCandidates resultStage preparedResults = Except.ExceptT do
        recorder <- Declaration.formationRecorderLowering
        FormationDiagnostics.continueCompletion recorder (preparedDefinitionCompletion preparedResults)
            (Except.runExceptT (traverse
                (uncurry (prepareDefinitionResultCandidate resultStage))
                (NonEmpty.zip (0 :| [1 ..]) (preparedDefinitionResultItems preparedResults))))

    prepareDefinitionResultCandidate resultStage resultOrdinal preparedResult = do
        let key = preparedBindingGlobalKey prepared
            owner = preparedBindingDeclarationSlot prepared
            providerReference = globalBindingRef owner key
            providerType = fromMaybe
                (impossible "a definition result provider has no semantic type")
                (semanticGlobalKeyType key)
            arity = case firstOrderSymbolShape providerType of
                Just (value, TySet) -> fromIntegral value
                _ -> impossible
                    "a definition result provider is not first-order set-valued"
            argumentTerms =
                [ CBound (arity - argument - 1)
                | argument <-
                    if arity == 0 then [] else [0 .. arity - 1]
                ]
            providerTerm =
                foldl' CApp (CGlobal identity) argumentTerms
            headers = preparedDefinitionResultHeaders preparedResult
            headerTerms = scopedCoreTerm . compiledHeaderCore <$> headers
            body = preparedDefinitionResultBody preparedResult
            bodyTerm = scopedCoreTerm
                (SourceTerm.sourceTermOccurrenceCore body)
            premise = preparedDefinitionResultProposition preparedResult
            predicate = preparedDefinitionResultPredicate preparedResult
            context = replicate (fromIntegral arity) TySet
            evidence = preparedDefinitionResultEvidence preparedResult
            fingerprints = Notion.materializedFormationImports evidence
            evidenceHypotheses =
                Notion.materializedFormationHypotheses evidence
            predicateBody = case scopedCoreTerm predicate of
                CLam TySet value -> value
                _ -> impossible
                    "a prepared definition result predicate is not set-valued"
            resultTerm = instantiateCanonical providerTerm predicateBody
            targetTerm = closeSetBinders arity
                (foldr CImp resultTerm headerTerms)
            equalityTerm = CEq TySet providerTerm bodyTerm
            equationImport = importIx (fromIntegral (Vector.length fingerprints))
        unless
            ( resultProviderTemplateHead
                (preparedDefinitionResultProvider preparedResult)
                == GlobalSourceProvider providerReference
            )
            (impossible
                "a prepared definition result names a different provider")
        unless
            ( instantiateCanonical bodyTerm predicateBody
                == scopedCoreTerm premise
            )
            (impossible
                "a prepared definition result predicate differs from its body atom")
        target <-
            either
                (Except.throwError
                    . Declaration.DeclarationPropositionValidationFailed
                    . PropositionCoreCheckError)
                pure
                (checkCanonicalCore globalTyping targetTerm)
        spec <-
            Trans.lift
                (Declaration.prepareFrozenCandidateSpecLowering
                    objects target SearchIneligible [])
                >>= Except.liftEither
        arguments <- traverse
            (checkResultScoped globalTyping context)
            argumentTerms
        equality <- checkResultScoped globalTyping context equalityTerm
        result <- checkResultScoped globalTyping context resultTerm
        unless (scopedCoreType result == TyProp)
            (impossible "a prepared definition result target is not a proposition")
        foundation <- Trans.lift Declaration.currentFoundationLowering
        formationContext <-
            either
                (Except.throwError . Declaration.DefinitionResultFormationProofFailed
                    . Notion.FormationProofKernelError)
                pure
                (KernelProof.scopedProofContext foundation globalTyping context
                    (toList (Notion.materializedFormationHypothesisPropositions evidence)))
        formationImports <- for fingerprints \fingerprint -> do
            proposition <-
                Trans.lift (Declaration.resolveVisibleFactLowering fingerprint)
                    >>= maybe
                        (Except.throwError (Declaration.AuthorizedFactNotVisible fingerprint))
                        pure
            either
                (Except.throwError . Declaration.DerivationImportFailed)
                pure
                (derivationImportJudgement (checkedPropositionTerm proposition))
        formationProof <- Trans.lift (Declaration.materializeFormationProofLowering formationContext evidence formationImports)
            >>= either (Except.throwError . Declaration.DefinitionResultFormationProofFailed) pure
        unless (KernelProof.builtProofStatement formationProof == premise)
            (Except.throwError Declaration.DefinitionResultFormationTargetMismatch)
        proofContext <-
            either
                (Except.throwError . Declaration.KernelProofBuildFailed)
                pure
                (KernelProof.scopedProofContext
                    foundation
                    globalTyping
                    context
                    (reverse (compiledHeaderCore <$> headers)))
        let remappedEvidence =
                remapDerivationExternalHypotheses
                    (selectedHeaderHypothesis headers evidenceHypotheses)
                    (KernelProof.builtProofDerivation formationProof)
            specializedEquation = foldl'
                forallEliminationDerivation
                (importedFactDerivation equationImport)
                arguments
        transported <-
            either
                (Except.throwError . Declaration.KernelProofBuildFailed)
                pure
                (KernelProof.equalityTransportDerivationProof
                    proofContext
                    KernelProof.EqualityRightToLeft
                    equality
                    specializedEquation
                    predicate
                    premise
                    remappedEvidence
                    result)
        let openDerivation = KernelProof.builtProofDerivation transported
            headerClosed = foldl'
                (flip implicationIntroductionDerivation)
                openDerivation
                (reverse (compiledHeaderCore <$> headers))
            closedDerivation = closeDerivationBinders arity headerClosed
            pending = Registration (Planning.plannedEarlierCandidate resultStage resultOrdinal) Notion.ConjunctionHere
                (case preparedDefinitionResultConclusion preparedResult of
                    AtomicLeaf conclusion -> RegisterProviderResult (ProviderResultRule
                        (preparedDefinitionResultProvider preparedResult)
                        (ProviderResultGuarded (preparedDefinitionResultPremises preparedResult)) conclusion)
                    WholeLeaf description ->
                        let RulePremiseBundles premises = preparedDefinitionResultPremises preparedResult
                            provider = preparedDefinitionResultProvider preparedResult
                            metadata = fmap (runIdentity . SourceEvidence.traverseSourceAtDepth
                                (\depth -> instantiateSupportPrefixWith (pure ()) 1
                                    (\nested _ -> pure
                                        (fmap (\(ViewVariableIx slot) -> CBound (slot+nested))
                                            (TemplateProvider (resultProviderTemplateHead provider) (resultProviderTemplateArguments provider)),
                                         shiftCanonical nested 0 providerTerm)) depth)
                                (\depth -> pure . fmap (replaceResultFocus provider depth))) (residualTemplateEvidence description)
                            conclusion = maybe (ResidualTemplate resultTerm) (describedResidualTemplate resultTerm) metadata
                        in RegisterWholeConclusion (WholeConclusionRule arity (toList premises) conclusion))
            authorization = CheckedBindingResultAuthorization
                fingerprints
                (\actualImports actualEquation ->
                    fromMaybe
                        (impossible
                            "a definition result lost a planned kernel import")
                        (remapKernelDerivationImports
                            (remapResultImport actualImports actualEquation)
                            closedDerivation))
        pure (PreparedBindingResultCandidate spec pending authorization)

    -- Slot zero is the annotation's result focus. Other slots are the
    -- declaration parameters; formula-internal binders retain their positions.
    replaceResultFocus provider depth = \case
        TemplateVariable (ViewVariableIx index)
            | index < depth -> TemplateVariable (ViewVariableIx index)
            | index == depth -> TemplateProvider (resultProviderTemplateHead provider)
                (fmap (fmap (\(ViewVariableIx slot) -> ViewVariableIx (slot+depth)))
                    (resultProviderTemplateArguments provider))
            | otherwise -> TemplateVariable (ViewVariableIx (index-1))
        TemplateClosed value -> TemplateClosed value
        TemplateProvider head' arguments -> TemplateProvider head' (replaceResultFocus provider depth <$> arguments)
        TemplateOrderedPair a b -> TemplateOrderedPair (replaceResultFocus provider depth a) (replaceResultFocus provider depth b)

    checkResultScoped globalTyping' context term =
        either
            (Except.throwError
                . Declaration.DeclarationPropositionValidationFailed
                . PropositionCoreCheckError)
            pure
            (checkScopedCanonicalCore globalTyping' context term)

    selectedHeaderHypothesis headers selected original =
        fromMaybe
            (impossible
                "definition-result evidence refers to a non-header hypothesis")
            (mapping Vector.!? fromIntegral (hypothesisIxValue original))
      where
        mapping = selectedHeaderIndex headers <$> selected

    selectedHeaderIndex headers hypothesis =
        case
            [ hypothesisIx
                (fromIntegral (length headers - index - 1))
            | (index, header) <- zip [0 :: Int ..] headers
            , headerMatches header
            ]
        of
            [single] -> single
            _ -> impossible
                "definition-result evidence does not identify one exact header"
      where
        proposition = Notion.materializedNotionHypothesisProposition hypothesis
        headerMatches header =
            compiledHeaderCore header == proposition
                && case Notion.materializedNotionHypothesisOrigin hypothesis of
                    FormationFromDefinitionHeader source variable _location ->
                        compiledHeaderSourceOrdinal header == source
                            && compiledHeaderVariableOrdinal header == variable
                    _ -> False

    remapResultImport actualImports actualEquation original
        | index < Vector.length actualImports = actualImports Vector.!? index
        | index == Vector.length actualImports = Just actualEquation
        | otherwise = Nothing
      where
        index = fromIntegral (importIxValue original)

    preparedResultsStage = fmap prepareStageCandidate . fst
      where
        prepareStageCandidate
                (PreparedBindingResultCandidate spec _pending authorization) =
            Declaration.checkedCandidate spec
                (Declaration.checkedNoExternalSourceProofPlanningWithFacts
                    (toList fingerprints)
                    [Planning.plannedEarlierCandidate 0 0])
          where
            CheckedBindingResultAuthorization fingerprints _builder =
                authorization

    preparedResultsPending =
        fmap
            (\(PreparedBindingResultCandidate _spec pending _authorization) ->
                pending)
            . toList . fst

    preparedResultsAuthorization (results, completion) =
        ( fmap (\(PreparedBindingResultCandidate _spec _pending authorization) -> authorization) results
        , completion )

    notionArity key =
        case semanticGlobalKeyType key >>= firstOrderSymbolShape of
            Just (arity, TyProp) -> fromIntegral arity
            _ -> impossible "a definition projection has a non-predicate head"

    closeSetBinders remaining term
        | remaining == 0 = term
        | otherwise =
            closeSetBinders (remaining - 1) (CForall TySet term)

    closeDerivationBinders remaining derivation
        | remaining == 0 = derivation
        | otherwise =
            closeDerivationBinders (remaining - 1)
                (forallIntroductionDerivation TySet derivation)

    occurrenceTemplateToView arity =
        fmap (fmap convertVariable)
      where
        convertVariable (OccurrenceArgumentIx argument)
            | argument < arity =
                ViewVariableIx (arity - argument - 1)
            | otherwise =
                impossible "a definition projection has an invalid argument"

    projectBase Notion.ConjunctionHere derivation = derivation
    projectBase (Notion.ConjunctionLeft path) derivation =
        projectBase path (conjunctionLeftEliminationDerivation derivation)
    projectBase (Notion.ConjunctionRight path) derivation =
        projectBase path (conjunctionRightEliminationDerivation derivation)

data CheckedBindingAuthorization = CheckedBindingAuthorization
    !CheckedBindingBaseAuthorization
    !(Maybe (NonEmpty CheckedBindingResultAuthorization, FormationDiagnostics.Completion))

data CheckedBindingBaseAuthorization
    = CheckedBindingNone
    | CheckedBindingDefinition
        !ObjectId ![(KernelConstructionDescriptor, ImportIx -> KernelDerivation ObjectId)]
    | CheckedBindingConstruction
        !ObjectId
        !(NamedSetConstruction ObjectId)
    | CheckedBindingRelationalConstruction
        !ObjectId
        !(CheckedRelationalSetConstruction ObjectId)
        !(Declaration.PreparedVampireObligation Void ())

authorizeCheckedBinding
    :: CheckedBindingAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedBinding (CheckedBindingAuthorization body maybeResults) stages = do
    let (baseStages, maybeResultStage) = case maybeResults of
            Nothing -> (stages, Nothing)
            Just{} -> case reverse stages of
                [] -> ([], Nothing)
                resultStage : remaining ->
                    (reverse remaining, Just resultStage)
    maybeEquation <- authorizeBase body baseStages
    case (maybeResults, maybeResultStage, maybeEquation) of
        (Nothing, Nothing, _equation) -> pure ()
        (Just (resultAuthorizations, completion), Just resultStage, Just equation)
            | NonEmpty.length resultAuthorizations
                == NonEmpty.length resultStage ->
                Declaration.completeFormationDeclaration completion
                    (traverse_
                        (\(resultAuthorization, result) -> authorizeResult equation resultAuthorization result)
                        (NonEmpty.zip resultAuthorizations resultStage))
            | otherwise ->
                Declaration.failDeclaration
                    (Declaration.CheckedAuthorizationCandidateShapeMismatch
                        (NonEmpty.length resultAuthorizations)
                        (NonEmpty.length resultStage))
        _ -> shapeMismatch body baseStages
  where
    authorizeBase base baseStages = case (base, baseStages) of
        (CheckedBindingNone, []) -> pure Nothing
        (CheckedBindingDefinition identity [], [candidate :| []]) -> do
            Declaration.authorizeDefinitionEquationCandidate identity candidate
            pure (Just candidate)
        ( CheckedBindingDefinition identity derivations
          , [equation :| [], projections]
          ) | length derivations == NonEmpty.length projections -> do
                Declaration.authorizeDefinitionEquationCandidate
                    identity equation
                traverse_
                    (\(candidate, (descriptor, buildDerivation)) ->
                        Declaration.authorizeKernelConstructionCandidate
                            descriptor candidate
                            (buildDerivation
                                <$> Declaration.useStagedCandidate equation))
                    (zip (toList projections) derivations)
                pure (Just equation)
        ( CheckedBindingConstruction identity construction
          , [equation :| [extensional]]
          ) -> do
            Declaration.authorizeDefinitionEquationCandidate
                identity equation
            Declaration.authorizeNamedSetConstructionCandidate
                identity construction extensional
            pure (Just equation)
        ( CheckedBindingRelationalConstruction
                identity construction obligation
          , [equation :| [functionality], extensional :| []]
          ) -> do
            Declaration.authorizeDefinitionEquationCandidate
                identity equation
            Declaration.authorizeVampireCandidate
                functionality
                (Declaration.acceptPreparedVampireObligation obligation)
            Declaration.authorizeRelationalSetConstructionCandidate
                identity construction functionality extensional
            pure (Just equation)
        _ -> shapeMismatch base baseStages

    authorizeResult equation
            (CheckedBindingResultAuthorization fingerprints buildDerivation)
            result =
        Declaration.authorizeKernelProofCandidate result do
            actualImports <- traverse Declaration.useAuthorizedFact fingerprints
            actualEquation <- Declaration.useStagedCandidate equation
            pure (buildDerivation actualImports actualEquation)

    shapeMismatch base baseStages =
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                (case base of
                        CheckedBindingNone -> 0
                        CheckedBindingDefinition _ derivations ->
                            if null derivations then 1 else 2
                        CheckedBindingConstruction{} -> 1
                        CheckedBindingRelationalConstruction{} -> 2)
                (length baseStages))

prepareHead
    :: Raw.Block
    -> SemanticGlobalKey
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ( BindingHead
        , BindingFamily
        , Maybe (Elaborate CompiledBody)
        )
prepareHead block key =
    case block of
        Raw.BlockSig location _title _marker assumptions signature -> do
            rejectHeaderAssumptions ElaborationGuardedOpaqueSignature assumptions
            head' <- prepareSignature location key signature
            pure (head', SignatureBinding, Nothing)
        Raw.BlockAbbr location _title _marker abbreviation -> do
            (head', buildBody) <-
                prepareAbbreviation location key abbreviation
            pure (head', AbbreviationBinding, Just buildBody)
        Raw.BlockDefn location _title _marker definition -> do
            (head', buildBody) <-
                prepareDefinition location key definition
            pure (head', DefinitionBinding, Just buildBody)
        Raw.BlockConstruction location _title _marker construction -> do
            let Raw.SymbolPattern symbol parameters = Raw.constructionHead construction
            ensureExpressionKey location symbol key
            (head', buildBody) <- makeTransparentHead location key parameters TySet
                (compileHostedConstructionDefinition location
                    (Raw.constructionAssumptions construction)
                    (Raw.constructionValue construction))
            pure (head', DefinitionBinding, Just buildBody)
        _ ->
            Except.throwError (ElaborationUnsupportedDeclaration (locate block))

prepareSignature
    :: Location
    -> SemanticGlobalKey
    -> Raw.Signature
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        BindingHead
prepareSignature location key = \case
    Raw.SignatureAdj subject (Raw.Adj _ item arguments) -> do
        ensureAdjectiveKey location item key
        makeBindingHead
            location key (subject : arguments) TyProp
    Raw.SignatureSymbolic (Raw.SymbolPattern symbol parameters) nounPhrase -> do
        unless
            ( key
                == SemanticExpressionFunction
                    (Raw.mixfixPattern symbol)
            )
            (Except.throwError (ElaborationDeclarationHeadMismatch location))
        unless
            (isSetNounPhrase nounPhrase)
            (Except.throwError (ElaborationUnsupportedDeclarationBody location))
        makeBindingHead location key parameters TySet
    Raw.SignatureTypedConstant _headLocation token concreteType -> do
        let coreType = concreteTypeCoreType concreteType
        unless
            (key == SemanticTypedConstant token coreType)
            (Except.throwError (ElaborationDeclarationHeadMismatch location))
        makeBindingHead location key [] coreType
    _ ->
        Except.throwError (ElaborationUnsupportedDeclaration location)

prepareAbbreviation
    :: Location
    -> SemanticGlobalKey
    -> Raw.Abbreviation
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ( BindingHead
        , Elaborate CompiledBody
        )
prepareAbbreviation location key = \case
    Raw.AbbreviationEq (Raw.SymbolPattern symbol parameters) expression -> do
        ensureExpressionKey location symbol key
        makeContextualTransparentHead
            location key parameters TySet
            (sourceTermCompiledBody <$> compileSourceExpressionAsSetTerm expression)
    Raw.AbbreviationFun (Raw.Fun _ item parameters) term -> do
        ensureFunctionPhraseKey location item key
        makeContextualTransparentHead
            location key parameters TySet
            (sourceTermCompiledBody <$> compileSourceTermAsSet term)
    Raw.AbbreviationAdj subject (Raw.Adj _ item arguments) statement -> do
        ensureAdjectiveKey location item key
        makeContextualTransparentHead
            location key (subject : arguments) TyProp
            (propositionCompiledBody
                <$> compileStatement statement)
    Raw.AbbreviationVerb subject (Raw.Verb _ item arguments) statement -> do
        ensureVerbKey location item key
        makeContextualTransparentHead
            location key (subject : arguments) TyProp
            (propositionCompiledBody
                <$> compileStatement statement)
    Raw.AbbreviationNoun subject (Raw.Noun _ item arguments) statement -> do
        ensureNounKey location item key
        makeContextualTransparentHead
            location key (subject : arguments) TyProp
            (propositionCompiledBody
                <$> compileStatement statement)
    Raw.AbbreviationRel left relation parameters right statement -> do
        ensureRelationKey location relation key
        makeContextualTransparentHead
            location key (parameters <> [left, right]) TyProp
            (propositionCompiledBody
                <$> compileStatement statement)

prepareDefinition
    :: Location
    -> SemanticGlobalKey
    -> Raw.Defn
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ( BindingHead
        , Elaborate CompiledBody
        )
prepareDefinition location key = \case
    Raw.Defn assumptions head' statement -> do
        (parameters, resultType) <-
            definitionHead location key head'
        let distinguishedBase =
                case head' of
                    Raw.DefnNoun{} -> Just (OccurrenceArgumentIx 0)
                    _ -> Nothing
        makeTransparentHead
            location key parameters resultType
            (compilePredicateDefinition
                distinguishedBase assumptions statement)
    Raw.DefnFun assumptions (Raw.Fun _ item parameters) symbolic term
            maybeResult -> do
        traverse_
            (Except.throwError
                . ElaborationDefinitionCombinedSymbolicAlias
                . locate)
            symbolic
        ensureFunctionPhraseKey location item key
        makeTransparentHead
            location key parameters TySet
            (compileHostedSetTermDefinition
                location assumptions maybeResult
                (compileNamedSetTermWithSource term))
    Raw.DefnOp assumptions (Raw.SymbolPattern symbol parameters) expression
            maybeResult -> do
        ensureExpressionKey location symbol key
        makeTransparentHead
            location key parameters TySet
            (compileHostedSetTermDefinition
                location assumptions maybeResult
                (compileNamedSetExpressionWithSource expression))
    Raw.DefnTypedConstant
            _headLocation constantToken concreteType body -> do
        let coreType = concreteTypeCoreType concreteType
        unless
            (key == SemanticTypedConstant constantToken coreType)
            (Except.throwError (ElaborationDeclarationHeadMismatch location))
        makeTransparentHead
            location key [] coreType
            (ordinaryCompiledBody
                <$> compileTypedExpressionAs location coreType body)

compileTypedExpressionAs
    :: Location
    -> CoreType
    -> Raw.TypedExpression
    -> Elaborate (CanonicalTerm ObjectId)
compileTypedExpressionAs location expected expression = do
    (term, actual) <- compileTypedExpression expression
    unless (actual == expected)
        (Except.throwError
            (ElaborationObjectTypeMismatch location expected actual))
    pure term

definitionHead
    :: Location
    -> SemanticGlobalKey
    -> Raw.DefnHead
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ([Raw.VarSymbol], CoreType)
definitionHead location key = \case
    Raw.DefnAdj subject (Raw.Adj _ item arguments) -> do
        ensureAdjectiveKey location item key
        pure (subject : arguments, TyProp)
    Raw.DefnVerb subject (Raw.Verb _ item arguments) -> do
        ensureVerbKey location item key
        pure (subject : arguments, TyProp)
    Raw.DefnNoun subject (Raw.Noun _ item arguments) -> do
        ensureNounKey location item key
        pure (subject : arguments, TyProp)
    Raw.DefnRel left relation parameters right -> do
        ensureRelationKey location relation key
        pure (parameters <> [left, right], TyProp)
    Raw.DefnSymbolicPredicate
            (Raw.PrefixPredicate command arity)
            _marker
            parameters -> do
        unless
            ( key
                == SemanticPrefixPredicate
                    command
                    (fromIntegral arity)
            )
            (Except.throwError (ElaborationDeclarationHeadMismatch location))
        pure (toList parameters, TyProp)

rejectHeaderAssumptions
    :: MonadError ElaborationError monad
    => (Location -> ElaborationError)
    -> [Raw.Asm]
    -> monad ()
rejectHeaderAssumptions makeError = \case
    [] -> pure ()
    assumption : _ ->
        throwError (makeError (assumptionLocation assumption))

assumptionLocation :: Raw.Asm -> Location
assumptionLocation = \case
    Raw.AsmSuppose statement -> locate statement
    Raw.AsmLetNoun variables _nounPhrase -> locate variables
    Raw.AsmLetIn variables _expression -> locate variables
    Raw.AsmLetRelation variables _relation _right -> locate variables
    Raw.AsmLetThe variable _function -> locate variable
    Raw.AsmLetEq variable _expression -> locate variable
    Raw.AsmLetStruct variables _structure -> locate variables

makeTransparentHead
    :: Location
    -> SemanticGlobalKey
    -> [Raw.VarSymbol]
    -> CoreType
    -> Elaborate CompiledBody
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ( BindingHead
        , Elaborate CompiledBody
        )
makeTransparentHead location key parameters resultType body = do
    (prepared, binders) <-
        prepareParameters location key parameters resultType
    let close = do
            initializeDefinitionElaboration
                binders
                (fromIntegral (length parameters))
                False
            CompiledBody body' construction proposition <- body
            pure
                (CompiledBody
                    (foldr (const (CLam TySet)) body' parameters)
                    construction
                    proposition)
    pure (prepared, close)

makeContextualTransparentHead
    :: Location
    -> SemanticGlobalKey
    -> [Raw.VarSymbol]
    -> CoreType
    -> Elaborate CompiledBody
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ( BindingHead
        , Elaborate CompiledBody
        )
makeContextualTransparentHead location key parameters resultType body = do
    (prepared, binders) <-
        prepareParameters location key parameters resultType
    let close = do
            initializeDefinitionElaboration
                binders
                (fromIntegral (length parameters))
                True
            CompiledBody body' _construction proposition <- body
            pure
                (CompiledBody
                    (foldr (const (CLam TySet)) body' parameters)
                    Nothing
                    proposition)
    pure (prepared, close)

makeBindingHead
    :: Location
    -> SemanticGlobalKey
    -> [Raw.VarSymbol]
    -> CoreType
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        BindingHead
makeBindingHead location key parameters resultType = do
    (prepared, _binders) <-
        prepareParameters location key parameters resultType
    pure prepared

prepareParameters
    :: Location
    -> SemanticGlobalKey
    -> [Raw.VarSymbol]
    -> CoreType
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        ( BindingHead
        , Map.Map Raw.VarSymbol (Natural, CoreType)
        )
prepareParameters
        location key parameters resultType = do
    case firstDuplicate parameters of
        Just duplicate ->
            Except.throwError
                (ElaborationDuplicateParameter location duplicate)
        Nothing -> pure ()
    let indices =
            reverse (take (length parameters) [0 ..])
        binders =
            Map.fromList
                [ (parameter, (index, TySet))
                | (parameter, index) <- zip parameters indices
                ]
        coreType = foldr (const (TyArrow TySet)) resultType parameters
    pure
        ( BindingHead key parameters coreType
        , binders
        )

ensureExpressionKey
    :: MonadError ElaborationError monad
    => Location
    -> Raw.FunctionSymbol
    -> SemanticGlobalKey
    -> monad ()
ensureExpressionKey location symbol key =
    unless
        (key == SemanticExpressionFunction (Raw.mixfixPattern symbol))
        (throwError (ElaborationDeclarationHeadMismatch location))

ensureAdjectiveKey
    :: MonadError ElaborationError monad
    => Location
    -> Raw.AdjectiveLexicalItem
    -> SemanticGlobalKey
    -> monad ()
ensureAdjectiveKey location item key =
    unless (matchesAdjectiveSurface key)
        (throwError (ElaborationDeclarationHeadMismatch location))
  where
    matchesAdjectiveSurface = \case
        SemanticLeftAdjective _reading pattern' ->
            Raw.adjectiveLexicalSide item == Raw.LeftAdjectiveSide
                && pattern' == Raw.adjectiveLexicalPattern item
        SemanticRightAdjective _reading pattern' ->
            Raw.adjectiveLexicalSide item == Raw.RightAdjectiveSide
                && pattern' == Raw.adjectiveLexicalPattern item
        _ -> False

ensureFunctionPhraseKey
    :: MonadError ElaborationError monad
    => Location
    -> Raw.LexicalItemSgPl
    -> SemanticGlobalKey
    -> monad ()
ensureFunctionPhraseKey location item key =
    let patterns = Raw.lexicalItemSgPlPattern item
    in unless
        (key == SemanticFunctionPhrase (Raw.sg patterns) (Raw.pl patterns))
        (throwError (ElaborationDeclarationHeadMismatch location))

ensureNounKey
    :: MonadError ElaborationError monad
    => Location
    -> Raw.LexicalItemSgPl
    -> SemanticGlobalKey
    -> monad ()
ensureNounKey location item key =
    let patterns = Raw.lexicalItemSgPlPattern item
    in unless
        (key == SemanticNoun (Raw.sg patterns) (Raw.pl patterns))
        (throwError (ElaborationDeclarationHeadMismatch location))

ensureVerbKey
    :: MonadError ElaborationError monad
    => Location
    -> Raw.VerbLexicalItem
    -> SemanticGlobalKey
    -> monad ()
ensureVerbKey location item key =
    unless
        (key == SemanticVerb (Raw.verbLexicalSurfaces item))
        (throwError (ElaborationDeclarationHeadMismatch location))

ensureRelationKey
    :: MonadError ElaborationError monad
    => Location
    -> Raw.RelationSymbol
    -> SemanticGlobalKey
    -> monad ()
ensureRelationKey location relation key =
    unless
        ( key
            == SemanticRelation
                (Raw.relationSymbolToken relation)
                (Raw.relationSymbolParameterArity relation)
        )
        (throwError (ElaborationDeclarationHeadMismatch location))

encodePreparedSyntax
    :: BindingFamily
    -> BindingHead
    -> PreparedBindingBody
    -> Maybe SemanticName
    -> Maybe PreparedDefinitionResults
    -> Maybe AbbreviationExpansion
    -> ByteString
encodePreparedSyntax family head' body alias result =
    runIdentity . encodePreparedSyntaxWith (pure ()) family head' body alias result

encodePreparedSyntaxWith
    :: Monad m => m () -> BindingFamily -> BindingHead -> PreparedBindingBody
    -> Maybe SemanticName -> Maybe PreparedDefinitionResults -> Maybe AbbreviationExpansion
    -> m ByteString
encodePreparedSyntaxWith visit family (BindingHead key _ coreType) body alias result expansion = do
    visit
    encodedType <- putCoreTypeCacheWith visit coreType
    encodedBody <- case body of
        OpaqueBody -> pure (putCacheTag 0x00)
        TransparentBody canonical _ -> (putCacheTag 0x01 >>) <$> putCanonicalTermCacheWith visit putObjectIdCache canonical
        ContextualTransparentBody requirements canonical -> do
            encoded <- putCanonicalTermCacheWith visit putObjectIdCache canonical
            for_ requirements (const visit)
            pure do
                putCacheTag 0x02
                putCanonicalCacheMap
                    (\(Raw.StructSymbol symbol) -> putCacheText symbol)
                    (\(field, projection) -> putFieldIdCache field >> putObjectIdCache projection) requirements
                encoded
    encodedExpansion <- traverse (putAbbreviationExpansionCacheWith visit) expansion
    pure $ encodeCache do
        putCacheTag case family of SignatureBinding -> 0x00; AbbreviationBinding -> 0x01; DefinitionBinding -> 0x02
        putSemanticGlobalKeyCache key
        encodedType
        encodedBody
        putCacheMaybe (putCacheText . semanticNameText) alias
        putCacheMaybe (putCacheList ((\case
            AtomicLeaf atom -> putCacheTag 0 >> putResultNotionRuleTemplateCache atom
            WholeLeaf whole -> putCacheTag 1 >> putResidualTemplateCache whole) . preparedDefinitionResultConclusion)
            . toList . preparedDefinitionResultItems) result
        putCacheMaybe id encodedExpansion

definitionAlias :: Raw.Block -> Maybe SemanticName
definitionAlias = \case
    Raw.BlockDefn _location _title (Raw.Marker marker) _definition ->
        Just (semanticName marker)
    Raw.BlockConstruction _location _title (Raw.Marker marker) _construction ->
        Just (semanticName marker)
    _ -> Nothing

declarationBindingLabel :: Raw.Block -> SemanticBindingLabel
declarationBindingLabel = \case
    Raw.BlockDefn _location _title (Raw.Marker marker) _definition ->
        semanticBindingLabel marker
    Raw.BlockConstruction _location _title (Raw.Marker marker) _construction ->
        semanticBindingLabel marker
    Raw.BlockAbbr _location _title (Raw.Marker marker) _abbreviation ->
        semanticBindingLabel marker
    Raw.BlockSig _location _title (Raw.Marker marker) _assumptions _signature ->
        semanticBindingLabel marker
    block ->
        impossible
            ("binding preparation received an unsupported block: "
                <> show block)
