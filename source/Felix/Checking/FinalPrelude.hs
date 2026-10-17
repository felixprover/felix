{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

-- | Authority-confined construction of the inert final-prelude candidate.
module Felix.Checking.FinalPrelude
    ( FinalPreludeCandidate
    , finalPreludeParsed
    , finalPreludeSyntax
    , finalPreludeSemantic
    , finalPreludeEvidence
    , finalPreludePrefix
    , finalPreludeObjects
    , finalPreludeNaturalNumeralBasis
    , PreludePublicRole(..)
    , expectedFinalPreludePublicRoles
    , FinalPreludeRoleTarget(..)
    , finalPreludePublicRole
    , FinalPreludeValidationError(..)
    , FinalPreludeFailure(..)
    , FinalPreludeBuildResult(..)
    , buildFinalPreludeCandidate
    , buildParsedFinalPreludeCandidate
    , validateFinalPreludeSuccessorObject
    , recoverCachedFinalPreludeSuccessor
    , validateOmegaFactInventory
    ) where

import Base hiding (Empty)
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Builtin qualified as Builtin
import Felix.Checking.Structure.Generated qualified as Generated
import Felix.Checking.Structure.Predicate qualified as Predicate
import Felix.Checking.Structure.Interface qualified as StructureInterface
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Binding qualified as Binding
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core
import Felix.Checking.Elimination (predicateProjectionTarget)
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Foundation
import Felix.Checking.Identity
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.NaturalNumeral
    ( NaturalNumeralBasis
    , naturalNumeralBasisObject
    )
import Felix.Checking.NaturalNumeral qualified as NaturalNumeral
import Felix.Checking.Record qualified as Record
import Felix.Checking.SetConstruction
import Felix.Checking.Semantic
import Felix.Checking.Semantic qualified as Semantic
import Felix.Module
import Felix.Cache.Codec (CacheDigest)
import Felix.Parse
import Felix.Parsed.Module
import Felix.Prelude qualified as Prelude
import Felix.Source (ImportRef)
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface

import Control.Monad (unless)
import Control.Monad.Except qualified as Except
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)
import Data.Text qualified as Text


data FinalPreludeCandidate = FinalPreludeCandidate
    !Prelude.ReservedParsedPrelude
    !ModuleSyntaxInterface
    !Declaration.ImportedModuleEvidence
    !Commit.PendingModulePrefix
    !NaturalNumeralBasis
    !(Map.Map PreludePublicRole FinalPreludeRoleTarget)

finalPreludeParsed :: FinalPreludeCandidate -> Prelude.ReservedParsedPrelude
finalPreludeParsed (FinalPreludeCandidate parsed _ _ _ _ _) = parsed

finalPreludeSyntax :: FinalPreludeCandidate -> ModuleSyntaxInterface
finalPreludeSyntax (FinalPreludeCandidate _ syntax _ _ _ _) = syntax

finalPreludeEvidence :: FinalPreludeCandidate -> Declaration.ImportedModuleEvidence
finalPreludeEvidence (FinalPreludeCandidate _ _ evidence _ _ _) = evidence

finalPreludeSemantic :: FinalPreludeCandidate -> SemanticInterface
finalPreludeSemantic = Declaration.evidenceInterface . finalPreludeEvidence

finalPreludePrefix :: FinalPreludeCandidate -> Commit.PendingModulePrefix
finalPreludePrefix (FinalPreludeCandidate _ _ _ prefix _ _) = prefix

finalPreludeObjects :: FinalPreludeCandidate -> CheckedObjectClosure
finalPreludeObjects = Declaration.evidenceClosure . finalPreludeEvidence

finalPreludeNaturalNumeralBasis :: FinalPreludeCandidate -> NaturalNumeralBasis
finalPreludeNaturalNumeralBasis (FinalPreludeCandidate _ _ _ _ basis _) = basis

data FinalPreludeRoleTarget
    = FinalPreludeObjectRole !ObjectId
    | FinalPreludeTheoremRole !TheoremRef
    deriving stock (Show, Eq, Ord)

-- | Stable public roles exported by the packaged prelude.
data PreludePublicRole
    = PreludeGlobalChoiceMemberTheorem
    | PreludeUniverseReplacementClosedTheorem
    | PreludeUniverseMinimalTheorem
    | PreludeUniverseNestedTheorem
    | PreludeSetLfpBoundTheorem
    | PreludeSetLfpLeastTheorem
    | PreludeSetLfpFixedTheorem
    | PreludeSetLfpInductTheorem
    | PreludeSuccessorObject
    | PreludeTransitiveSetPredicate
    | PreludeInductiveSetPredicate
    | PreludeInfinityTheorem
    | PreludeOmegaObject
    | PreludeOmegaDefiningEquation
    | PreludeNaturalsObject
    | PreludeNaturalNumberPredicate
    | PreludeOmegaInductiveTheorem
    | PreludeOmegaMinimalTheorem
    deriving stock (Show, Eq, Ord, Enum, Bounded)

expectedFinalPreludePublicRoles :: Set PreludePublicRole
expectedFinalPreludePublicRoles =
    Set.fromList [minBound .. maxBound]

finalPreludePublicRole
    :: FinalPreludeCandidate
    -> PreludePublicRole
    -> Maybe FinalPreludeRoleTarget
finalPreludePublicRole
        (FinalPreludeCandidate _parsed _syntax _evidence _prefix _basis roles) role =
    Map.lookup role roles

data FinalPreludeValidationError
    = FinalPreludePackagedInputMismatch
    | FinalPreludeSemanticEnvironmentMismatch
    | FinalPreludeDeclarationAssociationMismatch
    | FinalPreludeUnexpectedObject !ObjectId
    | FinalPreludeDeclarationMissing !Text
    | FinalPreludeDeclarationDuplicate !Text
    | FinalPreludeDeclarationShapeMismatch !Text
    | FinalPreludeDefinitionContentMismatch !Text
    | FinalPreludeFactContentMismatch !Text
    | FinalPreludeValidationInventoryMismatch !DeclarationSlot
    | FinalPreludeAuthorityMismatch !DeclarationSlot
    | FinalPreludeBaseStructureMismatch
    | FinalPreludePublicRoleMismatch !PreludePublicRole
    deriving stock (Show, Eq)

data FinalPreludeFailure
    = FinalPreludeWrongOwner !ModuleName
    | FinalPreludeHasImports ![ImportRef]
    | FinalPreludeHasSyntaxImports ![SyntaxInterfaceId]
    | FinalPreludeUnsupportedBlock !Location
    | FinalPreludeUnmatchedProof !Location
    | FinalPreludeElaborationFailed !Elaboration.ElaborationError
    | FinalPreludeProofFailed !Proof.ProofError
    | FinalPreludeOmittedProof !Location
    | FinalPreludeDeclarationFailed !Declaration.DeclarationError
    | FinalPreludeSealFailed !SemanticInterfaceError
    | FinalPreludeValidationFailed !FinalPreludeValidationError
    deriving stock (Show, Eq)

data FinalPreludeBuildResult
    = FinalPreludeSourceLoadFailed !Prelude.PreludeLoadError
    | FinalPreludeSourceParseFailed !Prelude.PreludeParseError
    | FinalPreludeBuilt !FinalPreludeCandidate
    | FinalPreludeBuildFailed
        !FinalPreludeFailure
        !Commit.PendingModulePrefix
    | FinalPreludeBuildOpenFailed !Declaration.DriverOpenError

data PlannedPreludeDeclaration
    = PlannedPreludeBinding
        !(Declaration.PlannedDeclaration
            Binding.CheckedBindingAuthorization)
    | PlannedPreludeFoundation
        !(Declaration.PlannedDeclaration
            Proof.CheckedFinalPreludeFoundationAuthorization)
    | PlannedPreludeGuardedRule
        !(Declaration.PlannedDeclaration
            Proof.CheckedFinalPreludeGuardedRuleAuthorization)
    | PlannedPreludeProof
        !(Declaration.PlannedDeclaration
            Proof.CheckedProofAuthorization)
    | PlannedPreludeBase
        !(Declaration.PlannedDeclaration
            CheckedPreludeBaseStructureAuthorization)

type CheckedPreludeBaseStructureAuthorization = Generated.CheckedStructureBatchAuthorization

data PreludePlanningFailure
    = PreludePlanningAction !FinalPreludeFailure
    | PreludePlanningDeclaration !Declaration.DeclarationError

data PreludeModulePlan = PreludeModulePlan
    ![PlannedPreludeDeclaration]
    !(Maybe PreludePlanningFailure)

buildFinalPreludeCandidate
    :: CheckedFoundation
    -> Declaration.VampireResolver
    -> IO FinalPreludeBuildResult
buildFinalPreludeCandidate foundation resolver =
    Prelude.loadReservedPreludeSourceInput >>= \case
        Left failure ->
            pure (FinalPreludeSourceLoadFailed failure)
        Right source ->
            Prelude.parseReservedPreludeSource source >>= \case
                Left failure ->
                    pure (FinalPreludeSourceParseFailed failure)
                Right parsed -> do
                    check <- Declaration.newImportCheck foundation
                    prepared <- either (impossible . show) pure =<< Declaration.prepareImports check []
                    buildParsedFinalPreludeCandidate foundation prepared parsed resolver

-- The production acquisition path establishes packaged provenance before
-- passing its already parsed source here.  The explicit parsed seam avoids a
-- second load and parse on a cache miss.
buildParsedFinalPreludeCandidate
    :: CheckedFoundation
    -> Declaration.PreparedImports
    -> Prelude.ReservedParsedPrelude
    -> Declaration.VampireResolver
    -> IO FinalPreludeBuildResult
buildParsedFinalPreludeCandidate foundation checkedImports parsed resolver =
    case validatePackagedPreludeInput parsed syntax >>
            unless (null (Declaration.preparedImportIds checkedImports))
                (Left (FinalPreludeValidationFailed FinalPreludeSemanticEnvironmentMismatch)) of
        Left failure -> do
            case emptyPrefix of
                Left prefixFailure ->
                    pure
                        (FinalPreludeBuildOpenFailed
                            (Declaration.DriverInitialPrefixError
                                prefixFailure))
                Right prefix ->
                    pure (FinalPreludeBuildFailed failure prefix)
        Right () -> do
            outcome <-
                Declaration.runModuleDriverFreshIO
                    foundation
                    preludeModuleName
                    checkedImports
                    resolver
                    do
                        PreludeModulePlan declarations terminal <-
                            Declaration.runProspectiveLoweringDriver
                                (planBlocks [] 0 blocks)
                        traverse_ admitPreludeDeclaration declarations
                        traverse_ failPreludePlanning terminal
            pure case outcome of
                Left failure ->
                    FinalPreludeBuildOpenFailed failure
                Right (Declaration.DriverFailed failure prefix) ->
                    FinalPreludeBuildFailed
                        (case failure of
                            Declaration.DriverDeclarationFailed err ->
                                FinalPreludeDeclarationFailed err
                            Declaration.DriverActionFailed err ->
                                err)
                        prefix
                Right (Declaration.DriverSealFailed failure prefix) ->
                    FinalPreludeBuildFailed
                        (FinalPreludeSealFailed failure)
                        prefix
                Right (Declaration.DriverSucceeded () evidence prefix) ->
                    case validateFinalPrelude foundation parsed
                            (Declaration.evidenceInterface evidence) prefix
                            (Declaration.evidenceClosure evidence) of
                        Left failure ->
                            FinalPreludeBuildFailed
                                (FinalPreludeValidationFailed failure)
                                prefix
                        Right (roles, basis) ->
                            FinalPreludeBuilt
                                (FinalPreludeCandidate
                                    parsed syntax evidence prefix basis roles)
  where
    identified = Prelude.reservedParsedPreludeModule parsed
    blocks = identifiedParsedModuleBlocks identified
    occurrences = identifiedParsedModuleSyntaxOccurrences identified
    syntax = identifiedParsedModuleSyntaxInterface identified

    emptyPrefix =
        Commit.emptyPendingModulePrefix
            <$> initialPrefixContextId
                (theoryId foundation)
                preludeModuleName
                []

    planBlocks completed _blockIndex [] = do
        planBaseStructure >>= \case
            Left failure ->
                pure
                    (PreludeModulePlan
                        (reverse completed)
                        (Just failure))
            Right base ->
                pure
                    (PreludeModulePlan
                        (reverse (base : completed))
                        Nothing)
    planBlocks completed blockIndex (block : remaining) =
        case block of
            Raw.BlockClaim Raw.Classification location _title _marker _claim ->
                pure
                    (PreludeModulePlan
                        (reverse completed)
                        (Just
                            (PreludePlanningAction
                                (FinalPreludeUnsupportedBlock location))))
            Raw.BlockClaim{} ->
                case remaining of
                    Raw.BlockProof _location proof _end : rest -> do
                        continue completed (blockIndex + 2) rest
                            =<< planOrdinaryProof block (Just proof)
                    _ -> do
                        continue completed (blockIndex + 1) remaining
                            =<< planImplicitClaim block
            Raw.BlockProof location _proof _end ->
                pure
                    (PreludeModulePlan
                        (reverse completed)
                        (Just
                            (PreludePlanningAction
                                (FinalPreludeUnmatchedProof location))))
            Raw.BlockAbbr{} -> do
                continue completed (blockIndex + 1) remaining
                    =<< planBinding blockIndex block
            Raw.BlockDefn{} -> do
                continue completed (blockIndex + 1) remaining
                    =<< planBinding blockIndex block
            _ ->
                pure
                    (PreludeModulePlan
                        (reverse completed)
                        (Just
                            (PreludePlanningAction
                                (FinalPreludeUnsupportedBlock
                                    (locate block)))))
      where
        continue accumulated nextIndex rest = \case
            Left failure ->
                pure
                    (PreludeModulePlan
                        (reverse accumulated)
                        (Just failure))
            Right declaration ->
                planBlocks (declaration : accumulated) nextIndex rest

    planBaseStructure = do
        slot <- Declaration.nextDeclarationSlotLowering
        theory <- Declaration.currentTheoryLowering
        baseClosure <- Declaration.checkedObjectClosureLowering
        let manifest = Builtin.builtinStructureManifest (declarationSlotOrdinal slot)
            field = Builtin.builtinCarrierFieldId manifest
            objects = [Record.fieldSelectorObject theory field, Record.fieldProjectionObject theory field]
        prepared <- Except.runExceptT do
            closure <- Except.liftEither (first Declaration.DeclarationObjectValidationFailed
                (extendObjectClosure baseClosure objects))
            contribution <- Except.liftEither (first Declaration.DeclarationObjectValidationFailed
                (checkedObjectContribution closure (assertedObjectId <$> objects)))
            inputs <- Except.liftEither (first (Declaration.StructureDeclarationInvalid . Text.pack . show)
                (Builtin.builtinStructureInputs closure manifest))
            Trans.lift (Generated.lowerStructureBatch contribution inputs) >>= Except.liftEither
        case prepared of
            Left failure -> planningDeclarationFailure failure
            Right checked -> planPreludeChecked PlannedPreludeBase checked

    planBinding blockIndex block = do
        prepared <-
            Binding.prepareBinding
                block
                [ parsedSyntaxOccurrenceEntry occurrence
                | occurrence <- occurrences
                , parsedSyntaxOccurrenceBlockIndex occurrence == blockIndex
                ]
        case prepared of
            Left failure ->
                pure
                    (Left
                        (PreludePlanningAction
                            (FinalPreludeElaborationFailed failure)))
            Right declaration -> do
                Binding.lowerPreparedBinding declaration >>= \case
                    Left failure -> planningDeclarationFailure failure
                    Right checked ->
                        planPreludeChecked PlannedPreludeBinding checked

    planImplicitClaim block = do
        foundationClaim <-
            Proof.prepareFinalPreludeFoundationClaim
                foundation block Nothing
        case foundationClaim of
            Right claim -> do
                Proof.lowerPreparedFinalPreludeFoundationClaim claim
                    >>= \case
                        Left failure -> planningDeclarationFailure failure
                        Right checked ->
                            planPreludeChecked PlannedPreludeFoundation checked
            Left Proof.ProofFoundationLeafTargetMismatch{} ->
                planGuardedRule block
            Left Proof.ProofFoundationLeafRequiresImplicitAuto{} ->
                planOrdinaryProof block Nothing
            Left failure ->
                pure
                    (Left
                        (PreludePlanningAction
                            (FinalPreludeProofFailed failure)))

    planGuardedRule block = do
        guarded <-
            Proof.prepareFinalPreludeGuardedRuleClaim
                foundation block
        case guarded of
            Right claim ->
                Proof.lowerPreparedFinalPreludeGuardedRuleClaim claim
                    >>= \case
                        Left failure -> planningDeclarationFailure failure
                        Right checked ->
                            planPreludeChecked PlannedPreludeGuardedRule checked
            Left Proof.ProofGuardedRuleTargetMismatch{} ->
                planOrdinaryProof block Nothing
            Left failure ->
                pure
                    (Left
                        (PreludePlanningAction
                            (FinalPreludeProofFailed failure)))

    planOrdinaryProof block explicitProof = do
        prepared <- Proof.prepareProof block explicitProof
        case prepared of
            Left failure ->
                pure
                    (Left
                        (PreludePlanningAction
                            (FinalPreludeProofFailed failure)))
            Right proof
                | Just location <-
                    Proof.preparedProofFirstOmission proof ->
                    pure
                        (Left
                            (PreludePlanningAction
                                (FinalPreludeOmittedProof location)))
                | otherwise ->
                    Proof.lowerPreparedProof proof >>= \case
                        Left failure -> planningDeclarationFailure failure
                        Right checked ->
                            planPreludeChecked PlannedPreludeProof checked

    planPreludeChecked
        :: forall body.
           (Declaration.PlannedDeclaration body
                -> PlannedPreludeDeclaration)
        -> Declaration.CheckedDeclaration body
        -> Declaration.LoweringDriver
            (Either PreludePlanningFailure PlannedPreludeDeclaration)
    planPreludeChecked constructor checked =
        Declaration.planCheckedDeclaration checked >>= \case
            Left failure -> planningDeclarationFailure failure
            Right planned -> pure (Right (constructor planned))

    planningDeclarationFailure =
        pure . Left . PreludePlanningDeclaration

    admitPreludeDeclaration = \case
        PlannedPreludeBinding planned ->
            void
                (Declaration.admitPlannedCheckedDeclaration
                    planned Binding.authorizeCheckedBinding)
        PlannedPreludeFoundation planned ->
            void
                (Declaration.admitPlannedCheckedDeclaration planned
                    Proof.authorizeCheckedFinalPreludeFoundationClaim)
        PlannedPreludeGuardedRule planned ->
            void
                (Declaration.admitPlannedCheckedDeclaration planned
                    Proof.authorizeCheckedFinalPreludeGuardedRuleClaim)
        PlannedPreludeProof planned ->
            void
                (Declaration.admitPlannedCheckedDeclaration
                    planned Proof.authorizeCheckedProof)
        PlannedPreludeBase planned ->
            void
                (Declaration.admitPlannedCheckedDeclaration planned
                    authorizeCheckedPreludeBaseStructure)

    failPreludePlanning = \case
        PreludePlanningAction failure ->
            Declaration.failModuleDriver failure
        PreludePlanningDeclaration failure ->
            Declaration.failDeclarationDriver failure

authorizeCheckedPreludeBaseStructure
    :: CheckedPreludeBaseStructureAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedPreludeBaseStructure = Generated.authorizeStructureBatch

data PreludeDeclaration = PreludeDeclaration
    !Raw.Block
    !Commit.CommittedDeclarationBatch

data PreludeDefinitionKind
    = PreludeDefinition
    | PreludeAbbreviation

data PreludeDefinitionView = PreludeDefinitionView
    !ObjectId
    !SemanticGlobalTarget

validateFinalPrelude
    :: CheckedFoundation
    -> Prelude.ReservedParsedPrelude
    -> SemanticInterface
    -> Commit.PendingModulePrefix
    -> CheckedObjectClosure
    -> Either
        FinalPreludeValidationError
        ( Map.Map PreludePublicRole FinalPreludeRoleTarget
        , NaturalNumeralBasis
        )
validateFinalPrelude foundation parsed semantic prefix objects = do
    (declarations, baseStructure) <-
        associatePreludeDeclarations parsed prefix
    validateConfinedAuthority
        foundation semantic objects declarations baseStructure
    resolveAndValidatePublicRoles foundation objects declarations

resolveAndValidatePublicRoles
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> [PreludeDeclaration]
    -> Either
        FinalPreludeValidationError
        ( Map.Map PreludePublicRole FinalPreludeRoleTarget
        , NaturalNumeralBasis
        )
resolveAndValidatePublicRoles foundation objects declarations = do
    choiceMember <-
        fst
            <$> expectClaimTarget
                declarations
                "choice_member"
                (frozenCoreTerm
                    (eliminateFrozenVoid
                        (foundationAxiomFrozen
                            foundation
                            GlobalChoiceMember)))

    universeReplacementClosed <-
        fst
            <$> expectClaimTarget
                declarations
                "universe_replacement_closed"
                (foundationTarget UnivOfReplacementClosed)

    universeMinimal <-
        fst
            <$> expectClaimTarget
                declarations
                "universe_minimal"
                (foundationTarget UnivOfMinimal)

    universeNested <-
        fst
            <$> expectClaimTarget
                declarations
                "universe_nested"
                expectedUniverseNested

    setLfpBound <- expectSetLfpClaim "lfp_bound" SetLfpBound
    setLfpLeast <- expectSetLfpClaim "lfp_least" SetLfpLeast
    setLfpFixed <- expectSetLfpClaim "lfp_fixed" SetLfpFixed
    setLfpInduct <- expectSetLfpClaim "lfp_induct" SetLfpInduct

    successor <-
        expectDefinitionBinding declarations "suc" PreludeDefinition
    let successorId = definitionViewObject successor
    successorBasis <-
        validateFinalPreludeSuccessorObject foundation objects successorId

    transitiveSet <-
        expectDefinition
            foundation objects declarations
            "transitiveset"
            PreludeDefinition
            (TyArrow TySet TyProp)
            expectedTransitiveSetBody
    let transitiveSetId = definitionViewObject transitiveSet

    inductive <-
        expectDefinition
            foundation objects declarations
            "inductive_set"
            PreludeDefinition
            (TyArrow TySet TyProp)
            (expectedInductiveBody successorId)
    let inductiveId = definitionViewObject inductive

    u0 <-
        expectDefinition
            foundation objects declarations
            "omega_universe"
            PreludeDefinition
            TySet
            (applyIntrinsic UnivOf (CIntrinsic Empty))
    let u0Id = definitionViewObject u0

    let omegaBody = expectedOmegaBody u0Id inductiveId
    omega <-
        expectDefinition
            foundation objects declarations
            "omega"
            PreludeDefinition
            TySet
            omegaBody
    let omegaId = definitionViewObject omega

    omegaConstruction <-
        expectedOmegaConstruction objects omegaBody
    omegaDerived <-
        maybe
            (Left
                (FinalPreludeFactContentMismatch
                    "omega"))
            Right
            (namedSetConstructionObjectFact
                (checkedFoundationSetConstruction foundation)
                objects
                omegaId
                omegaConstruction)

    naturalNumber <-
        expectDefinition
            foundation objects declarations
            "natural_number"
            PreludeAbbreviation
            (TyArrow TySet TyProp)
            (expectedNaturalNumberBody omegaId)
    let naturalNumberId = definitionViewObject naturalNumber
    case definitionViewTarget naturalNumber of
        TransparentExpansion{} -> pure ()
        _ ->
            Left
                (FinalPreludeDefinitionContentMismatch
                    "natural_number")

    (infinity, infinityTarget) <-
        expectClaim declarations "infinity"
    validateInfinityTarget objects inductiveId infinityTarget
    omegaDeclaration <- findDeclaration "omega" declarations
    omegaEquation <-
        validateOmegaDeclaration
            objects
            omegaId
            omegaBody
            omegaDerived
            omegaDeclaration
    let inductiveOmega =
            CApp (CGlobal inductiveId) (CGlobal omegaId)
        minimalOmega = expectedMinimality inductiveId omegaId
    omegaInductive <-
        fst
            <$> expectClaimTarget
                declarations
                "omega_inductive"
                inductiveOmega
    omegaMinimal <-
        fst
            <$> expectClaimTarget
                declarations
                "omega_minimal"
                minimalOmega

    let roles = Map.fromList
            [ ( PreludeGlobalChoiceMemberTheorem
              , FinalPreludeTheoremRole choiceMember
              )
            , ( PreludeUniverseReplacementClosedTheorem
              , FinalPreludeTheoremRole universeReplacementClosed
              )
            , ( PreludeUniverseMinimalTheorem
              , FinalPreludeTheoremRole universeMinimal
              )
            , ( PreludeUniverseNestedTheorem
              , FinalPreludeTheoremRole universeNested
              )
            , ( PreludeSetLfpBoundTheorem
              , FinalPreludeTheoremRole setLfpBound
              )
            , ( PreludeSetLfpLeastTheorem
              , FinalPreludeTheoremRole setLfpLeast
              )
            , ( PreludeSetLfpFixedTheorem
              , FinalPreludeTheoremRole setLfpFixed
              )
            , ( PreludeSetLfpInductTheorem
              , FinalPreludeTheoremRole setLfpInduct
              )
            , ( PreludeSuccessorObject
              , FinalPreludeObjectRole successorId
              )
            , ( PreludeTransitiveSetPredicate
              , FinalPreludeObjectRole transitiveSetId
              )
            , ( PreludeInductiveSetPredicate
              , FinalPreludeObjectRole inductiveId
              )
            , ( PreludeInfinityTheorem
              , FinalPreludeTheoremRole infinity
              )
            , ( PreludeOmegaObject
              , FinalPreludeObjectRole omegaId
              )
            , ( PreludeOmegaDefiningEquation
              , FinalPreludeTheoremRole omegaEquation
              )
            , ( PreludeNaturalsObject
              , FinalPreludeObjectRole omegaId
              )
            , ( PreludeNaturalNumberPredicate
              , FinalPreludeObjectRole naturalNumberId
              )
            , ( PreludeOmegaInductiveTheorem
              , FinalPreludeTheoremRole omegaInductive
              )
            , ( PreludeOmegaMinimalTheorem
              , FinalPreludeTheoremRole omegaMinimal
              )
            ]
    unless
        (Map.keysSet roles == expectedFinalPreludePublicRoles)
        (Left
            (FinalPreludePublicRoleMismatch
                PreludeInfinityTheorem))
    unless
        (Map.lookup PreludeSuccessorObject roles
            == Just
                (FinalPreludeObjectRole
                    (naturalNumeralBasisObject successorBasis)))
        (Left (FinalPreludePublicRoleMismatch PreludeSuccessorObject))
    pure (roles, successorBasis)
  where
    foundationTarget tag =
        frozenCoreTerm
            (eliminateFrozenVoid
                (foundationAxiomFrozen foundation tag))

    expectSetLfpClaim marker tag = do
        target <- expectedSetLfpRuleTarget foundation tag
        fst <$> expectClaimTarget declarations marker target

expectedSetLfpRuleTarget
    :: CheckedFoundation
    -> KernelRuleTag
    -> Either FinalPreludeValidationError (CanonicalTerm ObjectId)
expectedSetLfpRuleTarget foundation tag = do
    proof <-
        first (const (FinalPreludeFactContentMismatch marker))
            (KernelProof.setLfpRuleSchemaProof foundation tag)
    frozen <-
        maybe
            (Left (FinalPreludeFactContentMismatch marker))
            Right
            (closeScopedCore (KernelProof.builtProofStatement proof))
    pure
        (mapCanonicalGlobals absurd
            (frozenCoreTerm frozen))
  where
    marker = case tag of
        SetLfpBound -> "lfp_bound"
        SetLfpLeast -> "lfp_least"
        SetLfpFixed -> "lfp_fixed"
        SetLfpInduct -> "lfp_induct"

expectedOmegaConstruction
    :: CheckedObjectClosure
    -> CanonicalTerm ObjectId
    -> Either
        FinalPreludeValidationError
        (NamedSetConstruction ObjectId)
expectedOmegaConstruction objects = \case
    CApp (CApp (CIntrinsic Sep) bound) (CLam TySet predicate) -> do
        checkedBound <- checked [] bound
        checkedPredicate <- checked [TySet] predicate
        maybe
            (Left
                (FinalPreludeFactContentMismatch
                    "omega"))
            Right
            (checkedSeparationConstruction
                (globalTypingFromClosure objects)
                checkedBound
                checkedPredicate)
    _ ->
        Left
            (FinalPreludeFactContentMismatch
                "omega")
  where
    checked context term =
        first
            (const
                (FinalPreludeFactContentMismatch
                    "omega"))
            (checkScopedCanonicalCore
                (globalTypingFromClosure objects)
                context
                term)

validateOmegaDeclaration
    :: CheckedObjectClosure
    -> ObjectId
    -> CanonicalTerm ObjectId
    -> NamedSetConstructionFact
    -> PreludeDeclaration
    -> Either FinalPreludeValidationError TheoremRef
validateOmegaDeclaration objects omegaId omegaBody derived declaration = do
    let batch = declarationBatch declaration
        delta = Commit.committedBatchDelta batch
    omegaContent <- case lookupCheckedObjectContent omegaId objects of
        Just content@TransparentObjectContent{} -> pure content
        _ ->
            Left
                (FinalPreludeFactContentMismatch
                    "omega")
    unless
        ( declarationDeltaObjects delta == [omegaId]
          && case Commit.committedBatchObjects batch of
                [asserted] ->
                    assertedObjectId asserted == omegaId
                        && assertedObjectContent asserted == omegaContent
                _ -> False
          && null (Commit.committedBatchProofValidations batch)
        )
        (Left
            (FinalPreludeFactContentMismatch
                "omega"))
    certificates <-
        maybe
            (Left
                (FinalPreludeFactContentMismatch
                    "omega"))
            (Right . declarationValidationRecordCertificates)
            (Commit.committedBatchDeclarationValidation batch)
    validateOmegaFactInventory
        omegaId
        omegaBody
        (namedSetConstructionFactProposition derived)
        (namedSetConstructionFactDescriptor derived)
        (declarationDeltaFacts delta)
        (declarationDeltaAliases delta)
        (Commit.committedBatchPropositions batch)
        certificates

-- | Purpose-specific audit of the distinguished Omega definition.  It is
-- deliberately not a general declaration manifest: the confined prelude has
-- exactly one declaration whose public role requires this two-fact shape.
-- The explicit arguments also provide a narrow pure seam for corruption
-- regression tests.
validateOmegaFactInventory
    :: ObjectId
    -> CanonicalTerm ObjectId
    -> FrozenCheckedCore ObjectId
    -> CacheDigest
    -> [SemanticFactOccurrence]
    -> [SemanticAlias]
    -> [CheckedPropositionContent]
    -> [Authority.ValidationCertificate]
    -> Either FinalPreludeValidationError TheoremRef
validateOmegaFactInventory
        omegaId omegaBody expectedExtensional expectedDescriptor
        facts aliases propositions certificates = do
    (equationOccurrence, extensionalOccurrence) <-
        case facts of
            [equation, extensional] -> Right (equation, extensional)
            _ -> mismatch
    (equationCertificate, extensionalCertificate) <-
        case certificates of
            [equation, extensional] -> Right (equation, extensional)
            _ -> mismatch
    case aliases of
        [alias]
            | semanticAliasName alias == semanticName "omega"
            , semanticAliasTarget alias
                == semanticFactFingerprint extensionalOccurrence ->
                    pure ()
        _ -> mismatch
    equation <- propositionFor equationOccurrence
    extensional <- propositionFor extensionalOccurrence
    unless
        ( length propositions == 2
          && semanticFactSearchEligibility equationOccurrence
                == SearchIneligible
          && frozenCoreTerm (checkedPropositionTerm equation)
                == CEq TySet (CGlobal omegaId) omegaBody
          && Authority.validationTarget equationCertificate
                == semanticFactAuthority equationOccurrence
          && Authority.validationDirectAuthorization equationCertificate
                == Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionEquation omegaId)
          && semanticFactSearchEligibility extensionalOccurrence
                == SearchEligible
          && checkedPropositionTerm extensional == expectedExtensional
          && Authority.validationTarget extensionalCertificate
                == semanticFactAuthority extensionalOccurrence
          && Authority.validationDirectAuthorization extensionalCertificate
                == Authority.CheckedKernelConstruction
                    (Authority.CheckedSetConstructionExtensionality
                        omegaId expectedDescriptor)
        )
        mismatch
    pure
        (Authority.factAuthorityTheorem
            (semanticFactAuthority equationOccurrence))
  where
    mismatch =
        Left
            (FinalPreludeFactContentMismatch
                "omega")

    propositionFor occurrence =
        case List.filter
                ((== semanticFactProposition occurrence)
                    . checkedPropositionId)
                propositions of
            [proposition] -> Right proposition
            _ -> mismatch

validatePackagedPreludeInput
    :: Prelude.ReservedParsedPrelude
    -> ModuleSyntaxInterface
    -> Either FinalPreludeFailure ()
validatePackagedPreludeInput parsed syntax
    | freshModuleInputOwner input /= preludeModuleName =
        Left (FinalPreludeWrongOwner (freshModuleInputOwner input))
    | not (null (freshModuleInputImports input)) =
        Left (FinalPreludeHasImports (freshModuleInputImports input))
    | not (null (moduleSyntaxDirectInputs syntax)) =
        Left
            (FinalPreludeHasSyntaxImports
                (moduleSyntaxDirectInputs syntax))
    | otherwise = do
        unless
            ( freshModuleInputIsReserved input
              && freshModuleInputLocationPath input
                    == Prelude.preludeDiagnosticLabel
              && freshModuleInputSyntaxInterface input == syntax
              && identifiedParsedModuleSyntaxInterface identified == syntax
            )
            (Left
                (FinalPreludeValidationFailed
                    FinalPreludePackagedInputMismatch))
  where
    input = Prelude.reservedParsedPreludeInput parsed
    identified = Prelude.reservedParsedPreludeModule parsed

associatePreludeDeclarations
    :: Prelude.ReservedParsedPrelude
    -> Commit.PendingModulePrefix
    -> Either
        FinalPreludeValidationError
        ([PreludeDeclaration], Commit.CommittedDeclarationBatch)
associatePreludeDeclarations parsed prefix = do
    case List.splitAt (length sourceDeclarations) batches of
        (sourceBatches, [baseStructure])
            | length sourceBatches == length sourceDeclarations ->
                pure
                    ( zipWith PreludeDeclaration
                        sourceDeclarations sourceBatches
                    , baseStructure
                    )
        _ -> Left FinalPreludeDeclarationAssociationMismatch
  where
    sourceDeclarations =
        [ block
        | block <-
            identifiedParsedModuleBlocks
                (Prelude.reservedParsedPreludeModule parsed)
        , case block of
            Raw.BlockProof{} -> False
            _ -> True
        ]
    batches = Commit.pendingModulePrefixBatches prefix

validateConfinedAuthority
    :: CheckedFoundation
    -> SemanticInterface
    -> CheckedObjectClosure
    -> [PreludeDeclaration]
    -> Commit.CommittedDeclarationBatch
    -> Either FinalPreludeValidationError ()
validateConfinedAuthority
        foundation semantic objects declarations baseStructure = do
    unless
        ( semanticInterfaceOwner semantic == preludeModuleName
          && null (semanticInterfaceDirectInputs semantic)
        )
        (Left FinalPreludeSemanticEnvironmentMismatch)
    traverse_ requireTransparent
        [ identity
        | declaration <- declarations
        , identity <-
            declarationDeltaObjects
                (Commit.committedBatchDelta
                    (declarationBatch declaration))
        ]
    traverse_ (validateDeclarationAuthority foundation objects) declarations
    validateBaseStructure foundation objects baseStructure
  where
    requireTransparent identity =
        case lookupCheckedObjectContent identity objects of
            Just TransparentObjectContent{} -> pure ()
            _ -> Left (FinalPreludeUnexpectedObject identity)

validateBaseStructure
    :: CheckedFoundation -> CheckedObjectClosure -> Commit.CommittedDeclarationBatch
    -> Either FinalPreludeValidationError ()
validateBaseStructure foundation objects batch = do
    let slot = Commit.committedBatchSlot batch
        manifest = Builtin.builtinStructureManifest (declarationSlotOrdinal slot)
        delta = Commit.committedBatchDelta batch
        environment = declarationDeltaEnvironment delta
        facts = declarationDeltaFacts delta
        wires = semanticEnvironmentStructures environment
        certificates = maybe [] declarationValidationRecordCertificates
            (Commit.committedBatchDeclarationValidation batch)
        propositions = Map.fromList [(checkedPropositionId proposition, proposition)
            | proposition <- Commit.committedBatchPropositions batch]
        field = Builtin.builtinCarrierFieldId manifest
        theory = theoryId foundation
        selector = Record.fieldSelectorObjectId theory field
        projection = Record.fieldProjectionObjectId theory field
    unless (declarationSlotModule slot == preludeModuleName
            && null (semanticEnvironmentBindings environment)
            && null (Commit.committedBatchProofValidations batch)
            && length facts == length certificates
            && (Authority.validationTarget <$> certificates) == (semanticFactAuthority <$> facts)) mismatch
    inputs <- checked (Builtin.builtinStructureInputs objects manifest)
    schemas <- checked (Schema.resolveStructureBatch (const Nothing) inputs)
    checked (Builtin.checkBuiltinStructureSchemas manifest schemas)
    registrations <- for schemas \schema ->
        checked (Predicate.checkPendingStructureRegistration objects schema
            (transparentObjectId theory (Predicate.structurePredicateType schema) (Predicate.structurePredicateBody schema)))
    unless (length wires == length inputs) mismatch
    let factsByFingerprint = Map.fromList
            [(semanticFactFingerprint fact, (fact, certificate)) | (fact, certificate) <- zip facts certificates]
        registrationMap = Map.fromList [(Schema.resolvedSchemaId (Predicate.pendingStructureSchema registration), registration)
            | registration <- toList registrations]
    supplied <- fmap Map.fromList $ for (zip (toList inputs) wires) \(input, wire) -> do
        registration <- require (Map.lookup (Schema.localSchemaId input) registrationMap)
        expected <- checked (structureInterfaceWire input registration (structureWireLawIndex wire) (structureWireResourceIndex wire))
        unless (wire == expected) mismatch
        let references = Map.fromList
                ([(Schema.StructureLawFact key, fingerprint) | (key, fingerprint) <- Map.toAscList (structureWireLawIndex wire)]
                <> [(Schema.StructureResourceFact key, fingerprint) | (key, fingerprint) <- Map.toAscList (structureWireResourceIndex wire)])
        occurrences <- for references \fingerprint -> do
            (fact, certificate) <- require (Map.lookup fingerprint factsByFingerprint)
            proposition <- require (Map.lookup (semanticFactProposition fact) propositions)
            pure (StructureInterface.StructureOccurrence proposition fact certificate)
        pure (Schema.localSchemaId input, occurrences)
    _ <- checked (StructureInterface.checkStructureInterfaces foundation objects
        (Just . Authority.validationDirectAuthorization) (const Nothing) inputs registrations supplied)
    let indexed = Set.fromList [semanticFactFingerprint (StructureInterface.structureOccurrenceMetadata occurrence)
            | rows <- Map.elems supplied, occurrence <- Map.elems rows]
        extra = [(fact, certificate) | (fact, certificate) <- zip facts certificates
            , Set.notMember (semanticFactFingerprint fact) indexed]
        expectedObjects = Map.fromList
            [(assertedObjectId object, assertedObjectContent object)
            | object <- [Record.fieldSelectorObject theory field, Record.fieldProjectionObject theory field]
                <> [transparentObject theory (Predicate.structurePredicateType schema) (Predicate.structurePredicateBody schema)
                    | schema <- toList schemas]]
    case extra of
        [(fact, certificate)] -> do
            proposition <- require (Map.lookup (semanticFactProposition fact) propositions)
            unless (semanticFactPurpose fact == GeneralFactPurpose
                && frozenCoreTerm (checkedPropositionTerm proposition)
                    == canonicalDefinitionEquationTarget projection (TyArrow TySet TySet) (Record.fieldProjectionBody selector)
                && Authority.validationDirectAuthorization certificate
                    == Authority.CheckedKernelConstruction (Authority.CheckedDefinitionEquation projection)) mismatch
        _ -> mismatch
    unless (Set.fromList (declarationDeltaObjects delta) `Set.isSubsetOf` Map.keysSet expectedObjects
        && all (\(identity, content) -> lookupCheckedObjectContent identity objects == Just content) (Map.toAscList expectedObjects)
        && all (\object -> Map.lookup (assertedObjectId object) expectedObjects == Just (assertedObjectContent object))
            (Commit.committedBatchObjects batch)) mismatch
  where
    mismatch = Left FinalPreludeBaseStructureMismatch
    checked = first (const FinalPreludeBaseStructureMismatch)
    require = maybe mismatch Right

validateDeclarationAuthority
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> PreludeDeclaration
    -> Either FinalPreludeValidationError ()
validateDeclarationAuthority foundation objects declaration = do
    unless
        (fmap Authority.validationTarget certificates
            == fmap semanticFactAuthority facts)
        (Left (FinalPreludeValidationInventoryMismatch slot))
    traverse_ validateOne (zip facts certificates)
  where
    batch = declarationBatch declaration
    delta = Commit.committedBatchDelta batch
    slot = Commit.committedBatchSlot batch
    facts = declarationDeltaFacts delta
    certificates =
        ( Semantic.proofValidationRecordCertificate
            <$> Commit.committedBatchProofValidations batch
        )
        <> maybe
            []
            Semantic.declarationValidationRecordCertificates
            (Commit.committedBatchDeclarationValidation batch)

    validateOne (occurrence, certificate) = do
        unless
            (Authority.factAuthoritySafety
                (semanticFactAuthority occurrence)
                    == Authority.cleanAuthoritySafety)
            (Left (FinalPreludeAuthorityMismatch slot))
        proposition <-
            maybe
                (Left (FinalPreludeValidationInventoryMismatch slot))
                Right
                (List.find
                    ((== semanticFactProposition occurrence)
                        . checkedPropositionId)
                    (Commit.committedBatchPropositions batch))
        let target = frozenCoreTerm (checkedPropositionTerm proposition)
        case Authority.validationDirectAuthorization certificate of
            Authority.CheckedKernelConstruction
                    (Authority.FoundationLeaf tag) -> do
                let expected =
                        frozenCoreTerm
                            (eliminateFrozenVoid
                                (foundationAxiomFrozen foundation tag))
                    expectedEligibility =
                        case foundationAxiomBackendClass foundation tag of
                            FoundationFofProjectable -> SearchEligible
                            FoundationRequiresTh0{} -> SearchIneligible
                unless
                    ( target == expected
                      && semanticFactSearchEligibility occurrence
                            == expectedEligibility
                    )
                    (Left (FinalPreludeAuthorityMismatch slot))
            Authority.CheckedKernelConstruction
                    (Authority.GuardedFoundationRules rules) ->
                case Set.toList (Authority.guardedRuleTags rules) of
                    [tag] -> do
                        expected <-
                            expectedSetLfpRuleTarget foundation tag
                        unless
                            ( target == expected
                              && semanticFactSearchEligibility occurrence
                                    == SearchIneligible
                            )
                            (Left (FinalPreludeAuthorityMismatch slot))
                    _ ->
                        Left (FinalPreludeAuthorityMismatch slot)
            Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionEquation identity) ->
                case lookupCheckedObjectContent identity objects of
                    Just (TransparentObjectContent _theory coreType body) ->
                        unless
                            (target
                                == Declaration.definitionEquationTarget
                                    identity coreType body)
                            (Left (FinalPreludeAuthorityMismatch slot))
                    _ ->
                        Left (FinalPreludeAuthorityMismatch slot)
            Authority.CheckedKernelConstruction
                    (Authority.CheckedSetConstructionExtensionality
                        identity _descriptor) ->
                case lookupCheckedObjectContent identity objects of
                    Just TransparentObjectContent{}
                        | semanticFactSearchEligibility occurrence
                            == SearchEligible ->
                                pure ()
                    _ ->
                        Left (FinalPreludeAuthorityMismatch slot)
            Authority.CheckedSourceProof
                    (Authority.UsesExternalProof _requests) ->
                unless
                    ( case declarationBlock declaration of
                            Raw.BlockClaim kind _ _ _ _ ->
                                kind /= Raw.Classification
                            _ -> False
                    )
                    (Left (FinalPreludeAuthorityMismatch slot))
            Authority.CheckedKernelConstruction (Authority.CheckedDefinitionProjection identity path) ->
                unless (isDefinitionView occurrence target identity path)
                    (Left (FinalPreludeAuthorityMismatch slot))
            _ ->
                Left (FinalPreludeAuthorityMismatch slot)

    -- The ordinary declaration checker has already replayed these proofs.
    -- The confined prelude additionally admits only positive projections of
    -- this declaration's own equation, not arbitrary no-ATP source proofs.
    isDefinitionView occurrence target identity path =
        case declarationBlock declaration of
            Raw.BlockDefn{} ->
                semanticFactSearchEligibility occurrence == SearchIneligible
                    && semanticFactPurpose occurrence == GeneralFactPurpose
                    && any
                        ((== semanticFactFingerprint occurrence)
                            . registrationSource)
                        ([registration | registration <- declarationDeltaRegistrations delta
                            , RegisterNotionView{} <- [registrationBody registration]])
                    && any (projectsOwnDefinition target identity path)
                        (semanticEnvironmentBindings
                            (declarationDeltaEnvironment delta))
            _ -> False

    projectsOwnDefinition target expectedIdentity path binding =
        case semanticGlobalBindingTarget binding of
            GlobalReference identity
                | identity == expectedIdentity
                , Authority.CheckedKernelConstruction
                    (Authority.CheckedDefinitionEquation identity)
                    `elem` (Authority.validationDirectAuthorization <$> certificates)
                , Just (TransparentObjectContent _theory coreType body) <-
                    lookupCheckedObjectContent identity objects ->
                        predicateProjectionTarget identity coreType body path == Just target
            _ -> False

validateFinalPreludeSuccessorObject
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> ObjectId
    -> Either FinalPreludeValidationError NaturalNumeralBasis
validateFinalPreludeSuccessorObject foundation objects identity =
    first mapFailure
        (NaturalNumeral.checkNaturalNumeralBasis
            foundation objects identity)
  where
    mapFailure = \case
        NaturalNumeral.NaturalNumeralBasisTheoryMismatch{} ->
            FinalPreludeSemanticEnvironmentMismatch
        NaturalNumeral.NaturalNumeralBasisObjectMissing{} ->
            invalid
        NaturalNumeral.NaturalNumeralBasisObjectTypeMismatch{} ->
            invalid
        NaturalNumeral.NaturalNumeralBasisObjectNotTransparent{} ->
            invalid
        NaturalNumeral.NaturalNumeralBasisObjectBodyMismatch{} ->
            invalid

    invalid = FinalPreludeDefinitionContentMismatch "suc"

-- | Recover only the distinguished successor association from an already
-- validated cached semantic interface and its retained checked closure.  This
-- intentionally aligns parsed source declarations with semantic deltas
-- directly; transient commit batches do not exist on the cache-hit path.
recoverCachedFinalPreludeSuccessor
    :: CheckedFoundation
    -> Prelude.ReservedParsedPrelude
    -> SemanticInterface
    -> CheckedObjectClosure
    -> Either FinalPreludeValidationError NaturalNumeralBasis
recoverCachedFinalPreludeSuccessor foundation parsed semantic objects = do
    unless
        ( semanticInterfaceOwner semantic == preludeModuleName
          && null (semanticInterfaceDirectInputs semantic)
        )
        (Left FinalPreludeSemanticEnvironmentMismatch)
    (sourceDeltas, baseDelta) <-
        case List.splitAt (length sourceDeclarations) deltas of
            (aligned, [base])
                | length aligned == length sourceDeclarations ->
                    pure (aligned, base)
            _ -> Left FinalPreludeDeclarationAssociationMismatch
    traverse_ requireSlot
        (zip [0 :: Natural ..] (sourceDeltas <> [baseDelta]))
    case semanticEnvironmentStructures (declarationDeltaEnvironment baseDelta) of
        [root, onesorted]
            | structureWireSlot root == structureSlot 0
            , structureWireSlot onesorted == structureSlot 1 -> pure ()
        _ -> Left FinalPreludeBaseStructureMismatch
    (block, delta) <-
        case
            [ pair
            | pair@(candidate, _delta) <-
                zip sourceDeclarations sourceDeltas
            , blockMarkerText candidate == Just "suc"
            ] of
            [] -> Left (FinalPreludeDeclarationMissing "suc")
            [single] -> pure single
            _ -> Left (FinalPreludeDeclarationDuplicate "suc")
    successor <-
        expectDefinitionBindingFrom block delta "suc" PreludeDefinition
    validateFinalPreludeSuccessorObject
        foundation objects (definitionViewObject successor)
  where
    sourceDeclarations =
        [ block
        | block <-
            identifiedParsedModuleBlocks
                (Prelude.reservedParsedPreludeModule parsed)
        , case block of
            Raw.BlockProof{} -> False
            _ -> True
        ]
    deltas = semanticInterfaceDeclarations semantic

    requireSlot (ordinal, delta) =
        unless
            (declarationDeltaSlot delta
                == declarationSlot
                    preludeModuleName
                    (localDeclarationOrdinal ordinal))
            (Left FinalPreludeDeclarationAssociationMismatch)

expectDefinitionBinding
    :: [PreludeDeclaration]
    -> Text
    -> PreludeDefinitionKind
    -> Either FinalPreludeValidationError PreludeDefinitionView
expectDefinitionBinding declarations marker kind = do
    declaration <- findDeclaration marker declarations
    expectDefinitionBindingFrom
        (declarationBlock declaration)
        (Commit.committedBatchDelta (declarationBatch declaration))
        marker
        kind

expectDefinitionBindingFrom
    :: Raw.Block
    -> DeclarationInterfaceDelta
    -> Text
    -> PreludeDefinitionKind
    -> Either FinalPreludeValidationError PreludeDefinitionView
expectDefinitionBindingFrom block delta marker kind = do
    unless
        (case (kind, block) of
            (PreludeDefinition, Raw.BlockDefn{}) -> True
            (PreludeAbbreviation, Raw.BlockAbbr{}) -> True
            _ -> False)
        (Left (FinalPreludeDeclarationShapeMismatch marker))
    binding <-
        case semanticEnvironmentBindings
                (declarationDeltaEnvironment delta) of
            [single] -> Right single
            _ -> Left (FinalPreludeDeclarationShapeMismatch marker)
    let target = semanticGlobalBindingTarget binding
        identity = semanticGlobalTargetObject target
    unless
        (case (kind, target) of
            (PreludeDefinition, GlobalReference{}) -> True
            (PreludeAbbreviation, TransparentExpansion{}) -> True
            _ -> False)
        (Left (FinalPreludeDefinitionContentMismatch marker))
    pure (PreludeDefinitionView identity target)

expectDefinition
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> [PreludeDeclaration]
    -> Text
    -> PreludeDefinitionKind
    -> CoreType
    -> CanonicalTerm ObjectId
    -> Either FinalPreludeValidationError PreludeDefinitionView
expectDefinition foundation objects declarations marker kind coreType body = do
    view@(PreludeDefinitionView identity _target) <-
        expectDefinitionBinding declarations marker kind
    content <-
        maybe
            (Left (FinalPreludeDefinitionContentMismatch marker))
            Right
            (lookupCheckedObjectContent identity objects)
    let expected =
            TransparentObjectContent
                (theoryId foundation)
                coreType
                body
    unless (content == expected)
        (Left (FinalPreludeDefinitionContentMismatch marker))
    pure view

expectClaim
    :: [PreludeDeclaration]
    -> Text
    -> Either
        FinalPreludeValidationError
        (TheoremRef, CanonicalTerm ObjectId)
expectClaim declarations marker = do
    declaration <- findDeclaration marker declarations
    unless
        (case declarationBlock declaration of
            Raw.BlockClaim kind _ _ _ _ ->
                kind /= Raw.Classification
            _ -> False)
        (Left (FinalPreludeDeclarationShapeMismatch marker))
    expectFact declarations marker

expectClaimTarget
    :: [PreludeDeclaration]
    -> Text
    -> CanonicalTerm ObjectId
    -> Either
        FinalPreludeValidationError
        (TheoremRef, CanonicalTerm ObjectId)
expectClaimTarget declarations marker expected = do
    result@(_theorem, actual) <- expectClaim declarations marker
    unless
        (actual == expected)
        (Left (FinalPreludeFactContentMismatch marker))
    pure result

expectFact
    :: [PreludeDeclaration]
    -> Text
    -> Either
        FinalPreludeValidationError
        (TheoremRef, CanonicalTerm ObjectId)
expectFact declarations marker = do
    declaration <- findDeclaration marker declarations
    unless
        (length
            (declarationDeltaFacts
                (Commit.committedBatchDelta
                    (declarationBatch declaration))) == 1)
        (Left (FinalPreludeFactContentMismatch marker))
    expectAliasedFact declaration marker

expectAliasedFact
    :: PreludeDeclaration
    -> Text
    -> Either
        FinalPreludeValidationError
        (TheoremRef, CanonicalTerm ObjectId)
expectAliasedFact declaration marker = do
    let batch = declarationBatch declaration
        delta = Commit.committedBatchDelta batch
        expectedAlias = semanticName marker
    fingerprint <- case declarationDeltaAliases delta of
        [alias]
            | semanticAliasName alias == expectedAlias ->
                Right (semanticAliasTarget alias)
        _ -> Left (FinalPreludeFactContentMismatch marker)
    occurrence <- case List.filter
            ((== fingerprint) . semanticFactFingerprint)
            (declarationDeltaFacts delta) of
        [single] -> Right single
        _ -> Left (FinalPreludeFactContentMismatch marker)
    proposition <-
        maybe
            (Left (FinalPreludeFactContentMismatch marker))
            Right
            (List.find
                ((== semanticFactProposition occurrence)
                    . checkedPropositionId)
                (Commit.committedBatchPropositions batch))
    pure
        ( Authority.factAuthorityTheorem
            (semanticFactAuthority occurrence)
        , frozenCoreTerm (checkedPropositionTerm proposition)
        )

validateInfinityTarget
    :: CheckedObjectClosure
    -> ObjectId
    -> CanonicalTerm ObjectId
    -> Either FinalPreludeValidationError ()
validateInfinityTarget objects inductive = \case
    CApp (CGlobal predicate) (CGlobal witness)
        | predicate == inductive ->
            case lookupCheckedObjectContent witness objects of
                Just TransparentObjectContent{} -> pure ()
                _ ->
                    Left
                        (FinalPreludeFactContentMismatch
                            "infinity")
    _ ->
        Left
            (FinalPreludeFactContentMismatch
                "infinity")

findDeclaration
    :: Text
    -> [PreludeDeclaration]
    -> Either FinalPreludeValidationError PreludeDeclaration
findDeclaration marker declarations =
    case List.filter ((== marker) . declarationMarker) declarations of
        [] -> Left (FinalPreludeDeclarationMissing marker)
        [single] -> Right single
        _ -> Left (FinalPreludeDeclarationDuplicate marker)

declarationBlock :: PreludeDeclaration -> Raw.Block
declarationBlock (PreludeDeclaration block _batch) =
    block

declarationBatch
    :: PreludeDeclaration
    -> Commit.CommittedDeclarationBatch
declarationBatch (PreludeDeclaration _block batch) =
    batch

declarationMarker :: PreludeDeclaration -> Text
declarationMarker =
    fromMaybe "<unmarked>" . blockMarkerText . declarationBlock

definitionViewObject :: PreludeDefinitionView -> ObjectId
definitionViewObject (PreludeDefinitionView identity _target) =
    identity

definitionViewTarget
    :: PreludeDefinitionView
    -> SemanticGlobalTarget
definitionViewTarget (PreludeDefinitionView _identity target) =
    target

blockMarkerText :: Raw.Block -> Maybe Text
blockMarkerText = fmap (\(Raw.Marker marker) -> marker) . \case
    Raw.BlockAxiom _location _title marker _axiom -> Just marker
    Raw.BlockClaim _kind _location _title marker _claim -> Just marker
    Raw.BlockDefn _location _title marker _definition -> Just marker
    Raw.BlockAbbr _location _title marker _abbreviation -> Just marker
    Raw.BlockData _location _title marker _datatype -> Just marker
    Raw.BlockRecursive _location _title marker _definition -> Just marker
    Raw.BlockInductive _location _title marker _inductive -> Just marker
    Raw.BlockSig _location _title marker _assumptions _signature -> Just marker
    Raw.BlockStruct _location _title marker _structure -> Just marker
    Raw.BlockInstance _location _title marker _instance -> Just marker
    Raw.BlockConstruction _location _title marker _construction -> Just marker
    Raw.BlockProof{} -> Nothing

expectedUniverseNested :: CanonicalTerm ObjectId
expectedUniverseNested =
    CForall TySet
        (CForall TySet
            (CImp
                (memberTerm
                    (CBound 0)
                    (applyIntrinsic UnivOf (CBound 1)))
                (CForall TySet
                    (CImp
                        (memberTerm
                            (CBound 0)
                            (applyIntrinsic UnivOf (CBound 1)))
                        (memberTerm
                            (CBound 0)
                            (applyIntrinsic UnivOf (CBound 2)))))))

expectedTransitiveSetBody :: CanonicalTerm ObjectId
expectedTransitiveSetBody =
    CLam TySet
        (CForall TySet
            (CImp
                (memberTerm (CBound 0) (CBound 1))
                (CForall TySet
                    (CImp
                        (memberTerm (CBound 0) (CBound 1))
                        (memberTerm (CBound 0) (CBound 2))))))

expectedInductiveBody :: ObjectId -> CanonicalTerm ObjectId
expectedInductiveBody successor =
    CLam TySet
        (CAnd
            (memberTerm (CIntrinsic Empty) (CBound 0))
            (CForall TySet
                (CImp
                    (memberTerm (CBound 0) (CBound 1))
                    (memberTerm
                        (CApp (CGlobal successor) (CBound 0))
                        (CBound 1)))))

expectedOmegaBody
    :: ObjectId
    -> ObjectId
    -> CanonicalTerm ObjectId
expectedOmegaBody u0 inductive =
    CApp
        (CApp (CIntrinsic Sep) (CGlobal u0))
        (CLam TySet
            (CForall TySet
                (CImp
                    (CApp (CGlobal inductive) (CBound 0))
                    (memberTerm (CBound 1) (CBound 0)))))

expectedMinimality
    :: ObjectId
    -> ObjectId
    -> CanonicalTerm ObjectId
expectedMinimality inductive omega =
    CForall TySet
        (CImp
            (CApp (CGlobal inductive) (CBound 0))
            (CForall TySet
                (CImp
                    (memberTerm (CBound 0) (CGlobal omega))
                    (memberTerm (CBound 0) (CBound 1)))))

expectedNaturalNumberBody
    :: ObjectId
    -> CanonicalTerm ObjectId
expectedNaturalNumberBody omega =
    CLam TySet
        (memberTerm (CBound 0) (CGlobal omega))

applyIntrinsic
    :: CoreIntrinsicTag
    -> CanonicalTerm global
    -> CanonicalTerm global
applyIntrinsic intrinsic argument =
    CApp (CIntrinsic intrinsic) argument

applyIntrinsic2
    :: CoreIntrinsicTag
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
applyIntrinsic2 intrinsic firstArgument secondArgument =
    CApp
        (CApp (CIntrinsic intrinsic) firstArgument)
        secondArgument

memberTerm
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
memberTerm =
    applyIntrinsic2 Member
