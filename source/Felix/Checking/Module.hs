{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

-- | Explicit inputs and sealed outputs for the typed module driver.
module Felix.Checking.Module
    ( LiveModuleBinding(..)
    , IdentifiedModuleInput
    , identifiedPhysicalModule
    , identifiedReservedPrelude
    , identifiedModuleOwner
    , identifiedModuleBinding
    , identifiedModuleParsed
    , TypedSourceDeclaration
    , typedSourceDeclarationBlockIndex
    , typedSourceDeclarationHead
    , typedSourceDeclarationProof
    , typedSourceDeclarations
    , SealedTypedModule
    , sealedTypedModuleOwner
    , sealedTypedModuleSyntax
    , sealedTypedModuleSemantic
    , sealedTypedModuleEvidence
    , CachedTypedModuleError(..)
    , renderCachedTypedModuleError
    , cachedSealedTypedModule
    , CompletedTypedModule
    , completedTypedModuleSealed
    , completedTypedModulePrefix
    , publishCompletedModule
    , completeFinalPreludeCandidate
    , FinalPreludeSession
    , ModuleRootAcquisition(..)
    , finalPreludeSource
    , finalPreludeInput
    , finalPreludeModule
    , finalPreludeAcquisition
    , FinalPreludeReadiness
    , finalPreludeReadiness
    , BootstrapPreludeFixture
    , bootstrapPreludeInput
    , bootstrapPreludeCompleted
    , bootstrapPreludeReadiness
    , fixtureFinalPreludeReadinessFromSealed
    , BootstrapError(..)
    , buildBootstrapPreludeFixture
    , FinalPreludeReadinessError(..)
    , acquireFinalPreludeSession
    , TypedModuleInput
    , typedModulePreparedImports
    , TypedModuleInputError(..)
    , renderTypedModuleInputError
    , typedModuleInput
    , TypedPathError(..)
    , typedPathErrorDisposition
    , TypedModuleFailure(..)
    , typedModuleFailureLocation
    , renderTypedModuleFailure
    , typedModuleFailureDiagnostic
    , TypedModuleResult(..)
    , runTypedModuleEff
    , runTypedModuleFreshIO
    ) where

import Base
import Felix.Checking.Binding qualified as Binding
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Datatype qualified as Datatype
import Felix.Checking.Recursion qualified as Recursion
import Felix.Checking.Recursion.Frontend qualified as RecursionFrontend
import Felix.Checking.Inductive qualified as Inductive
import Felix.Checking.Instance qualified as Instance
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.SourceAxiom qualified as SourceAxiom
import Felix.Checking.Structure qualified as Structure
import Felix.Checking.FinalPrelude qualified as FinalPrelude
import Felix.Checking.Foundation
import Felix.Checking.Identity
import Felix.Checking.Semantic
import Felix.Checking.ValidationCache qualified as ValidationCache
import Felix.Module
import Felix.Parse
import Felix.Parsed.Module
import Felix.Prelude qualified as Prelude
import Felix.Source
import Felix.Store qualified as Store
import Felix.Report.Location
import Felix.Report.Diagnostic (Diagnostic)
import Felix.Syntax.Interface
import Felix.Syntax.Abstract qualified as Raw

import Control.Monad (unless)
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Text qualified as Text
import Effectful (Eff, IOE, (:>), runEff)


data LiveModuleBinding
    = PhysicalModuleBinding !ResolvedSource
    | ReservedModuleBinding !SourceDescriptor !FilePath
    deriving stock (Show, Eq)

data IdentifiedModuleInput = IdentifiedModuleInput
    !ModuleName
    !LiveModuleBinding
    !IdentifiedParsedModule

identifiedPhysicalModule :: ParsedModule -> IdentifiedModuleInput
identifiedPhysicalModule parsed =
    IdentifiedModuleInput
        (moduleName (parsedModuleAddress parsed))
        (PhysicalModuleBinding (parsedModuleResolved parsed))
        (parsedModuleIdentified parsed)

identifiedReservedPrelude
    :: Prelude.ReservedParsedPrelude
    -> IdentifiedModuleInput
identifiedReservedPrelude reserved =
    IdentifiedModuleInput
        (freshModuleInputOwner input)
        (ReservedModuleBinding
            (freshModuleInputSourceDescriptor input)
            (freshModuleInputLocationPath input))
        (Prelude.reservedParsedPreludeModule reserved)
  where
    input = Prelude.reservedParsedPreludeInput reserved

identifiedModuleOwner :: IdentifiedModuleInput -> ModuleName
identifiedModuleOwner (IdentifiedModuleInput owner _binding _parsed) =
    owner

identifiedModuleBinding
    :: IdentifiedModuleInput
    -> LiveModuleBinding
identifiedModuleBinding
        (IdentifiedModuleInput _owner binding _parsed) =
    binding

identifiedModuleParsed
    :: IdentifiedModuleInput
    -> IdentifiedParsedModule
identifiedModuleParsed
        (IdentifiedModuleInput _owner _binding parsed) =
    parsed


-- | One source declaration as consumed by the typed module driver.
--
-- A claim and its immediately following proof occupy one declaration slot.
-- The head block index remains the syntax-occurrence association index.
data TypedSourceDeclaration = TypedSourceDeclaration
    !Int
    !Raw.Block
    !(Maybe Raw.Proof)

typedSourceDeclarationBlockIndex :: TypedSourceDeclaration -> Int
typedSourceDeclarationBlockIndex
        (TypedSourceDeclaration blockIndex _head _proof) =
    blockIndex

typedSourceDeclarationHead :: TypedSourceDeclaration -> Raw.Block
typedSourceDeclarationHead
        (TypedSourceDeclaration _blockIndex headBlock _proof) =
    headBlock

typedSourceDeclarationProof
    :: TypedSourceDeclaration
    -> Maybe Raw.Proof
typedSourceDeclarationProof
        (TypedSourceDeclaration _blockIndex _head proof) =
    proof

typedSourceDeclarations
    :: IdentifiedParsedModule
    -> [TypedSourceDeclaration]
typedSourceDeclarations parsed =
    [ declaration
    | item <- typedSourceItems (identifiedParsedModuleBlocks parsed)
    , Just declaration <- [sourceItemDeclaration item]
    ]

data TypedSourceItem
    = TypedSourceDeclarationItem !TypedSourceDeclaration
    | TypedUnmatchedSourceProof !Location

sourceItemDeclaration
    :: TypedSourceItem
    -> Maybe TypedSourceDeclaration
sourceItemDeclaration = \case
    TypedSourceDeclarationItem declaration -> Just declaration
    TypedUnmatchedSourceProof{} -> Nothing

typedSourceItems :: [Raw.Block] -> [TypedSourceItem]
typedSourceItems = go 0
  where
    go _blockIndex [] = []
    go blockIndex (block : remaining)
        | isProofBearingHead block =
            case remaining of
                Raw.BlockProof _location proof _end : rest ->
                    TypedSourceDeclarationItem
                        (TypedSourceDeclaration blockIndex block (Just proof))
                        : go (blockIndex + 2) rest
                _ ->
                    TypedSourceDeclarationItem
                        (TypedSourceDeclaration blockIndex block Nothing)
                        : go (blockIndex + 1) remaining
    go blockIndex (Raw.BlockProof location _proof _end : remaining) =
        TypedUnmatchedSourceProof location
            : go (blockIndex + 1) remaining
    go blockIndex (block : remaining) =
        TypedSourceDeclarationItem
            (TypedSourceDeclaration blockIndex block Nothing)
            : go (blockIndex + 1) remaining

    isProofBearingHead = \case
        Raw.BlockClaim{} -> True
        Raw.BlockInstance{} -> True
        Raw.BlockConstruction{} -> True
        _ -> False


data SealedTypedModule = SealedTypedModule
    !ModuleSyntaxInterface
    !Declaration.ImportedModuleEvidence

-- Only a successful fresh check owns the actual batches available to publish.
data CompletedTypedModule = CompletedTypedModule
    !SealedTypedModule
    !Commit.PendingModulePrefix

completedTypedModuleSealed :: CompletedTypedModule -> SealedTypedModule
completedTypedModuleSealed (CompletedTypedModule sealed _) = sealed

completedTypedModulePrefix :: CompletedTypedModule -> Commit.PendingModulePrefix
completedTypedModulePrefix (CompletedTypedModule _ prefix) = prefix

-- The confined prelude checker has the same fresh publication product.
completeFinalPreludeCandidate :: FinalPrelude.FinalPreludeCandidate -> CompletedTypedModule
completeFinalPreludeCandidate candidate = CompletedTypedModule
    (SealedTypedModule (FinalPrelude.finalPreludeSyntax candidate) (FinalPrelude.finalPreludeEvidence candidate))
    (FinalPrelude.finalPreludePrefix candidate)

publishCompletedModule
    :: Store.StoreCheck -> ModuleArtefactKey -> CompletedTypedModule
    -> IO (Either Store.StoreFailure SealedTypedModule)
publishCompletedModule store key (CompletedTypedModule sealed prefix) = do
    written <- Store.writeSealedModule store key prefix
        (sealedTypedModuleSyntax sealed) (sealedTypedModuleSemantic sealed)
    pure (sealed <$ written)

sealedTypedModuleOwner :: SealedTypedModule -> ModuleName
sealedTypedModuleOwner = semanticInterfaceOwner . sealedTypedModuleSemantic

sealedTypedModuleSyntax :: SealedTypedModule -> ModuleSyntaxInterface
sealedTypedModuleSyntax (SealedTypedModule syntax _) = syntax

sealedTypedModuleSemantic :: SealedTypedModule -> SemanticInterface
sealedTypedModuleSemantic = Declaration.evidenceInterface . sealedTypedModuleEvidence

sealedTypedModuleEvidence :: SealedTypedModule -> Declaration.ImportedModuleEvidence
sealedTypedModuleEvidence (SealedTypedModule _ evidence) = evidence

sealedTypedModuleClosure :: SealedTypedModule -> CheckedObjectClosure
sealedTypedModuleClosure = Declaration.evidenceClosure . sealedTypedModuleEvidence


data CachedTypedModuleError
    = CachedTypedModuleEvidenceError !Declaration.DeclarationError
    deriving stock (Show, Eq)

renderCachedTypedModuleError :: CachedTypedModuleError -> Text
renderCachedTypedModuleError = \case
    CachedTypedModuleEvidenceError failure ->
        Declaration.renderDeclarationError failure

cachedSealedTypedModule
    :: Declaration.PreparedImports
    -> Store.CachedModuleCandidate
    -> IO (Either CachedTypedModuleError SealedTypedModule)
cachedSealedTypedModule prepared candidate = do
    admitted <- Declaration.admitCachedModuleEvidence prepared
        (Store.cachedCandidateSemantic candidate)
        (Store.cachedCandidateObjects candidate)
        (Store.cachedCandidatePropositions candidate)
        (Store.cachedCandidateCertificates candidate)
    pure (first CachedTypedModuleEvidenceError
        (fmap (\evidence -> SealedTypedModule
            (Store.cachedCandidateSyntax candidate)
            evidence) admitted))


data ModuleRootAcquisition
    = ModuleRootHit
    | ModuleRootMiss
    deriving stock (Show, Eq)

data FinalPreludeSession = FinalPreludeSession
    !Prelude.ReservedPreludeSourceInput
    !IdentifiedModuleInput
    !SealedTypedModule
    !Declaration.NaturalNumeralBasis
    !ModuleRootAcquisition

finalPreludeSource
    :: FinalPreludeSession
    -> Prelude.ReservedPreludeSourceInput
finalPreludeSource
        (FinalPreludeSession source _input _module _basis _acquisition) =
    source

finalPreludeInput
    :: FinalPreludeSession
    -> IdentifiedModuleInput
finalPreludeInput
        (FinalPreludeSession _source input _module _basis _acquisition) =
    input

finalPreludeModule
    :: FinalPreludeSession
    -> SealedTypedModule
finalPreludeModule
        (FinalPreludeSession _source _input sealed _basis _acquisition) =
    sealed

finalPreludeAcquisition
    :: FinalPreludeSession
    -> ModuleRootAcquisition
finalPreludeAcquisition
        (FinalPreludeSession _source _input _sealed _basis acquisition) =
    acquisition

data FinalPreludeReadiness = FinalPreludeReadiness
    !SealedTypedModule
    !(Maybe Declaration.NaturalNumeralBasis)

finalPreludeReadiness
    :: FinalPreludeSession
    -> FinalPreludeReadiness
finalPreludeReadiness session =
    FinalPreludeReadiness
        (finalPreludeModule session)
        (Just basis)
  where
    FinalPreludeSession _source _input _module basis _acquisition = session

-- | Test-only empty-prelude fixture.
--
-- It is exported for focused declaration-compiler tests.  Production
-- acquisition is exclusively 'acquireFinalPreludeSession'.
data BootstrapPreludeFixture = BootstrapPreludeFixture
    !IdentifiedModuleInput
    !CompletedTypedModule

bootstrapPreludeInput
    :: BootstrapPreludeFixture
    -> IdentifiedModuleInput
bootstrapPreludeInput (BootstrapPreludeFixture input _module) = input

bootstrapPreludeCompleted
    :: BootstrapPreludeFixture
    -> CompletedTypedModule
bootstrapPreludeCompleted (BootstrapPreludeFixture _input sealed) = sealed

-- | Test-only seam for the empty bootstrap compiler input.
bootstrapPreludeReadiness
    :: BootstrapPreludeFixture
    -> FinalPreludeReadiness
bootstrapPreludeReadiness =
    (\sealed -> FinalPreludeReadiness sealed Nothing)
        . completedTypedModuleSealed . bootstrapPreludeCompleted

-- | Test-only seam for exercising a synthetic distinguished prelude.
fixtureFinalPreludeReadinessFromSealed
    :: CheckedFoundation
    -> ObjectId
    -> SealedTypedModule
    -> Either
        FinalPrelude.FinalPreludeValidationError
        FinalPreludeReadiness
fixtureFinalPreludeReadinessFromSealed foundation successor sealed = do
    basis <- FinalPrelude.validateFinalPreludeSuccessorObject
        foundation (sealedTypedModuleClosure sealed) successor
    pure (FinalPreludeReadiness sealed (Just basis))

data BootstrapError
    = BootstrapParseFailed !Prelude.PreludeParseError
    | BootstrapDriverOpenFailed !Declaration.DriverOpenError
    | BootstrapDeclarationFailed !Declaration.DeclarationError
    | BootstrapSealFailed !SemanticInterfaceError
    deriving stock (Show)

-- | Construct the empty distinguished prelude used only by compiler fixtures.
buildBootstrapPreludeFixture
    :: CheckedFoundation
    -> Declaration.VampireResolver
    -> IO (Either BootstrapError BootstrapPreludeFixture)
buildBootstrapPreludeFixture foundation resolver = do
    parsedResult <-
        Prelude.parseReservedPreludeSource
            Prelude.emptyBootstrapSourceInput
    case parsedResult of
        Left err ->
            pure (Left (BootstrapParseFailed err))
        Right reserved -> do
            let input = identifiedReservedPrelude reserved
                syntax =
                    identifiedParsedModuleSyntaxInterface
                        (identifiedModuleParsed input)
            check <- Declaration.newImportCheck foundation
            prepared <- either (impossible . show) pure =<< Declaration.prepareImports check []
            driver <-
                Declaration.runModuleDriverFreshIO
                    foundation
                    preludeModuleName
                    prepared
                    resolver
                    emptyDriver
            pure case driver of
                Left err ->
                    Left (BootstrapDriverOpenFailed err)
                Right (Declaration.DriverSucceeded () evidence prefix) ->
                    Right (BootstrapPreludeFixture input
                        (CompletedTypedModule (SealedTypedModule syntax evidence) prefix))
                Right
                    (Declaration.DriverFailed
                        (Declaration.DriverDeclarationFailed err)
                        _prefix) ->
                            Left (BootstrapDeclarationFailed err)
                Right (Declaration.DriverSealFailed err _prefix) ->
                    Left (BootstrapSealFailed err)
  where
    emptyDriver :: Declaration.ModuleDriver Void ()
    emptyDriver = pure ()


data FinalPreludeReadinessError
    = FinalPreludeReadinessSourceLoadFailed !Prelude.PreludeLoadError
    | FinalPreludeReadinessSourceParseFailed !Prelude.PreludeParseError
    | FinalPreludeReadinessBuildFailed !FinalPrelude.FinalPreludeFailure
    | FinalPreludeReadinessBuildOpenFailed !Declaration.DriverOpenError
    | FinalPreludeReadinessArtefactKeyFailed !ModuleArtefactKeyError
    | FinalPreludeReadinessStoreFailed !Store.StoreFailure
    | FinalPreludeReadinessCachedModuleFailed !CachedTypedModuleError
    | FinalPreludeReadinessCachedPreludeInvalid
        !FinalPrelude.FinalPreludeValidationError
    deriving stock (Show)

-- | Acquire the exact packaged prelude through its ordinary module root.
--
-- Loading and parsing happen once before the root lookup.  A hit is validated
-- and materialized through the generic cached-module boundary; a miss reuses
-- that parsed input for confined construction and atomic publication.
acquireFinalPreludeSession
    :: Declaration.ImportCheck
    -> Store.StoreCheck
    -> CheckedFoundation
    -> Declaration.VampireResolver
    -> IO (Either FinalPreludeReadinessError FinalPreludeSession)
acquireFinalPreludeSession check storeCheck foundation resolver = do
    prepared <- either (impossible . show) pure =<< Declaration.prepareImports check []
    acquirePrepared prepared
  where
    acquirePrepared prepared = Prelude.loadReservedPreludeSourceInput >>= \case
        Left failure ->
            pure (Left (FinalPreludeReadinessSourceLoadFailed failure))
        Right source ->
            Prelude.parseReservedPreludeSource source >>= \case
                Left failure ->
                    pure (Left (FinalPreludeReadinessSourceParseFailed failure))
                Right parsed ->
                    acquire prepared source parsed
    acquire prepared source parsed =
        case moduleArtefactKey
                preludeModuleName
                parsedId
                []
                (theoryId foundation) of
            Left failure ->
                pure (Left (FinalPreludeReadinessArtefactKeyFailed failure))
            Right key -> do
                Store.loadCachedModuleCandidate
                    storeCheck key (moduleSyntaxAssertedId syntax) >>= \case
                    Left failure ->
                        pure (Left (FinalPreludeReadinessStoreFailed failure))
                    Right (Just installation) -> do
                        admitted <- cachedSealedTypedModule prepared installation
                        pure do
                            sealed <- first FinalPreludeReadinessCachedModuleFailed admitted
                            basis <-
                                first FinalPreludeReadinessCachedPreludeInvalid
                                    (FinalPrelude.recoverCachedFinalPreludeSuccessor
                                        foundation
                                        parsed
                                        (sealedTypedModuleSemantic sealed)
                                        (sealedTypedModuleClosure sealed))
                            pure
                                (FinalPreludeSession
                                    source identified sealed basis ModuleRootHit)
                    Right Nothing ->
                        build prepared source parsed key
      where
        identified = identifiedReservedPrelude parsed
        parsedId = identifiedParsedModuleId (identifiedModuleParsed identified)
        syntax = identifiedParsedModuleSyntaxInterface
            (identifiedModuleParsed identified)

    build prepared source parsed key =
        FinalPrelude.buildParsedFinalPreludeCandidate
            foundation prepared parsed resolver >>= \case
                FinalPrelude.FinalPreludeBuildFailed failure _prefix ->
                    pure (Left (FinalPreludeReadinessBuildFailed failure))
                FinalPrelude.FinalPreludeBuildOpenFailed failure ->
                    pure (Left (FinalPreludeReadinessBuildOpenFailed failure))
                FinalPrelude.FinalPreludeBuilt candidate ->
                    publish source key candidate
                FinalPrelude.FinalPreludeSourceLoadFailed failure ->
                    pure (Left (FinalPreludeReadinessSourceLoadFailed failure))
                FinalPrelude.FinalPreludeSourceParseFailed failure ->
                    pure (Left (FinalPreludeReadinessSourceParseFailed failure))

    publish source key candidate = do
        let parsed = FinalPrelude.finalPreludeParsed candidate
            identified = identifiedReservedPrelude parsed
            basis = FinalPrelude.finalPreludeNaturalNumeralBasis candidate
            completed = completeFinalPreludeCandidate candidate
        publishCompletedModule storeCheck key completed >>= \case
            Left failure -> pure (Left (FinalPreludeReadinessStoreFailed failure))
            Right sealed -> pure (Right (FinalPreludeSession source identified sealed basis ModuleRootMiss))



data TypedModuleInput = TypedModuleInput
    !ModuleName
    !IdentifiedModuleInput
    !ModuleSyntaxInterface
    !CheckedFoundation
    !FinalPreludeReadiness
    !Declaration.PreparedImports
    !Declaration.VampireResolver

typedModulePreparedImports :: TypedModuleInput -> Declaration.PreparedImports
typedModulePreparedImports (TypedModuleInput _ _ _ _ _ prepared _) = prepared

data TypedModuleInputError
    = TypedDirectModuleMismatch ![ModuleName] ![ModuleName]
    | TypedSyntaxInputMismatch ![SyntaxInterfaceId] ![SyntaxInterfaceId]
    | TypedImportPreparationFailed !Declaration.DeclarationError
    deriving stock (Show, Eq)

renderTypedModuleInputError :: TypedModuleInputError -> Text
renderTypedModuleInputError = \case
    TypedImportPreparationFailed failure -> Declaration.renderDeclarationError failure
    TypedDirectModuleMismatch expected actual ->
        "direct module inputs differ: expected " <> shown expected
            <> ", found " <> shown actual
    TypedSyntaxInputMismatch expected actual ->
        "direct syntax inputs differ: expected " <> shown expected
            <> ", found " <> shown actual
  where
    shown :: Show value => value -> Text
    shown = Text.pack . show

typedModuleInput
    :: Declaration.ImportCheck
    -> CheckedFoundation
    -> FinalPreludeReadiness
    -> Declaration.VampireResolver
    -> ParsedModule
    -> [SealedTypedModule]
    -> IO (Either TypedModuleInputError TypedModuleInput)
typedModuleInput check foundation readiness resolver parsed direct =
    case associate of
        Left failure -> pure (Left failure)
        Right () -> do
            prepared <- Declaration.prepareImports check
                (sealedTypedModuleEvidence <$> (prelude : direct))
            pure (first TypedImportPreparationFailed
                (TypedModuleInput owner identified syntax foundation readiness
                    <$> prepared <*> pure resolver))
  where
    associate = do
        unless (expectedOwners == actualOwners)
            (Left
                (TypedDirectModuleMismatch
                    expectedOwners
                    actualOwners))
        unless (expectedSyntax == actualSyntax)
            (Left
                (TypedSyntaxInputMismatch
                    expectedSyntax
                    actualSyntax))
        pure ()
    identified = identifiedPhysicalModule parsed
    owner = identifiedModuleOwner identified
    syntax = identifiedParsedModuleSyntaxInterface (identifiedModuleParsed identified)
    expectedOwners =
        moduleName
            <$> nubOrd
                (parsedImportedAddress
                    <$> parsedModuleImports parsed)
    actualOwners = sealedTypedModuleOwner <$> direct
    expectedSyntax =
        nubOrd
            ( moduleSyntaxAssertedId
                (sealedTypedModuleSyntax prelude)
              : ( moduleSyntaxAssertedId
                    . sealedTypedModuleSyntax
                    <$> direct
                )
            )
    actualSyntax = moduleSyntaxDirectInputs syntax
    FinalPreludeReadiness prelude _basis = readiness

data TypedPathError
    = TypedElaborationFailed !Elaboration.ElaborationError
    | TypedDatatypeFailed !Datatype.DatatypeError
    | TypedInductiveFailed !Inductive.InductiveError
    | TypedInstanceFailed !Instance.InstanceError
    | TypedProofFailed !Proof.ProofError
    | TypedUnmatchedProof !Location
    deriving stock (Show, Eq)

typedPathErrorDisposition
    :: TypedPathError
    -> Proof.ProofErrorDisposition
typedPathErrorDisposition = \case
    TypedElaborationFailed{} -> Proof.ProofSourceRejection
    TypedDatatypeFailed{} -> Proof.ProofSourceRejection
    TypedInductiveFailed{} -> Proof.ProofSourceRejection
    TypedInstanceFailed failure ->
        Instance.instanceErrorDisposition failure
    TypedProofFailed failure -> Proof.proofErrorDisposition failure
    TypedUnmatchedProof{} -> Proof.ProofSourceRejection

data TypedModuleFailure
    = TypedDeclarationFailed !Declaration.DeclarationError
    | TypedActionFailed !TypedPathError
    | TypedSealFailed !SemanticInterfaceError
    deriving stock (Show, Eq)

typedModuleFailureLocation :: TypedModuleFailure -> Maybe Location
typedModuleFailureLocation = \case
    TypedActionFailed (TypedElaborationFailed failure) ->
        Just (Elaboration.elaborationErrorLocation failure)
    TypedActionFailed (TypedDatatypeFailed failure) ->
        Just (Datatype.datatypeErrorLocation failure)
    TypedActionFailed (TypedInductiveFailed failure) ->
        Just (Inductive.inductiveErrorLocation failure)
    TypedActionFailed (TypedInstanceFailed failure) ->
        Just (Instance.instanceErrorLocation failure)
    TypedActionFailed (TypedProofFailed failure) ->
        Just (Proof.proofErrorLocation failure)
    TypedActionFailed (TypedUnmatchedProof location) ->
        Just location
    TypedDeclarationFailed failure ->
        Declaration.declarationErrorLocation failure
    TypedSealFailed{} ->
        Nothing

renderTypedModuleFailure :: TypedModuleFailure -> Text
renderTypedModuleFailure = \case
    TypedDeclarationFailed failure ->
        Declaration.renderDeclarationError failure
    TypedActionFailed (TypedElaborationFailed failure) ->
        Elaboration.renderElaborationError failure
    TypedActionFailed (TypedDatatypeFailed failure) ->
        Datatype.renderDatatypeError failure
    TypedActionFailed (TypedInductiveFailed failure) ->
        Inductive.renderInductiveError failure
    TypedActionFailed (TypedInstanceFailed failure) ->
        Instance.renderInstanceError failure
    TypedActionFailed (TypedProofFailed failure) ->
        Proof.renderProofError failure
    TypedActionFailed (TypedUnmatchedProof location) ->
        locationToText location
            <> ": this proof does not follow a claim"
    TypedSealFailed failure ->
        renderSemanticInterfaceError failure

typedModuleFailureDiagnostic :: TypedModuleFailure -> Maybe Diagnostic
typedModuleFailureDiagnostic = \case
    TypedActionFailed (TypedInstanceFailed (Instance.InstanceProofFailed failure)) ->
        Proof.proofErrorDiagnostic failure
    TypedActionFailed (TypedProofFailed failure) ->
        Proof.proofErrorDiagnostic failure
    _failure -> Nothing

data TypedModuleResult
    = TypedModuleOpenFailed !Declaration.DriverOpenError
    | TypedModuleSucceeded !CompletedTypedModule
    | TypedModuleFailed
        !TypedModuleFailure
        !Commit.PendingModulePrefix

data PlannedTypedDeclaration
    = PlannedBinding
        !(Declaration.PlannedDeclaration
            Binding.CheckedBindingAuthorization)
    | PlannedSourceAxiom
        !(Declaration.PlannedDeclaration ())
    | PlannedInductive
        !(Declaration.PlannedDeclaration
            Inductive.CheckedInductiveAuthorization)
    | PlannedDatatype
        !(Declaration.PlannedDeclaration
            Datatype.CheckedDatatypeAuthorization)
    | PlannedRecursive
        !(Declaration.PlannedDeclaration Recursion.CheckedRecursionAuthorization)
    | PlannedStructure
        !(Declaration.PlannedDeclaration
            Structure.CheckedStructureAuthorization)
    | PlannedInstance
        !(Declaration.PlannedDeclaration
            Instance.CheckedInstanceAuthorization)
    | PlannedProof
        !(Declaration.PlannedDeclaration
            Proof.CheckedProofAuthorization)

data TypedPlanningFailure
    = TypedPlanningPathFailure !TypedPathError
    | TypedPlanningDeclarationFailure !Declaration.DeclarationError

data TypedModulePlan = TypedModulePlan
    ![PlannedTypedDeclaration]
    !(Maybe TypedPlanningFailure)

runTypedModuleEff
    :: (ValidationCache.ValidationCache :> es, IOE :> es)
    => TypedModuleInput
    -> Eff es TypedModuleResult
runTypedModuleEff
        (TypedModuleInput
            owner identified syntax foundation readiness checkedImports resolver) = do
    let FinalPreludeReadiness _prelude maybeBasis = readiness
        action = do
            TypedModulePlan planned terminal <-
                Declaration.runProspectiveLoweringDriver
                    (planSourceItems []
                        (typedSourceItems
                            (identifiedParsedModuleBlocks
                                (identifiedModuleParsed identified))))
            traverse_ admitPlannedDeclaration planned
            traverse_ failPlanning terminal
        occurrences =
            identifiedParsedModuleSyntaxOccurrences
                (identifiedModuleParsed identified)
        planSourceItems completed [] =
            pure (TypedModulePlan (reverse completed) Nothing)
        planSourceItems completed (item : remaining) =
            case item of
                TypedUnmatchedSourceProof location ->
                    pure
                        (TypedModulePlan
                            (reverse completed)
                            (Just
                                (TypedPlanningPathFailure
                                    (TypedUnmatchedProof location))))
                TypedSourceDeclarationItem declaration -> do
                    planDeclaration declaration >>= \case
                        Left failure ->
                            pure
                                (TypedModulePlan
                                    (reverse completed)
                                    (Just failure))
                        Right planned ->
                            planSourceItems (planned : completed) remaining

        planDeclaration sourceDeclaration =
            case block of
                Raw.BlockClaim{} ->
                    planClaim block explicitProof
                Raw.BlockProof{} ->
                    impossible
                        "typed declaration association retained a proof head"
                Raw.BlockSig{} ->
                    planSelected block
                Raw.BlockAbbr{} ->
                    planSelected block
                Raw.BlockDefn{} ->
                    planSelected block
                Raw.BlockAxiom{} ->
                    planSourceAxiom block
                Raw.BlockInductive{} ->
                    planInductive block
                Raw.BlockData{} ->
                    planDatatype block
                Raw.BlockRecursive{} ->
                    planPrepared TypedElaborationFailed PlannedRecursive
                        (RecursionFrontend.prepareRecursiveDefinition block lexicalEntries)
                        (fmap (first Declaration.BindingConstructionInvalid) . Recursion.lowerRecursiveDefinition)
                Raw.BlockStruct{} ->
                    planStructure block
                Raw.BlockInstance{} ->
                    planInstance block explicitProof
                Raw.BlockConstruction{} ->
                    planInstance block explicitProof
          where
            blockIndex =
                typedSourceDeclarationBlockIndex sourceDeclaration
            block = typedSourceDeclarationHead sourceDeclaration
            explicitProof =
                typedSourceDeclarationProof sourceDeclaration

            blockOccurrences =
                [ occurrence
                | occurrence <- occurrences
                , parsedSyntaxOccurrenceBlockIndex occurrence == blockIndex
                ]
            lexicalEntries = map parsedSyntaxOccurrenceEntry blockOccurrences

            planSelected selected =
                planPrepared TypedElaborationFailed PlannedBinding
                    (Binding.prepareBinding selected lexicalEntries)
                    Binding.lowerPreparedBinding

            planSourceAxiom selected =
                planPrepared TypedElaborationFailed PlannedSourceAxiom
                    (SourceAxiom.prepareSourceAxiom selected)
                    SourceAxiom.lowerPreparedSourceAxiom

            planInductive selected =
                planPrepared TypedInductiveFailed PlannedInductive
                    (Inductive.prepareInductive foundation selected lexicalEntries)
                    Inductive.lowerPreparedInductive

            planDatatype selected =
                planPrepared TypedDatatypeFailed PlannedDatatype
                    (Datatype.prepareDatatype selected
                        [ ( parsedSyntaxOccurrenceLocation occurrence
                          , parsedSyntaxOccurrenceMarker occurrence
                          , parsedSyntaxOccurrenceEntry occurrence
                          )
                        | occurrence <- blockOccurrences
                        ])
                    Datatype.lowerPreparedDatatype

            planStructure selected =
                planPrepared TypedElaborationFailed PlannedStructure
                    (Structure.prepareStructure selected lexicalEntries)
                    Structure.lowerPreparedStructure

            planClaim selected selectedProof =
                planPrepared TypedProofFailed PlannedProof
                    (Proof.prepareProof selected selectedProof)
                    Proof.lowerPreparedProof

            planInstance selected selectedProof =
                planPrepared TypedInstanceFailed PlannedInstance
                    (Instance.prepareInstance selected selectedProof lexicalEntries)
                    Instance.lowerPreparedInstance

            planPrepared
                :: forall failure prepared body.
                   (failure -> TypedPathError)
                -> (Declaration.PlannedDeclaration body -> PlannedTypedDeclaration)
                -> Declaration.LoweringDriver (Either failure prepared)
                -> (prepared -> Declaration.LoweringDriver
                        (Either Declaration.DeclarationError
                            (Declaration.CheckedDeclaration body)))
                -> Declaration.LoweringDriver
                    (Either TypedPlanningFailure PlannedTypedDeclaration)
            planPrepared toPathError constructor prepare lower = Except.runExceptT do
                prepared <- Except.ExceptT $
                    first (TypedPlanningPathFailure . toPathError) <$> prepare
                checked <- Except.ExceptT $
                    first TypedPlanningDeclarationFailure <$> lower prepared
                planned <- Except.ExceptT $
                    first TypedPlanningDeclarationFailure
                        <$> Declaration.planCheckedDeclaration checked
                pure (constructor planned)

        admitPlannedDeclaration = \case
            PlannedBinding planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned Binding.authorizeCheckedBinding)
            PlannedSourceAxiom planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned SourceAxiom.authorizeCheckedSourceAxiom)
            PlannedInductive planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned
                        Inductive.authorizeCheckedInductive)
            PlannedDatatype planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned Datatype.authorizeCheckedDatatype)
            PlannedRecursive planned ->
                void (Declaration.admitPlannedCheckedDeclaration planned Recursion.authorizeCheckedRecursion)
            PlannedStructure planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned Structure.authorizeCheckedStructure)
            PlannedInstance planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned
                        Instance.authorizeCheckedInstance)
            PlannedProof planned ->
                void
                    (Declaration.admitPlannedCheckedDeclaration
                        planned Proof.authorizeCheckedProof)

        failPlanning = \case
            TypedPlanningPathFailure failure ->
                Declaration.failModuleDriver failure
            TypedPlanningDeclarationFailure failure ->
                Declaration.failDeclarationDriver failure
    result <-
        case maybeBasis of
            Nothing ->
                Declaration.runModuleDriverEff
                    foundation
                    owner
                    checkedImports
                    resolver
                    action
            Just basis ->
                Declaration.runModuleDriverEffWithNaturalNumeralBasis
                    foundation
                    basis
                    owner
                    checkedImports
                    resolver
                    action
    pure case result of
        Left err ->
            TypedModuleOpenFailed err
        Right (Declaration.DriverSucceeded () evidence prefix) ->
            TypedModuleSucceeded (CompletedTypedModule (SealedTypedModule syntax evidence) prefix)
        Right
            (Declaration.DriverFailed failure prefix) ->
                TypedModuleFailed
                    (case failure of
                        Declaration.DriverDeclarationFailed err ->
                            TypedDeclarationFailed err
                        Declaration.DriverActionFailed err ->
                            TypedActionFailed err)
                    prefix
        Right (Declaration.DriverSealFailed err prefix) ->
            TypedModuleFailed (TypedSealFailed err) prefix

runTypedModuleFreshIO :: TypedModuleInput -> IO TypedModuleResult
runTypedModuleFreshIO input =
    runEff
        (ValidationCache.runValidationCacheAlwaysMiss
            (runTypedModuleEff input))
