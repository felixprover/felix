{-# LANGUAGE NoImplicitPrelude #-}

-- | The production declaration boundary for structural recursion. Source
-- elaboration supplies checked branch lambdas; this owner constructs and
-- replays all supporting laws before publishing the binding and equations.
module Felix.Checking.Recursion
    ( RecursiveDefinitionInput(..)
    , CheckedRecursionAuthorization
    , lowerRecursiveDefinition
    , authorizeCheckedRecursion
    ) where

import Base
import Felix.Cache.Codec
import Felix.Checking.Core
import Felix.Checking.Authority (KernelConstructionDescriptor(..))
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Planning
import Felix.Checking.Recursion.Interface qualified as Interface
import Felix.Checking.Recursion.Library
import Felix.Checking.Recursion.Named
import Felix.Checking.Recursion.Prepared
import Felix.Checking.Semantic

import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Effectful.Error.Static qualified as Error
import Numeric.Natural (Natural)

data RecursiveDefinitionInput = RecursiveDefinitionInput
    { recursionName :: !Text
    , recursionKey :: !SemanticGlobalKey
    , recursionLabel :: !SemanticBindingLabel
    , recursionDatatype :: !ResolvedGlobalBinding
    , recursionDatatypeArguments :: ![Natural]
    , recursionHeaders :: ![ResidualTemplate]
    , recursionBranches :: !(NonEmpty (ScopedCheckedCore ObjectId, AbbreviationExpansion))
    }

newtype CheckedRecursionAuthorization = CheckedRecursionAuthorization [RecursorEvidence]

lowerRecursiveDefinition
    :: RecursiveDefinitionInput -> Declaration.LoweringDriver
        (Either Text (Declaration.CheckedDeclaration CheckedRecursionAuthorization))
lowerRecursiveDefinition input = Except.runExceptT do
    (arity,resultType) <- maybe (Except.throwE "recursive head has an unsupported type") pure
        (semanticGlobalKeyType (recursionKey input) >>= firstOrderSymbolShape)
    unless (arity > 0 && (resultType == TySet || resultType == TyProp))
        (Except.throwE "recursive head requires a final structural Set argument")
    foundation <- lift Declaration.currentFoundationLowering
    closure <- lift Declaration.checkedObjectClosureLowering
    library <- Except.ExceptT loadRecursionLibrary
    datatype <- Except.ExceptT (loadCheckedDatatype (recursionDatatype input))
    let parameterCount = arity - 1
        types = replicate parameterCount TySet
        headers = recursionHeaders input
    checkedHeaders <- Except.except (traverse
        (first (Text.pack . show) . checkScopedCanonicalCore (globalTypingFromClosure closure) types . residualTemplateFormula) headers)
    named <- Except.except (prepareNamedRecursor foundation closure library datatype resultType parameterCount
        (recursionDatatypeArguments input) checkedHeaders (fst <$> recursionBranches input))
    datatypeDescriptor <- maybe (Except.throwE "recursive datatype descriptor disappeared") pure
        (semanticGlobalBindingDatatype (resolvedBindingDeclaration (recursionDatatype input)))
    positions <- for (namedRecursorEquations named) \(reference,_) -> case reference of
        LocalCandidateReference position -> pure position
        _ -> Except.throwE "a recursive equation is not declaration-local"
    let descriptions = datatypeDescriptorCases datatypeDescriptor
        descriptor = RecursiveDefinitionDescriptor (resolvedBindingRef (recursionDatatype input))
            (recursionDatatypeArguments input) headers (snd <$> recursionBranches input) (NonEmpty.zip (datatypeCaseConstructor <$> descriptions) positions)
        markers = Map.fromList
            [(position, semanticName (recursionName input <> "_" <> datatypeCaseName description))
            | (description,position) <- toList (NonEmpty.zip descriptions positions)]
        facts = namedRecursorFacts named
        assertions = namedRecursorObjects named
    contract <- Except.except (Interface.recursiveFormationContract parameterCount descriptor)
    let binding = semanticGlobalBindingWithContract (recursionKey input) (recursionLabel input)
            (GlobalReference (namedRecursorObject named)) (Just contract)
    environment <- Except.except (first (Text.pack . show) (semanticEnvironmentDelta [binding]))
    let syntax = declarationSyntaxId (encodeCache do
            putCacheText "structural-recursion"
            putCacheText (recursionName input)
            putSemanticEnvironmentDeltaCache environment
            putCacheList putAbbreviationExpansionCache (toList (snd <$> recursionBranches input))
            putCacheList (putCanonicalTermCache putObjectIdCache . frozenCoreTerm . recursorFactTarget) facts)
    candidates <- for (zip [0 ..] facts) \(ordinal,fact) -> do
        let marker = Map.lookup (PlannedCandidatePosition ordinal 0) markers
            planning = case recursorFactEvidence fact of
                RecursorDefinition object -> Declaration.checkedImplementationDefinitionPlanning object
                RecursorDerivation references _ -> Declaration.checkedKernelPlanningReferences CheckedDerivedConstruction references
        spec <- Except.ExceptT (first Declaration.renderDeclarationError <$>
            Declaration.prepareFrozenCandidateSpecLowering assertions (recursorFactTarget fact)
                (maybe SearchIneligible (const SearchEligible) marker) (maybeToList marker))
        pure (Declaration.checkedCandidate spec planning :| [])
    pure (Declaration.withRecursiveDefinitionDescriptor (recursionKey input) descriptor
        (Declaration.checkedCompiledDeclaration syntax assertions [] [binding] Nothing candidates
            (CheckedRecursionAuthorization (recursorFactEvidence <$> facts))))

authorizeCheckedRecursion
    :: CheckedRecursionAuthorization -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedRecursion (CheckedRecursionAuthorization evidence) stages = do
    unless (length evidence == length stages && all ((== 1) . NonEmpty.length) stages)
        (Declaration.failDeclaration (Declaration.CheckedAuthorizationCandidateShapeMismatch (length evidence) (length stages)))
    for_ (zip evidence stages) \(recipe,candidates) -> do
        let candidate = NonEmpty.head candidates
        case recipe of
            RecursorDefinition object -> Declaration.authorizeImplementationDefinitionCandidate object candidate
            RecursorDerivation references derivation ->
                Declaration.authorizeKernelConstructionCandidate CheckedDerivedConstruction candidate do
                    imports <- traverse consume references
                    maybe (Error.throwError_ Declaration.KernelConstructionDescriptorMismatch) pure
                        (Kernel.remapKernelDerivationImports (\index -> nth (Kernel.importIxValue index) imports) derivation)
  where
    consume = \case
        EnvironmentOccurrenceReference fingerprint -> Declaration.useAuthorizedFact fingerprint
        LocalCandidateReference position -> case Declaration.candidateAtPosition position stages of
            Nothing -> Error.throwError_ Declaration.KernelConstructionDescriptorMismatch
            Just candidate -> Declaration.useStagedCandidate candidate
