{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Small proof-producing natural-deduction combinators.  Builders check each
-- step through "Felix.Checking.Kernel.Semantics".  Trees retained for kernel
-- authorization are replayed independently.  Proof-producing composition
-- entry points retain those trees; compatibility validators merely discard
-- their result.
module Felix.Checking.Kernel.Proof
    ( ProofContext
    , rootProofContext
    , scopedProofContext
    , proofContextTypes
    , proofContextGlobalTyping
    , proofContextHypotheses
    , extendProofContextHypothesis
    , extendProofContextBinder
    , scopedTerm
    , admitScopedTerm
    , checkScopedTermUnderBinder
    , BuiltProof
    , builtProofStatement
    , builtProofDerivation
    , weakenProofHypotheses
    , countedWeakenProofHypotheses
    , importedProof
    , foundationProof
    , foundationInstanceProof
    , hypothesisProof
    , indexedHypothesisProof
    , implicationEliminationProof
    , implicationIntroductionProof
    , introduceImplications
    , forallEliminationProof
    , forallIntroductionProof
    , introduceForalls
    , specializeForalls
    , falsumEliminationProof
    , equalityReflexivityProof
    , equalityReverseProof
    , equalityCongruenceApplicationProof
    , equalityCongruenceLambdaProof
    , composeEqualityProof
    , equalityModusPonensProof
    , equalityTransportProof
    , EqualityTransportDirection(..)
    , equalityTransportDerivationProof
    , conversionProof
    , conversionProofWithPool
    , ProofConversionLimitOwner(..)
    , CountedProof
    , runSharedProofWork
    , countedScopedProofContext
    , runCountedProof
    , countedScopedTerm
    , countedAdmitScopedTerm
    , countedImportedProof
    , countedFoundationProof
    , countedIndexedHypothesisProof
    , countedHypothesisProofs
    , countedExtendProofContextHypothesis
    , countedExtendProofContextBinder
    , countedImplicationEliminationProof
    , countedImplicationIntroductionProof
    , countedComposeImplicationProof
    , countedProjectConjunctionProof
    , countedComposeReflexivityProof
    , countedComposeApplicationEqualityProof
    , countedComposeEqualityModusPonensProof
    , countedForallEliminationProof
    , countedForallIntroductionProof
    , countedFalsumEliminationProof
    , countedEqualityReflexivityProof
    , countedEqualityReverseProof
    , countedEqualityCongruenceApplicationProof
    , countedEqualityCongruenceLambdaProof
    , countedComposeEqualityProof
    , countedEqualityModusPonensProof
    , countedEqualityTransportProof
    , transportEqualityWithinWork
    , congruenceEqualityWithinWork
    , countedConversionProof
    , countedTruthIntroductionProof
    , countedNegationIntroductionProof
    , countedNegationEliminationProof
    , countedConjunctionIntroductionProof
    , countedConjunctionLeftProof
    , countedConjunctionRightProof
    , countedDisjunctionLeftProof
    , countedDisjunctionRightProof
    , countedPreparedDisjunctionEliminationProof
    , countedExistentialIntroductionProof
    , countedPreparedExistentialEliminationProof
    , countedDoubleNegationEliminationProof
    , countedExcludedMiddleProof
    , doubleNegationEliminationProof
    , truthIntroductionProof
    , negationIntroductionProof
    , negationEliminationProof
    , conjunctionTerm
    , conjunctionIntroductionProof
    , conjunctionLeftProof
    , conjunctionRightProof
    , buildLeftAssociatedConjunction
    , projectLeftAssociatedConjuncts
    , structuralLogicalProof
    , conjunctionAssumptionProof
    , structuralLogicalCompositionProof
    , validateStructuralLogicalComposition
    , transparentPredicateIntroductionProof
    , validateTransparentPredicateIntroductionComposition
    , disjunctionTerm
    , disjunctionLeftProof
    , disjunctionRightProof
    , disjunctionEliminationProof
    , introduceLeftAssociatedDisjunct
    , eliminateLeftAssociatedDisjunction
    , transportMembershipProof
    , validateExcludedMiddleComposition
    , buildAssumptionOpeningComposition
    , validateAssumptionOpeningComposition
    , validateClassicalDisjunctionAssumptionComposition
    , validateCaseAnalysisComposition
    , validateDoubleNegationComposition
    , validateFalsumEliminationComposition
    , validateSetInductionComposition
    , existentialTerm
    , existentialIntroductionProof
    , existentialEliminationProof
    , setLfpBoundProof
    , setLfpLeastProof
    , setLfpFixedProof
    , setLfpInductProof
    , setLfpRuleSchemaProof
    , KernelProofBuildError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , emptyGlobalTyping
    )
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Conversion.Checked
    ( ConversionWitnessResult(..)
    , witnessConversionChecked
    )
import Felix.Checking.Kernel.Conversion.Policy (productionConversionOperationLimit)
import Felix.Checking.Kernel.Derivation.Conversion
    ( ConversionSealError(..)
    , sealSuccessfulConversion
    )
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Semantics qualified as Semantics
import Felix.Checking.Kernel.SetLfp qualified as SetLfp
import Felix.Checking.LooseDeduction qualified as Loose

import Control.Monad (foldM, unless)
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word)
import Numeric.Natural (Natural)


data ProofContext global = ProofContext
    !CheckedFoundation
    !(GlobalTyping global)
    ![CoreType]
    ![ScopedCheckedCore global]

type role ProofContext nominal

rootProofContext
    :: CheckedFoundation
    -> GlobalTyping global
    -> ProofContext global
rootProofContext foundation globalType =
    ProofContext foundation globalType [] []

scopedProofContext
    :: CheckedFoundation
    -> GlobalTyping global
    -> [CoreType]
    -> [ScopedCheckedCore global]
    -> Either KernelProofBuildError (ProofContext global)
scopedProofContext foundation globalType context hypotheses = do
    traverse_
        (validatePropositionContext
            "proof-context hypothesis" context)
        hypotheses
    pure (ProofContext foundation globalType context hypotheses)

proofContextTypes
    :: ProofContext global
    -> [CoreType]
proofContextTypes
        (ProofContext
            _foundation
            _globalType
            context
            _hypotheses) =
    context

proofContextHypotheses
    :: ProofContext global
    -> [ScopedCheckedCore global]
proofContextHypotheses
        (ProofContext
            _foundation
            _globalType
            _context
            hypotheses) =
    hypotheses

data BuiltProof global = BuiltProof
    !(ScopedCheckedCore global)
    !(KernelDerivation global)

type role BuiltProof nominal

builtProofStatement
    :: BuiltProof global
    -> ScopedCheckedCore global
builtProofStatement
        (BuiltProof statement _derivation) =
    statement

builtProofDerivation
    :: BuiltProof global
    -> KernelDerivation global
builtProofDerivation
        (BuiltProof _statement derivation) =
    derivation

-- | The direction in which a checked equality is used by the bounded
-- derivation-level transport helper.
data EqualityTransportDirection
    = EqualityLeftToRight
    | EqualityRightToLeft
    deriving stock (Show, Eq, Ord)

data ProofConversionLimitOwner
    = ProofConversionOperationLimit
    | ProofConversionAggregatePool
    deriving stock (Show, Eq)

data KernelProofBuildError
    = ProofTermIllTyped !CoreCheckError
    | ProofSemanticsFailed
        !Semantics.KernelSemanticsError
    | ProofFoundationArgumentMismatch
        !FoundationAxiomTag
    | ProofHypothesisNotFound
    | ProofExpectedEquality
    | ProofExpectedUnaryBinder
    | ProofSetLfpRuleFailed !Text
    | ProofConversionNotConvertible
    | ProofConversionLimitExhausted
        !ProofConversionLimitOwner
        !Conversion.ConversionLimit
    | ProofConversionFailed !Conversion.ConversionFailure
    | ProofConversionWitnessSourceMismatch
    | ProofConversionPoolAccountingInvariant
    | ProofStructuralCompositionMismatch !Text
    deriving stock (Show, Eq)

scopedTerm
    :: ProofContext global
    -> CanonicalTerm global
    -> Either
        KernelProofBuildError
        (ScopedCheckedCore global)
scopedTerm
        (ProofContext
            _foundation
            globalType
            context
            _hypotheses) =
    first ProofTermIllTyped
        . checkScopedCanonicalCore
            globalType
            context

-- | Enter an already checked input under this owner's lexical context and
-- immutable snapshot. The returned term carries no transferable admission token.
admitScopedTerm
    :: Ord global
    => ProofContext global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError (ScopedCheckedCore global)
admitScopedTerm
        (ProofContext _foundation globalType context _hypotheses) term
    | context /= scopedCoreContext term =
        Left (ProofStructuralCompositionMismatch
            "checked input has a different lexical context")
    | otherwise =
        first ProofTermIllTyped (admitScopedCheckedCore globalType term)

-- | Check a term beneath one prospective lexical binder while keeping the
-- global snapshot confined to its proof context.
checkScopedTermUnderBinder
    :: ProofContext global
    -> CoreType
    -> CanonicalTerm global
    -> Either CoreCheckError (ScopedCheckedCore global)
checkScopedTermUnderBinder
        (ProofContext
            _foundation
            globalType
            context
            _hypotheses)
        binderType =
    checkScopedCanonicalCore globalType (binderType : context)

importedProof
    :: ProofContext global
    -> ImportIx
    -> FrozenCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
importedProof context index statement =
    pure
        (BuiltProof
            (embedClosedCore
                (proofContextTypes context)
                statement)
            (importedFactDerivation index))

foundationProof
    :: ProofContext global
    -> FoundationAxiomTag
    -> Either
        KernelProofBuildError
        (BuiltProof global)
foundationProof
        context@(ProofContext
            foundation
            _globalType
            _types
            _hypotheses)
        tag =
    pure
        (BuiltProof
            (embedClosedCore
                (proofContextTypes context)
                (eliminateFrozenVoid
                    (foundationAxiomFrozen
                        foundation
                        tag)))
            (foundationFactDerivation tag))

-- | Specialize one foundation schema in the supplied argument order.
foundationInstanceProof
    :: ProofContext global
    -> FoundationAxiomTag
    -> [ScopedCheckedCore global]
    -> Either KernelProofBuildError (BuiltProof global)
foundationInstanceProof context tag arguments = do
    initial <- foundationProof context tag
    foldM
        (forallEliminationProof context)
        initial
        arguments

hypothesisProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
hypothesisProof
        (ProofContext
            _foundation
            _globalType
            _context
            hypotheses)
        statement =
    case List.findIndex (== statement) hypotheses of
        Nothing ->
            Left ProofHypothesisNotFound
        Just index ->
            pure
                (BuiltProof
                    statement
                    (localHypothesisDerivation
                        (hypothesisIx
                            (fromIntegral index))))

-- | Select one hypothesis by its exact external position.  This differs from
-- 'hypothesisProof' when equal propositions occur more than once: provenance
-- remains attached to the requested source hypothesis.
indexedHypothesisProof
    :: ProofContext global
    -> HypothesisIx
    -> Either
        KernelProofBuildError
        (BuiltProof global)
indexedHypothesisProof
        (ProofContext
            _foundation
            _globalType
            _context
            hypotheses)
        index =
    maybe
        (Left ProofHypothesisNotFound)
        (\statement ->
            pure
                (BuiltProof
                    statement
                    (localHypothesisDerivation index)))
        (nth (hypothesisIxValue index) hypotheses)

implicationEliminationProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
implicationEliminationProof
        (ProofContext
            _foundation
            _globalType
            _context
            _hypotheses)
        implication
        premise = do
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.implicationElimination
                (builtProofStatement implication)
                (builtProofStatement premise))
    pure
        (BuiltProof
            conclusion
            (implicationEliminationDerivation
                (builtProofDerivation implication)
                (builtProofDerivation premise)))

implicationIntroductionProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> BuiltProof global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> Either
        KernelProofBuildError
        (BuiltProof global)
implicationIntroductionProof
        context
        premise
        buildBody = do
    body <- buildHypothesisBranch context premise buildBody
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.implicationIntroduction
                premise
                (builtProofStatement body))
    pure
        (BuiltProof
            conclusion
            (implicationIntroductionDerivation
                premise
                (builtProofDerivation body)))

introduceImplications
    :: Eq global
    => ProofContext global
    -> [CanonicalTerm global]
    -> ( ProofContext global
         -> Either KernelProofBuildError (BuiltProof global)
       )
    -> Either KernelProofBuildError (BuiltProof global)
introduceImplications context premises build =
    case premises of
        [] -> build context
        premise : remaining -> do
            checkedPremise <- scopedTerm context premise
            implicationIntroductionProof context checkedPremise
                (\extended _proof ->
                    introduceImplications extended remaining build)

buildHypothesisBranch
    :: ProofContext global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> BuiltProof global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> Either
        KernelProofBuildError
        (BuiltProof global)
buildHypothesisBranch
        (ProofContext foundation globalType types hypotheses)
        premise
        buildBody =
    buildBody extended premiseProof
  where
    extended =
        ProofContext
            foundation
            globalType
            types
            (premise : hypotheses)
    premiseProof =
        BuiltProof
            premise
            (localHypothesisDerivation (hypothesisIx 0))

extendProofContextHypothesis
    :: ProofContext global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError (ProofContext global)
extendProofContextHypothesis
        (ProofContext foundation globalType types hypotheses)
        premise = do
    validatePropositionContext
        "introduced proof hypothesis" types premise
    pure
        (ProofContext
            foundation
            globalType
            types
            (premise : hypotheses))

forallEliminationProof
    :: ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
forallEliminationProof
        (ProofContext
            _foundation
            _globalType
            _types
            _hypotheses)
        quantified
        argument = do
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.forallElimination
                (builtProofStatement quantified)
                argument)
    pure
        (BuiltProof
            conclusion
            (forallEliminationDerivation
                (builtProofDerivation quantified)
                argument))

forallIntroductionProof
    :: ProofContext global
    -> CoreType
    -> ( ProofContext global
         -> ScopedCheckedCore global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> Either
        KernelProofBuildError
        (BuiltProof global)
forallIntroductionProof
        context@(ProofContext
            _foundation
            globalType
            _types
            _hypotheses)
        binderType
        buildBody = do
    (extended, variable) <-
        extendProofContextBinder context binderType
    body <-
        buildBody extended variable
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.forallIntroduction
                globalType
                binderType
                (builtProofStatement body))
    pure
        (BuiltProof
            conclusion
            (forallIntroductionDerivation
                binderType
                (builtProofDerivation body)))

introduceForalls
    :: Eq global
    => ProofContext global
    -> [CoreType]
    -> ( ProofContext global
         -> Either KernelProofBuildError (BuiltProof global)
       )
    -> Either KernelProofBuildError (BuiltProof global)
introduceForalls context binderTypes build =
    case binderTypes of
        [] -> build context
        binderType : remaining ->
            forallIntroductionProof context binderType
                (\extended _variable ->
                    introduceForalls extended remaining build)

specializeForalls
    :: ProofContext global
    -> BuiltProof global
    -> [CanonicalTerm global]
    -> Either KernelProofBuildError (BuiltProof global)
specializeForalls context =
    foldM
        (\proof argument -> do
            checkedArgument <- scopedTerm context argument
            forallEliminationProof context proof checkedArgument)

extendProofContextBinder
    :: ProofContext global
    -> CoreType
    -> Either
        KernelProofBuildError
        (ProofContext global, ScopedCheckedCore global)
extendProofContextBinder
        (ProofContext foundation globalType types hypotheses)
        binderType = do
    weakenedHypotheses <-
        traverse
            (first ProofTermIllTyped
                . weakenScopedCore globalType binderType)
            hypotheses
    let extended =
            ProofContext
                foundation
                globalType
                (binderType : types)
                weakenedHypotheses
    variable <- scopedTerm extended (CBound 0)
    pure (extended, variable)

falsumEliminationProof
    :: ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
falsumEliminationProof
        (ProofContext
            _foundation
            globalType
            _types
            _hypotheses)
        falsum
        target = do
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.falsumElimination
                globalType
                (builtProofStatement falsum)
                target)
    pure
        (BuiltProof
            conclusion
            (falsumEliminationDerivation
                (builtProofDerivation falsum)
                target))

equalityReflexivityProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
equalityReflexivityProof
        (ProofContext
            _foundation
            _globalType
            _types
            _hypotheses)
        operand = do
    equality <-
        first ProofSemanticsFailed
            (Semantics.equalityReflexivity
                operand)
    pure
        (BuiltProof
            equality
            (scopedEqualityReflexivityDerivation
                operand))

equalityCongruenceApplicationProof
    :: ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
equalityCongruenceApplicationProof
        (ProofContext
            _foundation
            _globalType
            _types
            _hypotheses)
        functionEquality
        argumentEquality = do
    equality <-
        first ProofSemanticsFailed
            (Semantics.equalityCongruenceApplication
                (builtProofStatement functionEquality)
                (builtProofStatement argumentEquality))
    pure
        (BuiltProof
            equality
            (equalityCongruenceApplicationDerivation
                (builtProofDerivation
                    functionEquality)
                (builtProofDerivation
                    argumentEquality)))

-- | Abstract a checked equality. Replay still checks the child under weakened
-- outer hypotheses: constructing this node does not authorize new assumptions.
equalityCongruenceLambdaProof
    :: CoreType -> BuiltProof global -> Either KernelProofBuildError (BuiltProof global)
equalityCongruenceLambdaProof binderType body = do
    conclusion <- first ProofSemanticsFailed
        (Semantics.equalityCongruenceLambda binderType (builtProofStatement body))
    pure (BuiltProof conclusion
        (equalityCongruenceLambdaDerivation binderType (builtProofDerivation body)))

countedEqualityCongruenceLambdaProof
    :: CoreType -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedEqualityCongruenceLambdaProof binderType body = do
    consumeProofEntry
    conclusion <- liftProofSemantics (\work ->
        Semantics.countedEqualityCongruenceLambda work binderType (builtProofStatement body))
    pure (BuiltProof conclusion
        (equalityCongruenceLambdaDerivation binderType (builtProofDerivation body)))

-- | Compose two equalities through ordinary equality transport.  Replay sees
-- only the existing primitive equality rules.
composeEqualityProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> Either KernelProofBuildError (BuiltProof global)
composeEqualityProof context firstEquality secondEquality = do
    (firstType, source, middle) <-
        equalityParts (builtProofStatement firstEquality)
    (secondType, middle', target) <-
        equalityParts (builtProofStatement secondEquality)
    unless (firstType == secondType && middle == middle')
        (Left
            (ProofStructuralCompositionMismatch
                "equality composition has mismatched middle operands"))
    predicate <-
        scopedTerm context
            (CLam firstType
                (CEq firstType
                    (shiftCanonical 1 0 source)
                    (CBound 0)))
    composed <- equalityTransportProof
        context
        secondEquality
        predicate
        firstEquality
    expected <- scopedTerm context (CEq firstType source target)
    conversionProof context composed expected

equalityModusPonensProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
equalityModusPonensProof
        (ProofContext
            _foundation
            _globalType
            _types
            _hypotheses)
        equality
        premise = do
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.equalityModusPonens
                (builtProofStatement equality)
                (builtProofStatement premise))
    pure
        (BuiltProof
            conclusion
            (equalityModusPonensDerivation
                (builtProofDerivation equality)
                (builtProofDerivation premise)))

-- | Transport a proved proposition through an equality using the supplied
-- predicate.  This is a derived proof operation: replay sees only equality
-- reflexivity, application congruence, conversion, and equality elimination.
equalityTransportProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
equalityTransportProof context equality predicate premise = do
    (propositionEquality, leftApplication, rightApplication) <- prepare
    premise' <- conversionProof context premise leftApplication
    transported <- equalityModusPonensProof context propositionEquality premise'
    conversionProof context transported rightApplication
  where
    prepare = do
        (operandType, left, right) <-
            equalityParts (builtProofStatement equality)
        unless
            (scopedCoreType predicate == TyArrow operandType TyProp)
            (Left
                (ProofStructuralCompositionMismatch
                    "equality transport predicate has the wrong type"))
        predicateReflexivity <-
            equalityReflexivityProof context predicate
        propositionEquality <-
            equalityCongruenceApplicationProof
                context predicateReflexivity equality
        leftApplication <-
            scopedTerm context
                (CApp (scopedCoreTerm predicate) left)
        rightApplication <-
            scopedTerm context
                (CApp (scopedCoreTerm predicate) right)
        pure
            (propositionEquality, leftApplication, rightApplication)

-- | Compose an already selected equality derivation and premise derivation
-- through the ordinary checked equality builders. This is the narrow bridge
-- used by staged compiler proofs: callers supply the exact checked judgements,
-- while final candidate authorization independently replays the returned
-- derivation and therefore validates that its leaves establish those
-- judgements.
equalityTransportDerivationProof
    :: Eq global
    => ProofContext global
    -> EqualityTransportDirection
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError (BuiltProof global)
equalityTransportDerivationProof context direction equality equalityDerivation
        predicate premise premiseDerivation target = do
    let suppliedEquality = BuiltProof equality equalityDerivation
    directed <- case direction of
        EqualityLeftToRight -> pure suppliedEquality
        EqualityRightToLeft -> equalityReverseProof context suppliedEquality
    transported <-
        equalityTransportProof context directed predicate
            (BuiltProof premise premiseDerivation)
    conversionProof context transported target

conversionProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
conversionProof context source target =
    let pool = Conversion.conversionPool
            (Conversion.conversionLimitAmount productionConversionOperationLimit)
    in fst
        (runProofConversion
            ProofConversionOperationLimit pool context source target)

-- | Convert within the caller's aggregate allowance. Every attempted operation
-- returns its post-debit pool, including mismatch and failure.
conversionProofWithPool
    :: Eq global
    => Conversion.ConversionPool
    -> ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> (Either KernelProofBuildError (BuiltProof global), Conversion.ConversionPool)
conversionProofWithPool pool =
    runProofConversion (aggregateConversionLimitOwner pool) pool

aggregateConversionLimitOwner
    :: Conversion.ConversionPool
    -> ProofConversionLimitOwner
aggregateConversionLimitOwner pool
    | Conversion.conversionPoolAmount pool
        <= Conversion.conversionLimitAmount productionConversionOperationLimit =
            ProofConversionAggregatePool
    | otherwise = ProofConversionOperationLimit

runProofConversion
    :: Eq global
    => ProofConversionLimitOwner
    -> Conversion.ConversionPool
    -> ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> (Either KernelProofBuildError (BuiltProof global), Conversion.ConversionPool)
runProofConversion owner pool context source target
    | scopedCoreType (builtProofStatement source) /= TyProp =
        ( Left
            (ProofSemanticsFailed
                (Semantics.KernelExpectedProposition
                    (scopedCoreType (builtProofStatement source))))
        , pool
        )
    | otherwise =
        let limit = Conversion.capConversionLimit
                pool productionConversionOperationLimit
            report = witnessConversionChecked
                (proofContextGlobalTyping context) limit (builtProofStatement source) target
        in case Conversion.debitConversionCost (Conversion.conversionCost report) pool of
            Nothing -> (Left ProofConversionPoolAccountingInvariant, pool)
            Just remaining ->
                ( classifyProofConversion owner limit source
                    (Conversion.conversionResult report)
                , remaining
                )

classifyProofConversion
    :: Eq global
    => ProofConversionLimitOwner
    -> Conversion.ConversionLimit
    -> BuiltProof global
    -> Either Conversion.ConversionFailure (ConversionWitnessResult global)
    -> Either KernelProofBuildError (BuiltProof global)
classifyProofConversion owner limit (BuiltProof source derivation) = \case
    Left Conversion.ConversionLimitExhausted{} ->
        Left (ProofConversionLimitExhausted owner limit)
    Left failure -> Left (ProofConversionFailed failure)
    Right WitnessNotConvertible -> Left ProofConversionNotConvertible
    Right (WitnessConvertible witness) ->
        case sealSuccessfulConversion witness source derivation of
            Left ConversionSealSourceMismatch ->
                Left ProofConversionWitnessSourceMismatch
            Right (target, sealed) -> Right (BuiltProof target sealed)

equalityReverseProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
equalityReverseProof context equality = do
    (appliedEquality, leftReflexivity, appliedLeft, expected) <- prepare
    appliedLeftReflexivity <- conversionProof context leftReflexivity appliedLeft
    reversedApplication <-
        equalityModusPonensProof context appliedEquality appliedLeftReflexivity
    conversionProof context reversedApplication expected
  where
    prepare = do
        (operandType, left, right) <-
            equalityParts
                (builtProofStatement equality)
        leftOperand <-
            scopedTerm context left
        weakenedLeft <-
            first ProofTermIllTyped
                (weakenScopedCore
                    (proofContextGlobalTyping context)
                    operandType
                    leftOperand)
        function <-
            scopedTerm context
                (CLam operandType
                    (CEq
                        operandType
                        (CBound 0)
                        (scopedCoreTerm weakenedLeft)))
        functionReflexivity <-
            equalityReflexivityProof context function
        appliedEquality <-
            equalityCongruenceApplicationProof
                context functionReflexivity equality
        leftReflexivity <-
            equalityReflexivityProof context leftOperand
        appliedLeft <-
            scopedTerm context
                (CApp (scopedCoreTerm function) left)
        expected <-
            scopedTerm context
                (CEq operandType right left)
        pure
            (appliedEquality, leftReflexivity, appliedLeft, expected)

doubleNegationEliminationProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
doubleNegationEliminationProof
        context
        target
        doubleNegation = do
    axiom <-
        foundationProof
            context
            DoubleNegationElim
    instanceProof <-
        forallEliminationProof
            context
            axiom
            target
    implicationEliminationProof
        context
        instanceProof
        doubleNegation

truthIntroductionProof
    :: ProofContext global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
truthIntroductionProof context = do
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.truthIntroduction
                (proofContextGlobalTyping context)
                (proofContextTypes context))
    pure (BuiltProof conclusion truthIntroductionDerivation)

negationIntroductionProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> BuiltProof global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> Either
        KernelProofBuildError
        (BuiltProof global)
negationIntroductionProof context premise buildFalsum = do
    falsum <- buildHypothesisBranch context premise buildFalsum
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.negationIntroduction
                (proofContextGlobalTyping context)
                premise
                (builtProofStatement falsum))
    pure
        (BuiltProof
            conclusion
            (negationIntroductionDerivation
                premise
                (builtProofDerivation falsum)))

negationEliminationProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
negationEliminationProof context premise negation = do
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.negationElimination
                (proofContextGlobalTyping context)
                (builtProofStatement premise)
                (builtProofStatement negation))
    pure
        (BuiltProof
            conclusion
            (negationEliminationDerivation
                (builtProofDerivation premise)
                (builtProofDerivation negation)))

conjunctionTerm
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
conjunctionTerm = CAnd

conjunctionIntroductionProof
    :: ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
conjunctionIntroductionProof
        _context
        left
        right = do
    result <-
        first ProofSemanticsFailed
            (Semantics.conjunctionIntroduction
                (builtProofStatement left)
                (builtProofStatement right))
    pure
        (BuiltProof
            result
            (conjunctionIntroductionDerivation
                (builtProofDerivation left)
                (builtProofDerivation right)))

conjunctionLeftProof
    :: ProofContext global
    -> BuiltProof global
    -> Either KernelProofBuildError (BuiltProof global)
conjunctionLeftProof _context conjunction = do
    result <- first ProofSemanticsFailed
        (Semantics.conjunctionLeftElimination (builtProofStatement conjunction))
    pure (BuiltProof result
        (conjunctionLeftEliminationDerivation (builtProofDerivation conjunction)))

conjunctionRightProof
    :: ProofContext global
    -> BuiltProof global
    -> Either KernelProofBuildError (BuiltProof global)
conjunctionRightProof _context conjunction = do
    result <- first ProofSemanticsFailed
        (Semantics.conjunctionRightElimination (builtProofStatement conjunction))
    pure (BuiltProof result
        (conjunctionRightEliminationDerivation (builtProofDerivation conjunction)))

-- | Introduce the left-associated finite conjunction used by canonical record
-- targets.  The empty conjunction is truth.
buildLeftAssociatedConjunction
    :: ProofContext global
    -> [BuiltProof global]
    -> Either KernelProofBuildError (BuiltProof global)
buildLeftAssociatedConjunction context = \case
    [] -> truthIntroductionProof context
    initial : remaining ->
        foldM
            (conjunctionIntroductionProof context)
            initial
            remaining

-- | Project all source-ordered leaves from a left-associated conjunction.
-- The supplied term list fixes the expected association at every elimination
-- step rather than inferring it from an arbitrary proof statement.
projectLeftAssociatedConjuncts
    :: Eq global
    => ProofContext global
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> Either KernelProofBuildError [BuiltProof global]
projectLeftAssociatedConjuncts _context [] _proof =
    pure []
projectLeftAssociatedConjuncts _context [_only] proof =
    pure [proof]
projectLeftAssociatedConjuncts context terms proof = do
    (preceding, final) <-
        maybe
            (Left
                (ProofStructuralCompositionMismatch
                    "left-associated conjunction has no final conjunct"))
            Right
            (splitLast terms)
    let precedingTerm = leftAssociatedConjunction preceding
    unless
        (scopedCoreContext (builtProofStatement proof) == proofContextTypes context
            && scopedCoreTerm (builtProofStatement proof) == CAnd precedingTerm final)
        (Left (ProofStructuralCompositionMismatch
            "conjunction elimination received different conjuncts"))
    precedingProof <-
        conjunctionLeftProof context proof
    finalProof <-
        conjunctionRightProof context proof
    (<> [finalProof])
        <$> projectLeftAssociatedConjuncts
            context
            preceding
            precedingProof

-- Keep the original premises and build both immediate projections before
-- descending, preserving projection failure order as well as premise order.
expandConjunctionPremises
    :: ProofContext global
    -> [BuiltProof global]
    -> Either KernelProofBuildError [BuiltProof global]
expandConjunctionPremises context premises = concat <$> traverse expand premises
  where
    expand proof = case scopedCoreTerm (builtProofStatement proof) of
        CAnd _left _right -> do
            leftProof <- conjunctionLeftProof context proof
            rightProof <- conjunctionRightProof context proof
            leftClosure <- expand leftProof
            rightClosure <- expand rightProof
            pure (proof : leftClosure <> rightClosure)
        _ -> pure [proof]

-- | Deterministically derive a proposition from already checked proofs using
-- direct hypothesis reuse and the immediate introduction or elimination rules
-- for truth, conjunction, disjunction, and identity implication. This is not a
-- theorem prover: failure in this finite structural closure returns 'Nothing'
-- so the caller can retain its ordinary proof-search path.
--
-- Every successful result is an ordinary 'KernelDerivation' assembled by the
-- small proof combinators above and is therefore independently replayable.
structuralLogicalProof
    :: Eq global
    => ProofContext global
    -> [BuiltProof global]
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (Maybe (BuiltProof global))
structuralLogicalProof context premises target = do
    available <- expandConjunctionPremises context premises
    build available target
  where
    build available goal =
        case find
                ((== goal) . builtProofStatement)
                available of
            Just proof -> pure (Just proof)
            Nothing ->
                case splitConjunction (scopedCoreTerm goal) of
                    Just (left, right) -> do
                        leftGoal <- scopedTerm context left
                        rightGoal <- scopedTerm context right
                        leftProof <- build available leftGoal
                        rightProof <- build available rightGoal
                        case (leftProof, rightProof) of
                            (Just provedLeft, Just provedRight) ->
                                Just
                                    <$> conjunctionIntroductionProof
                                        context provedLeft provedRight
                            _ -> pure Nothing
                    Nothing -> buildNonConjunction available goal

    buildNonConjunction available goal =
        case scopedCoreTerm goal of
            CTruth ->
                Just <$> truthIntroductionProof context
            COr left right -> do
                leftGoal <- scopedTerm context left
                leftProof <- build available leftGoal
                case leftProof of
                    Just provedLeft ->
                        Just
                            <$> disjunctionLeftProof
                                context right provedLeft
                    Nothing -> do
                        rightGoal <- scopedTerm context right
                        rightProof <- build available rightGoal
                        traverse
                            (disjunctionRightProof context left)
                            rightProof
            _ ->
                case scopedCoreTerm goal of
                    CImp premise conclusion
                        | premise == conclusion -> do
                            premiseGoal <- scopedTerm context premise
                            Just
                                <$> implicationIntroductionProof
                                    context premiseGoal
                                    (\_extended premiseProof ->
                                        pure premiseProof)
                    _ -> pure Nothing

    splitConjunction = \case
        CAnd left right -> Just (left, right)
        _ -> Nothing

-- | Derive a target using only reusable local hypotheses and conjunction
-- projection/construction.  Unlike assumption-frontier matching, this is not
-- resource-sensitive: a projected local fact may be reused for every target
-- conjunct.  Exact matches are preferred, followed by the same bounded
-- conversion used by direct @by assumption@.
conjunctionAssumptionProof
    :: Eq global
    => ProofContext global
    -> [BuiltProof global]
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (Maybe (BuiltProof global))
conjunctionAssumptionProof context premises target = do
    available <- expandConjunctionPremises context premises
    build available target
  where
    build available goal =
        case find
                ((== goal) . builtProofStatement)
                available of
            Just proof -> pure (Just proof)
            Nothing ->
                case splitConjunction (scopedCoreTerm goal) of
                    Just (left, right) -> do
                        leftGoal <- scopedTerm context left
                        rightGoal <- scopedTerm context right
                        leftProof <- build available leftGoal
                        rightProof <- build available rightGoal
                        case (leftProof, rightProof) of
                            (Just provedLeft, Just provedRight) ->
                                Just
                                    <$> conjunctionIntroductionProof
                                        context provedLeft provedRight
                            _ -> pure Nothing
                    Nothing -> firstConvertible Nothing available goal

    firstConvertible remembered [] _goal =
        case remembered of
            Nothing -> pure Nothing
            Just limit ->
                Left (ProofConversionLimitExhausted ProofConversionOperationLimit limit)
    firstConvertible remembered (candidate : rest) goal =
        case conversionProof context candidate goal of
            Right converted -> pure (Just converted)
            Left ProofConversionNotConvertible -> firstConvertible remembered rest goal
            Left (ProofConversionLimitExhausted ProofConversionOperationLimit limit) ->
                firstConvertible (remembered <|> Just limit) rest goal
            Left failure -> Left failure

    splitConjunction = \case
        CAnd left right -> Just (left, right)
        _ -> Nothing

-- | Build the source-proof composition corresponding to
-- 'structuralLogicalProof'. The hypotheses and target must inhabit one
-- lexical context, and success is accepted only when the constructed proof
-- has exactly the caller-owned target.
structuralLogicalCompositionProof
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> [ScopedCheckedCore global]
    -> Either KernelProofBuildError (BuiltProof global)
structuralLogicalCompositionProof
        foundation globalType target hypotheses = do
    validatePropositionContext
        "structural logic target" lexicalContext target
    traverse_
        (validatePropositionContext
            "structural logic hypothesis" lexicalContext)
        hypotheses
    let context =
            ProofContext foundation globalType lexicalContext hypotheses
    premiseProofs <- traverse (hypothesisProof context) hypotheses
    result <- structuralLogicalProof context premiseProofs target
    case result of
        Just proof
            | builtProofStatement proof == target -> pure proof
        _ ->
            Left
                (ProofStructuralCompositionMismatch
                    "target is not in the finite conjunction closure of the local hypotheses")
  where
    lexicalContext = scopedCoreContext target

validateStructuralLogicalComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> [ScopedCheckedCore global]
    -> Either KernelProofBuildError ()
validateStructuralLogicalComposition
        foundation globalType target hypotheses =
    () <$ structuralLogicalCompositionProof
        foundation globalType target hypotheses

-- | Build a proposition from hypotheses and transparent predicate equations.
-- The search is deliberately finite: conjunction structure is traversed and
-- each predicate identity is unfolded at most once on a branch.
transparentPredicateIntroductionProof
    :: Ord global
    => ProofContext global
    -> Map.Map global (BuiltProof global)
    -> [BuiltProof global]
    -> Set.Set global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError (BuiltProof global)
transparentPredicateIntroductionProof
        context definitions premises active target = do
    direct <- structuralLogicalProof context premises target
    case direct of
        Just proof -> pure proof
        Nothing -> proveExpanded
  where
    proveExpanded =
        case scopedCoreTerm target of
            CAnd left right -> do
                leftTarget <- scopedTerm context left
                rightTarget <- scopedTerm context right
                leftProof <-
                    transparentPredicateIntroductionProof
                        context definitions premises active leftTarget
                rightProof <-
                    transparentPredicateIntroductionProof
                        context definitions premises active rightTarget
                conjunctionIntroductionProof context leftProof rightProof
            term ->
                case canonicalApplicationSpine term of
                    (CGlobal predicate, arguments)
                        | predicate `Set.notMember` active
                        , Just definition <- Map.lookup predicate definitions ->
                            unfoldPredicate predicate arguments definition
                    _ -> unavailable

    unfoldPredicate predicate arguments definition = do
        specialized <- foldM specialize definition arguments
        bodyTerm <-
            case scopedCoreTerm (builtProofStatement specialized) of
                CEq TyProp left right
                    | left == scopedCoreTerm target -> pure right
                _ ->
                    Left
                        (ProofStructuralCompositionMismatch
                            "transparent predicate definition did not specialize to its target application")
        bodyTarget <- scopedTerm context bodyTerm
        bodyProof <-
            transparentPredicateIntroductionProof
                context definitions premises
                (Set.insert predicate active)
                bodyTarget
        reversed <- equalityReverseProof context specialized
        result <- equalityModusPonensProof context reversed bodyProof
        conversionProof context result target

    specialize proof argument = do
        checkedArgument <- scopedTerm context argument
        forallEliminationProof context proof checkedArgument

    unavailable =
        Left
            (ProofStructuralCompositionMismatch
                "target is not derivable from the checked transparent predicate obligations")

-- | Validate and discard a checked transparent-predicate introduction proof.
-- Closed definition equations are embedded into the caller's lexical
-- context; all ordinary obligations must already inhabit that exact context.
validateTransparentPredicateIntroductionComposition
    :: Ord global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> [(global, FrozenCheckedCore global)]
    -> [ScopedCheckedCore global]
    -> Either KernelProofBuildError ()
validateTransparentPredicateIntroductionComposition
        foundation globalType target definitions hypotheses = do
    validatePropositionContext
        "transparent predicate target" lexicalContext target
    traverse_
        (validatePropositionContext
            "transparent predicate hypothesis" lexicalContext)
        hypotheses
    let definitionHypotheses =
            embedClosedCore lexicalContext . snd <$> definitions
        context =
            ProofContext foundation globalType lexicalContext
                (definitionHypotheses <> hypotheses)
    definitionProofs <-
        for definitions \(predicate, definition) -> do
            proof <- hypothesisProof context (embedClosedCore lexicalContext definition)
            pure (predicate, proof)
    premiseProofs <- traverse (hypothesisProof context) hypotheses
    result <-
        transparentPredicateIntroductionProof
            context (Map.fromList definitionProofs) premiseProofs Set.empty target
    unless (builtProofStatement result == target)
        (Left
            (ProofStructuralCompositionMismatch
                "transparent predicate introduction produced a different target"))
  where
    lexicalContext = scopedCoreContext target

disjunctionTerm
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
disjunctionTerm = COr

disjunctionLeftProof
    :: ProofContext global
    -> CanonicalTerm global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
disjunctionLeftProof context right leftProof = do
    rightTarget <- scopedTerm context right
    result <-
        first ProofSemanticsFailed
            (Semantics.disjunctionLeftIntroduction
                (proofContextGlobalTyping context)
                (builtProofStatement leftProof)
                rightTarget)
    pure
        (BuiltProof
            result
            (disjunctionLeftIntroductionDerivation
                (builtProofDerivation leftProof)
                rightTarget))

disjunctionRightProof
    :: ProofContext global
    -> CanonicalTerm global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
disjunctionRightProof context left rightProof = do
    leftTarget <- scopedTerm context left
    result <-
        first ProofSemanticsFailed
            (Semantics.disjunctionRightIntroduction
                (proofContextGlobalTyping context)
                leftTarget
                (builtProofStatement rightProof))
    pure
        (BuiltProof
            result
            (disjunctionRightIntroductionDerivation
                leftTarget
                (builtProofDerivation rightProof)))

disjunctionEliminationProof
    :: Eq global
    => ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> BuiltProof global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> ( ProofContext global
         -> BuiltProof global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> Either
        KernelProofBuildError
        (BuiltProof global)
disjunctionEliminationProof
        context
        left
        right
        disjunction
        result
        leftCase
        rightCase = do
    leftProposition <- scopedTerm context left
    rightProposition <- scopedTerm context right
    expectedDisjunction <- scopedTerm context (COr left right)
    unless (builtProofStatement disjunction == expectedDisjunction)
        (Left
            (ProofStructuralCompositionMismatch
                "disjunction elimination received different disjuncts"))
    leftBranch <-
        buildHypothesisBranch context leftProposition leftCase
    rightBranch <-
        buildHypothesisBranch context rightProposition rightCase
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.disjunctionElimination
                (proofContextGlobalTyping context)
                (builtProofStatement disjunction)
                (builtProofStatement leftBranch)
                (builtProofStatement rightBranch))
    unless (conclusion == result)
        (Left
            (ProofStructuralCompositionMismatch
                "disjunction branches did not derive the requested result"))
    pure
        (BuiltProof
            conclusion
            (disjunctionEliminationDerivation
                (builtProofDerivation disjunction)
                (builtProofDerivation leftBranch)
                (builtProofDerivation rightBranch)))

-- | Inject a proof into one source-ordered leaf of a left-associated finite
-- disjunction.
introduceLeftAssociatedDisjunct
    :: ProofContext global
    -> Natural
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> Either KernelProofBuildError (BuiltProof global)
introduceLeftAssociatedDisjunct context index alternatives proof =
    case splitAtNatural index alternatives of
        Nothing ->
            Left
                (ProofStructuralCompositionMismatch
                    "finite-disjunction index is outside the alternatives")
        Just (preceding, _selected, following) -> do
            selectedProof <-
                case preceding of
                    [] -> pure proof
                    _ ->
                        disjunctionRightProof
                            context
                            (leftAssociatedDisjunction preceding)
                            proof
            foldM
                (\current followingTerm ->
                    disjunctionLeftProof context followingTerm current)
                selectedProof
                following

-- | Eliminate a left-associated finite disjunction in source order.  The
-- callback receives the zero-based leaf index and its branch hypothesis.
eliminateLeftAssociatedDisjunction
    :: Eq global
    => ProofContext global
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> Natural
         -> BuiltProof global
         -> Either KernelProofBuildError (BuiltProof global)
       )
    -> Either KernelProofBuildError (BuiltProof global)
eliminateLeftAssociatedDisjunction
        initialContext
        alternatives
        proof
        target
        handle =
    go initialContext 0 alternatives proof
  where
    go context _offset [] falsum =
        falsumEliminationProof context falsum target
    go context offset [_only] onlyProof =
        handle context offset onlyProof
    go context offset current currentProof = do
        (preceding, final) <-
            maybe
                (Left
                    (ProofStructuralCompositionMismatch
                        "left-associated disjunction has no final disjunct"))
                Right
                (splitLast current)
        let precedingTerm = leftAssociatedDisjunction preceding
            finalIndex = offset + fromIntegral (length preceding)
        disjunctionEliminationProof
            context
            precedingTerm
            final
            currentProof
            target
            (\leftContext leftProof ->
                go leftContext offset preceding leftProof)
            (\rightContext rightProof ->
                handle rightContext finalIndex rightProof)

-- | Transport element membership along a checked set equality.
transportMembershipProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> Either KernelProofBuildError (BuiltProof global)
transportMembershipProof context element setEquality membership = do
    (sourceSet, targetSet) <-
        case scopedCoreTerm (builtProofStatement setEquality) of
            CEq TySet source target -> Right (source, target)
            _ ->
                Left
                    (ProofStructuralCompositionMismatch
                        "membership transport requires set equality")
    weakenedElement <-
        first ProofTermIllTyped
            (weakenScopedCore
                (proofContextGlobalTyping context)
                TySet
                element)
    function <-
        scopedTerm context
            (CLam TySet
                (membershipTerm
                    (scopedCoreTerm weakenedElement)
                    (CBound 0)))
    functionReflexivity <-
        equalityReflexivityProof context function
    propositionEquality <-
        equalityCongruenceApplicationProof
            context
            functionReflexivity
            setEquality
    appliedSource <-
        scopedTerm context
            (CApp (scopedCoreTerm function) sourceSet)
    sourceMembership <-
        conversionProof context membership appliedSource
    transported <-
        equalityModusPonensProof
            context
            propositionEquality
            sourceMembership
    targetMembership <-
        scopedTerm context
            (membershipTerm
                (scopedCoreTerm element)
                targetSet)
    conversionProof context transported targetMembership

-- | Validate the excluded-middle target generated by binary case analysis.
-- Classical strength enters only through the confined double-negation
-- elimination foundation fact.
validateExcludedMiddleComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validateExcludedMiddleComposition foundation globalType goal = do
    let lexicalContext = scopedCoreContext goal
    validatePropositionContext
        "excluded-middle goal" lexicalContext goal
    propositionTerm <-
        case scopedCoreTerm goal of
            COr proposition (CNot negated)
                | proposition == negated ->
                    pure proposition
            _ ->
                Left
                    (ProofStructuralCompositionMismatch
                        "goal is not an excluded-middle disjunction")
    let context =
            ProofContext foundation globalType lexicalContext []
    proposition <- scopedTerm context propositionTerm
    negation <- scopedTerm context (CNot propositionTerm)
    negatedGoal <- scopedTerm context (CNot (scopedCoreTerm goal))
    doubleNegation <-
        negationIntroductionProof context negatedGoal
            (\withNegatedGoal negatedGoalProof -> do
                negationProof <-
                    negationIntroductionProof withNegatedGoal proposition
                        (\withProposition propositionProof -> do
                            goalProof <-
                                disjunctionLeftProof
                                    withProposition
                                    (scopedCoreTerm negation)
                                    propositionProof
                            negationEliminationProof
                                withProposition
                                goalProof
                                (weakenForHypothesis negatedGoalProof))
                goalProof <-
                    disjunctionRightProof
                        withNegatedGoal
                        propositionTerm
                        negationProof
                negationEliminationProof
                    withNegatedGoal
                    goalProof
                    negatedGoalProof)
    result <- doubleNegationEliminationProof context goal doubleNegation
    unless (builtProofStatement result == goal)
        (Left
            (ProofStructuralCompositionMismatch
                "excluded middle did not derive the owned goal"))

-- | Build the classical textbook step that proves @left or right@ by
-- assuming @not left@ and deriving @right@. The admitted child is represented
-- by the exact implication from that assumption to its remaining goal.
buildClassicalDisjunctionAssumptionComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError (BuiltProof global)
buildClassicalDisjunctionAssumptionComposition
        foundation globalType goal assumption conclusion = do
    let lexicalContext = scopedCoreContext goal
    validatePropositionContext
        "classical disjunction goal" lexicalContext goal
    validatePropositionContext
        "classical disjunction assumption" lexicalContext assumption
    validatePropositionContext
        "classical disjunction remainder" lexicalContext conclusion
    (leftTerm, rightTerm) <-
        case scopedCoreTerm goal of
            COr left right -> pure (left, right)
            _ ->
                Left
                    (ProofStructuralCompositionMismatch
                        "classical disjunction opening requires a disjunction")
    unless
        ( scopedCoreTerm assumption == CNot leftTerm
            && scopedCoreTerm conclusion == rightTerm
        )
        (Left
            (ProofStructuralCompositionMismatch
                "classical disjunction opening changed its assumption or remainder"))
    implication <-
        scopedFromTerms lexicalContext
            (CImp
                (scopedCoreTerm assumption)
                (scopedCoreTerm conclusion))
    let context =
            ProofContext foundation globalType lexicalContext [implication]
    implicationProof <- hypothesisProof context implication
    left <- scopedTerm context leftTerm
    negatedGoal <- scopedTerm context (CNot (scopedCoreTerm goal))
    doubleNegation <-
        negationIntroductionProof context negatedGoal
            (\withNegatedGoal negatedGoalProof -> do
                notLeft <-
                    negationIntroductionProof withNegatedGoal left
                        (\withLeft leftProof -> do
                            goalProof <-
                                disjunctionLeftProof
                                    withLeft rightTerm leftProof
                            negationEliminationProof
                                withLeft
                                goalProof
                                (weakenForHypothesis negatedGoalProof))
                rightProof <-
                    implicationEliminationProof
                        withNegatedGoal
                        (weakenForHypothesis implicationProof)
                        notLeft
                goalProof <-
                    disjunctionRightProof
                        withNegatedGoal leftTerm rightProof
                negationEliminationProof
                    withNegatedGoal goalProof negatedGoalProof)
    result <- doubleNegationEliminationProof context goal doubleNegation
    unless (builtProofStatement result == goal)
        (Left
            (ProofStructuralCompositionMismatch
                "classical disjunction opening did not derive the owned goal"))
    pure result
  where
    scopedFromTerms context term =
        first ProofTermIllTyped
            (checkScopedCanonicalCore globalType context term)

validateClassicalDisjunctionAssumptionComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validateClassicalDisjunctionAssumptionComposition
        foundation globalType goal assumption conclusion =
    () <$ buildClassicalDisjunctionAssumptionComposition
        foundation globalType goal assumption conclusion

-- | Build the natural-deduction bridge for one checked assumption opening.
-- The detailed opening is ephemeral: it keeps the occurrence correspondence
-- needed to build the bridge, while callers may retain only its compact
-- proposition witness.
buildAssumptionOpeningComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> Loose.DetailedAssumptionOpening global
    -> Either KernelProofBuildError (BuiltProof global)
buildAssumptionOpeningComposition foundation globalType detailed = do
    validatePropositionContext
        "assumption-opening goal" lexicalContext goal
    validatePropositionContext
        "assumption-opening supplied proposition"
        lexicalContext
        assumption
    validatePropositionContext
        "assumption-opening residual"
        lexicalContext
        residual
    case Loose.detailedOpeningKind detailed of
        Loose.DirectImplicationOpening ->
            buildDirectImplication
        Loose.DirectNegationOpening ->
            buildDirectNegation
        Loose.ClassicalDisjunctionOpening ->
            buildClassicalDisjunctionAssumptionComposition
                foundation globalType goal assumption residual
        Loose.ConjunctiveFrontierOpening ->
            buildConjunctiveFrontier
  where
    goal = Loose.detailedOpeningGoal detailed
    assumption = Loose.detailedOpeningSupplied detailed
    residual = Loose.detailedOpeningResidual detailed
    lexicalContext = scopedCoreContext goal

    openingImplication = do
        implication <-
            maybe
                (Left
                    (ProofStructuralCompositionMismatch
                        "assumption opening has incompatible implication context"))
                pure
                (implyScopedCore assumption residual)
        pure
            ( ProofContext
                foundation
                globalType
                lexicalContext
                [implication]
            , implication
            )

    buildDirectImplication = do
        (context, implication) <- openingImplication
        result <- hypothesisProof context implication
        requireTarget result

    buildDirectNegation = do
        (context, implication) <- openingImplication
        result <-
            negationIntroductionProof
                context
                assumption
                (\extended _assumptionProof -> do
                    implicationProof <-
                        hypothesisProof extended implication
                    suppliedProof <-
                        hypothesisProof extended assumption
                    implicationEliminationProof
                        extended
                        implicationProof
                        suppliedProof)
        requireTarget result

    buildConjunctiveFrontier = do
        (context, implication) <- openingImplication
        result <-
            introducePositivePremises
                context
                implication
                []
                (Loose.frontierPositivePremises
                    (Loose.detailedOpeningFrontier detailed))
        requireTarget result

    introducePositivePremises
        context implication originalProofs = \case
        [] ->
            case Loose.frontierRemainder
                    (Loose.detailedOpeningFrontier detailed) of
                Loose.OrdinaryRemainder _ ->
                    buildOrdinaryRemainder
                        context implication originalProofs
                Loose.TerminalNegationRemainder ->
                    buildTerminalNegation
                        context implication originalProofs
        Loose.FrontierPremise tree : rest -> do
            premise <- requireView tree
            implicationIntroductionProof
                context
                premise
                (\extended premiseProof ->
                    introducePositivePremises
                        extended
                        implication
                        (map weakenForHypothesis originalProofs
                            <> [premiseProof])
                        rest)

    buildOrdinaryRemainder context implication originalProofs = do
        implicationProof <- hypothesisProof context implication
        suppliedProof <-
            buildSupplied
                context
                originalProofs
                Nothing
        residualProof <-
            implicationEliminationProof
                context
                implicationProof
                suppliedProof
        applyResidual
            context
            originalProofs
            residualProof

    buildTerminalNegation context implication originalProofs = do
        negativeTree <-
            maybe
                (Left
                    (ProofStructuralCompositionMismatch
                        "terminal-negation frontier has no negative tree"))
                pure
                (Loose.frontierNegativePremise
                    (Loose.detailedOpeningFrontier detailed))
        negativeProposition <- requireView negativeTree
        negationIntroductionProof
            context
            negativeProposition
            (\extended negativeProof -> do
                let weakenedOriginalProofs =
                        map weakenForHypothesis originalProofs
                implicationProof <- hypothesisProof extended implication
                suppliedProof <-
                    buildSupplied
                        extended
                        weakenedOriginalProofs
                        (Just negativeProof)
                residualProof <-
                    implicationEliminationProof
                        extended
                        implicationProof
                        suppliedProof
                residualAfterPositive <-
                    applyResidual
                        extended
                        weakenedOriginalProofs
                        residualProof
                case
                        Loose.detailedResidualNegativePremise detailed of
                    Nothing ->
                        pure residualAfterPositive
                    Just _remainingTree -> do
                        remainingProofMaybe <-
                            projectRemaining
                                extended
                                negativeSelections
                                negativeTree
                                negativeProof
                        remainingProof <-
                            maybe
                                (Left
                                    (ProofStructuralCompositionMismatch
                                        "terminal negation residual lost its proof"))
                                pure
                                remainingProofMaybe
                        negationEliminationProof
                            extended
                            remainingProof
                            residualAfterPositive)

    buildSupplied context originalProofs negativeProof = do
        let selected =
                Loose.detailedSelectedLeaves detailed
            selectedByPath =
                Map.fromList
                    [ ( Loose.selectedSuppliedPath leaf
                      , leaf)
                    | leaf <- selected
                    ]
        buildSuppliedTree
            context
            originalProofs
            negativeProof
            selectedByPath
            (Loose.detailedSuppliedTree detailed)

    buildSuppliedTree
        context originalProofs negativeProof selectedByPath =
        go []
      where
        go path (Loose.ConjunctionLeaf expected) = do
            selectedLeaf <-
                maybe
                    (Left
                        (ProofStructuralCompositionMismatch
                            "supplied conjunction leaf was not selected"))
                    pure
                    (Map.lookup path selectedByPath)
            proof <-
                proofForSelectedLeaf
                    context
                    originalProofs
                    negativeProof
                    selectedLeaf
            unless
                (builtProofStatement proof == expected)
                (Left
                    (ProofStructuralCompositionMismatch
                        "selected supplied leaf changed proposition"))
            pure proof
        go path (Loose.ConjunctionBranch left right) = do
            leftProof <-
                go (path <> [Loose.ConjunctionLeft]) left
            rightProof <-
                go (path <> [Loose.ConjunctionRight]) right
            conjunctionIntroductionProof
                context
                leftProof
                rightProof

    proofForSelectedLeaf
        context originalProofs negativeProof selectedLeaf =
        case Loose.selectedFrontierOccurrence selectedLeaf of
            Loose.PositiveFrontierOccurrence index path -> do
                originalProof <-
                    maybe
                        (Left
                            (ProofStructuralCompositionMismatch
                                "selected positive premise is out of range"))
                        pure
                        (nth index originalProofs)
                originalTree <-
                    maybe
                        (Left
                            (ProofStructuralCompositionMismatch
                                "selected positive tree is out of range"))
                        (pure . Loose.frontierPremiseTree)
                        (nth index
                            (Loose.frontierPositivePremises
                                (Loose.detailedOpeningFrontier detailed)))
                projectAtPath
                    context
                    originalTree
                    path
                    originalProof
            Loose.NegativeFrontierOccurrence path -> do
                proof <-
                    maybe
                        (Left
                            (ProofStructuralCompositionMismatch
                                "selected negative leaf is outside negation"))
                        pure
                        negativeProof
                originalTree <-
                    maybe
                        (Left
                            (ProofStructuralCompositionMismatch
                                "selected negative tree is absent"))
                        pure
                        (Loose.frontierNegativePremise
                            (Loose.detailedOpeningFrontier detailed))
                projectAtPath
                    context
                    originalTree
                    path
                    proof

    applyResidual context originalProofs current =
        foldM
            (applyResidualPremise context originalProofs)
            current
            (zip
                (Loose.frontierPositivePremises
                    (Loose.detailedOpeningFrontier detailed))
                (Loose.detailedResidualPositivePremises detailed))

    applyResidualPremise
        context originalProofs current
        (Loose.FrontierPremise originalTree, residualPremise) =
        case Loose.residualPositiveTree residualPremise of
            Nothing ->
                pure current
            Just _remainingTree -> do
                let index = Loose.residualPositiveIndex residualPremise
                originalProof <-
                    maybe
                        (Left
                            (ProofStructuralCompositionMismatch
                                "residual positive premise is out of range"))
                        pure
                        (nth index originalProofs)
                remainingProofMaybe <-
                    projectRemaining
                        context
                        (selectedPositive index)
                        originalTree
                        originalProof
                remainingProof <-
                    maybe
                        (Left
                            (ProofStructuralCompositionMismatch
                                "positive residual lost its proof"))
                        pure
                        remainingProofMaybe
                implicationEliminationProof
                    context
                    current
                    remainingProof

    selectedPositive index =
        Set.fromList
            [ path
            | leaf <- Loose.detailedSelectedLeaves detailed
            , Loose.PositiveFrontierOccurrence selectedIndex path <-
                [Loose.selectedFrontierOccurrence leaf]
            , selectedIndex == index
            ]

    negativeSelections =
        Set.fromList
            [ path
            | leaf <- Loose.detailedSelectedLeaves detailed
            , Loose.NegativeFrontierOccurrence path <-
                [Loose.selectedFrontierOccurrence leaf]
            ]

    projectAtPath context tree path proof =
        case (tree, path) of
            (_, []) ->
                pure proof
            (Loose.ConjunctionBranch left right, side : rest) -> do
                requireConjunctionView left right proof
                child <-
                    case side of
                        Loose.ConjunctionLeft ->
                            conjunctionLeftProof
                                context
                                proof
                        Loose.ConjunctionRight ->
                            conjunctionRightProof
                                context
                                proof
                projectAtPath context
                    (case side of
                        Loose.ConjunctionLeft -> left
                        Loose.ConjunctionRight -> right)
                    rest
                    child
            (Loose.ConjunctionLeaf{}, _ : _) ->
                Left
                    (ProofStructuralCompositionMismatch
                        "a selected leaf path crossed a conjunction leaf")

    projectRemaining context selected tree proof =
        case tree of
            Loose.ConjunctionLeaf _
                | Set.member [] selected ->
                    pure Nothing
                | otherwise ->
                    pure (Just proof)
            Loose.ConjunctionBranch left right -> do
                requireConjunctionView left right proof
                leftProof <-
                    conjunctionLeftProof
                        context
                        proof
                rightProof <-
                    conjunctionRightProof
                        context
                        proof
                leftRemaining <-
                    projectRemaining
                        context
                        (selectBranch Loose.ConjunctionLeft selected)
                        left
                        leftProof
                rightRemaining <-
                    projectRemaining
                        context
                        (selectBranch Loose.ConjunctionRight selected)
                        right
                        rightProof
                case (leftRemaining, rightRemaining) of
                    (Nothing, Nothing) ->
                        pure Nothing
                    (Just remaining, Nothing) ->
                        pure (Just remaining)
                    (Nothing, Just remaining) ->
                        pure (Just remaining)
                    (Just remainingLeft, Just remainingRight) ->
                        Just
                            <$> conjunctionIntroductionProof
                                context
                                remainingLeft
                                remainingRight

    selectBranch side selected =
        Set.fromList
            [ rest
            | path <- Set.toList selected
            , branchSide : rest <- [path]
            , branchSide == side
            ]

    requireConjunctionView left right proof = do
        leftCore <- requireView left
        rightCore <- requireView right
        expected <- maybe
            (Left (ProofStructuralCompositionMismatch
                "checked conjunction children changed lexical context"))
            pure (conjoinExactScopedCore leftCore rightCore)
        unless (builtProofStatement proof == expected)
            (Left (ProofStructuralCompositionMismatch
                "conjunction elimination received different conjuncts"))

    requireView tree =
        maybe
            (Left
                (ProofStructuralCompositionMismatch
                    "checked conjunction tree changed lexical context"))
            pure
            (Loose.conjunctionViewCore tree)

    requireTarget result
        | builtProofStatement result == Loose.detailedOpeningGoal detailed =
            pure result
        | otherwise =
            Left
                (ProofStructuralCompositionMismatch
                    "assumption opening did not derive its owned goal")

validateAssumptionOpeningComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> Loose.DetailedAssumptionOpening global
    -> Either KernelProofBuildError ()
validateAssumptionOpeningComposition foundation globalType detailed =
    () <$ buildAssumptionOpeningComposition foundation globalType detailed

-- | Validate the structural rule used by checked source case analysis.
-- The branch proofs and the exhaustive disjunction are represented here by
-- corresponding hypotheses; the kernel combinators must derive the owned goal
-- from precisely those propositions.  No derived proof escapes this check.
validateCaseAnalysisComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> NonEmpty (ScopedCheckedCore global)
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validateCaseAnalysisComposition
        foundation globalType goal cases exhaustive = do
    validatePropositionContext "case goal" lexicalContext goal
    traverse_
        (validatePropositionContext "case assumption" lexicalContext)
        cases
    validatePropositionContext
        "case exhaustiveness target" lexicalContext exhaustive
    let expectedExhaustive =
            foldl1
                COr
                (scopedCoreTerm <$> cases)
    unless (scopedCoreTerm exhaustive == expectedExhaustive)
        (Left
            (ProofStructuralCompositionMismatch
                "case exhaustiveness is not the source-ordered disjunction"))
    branchImplications <-
        traverse
            (checkedImplication lexicalContext goal)
            cases
    let context =
            ProofContext
                foundation
                globalType
                lexicalContext
                (exhaustive : toList branchImplications)
    exhaustiveProof <- hypothesisProof context exhaustive
    result <-
        eliminateCases
            context goal cases exhaustiveProof
    unless (builtProofStatement result == goal)
        (Left
            (ProofStructuralCompositionMismatch
                "case elimination did not derive the owned goal"))
  where
    lexicalContext = scopedCoreContext goal

    checkedImplication expectedContext conclusion antecedent =
        case implyScopedCore antecedent conclusion of
            Just implication
                | scopedCoreContext implication == expectedContext ->
                    pure implication
            _ ->
                Left
                    (ProofStructuralCompositionMismatch
                        "case branch implication changed context")

    eliminateCases context result (only :| []) caseProof = do
        branchImplication <-
            scopedTerm context
                (CImp
                    (scopedCoreTerm only)
                    (scopedCoreTerm result))
            >>= hypothesisProof context
        implicationEliminationProof context branchImplication caseProof
    eliminateCases context result (firstCase :| rest) disjunctionProof = do
        let allCases = firstCase :| rest
            leftCases = NonEmpty.fromList (NonEmpty.init allCases)
            rightCase = NonEmpty.last allCases
            leftTerm =
                foldl1 disjunctionTerm
                    (scopedCoreTerm <$> leftCases)
        disjunctionEliminationProof
            context
            leftTerm
            (scopedCoreTerm rightCase)
            disjunctionProof
            result
            (\extended leftProof ->
                eliminateCases extended result leftCases leftProof)
            (\extended rightProof -> do
                branchImplication <-
                    scopedTerm extended
                        (CImp
                            (scopedCoreTerm rightCase)
                            (scopedCoreTerm result))
                        >>= hypothesisProof extended
                implicationEliminationProof
                    extended branchImplication rightProof)

-- | Validate the classical closing step for a proof by contradiction.
-- The only classical input is the confined 'DoubleNegationElim' foundation
-- row already consumed by 'doubleNegationEliminationProof'.
validateDoubleNegationComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validateDoubleNegationComposition
        foundation globalType goal negation falsum = do
    let lexicalContext = scopedCoreContext goal
    validatePropositionContext "contradiction goal" lexicalContext goal
    validatePropositionContext
        "contradiction negation" lexicalContext negation
    validatePropositionContext "contradiction falsum" lexicalContext falsum
    unless (scopedCoreTerm falsum == CFalsum)
        (Left
            (ProofStructuralCompositionMismatch
                "proof by contradiction did not target falsum"))
    expectedNegation <-
        checkedNegation lexicalContext goal
    unless (negation == expectedNegation)
        (Left
            (ProofStructuralCompositionMismatch
                "proof by contradiction did not own the exact negated goal"))
    doubleNegation <-
        checkedNegation lexicalContext negation
    let context =
            ProofContext
                foundation globalType lexicalContext [doubleNegation]
    hypothesis <- hypothesisProof context doubleNegation
    result <- doubleNegationEliminationProof context goal hypothesis
    unless (builtProofStatement result == goal)
        (Left
            (ProofStructuralCompositionMismatch
                "double-negation elimination did not derive the owned goal"))

-- | Validate the exact ex-falso closing step used after a terminal indirect
-- contradiction discharge.
validateFalsumEliminationComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validateFalsumEliminationComposition foundation globalType goal falsum = do
    let lexicalContext = scopedCoreContext goal
    validatePropositionContext "contradiction goal" lexicalContext goal
    validatePropositionContext "contradiction falsum" lexicalContext falsum
    unless (scopedCoreTerm falsum == CFalsum)
        (Left
            (ProofStructuralCompositionMismatch
                "falsum elimination did not receive falsum"))
    let context =
            ProofContext foundation globalType lexicalContext [falsum]
    hypothesis <- hypothesisProof context falsum
    result <- falsumEliminationProof context hypothesis goal
    unless (builtProofStatement result == goal)
        (Left
            (ProofStructuralCompositionMismatch
                "falsum elimination did not derive the owned goal"))

-- | Validate the exact structural instance used by source set induction.
-- The admitted child is represented by its generalized step proposition;
-- the checked foundation row must specialize to that exact premise and the
-- owned binder-level result. No induction principle becomes an ATP premise.
validateSetInductionComposition
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> Natural
    -> ScopedCheckedCore global
    -> [ScopedCheckedCore global]
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validateSetInductionComposition
        foundation globalType selected property antecedents childTarget
        hypothesis result = do
    let lexicalContext = scopedCoreContext property
    traverse_
        (validatePropositionContext
            "set-induction antecedent" lexicalContext)
        antecedents
    validatePropositionContext
        "set-induction property" lexicalContext property
    validatePropositionContext
        "set-induction child target" lexicalContext childTarget
    validatePropositionContext
        "set-induction hypothesis" lexicalContext hypothesis
    validatePropositionContext
        "set-induction result" lexicalContext result
    expectedProperty <-
        foldrM implyChecked childTarget antecedents
    unless (property == expectedProperty)
        (Left
            (ProofStructuralCompositionMismatch
                "set-induction property does not own the child target and guards"))
    (predicate, expectedHypothesis, step, expectedResult) <-
        maybe
            (Left
                (ProofStructuralCompositionMismatch
                    "set-induction focus is not a set-valued ambient binder"))
            pure
            (scopedSetInductionInstance selected property)
    unless (hypothesis == expectedHypothesis)
        (Left
            (ProofStructuralCompositionMismatch
                "set-induction hypothesis does not match the owned property"))
    unless (result == expectedResult)
        (Left
            (ProofStructuralCompositionMismatch
                "set-induction result does not close the owned property"))
    let context =
            ProofContext foundation globalType lexicalContext [step]
    stepProof <- hypothesisProof context step
    axiom <- foundationProof context SetInduction
    instanceProof <- forallEliminationProof context axiom predicate
    expectedInstance <-
        maybe
            (Left
                (ProofStructuralCompositionMismatch
                    "set-induction instance changed lexical context"))
            pure
            (implyScopedCore step result)
    convertedInstance <-
        conversionProof context instanceProof expectedInstance
    resultProof <-
        implicationEliminationProof context convertedInstance stepProof
    unless (builtProofStatement resultProof == result)
        (Left
            (ProofStructuralCompositionMismatch
                "set-induction foundation instance did not derive the owned result"))
  where
    implyChecked antecedent conclusion =
        maybe
            (Left
                (ProofStructuralCompositionMismatch
                    "set-induction guard changed lexical context"))
            pure
            (implyScopedCore antecedent conclusion)

validatePropositionContext
    :: Text
    -> [CoreType]
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError ()
validatePropositionContext label expected proposition =
    unless
        ( scopedCoreType proposition == TyProp
            && scopedCoreContext proposition == expected
        )
        (Left
            (ProofStructuralCompositionMismatch
                (label <> " has the wrong type or lexical context")))

checkedNegation
    :: [CoreType]
    -> ScopedCheckedCore global
    -> Either KernelProofBuildError (ScopedCheckedCore global)
checkedNegation expectedContext proposition =
    case negateScopedCore proposition of
        Just negation
            | scopedCoreContext negation == expectedContext ->
                pure negation
        _ ->
            Left
                (ProofStructuralCompositionMismatch
                    "classical negation changed context")

existentialTerm
    :: CoreType
    -> CanonicalTerm global
    -> CanonicalTerm global
existentialTerm = CExists

existentialIntroductionProof
    :: Eq global
    => ProofContext global
    -> CoreType
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
existentialIntroductionProof
        context
        binderType
        bodyUnderBinder
        witness
        bodyAtWitness = do
    unless
        (case scopedCoreContext bodyUnderBinder of
            actualBinder : outerContext ->
                actualBinder == binderType
                    && outerContext == proofContextTypes context
            [] -> False)
        (Left ProofExpectedUnaryBinder)
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.existentialIntroduction
                (proofContextGlobalTyping context)
                bodyUnderBinder
                witness
                (builtProofStatement bodyAtWitness))
    pure
        (BuiltProof
            conclusion
            (existentialIntroductionDerivation
                bodyUnderBinder
                witness
                (builtProofDerivation bodyAtWitness)))

existentialEliminationProof
    :: Eq global
    => ProofContext global
    -> CoreType
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> ScopedCheckedCore global
         -> BuiltProof global
         -> Either
            KernelProofBuildError
            (BuiltProof global)
       )
    -> Either
        KernelProofBuildError
        (BuiltProof global)
existentialEliminationProof
        context
        binderType
        bodyUnderBinder
        existential
        result
        bodyCase = do
    expectedExistential <-
        scopedTerm context
            (CExists binderType (scopedCoreTerm bodyUnderBinder))
    unless (builtProofStatement existential == expectedExistential)
        (Left
            (ProofStructuralCompositionMismatch
                "existential elimination received a different binder body"))
    (withBinder, variable) <-
        extendProofContextBinder context binderType
    branch <-
        buildHypothesisBranch withBinder bodyUnderBinder
            (\withBody bodyProof ->
                bodyCase withBody variable bodyProof)
    conclusion <-
        first ProofSemanticsFailed
            (Semantics.existentialElimination
                (proofContextGlobalTyping context)
                (builtProofStatement existential)
                result
                (builtProofStatement branch))
    pure
        (BuiltProof
            conclusion
            (existentialEliminationDerivation
                (builtProofDerivation existential)
                result
                (builtProofDerivation branch)))

setLfpBoundProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
setLfpBoundProof
        (ProofContext
            foundation
            globalType
            _types
            _hypotheses)
        domain
        operator = do
    result <-
        first (ProofSetLfpRuleFailed . Text.pack . show)
            (SetLfp.setLfpBound
                foundation
                globalType
                domain
                operator)
    pure
        (BuiltProof
            result
            (setLfpBoundDerivation
                domain
                operator))

setLfpLeastProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
setLfpLeastProof
        (ProofContext
            foundation
            globalType
            _types
            _hypotheses)
        domain
        operator
        candidate
        closed
        bounded = do
    result <-
        first (ProofSetLfpRuleFailed . Text.pack . show)
            (SetLfp.setLfpLeast
                foundation
                globalType
                domain
                operator
                candidate
                (builtProofStatement closed)
                (builtProofStatement bounded))
    pure
        (BuiltProof
            result
            (setLfpLeastDerivation
                domain
                operator
                candidate
                (builtProofDerivation closed)
                (builtProofDerivation bounded)))

setLfpFixedProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
setLfpFixedProof
        (ProofContext
            foundation
            globalType
            _types
            _hypotheses)
        domain
        operator
        monotone = do
    result <-
        first (ProofSetLfpRuleFailed . Text.pack . show)
            (SetLfp.setLfpFixed
                foundation
                globalType
                domain
                operator
                (builtProofStatement
                    monotone))
    pure
        (BuiltProof
            result
            (setLfpFixedDerivation
                domain
                operator
                (builtProofDerivation
                    monotone)))

setLfpInductProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        KernelProofBuildError
        (BuiltProof global)
setLfpInductProof
        (ProofContext
            foundation
            globalType
            _types
            _hypotheses)
        domain
        operator
        predicate
        element
        monotone
        member
        closure = do
    result <-
        first (ProofSetLfpRuleFailed . Text.pack . show)
            (SetLfp.setLfpInduct
                foundation
                globalType
                domain
                operator
                predicate
                element
                (builtProofStatement
                    monotone)
                (builtProofStatement
                    member)
                (builtProofStatement
                    closure))
    pure
        (BuiltProof
            result
            (setLfpInductDerivation
                domain
                operator
                predicate
                element
                (builtProofDerivation
                    monotone)
                (builtProofDerivation
                    member)
                (builtProofDerivation
                    closure)))

-- | Close each guarded least-fixed-point rule into the exact theorem schema
-- exposed by the final prelude.  This is a presentation of the checked rule,
-- not a new foundation axiom: replay still records the corresponding guarded
-- rule tag and every logical introduction explicitly.
setLfpRuleSchemaProof
    :: CheckedFoundation
    -> KernelRuleTag
    -> Either KernelProofBuildError (BuiltProof Void)
setLfpRuleSchemaProof foundation tag =
    case tag of
        SetLfpBound -> boundSchema
        SetLfpLeast -> leastSchema
        SetLfpFixed -> fixedSchema
        SetLfpInduct -> inductSchema
  where
    root = rootProofContext foundation emptyGlobalTyping
    operatorType = TyArrow TySet TySet
    predicateType = TyArrow TySet TyProp

    boundSchema =
        forallIntroductionProof root TySet \withDomain _domain ->
            forallIntroductionProof withDomain operatorType
                \withOperator _operator -> do
                    domain <- boundAt withOperator 1
                    operator <- boundAt withOperator 0
                    setLfpBoundProof withOperator domain operator

    leastSchema =
        forallIntroductionProof root TySet \withDomain _domain ->
            forallIntroductionProof withDomain operatorType
                \withOperator _operator ->
                    forallIntroductionProof withOperator TySet
                        \withCandidate _candidate -> do
                            domain <- boundAt withCandidate 2
                            operator <- boundAt withCandidate 1
                            candidate <- boundAt withCandidate 0
                            operatorCandidate <-
                                scopedTerm withCandidate
                                    (CApp
                                        (scopedCoreTerm operator)
                                        (scopedCoreTerm candidate))
                            closed <- checkedSetLfpResult
                                (SetLfp.subsetProposition
                                    emptyGlobalTyping
                                    operatorCandidate
                                    candidate)
                            bounded <- checkedSetLfpResult
                                (SetLfp.subsetProposition
                                    emptyGlobalTyping
                                    candidate
                                    domain)
                            implicationIntroductionProof
                                withCandidate closed
                                \withClosed _closedProof ->
                                    implicationIntroductionProof
                                        withClosed bounded
                                        \withBounded _boundedProof -> do
                                            closedProof <-
                                                hypothesisProof
                                                    withBounded closed
                                            boundedProof <-
                                                hypothesisProof
                                                    withBounded bounded
                                            setLfpLeastProof
                                                withBounded
                                                domain
                                                operator
                                                candidate
                                                closedProof
                                                boundedProof

    fixedSchema =
        forallIntroductionProof root TySet \withDomain _domain ->
            forallIntroductionProof withDomain operatorType
                \withOperator _operator -> do
                    domain <- boundAt withOperator 1
                    operator <- boundAt withOperator 0
                    monotone <- checkedSetLfpResult
                        (SetLfp.boundedMonoProposition
                            emptyGlobalTyping
                            domain
                            operator)
                    implicationIntroductionProof
                        withOperator monotone
                        \withMonotone monotoneProof ->
                            setLfpFixedProof
                                withMonotone
                                domain
                                operator
                                monotoneProof

    inductSchema =
        forallIntroductionProof root TySet \withDomain _domain ->
            forallIntroductionProof withDomain operatorType
                \withOperator _operator ->
                    forallIntroductionProof withOperator predicateType
                        \withPredicate _predicate ->
                            forallIntroductionProof withPredicate TySet
                                \withElement _element -> do
                                    domain <- boundAt withElement 3
                                    operator <- boundAt withElement 2
                                    predicate <- boundAt withElement 1
                                    element <- boundAt withElement 0
                                    monotone <- checkedSetLfpResult
                                        (SetLfp.boundedMonoProposition
                                            emptyGlobalTyping
                                            domain
                                            operator)
                                    fixedPoint <- checkedSetLfpResult
                                        (SetLfp.setLfpTerm
                                            emptyGlobalTyping
                                            domain
                                            operator)
                                    member <- checkedSetLfpResult
                                        (SetLfp.memberProposition
                                            emptyGlobalTyping
                                            element
                                            fixedPoint)
                                    closure <- checkedSetLfpResult
                                        (SetLfp.inductionClosureProposition
                                            emptyGlobalTyping
                                            domain
                                            operator
                                            predicate)
                                    implicationIntroductionProof
                                        withElement monotone
                                        \withMonotone _monotoneProof ->
                                            implicationIntroductionProof
                                                withMonotone member
                                                \withMember _memberProof ->
                                                    implicationIntroductionProof
                                                        withMember closure
                                                        \withClosure _closureProof -> do
                                                            monotoneProof <-
                                                                hypothesisProof
                                                                    withClosure
                                                                    monotone
                                                            memberProof <-
                                                                hypothesisProof
                                                                    withClosure
                                                                    member
                                                            closureProof <-
                                                                hypothesisProof
                                                                    withClosure
                                                                    closure
                                                            setLfpInductProof
                                                                withClosure
                                                                domain
                                                                operator
                                                                predicate
                                                                element
                                                                monotoneProof
                                                                memberProof
                                                                closureProof

    boundAt context index =
        scopedTerm context (CBound index)

    checkedSetLfpResult =
        first (ProofSetLfpRuleFailed . Text.pack . show)

leftAssociatedConjunction :: [CanonicalTerm global] -> CanonicalTerm global
leftAssociatedConjunction = \case
    [] -> CTruth
    initial : remaining -> foldl' CAnd initial remaining

leftAssociatedDisjunction :: [CanonicalTerm global] -> CanonicalTerm global
leftAssociatedDisjunction = \case
    [] -> CFalsum
    initial : remaining -> foldl' COr initial remaining

membershipTerm
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
membershipTerm element set =
    CApp (CApp (CIntrinsic Member) element) set

splitLast :: [value] -> Maybe ([value], value)
splitLast = \case
    [] -> Nothing
    [final] -> Just ([], final)
    initial : remaining -> do
        (preceding, final) <- splitLast remaining
        pure (initial : preceding, final)

splitAtNatural
    :: Natural
    -> [value]
    -> Maybe ([value], value, [value])
splitAtNatural = go []
  where
    go _preceding _index [] = Nothing
    go preceding 0 (selected : rest) =
        Just (reverse preceding, selected, rest)
    go preceding index (item : rest) =
        go (item : preceding) (index - 1) rest

proofContextGlobalTyping
    :: ProofContext global
    -> GlobalTyping global
proofContextGlobalTyping
        (ProofContext
            _foundation
            globalType
            _types
            _hypotheses) =
    globalType

equalityParts
    :: ScopedCheckedCore global
    -> Either
        KernelProofBuildError
        ( CoreType
        , CanonicalTerm global
        , CanonicalTerm global
        )
equalityParts equality =
    case scopedCoreTerm equality of
        CEq operandType left right ->
            Right (operandType, left, right)
        _ ->
            Left ProofExpectedEquality

weakenForHypothesis
    :: BuiltProof global
    -> BuiltProof global
weakenForHypothesis = weakenProofHypotheses 1

-- | Reuse a proof underneath newly introduced proof hypotheses.  Term-binder
-- contexts are unchanged; only references to hypotheses outside the retained
-- derivation are shifted.
weakenProofHypotheses
    :: Natural
    -> BuiltProof global
    -> BuiltProof global
weakenProofHypotheses amount
        (BuiltProof statement derivation) =
    BuiltProof
        statement
        (weakenDerivationHypotheses amount derivation)

countedWeakenProofHypotheses
    :: Natural
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedWeakenProofHypotheses amount proof
    | amount == 0 = pure proof
countedWeakenProofHypotheses amount
        (BuiltProof statement derivation) = do
    available <- proofGets proofRemainingStructural
    case countedWeakenDerivationHypotheses
            available amount derivation of
        (Nothing, remaining) -> do
            modifyProofState
                (\state ->
                    state {proofRemainingStructural = remaining})
            throwCountedFailure CountedCoreStructuralWorkExhausted
        (Just weakened, remaining) -> do
            modifyProofState
                (\state ->
                    state {proofRemainingStructural = remaining})
            pure (BuiltProof statement weakened)


-- Counted focused materializers --------------------------------------------

-- The counted builders are a policy-free kernel seam.  Every builder entry
-- consumes one structural unit. Core and logical inference consume structural
-- work; conversion attempts debit the same caller-owned pool throughout a
-- compound proof. Uncounted builders use the operation policy for each attempt.
data CountedProofState = CountedProofState
    { proofRemainingStructural :: !Word
    , proofConversionAccount :: !ProofConversionAccount
    }

data ProofConversionAccount
    = DedicatedConversionPool !Conversion.ConversionPool
    | SharedProofWork

-- The hidden constructor and absence of MonadState/MonadError instances prevent
-- clients from restoring spent credit or catching a partial kernel operation.
newtype CountedProof global value = CountedProof
    (Except.ExceptT (CountedCoreFailure KernelProofBuildError) (State CountedProofState) value)
    deriving newtype (Functor, Applicative, Monad)

type role CountedProof nominal nominal

proofGets :: (CountedProofState -> value) -> CountedProof global value
proofGets select = CountedProof (State.gets select)

modifyProofState :: (CountedProofState -> CountedProofState) -> CountedProof global ()
modifyProofState update = CountedProof (State.modify' update)

throwCountedFailure :: CountedCoreFailure KernelProofBuildError -> CountedProof global value
throwCountedFailure = CountedProof . Except.throwE

-- | Run one atomic proof attempt, retaining both accounts on success or failure.
runCountedProof
    :: Word
    -> Conversion.ConversionPool
    -> CountedProof global value
    -> (Either (CountedCoreFailure KernelProofBuildError) value, Word, Conversion.ConversionPool)
runCountedProof structural pool (CountedProof operation) =
    let (result, finalState) =
            State.runState
                (Except.runExceptT operation)
                (CountedProofState structural (DedicatedConversionPool pool))
    in ( result
       , proofRemainingStructural finalState
       , case proofConversionAccount finalState of
            DedicatedConversionPool remaining -> remaining
            SharedProofWork -> impossible "a counted proof changed its conversion account"
       )

runSharedProofWork
    :: Word -> CountedProof global value
    -> (Either (CountedCoreFailure KernelProofBuildError) value, Word)
runSharedProofWork work (CountedProof operation) =
    let (result, final) = State.runState (Except.runExceptT operation)
            (CountedProofState work SharedProofWork)
    in (result, proofRemainingStructural final)

consumeProofEntry :: CountedProof global ()
consumeProofEntry = do
    remaining <- proofGets proofRemainingStructural
    if remaining == 0
        then throwCountedFailure CountedCoreStructuralWorkExhausted
        else
            modifyProofState
                (\state ->
                    state {proofRemainingStructural = remaining - 1})

liftProofCore
    :: (failure -> KernelProofBuildError)
    -> ( Word
         -> (Either (CountedCoreFailure failure) value, Word)
       )
    -> CountedProof global value
liftProofCore mapFailure operation = do
    remaining <- proofGets proofRemainingStructural
    let (result, afterOperation) = operation remaining
    modifyProofState
        (\state ->
            state {proofRemainingStructural = afterOperation})
    either (throwCountedFailure . fmap mapFailure) pure result

liftProofExact
    :: ( Word
         -> (Either (CountedCoreFailure Void) value, Word)
       )
    -> CountedProof global value
liftProofExact =
    liftProofCore absurd

liftProofSemantics
    :: ( Word
         -> ( Either
                (CountedCoreFailure Semantics.KernelSemanticsError)
                value
            , Word
            )
       )
    -> CountedProof global value
liftProofSemantics = liftProofCore ProofSemanticsFailed

proofOperationFailure
    :: KernelProofBuildError
    -> CountedProof global value
proofOperationFailure =
    throwCountedFailure . CountedCoreOperationFailed

countedScopedIdentityAction
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> CountedProof global Bool
countedScopedIdentityAction left right =
    liftProofExact
        (\remaining -> countedScopedCoreIdentity remaining left right)

countedTypeIdentityAction
    :: CoreType
    -> CoreType
    -> CountedProof global Bool
countedTypeIdentityAction left right =
    liftProofExact
        (\remaining -> countedCoreTypeIdentity remaining left right)

countedContextIdentityAction
    :: [CoreType]
    -> [CoreType]
    -> CountedProof global Bool
countedContextIdentityAction left right =
    liftProofExact
        (\remaining -> countedCoreTypeListIdentity remaining left right)

countedScopedProofContext
    :: CheckedFoundation -> GlobalTyping global -> [CoreType] -> [ScopedCheckedCore global]
    -> CountedProof global (ProofContext global)
countedScopedProofContext foundation typing context hypotheses = do
    for_ hypotheses \hypothesis -> do
        consumeProofEntry
        same <- countedContextIdentityAction context (scopedCoreContext hypothesis)
        unless (same && scopedCoreType hypothesis == TyProp)
            (proofOperationFailure (ProofStructuralCompositionMismatch "a composition child changed scope or type"))
    pure (ProofContext foundation typing context hypotheses)

countedScopedTerm
    :: ProofContext global
    -> CanonicalTerm global
    -> CountedProof global (ScopedCheckedCore global)
countedScopedTerm
        (ProofContext _foundation globalType context _hypotheses)
        term = do
    consumeProofEntry
    liftProofCore ProofTermIllTyped
        (\remaining ->
            countedCheckScopedCanonicalCore
                globalType remaining context term)

-- | Owner-local admission consumes structural work, never conversion credit.
countedAdmitScopedTerm
    :: ProofContext global
    -> ScopedCheckedCore global
    -> CountedProof global (ScopedCheckedCore global)
countedAdmitScopedTerm (ProofContext _foundation globalType context _hypotheses) term = do
    consumeProofEntry
    same <- countedContextIdentityAction context (scopedCoreContext term)
    unless same
        (proofOperationFailure (ProofStructuralCompositionMismatch
            "checked input has a different lexical context"))
    liftProofCore ProofTermIllTyped
        (\remaining -> countedAdmitScopedCheckedCore globalType remaining term)

countedImportedProof
    :: ProofContext global
    -> ImportIx
    -> FrozenCheckedCore global
    -> CountedProof global (BuiltProof global)
countedImportedProof context index statement = do
    consumeProofEntry
    pure
        (BuiltProof
            (embedClosedCore (proofContextTypes context) statement)
            (importedFactDerivation index))

countedIndexedHypothesisProof
    :: ProofContext global
    -> HypothesisIx
    -> CountedProof global (BuiltProof global)
countedIndexedHypothesisProof
        (ProofContext _foundation _globalType _context hypotheses)
        index = do
    consumeProofEntry
    statement <- select (hypothesisIxValue index) hypotheses
    pure
        (BuiltProof
            statement
            (localHypothesisDerivation index))
  where
    select _position [] =
        proofOperationFailure ProofHypothesisNotFound
    select 0 (statement : _rest) = do
        consumeProofEntry
        pure statement
    select position (_statement : rest) = do
        consumeProofEntry
        select (position - 1) rest

countedHypothesisProofs
    :: ProofContext global
    -> CountedProof global [BuiltProof global]
countedHypothesisProofs
        (ProofContext _foundation _globalType _context hypotheses) = do
    consumeProofEntry
    go 0 hypotheses
  where
    go _position [] = pure []
    go position (statement : rest) = do
        consumeProofEntry
        remaining <- go (position + 1) rest
        pure
            ( BuiltProof
                statement
                (localHypothesisDerivation (hypothesisIx position))
            : remaining
            )

requireCountedPropositionContext
    :: Text
    -> [CoreType]
    -> ScopedCheckedCore global
    -> CountedProof global ()
requireCountedPropositionContext label expected proposition = do
    sameContext <-
        countedContextIdentityAction
            expected (scopedCoreContext proposition)
    propositionType <-
        countedTypeIdentityAction TyProp (scopedCoreType proposition)
    unless (sameContext && propositionType)
        (proofOperationFailure
            (ProofStructuralCompositionMismatch
                (label <> " has the wrong type or lexical context")))

countedExtendProofContextHypothesis
    :: ProofContext global
    -> ScopedCheckedCore global
    -> CountedProof global (ProofContext global)
countedExtendProofContextHypothesis
        (ProofContext foundation globalType types hypotheses)
        premise = do
    consumeProofEntry
    requireCountedPropositionContext
        "introduced proof hypothesis" types premise
    pure
        (ProofContext
            foundation globalType types (premise : hypotheses))

countedExtendProofContextBinder
    :: ProofContext global
    -> CoreType
    -> CountedProof
        global
        (ProofContext global, ScopedCheckedCore global)
countedExtendProofContextBinder
        (ProofContext foundation globalType types hypotheses)
        binderType = do
    consumeProofEntry
    weakened <- weakenHypotheses hypotheses
    let extended =
            ProofContext
                foundation
                globalType
                (binderType : types)
                weakened
    variable <- countedScopedTerm extended (CBound 0)
    pure (extended, variable)
  where
    weakenHypotheses [] =
        pure []
    weakenHypotheses (hypothesis : rest) = do
        consumeProofEntry
        weakened <-
            liftProofExact
                (\remaining ->
                    countedWeakenCheckedScopedCore
                        remaining binderType hypothesis)
        remaining <- weakenHypotheses rest
        pure (weakened : remaining)

countedTruthIntroductionProof
    :: ProofContext global
    -> CountedProof global (BuiltProof global)
countedTruthIntroductionProof context = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedTruthIntroduction
                    (proofContextGlobalTyping context)
                    structural
                    (proofContextTypes context))
    pure (BuiltProof conclusion truthIntroductionDerivation)

-- | Compose premises already entered by their consumer. Already checked inputs
-- entering a new owner use 'countedAdmitScopedTerm'; raw 'countedScopedTerm'
-- checking already establishes admission. BuiltProof carries no such token.
countedConjunctionIntroductionProof
    :: BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedConjunctionIntroductionProof left right = do
    consumeProofEntry
    result <-
        liftProofSemantics
            (\structural ->
                Semantics.countedConjunctionIntroduction
                    structural
                    (builtProofStatement left)
                    (builtProofStatement right))
    pure
        (BuiltProof
            result
            (conjunctionIntroductionDerivation
                (builtProofDerivation left)
                (builtProofDerivation right)))

countedDisjunctionLeftProof
    :: ProofContext global
    -> CanonicalTerm global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedDisjunctionLeftProof context right leftProof = do
    consumeProofEntry
    rightTarget <- countedScopedTerm context right
    result <-
        liftProofSemantics
            (\structural ->
                Semantics.countedDisjunctionLeftIntroduction
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement leftProof)
                    rightTarget)
    pure
        (BuiltProof
            result
            (disjunctionLeftIntroductionDerivation
                (builtProofDerivation leftProof)
                rightTarget))

countedDisjunctionRightProof
    :: ProofContext global
    -> CanonicalTerm global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedDisjunctionRightProof context left rightProof = do
    consumeProofEntry
    leftTarget <- countedScopedTerm context left
    result <-
        liftProofSemantics
            (\structural ->
                Semantics.countedDisjunctionRightIntroduction
                    (proofContextGlobalTyping context)
                    structural
                    leftTarget
                    (builtProofStatement rightProof))
    pure
        (BuiltProof
            result
            (disjunctionRightIntroductionDerivation
                leftTarget
                (builtProofDerivation rightProof)))

countedPreparedDisjunctionEliminationProof
    :: Eq global
    => ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedPreparedDisjunctionEliminationProof
        context left right disjunction result leftBranch rightBranch = do
    consumeProofEntry
    expectedDisjunction <-
        countedScopedTerm context (COr left right)
    matches <-
        countedScopedIdentityAction
            (builtProofStatement disjunction) expectedDisjunction
    unless matches
        (proofOperationFailure
            (ProofStructuralCompositionMismatch
                "disjunction elimination received different disjuncts"))
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedDisjunctionElimination
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement disjunction)
                    (builtProofStatement leftBranch)
                    (builtProofStatement rightBranch))
    resultMatches <- countedScopedIdentityAction conclusion result
    unless resultMatches
        (proofOperationFailure
            (ProofStructuralCompositionMismatch
                "disjunction branches did not derive the requested result"))
    pure
        (BuiltProof
            conclusion
            (disjunctionEliminationDerivation
                (builtProofDerivation disjunction)
                (builtProofDerivation leftBranch)
                (builtProofDerivation rightBranch)))

countedConjunctionProjectionAction
    :: Eq global
    => Bool
    -> ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedConjunctionProjectionAction selectLeft context left right conjunction = do
    consumeProofEntry
    expected <- countedScopedTerm context (CAnd left right)
    matches <-
        countedScopedIdentityAction
            (builtProofStatement conjunction) expected
    unless matches
        (proofOperationFailure
            (ProofStructuralCompositionMismatch
                "conjunction elimination received different conjuncts"))
    result <-
        liftProofSemantics
            (\structural ->
                (if selectLeft
                    then Semantics.countedConjunctionLeftElimination
                    else Semantics.countedConjunctionRightElimination)
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement conjunction))
    pure
        (BuiltProof
            result
            ((if selectLeft
                then conjunctionLeftEliminationDerivation
                else conjunctionRightEliminationDerivation)
                (builtProofDerivation conjunction)))

countedConjunctionLeftProof
    :: Eq global
    => ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedConjunctionLeftProof context left right conjunction =
    (countedConjunctionProjectionAction
            True context left right conjunction)

countedConjunctionRightProof
    :: Eq global
    => ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedConjunctionRightProof context left right conjunction =
    (countedConjunctionProjectionAction
            False context left right conjunction)

countedImplicationEliminationProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedImplicationEliminationProof _context implication premise = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedImplicationElimination
                    structural
                    (builtProofStatement implication)
                    (builtProofStatement premise))
    pure
        (BuiltProof
            conclusion
            (implicationEliminationDerivation
                (builtProofDerivation implication)
                (builtProofDerivation premise)))

countedImplicationIntroductionProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedImplicationIntroductionProof context premise body = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedImplicationIntroduction
                    (proofContextGlobalTyping context)
                    structural
                    premise
                    (builtProofStatement body))
    pure
        (BuiltProof
            conclusion
            (implicationIntroductionDerivation
                premise (builtProofDerivation body)))

-- Composition for callers which already own their branch contexts. These
-- mirror the ordinary checked rules without adding snapshot readmission.
countedComposeImplicationProof
    :: ProofContext global -> ScopedCheckedCore global -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedComposeImplicationProof context premise body = do
    consumeProofEntry
    requireCountedPropositionContext "introduced proof hypothesis" (proofContextTypes context) premise
    conclusion <- liftProofSemantics (\work -> Semantics.countedComposeImplication work premise (builtProofStatement body))
    pure (BuiltProof conclusion (implicationIntroductionDerivation premise (builtProofDerivation body)))

countedProjectConjunctionProof
    :: Bool -> ProofContext global -> BuiltProof global -> CountedProof global (BuiltProof global)
countedProjectConjunctionProof selectLeft _context conjunction = do
    consumeProofEntry
    conclusion <- liftProofSemantics (\work -> Semantics.countedProjectConjunction selectLeft work (builtProofStatement conjunction))
    pure (BuiltProof conclusion ((if selectLeft then conjunctionLeftEliminationDerivation else conjunctionRightEliminationDerivation)
        (builtProofDerivation conjunction)))

countedComposeReflexivityProof
    :: ProofContext global -> ScopedCheckedCore global -> CountedProof global (BuiltProof global)
countedComposeReflexivityProof _context operand = do
    consumeProofEntry
    conclusion <- liftProofSemantics (\work -> Semantics.countedComposeReflexivity work operand)
    pure (BuiltProof conclusion (scopedEqualityReflexivityDerivation operand))

countedComposeApplicationEqualityProof
    :: ProofContext global -> BuiltProof global -> BuiltProof global -> CountedProof global (BuiltProof global)
countedComposeApplicationEqualityProof _context function argument = do
    consumeProofEntry
    conclusion <- liftProofSemantics (\work -> Semantics.countedComposeApplicationEquality work
        (builtProofStatement function) (builtProofStatement argument))
    pure (BuiltProof conclusion (equalityCongruenceApplicationDerivation
        (builtProofDerivation function) (builtProofDerivation argument)))

countedComposeEqualityModusPonensProof
    :: Eq global => ProofContext global -> BuiltProof global -> BuiltProof global -> CountedProof global (BuiltProof global)
countedComposeEqualityModusPonensProof _context equality premise = do
    consumeProofEntry
    conclusion <- liftProofSemantics (\work -> Semantics.countedComposeEqualityModusPonens work
        (builtProofStatement equality) (builtProofStatement premise))
    pure (BuiltProof conclusion (equalityModusPonensDerivation
        (builtProofDerivation equality) (builtProofDerivation premise)))

countedNegationIntroductionProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedNegationIntroductionProof context premise falsum = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedNegationIntroduction
                    (proofContextGlobalTyping context)
                    structural
                    premise
                    (builtProofStatement falsum))
    pure
        (BuiltProof
            conclusion
            (negationIntroductionDerivation
                premise (builtProofDerivation falsum)))

countedNegationEliminationProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedNegationEliminationProof context premise negation = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedNegationElimination
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement premise)
                    (builtProofStatement negation))
    pure
        (BuiltProof
            conclusion
            (negationEliminationDerivation
                (builtProofDerivation premise)
                (builtProofDerivation negation)))

countedFoundationProof
    :: ProofContext global
    -> FoundationAxiomTag
    -> CountedProof global (BuiltProof global)
countedFoundationProof
        context@(ProofContext
            foundation _globalType _types _hypotheses)
        tag = do
    consumeProofEntry
    pure
        (BuiltProof
            (embedClosedCore
                (proofContextTypes context)
                (eliminateFrozenVoid
                    (foundationAxiomFrozen foundation tag)))
            (foundationFactDerivation tag))

countedDoubleNegationEliminationProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedDoubleNegationEliminationProof
        context target doubleNegation = do
    axiom <- countedFoundationProof context DoubleNegationElim
    instanceProof <-
        countedForallEliminationProof context axiom target
    countedImplicationEliminationProof
        context instanceProof doubleNegation

-- | Derive @proposition or not proposition@ with all proof construction and
-- nested-hypothesis weakening charged to the supplied budgets.  This is the
-- single classical branch-splitting seam used by deterministic refutation.
countedExcludedMiddleProof
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> CountedProof global (BuiltProof global)
countedExcludedMiddleProof context proposition = do
    requireCountedPropositionContext
        "excluded-middle proposition"
        (proofContextTypes context)
        proposition
    let propositionTerm = scopedCoreTerm proposition
        goalTerm = COr propositionTerm (CNot propositionTerm)
    negation <- countedScopedTerm context (CNot propositionTerm)
    goal <- countedScopedTerm context goalTerm
    negatedGoal <- countedScopedTerm context (CNot goalTerm)
    withNegatedGoal <-
        countedExtendProofContextHypothesis context negatedGoal
    negatedGoalProof <-
        countedIndexedHypothesisProof
            withNegatedGoal (hypothesisIx 0)
    withProposition <-
        countedExtendProofContextHypothesis
            withNegatedGoal proposition
    propositionProof <-
        countedIndexedHypothesisProof
            withProposition (hypothesisIx 0)
    leftGoalProof <-
        countedDisjunctionLeftProof
            withProposition
            (scopedCoreTerm negation)
            propositionProof
    nestedNegatedGoalProof <-
        countedWeakenProofHypotheses 1 negatedGoalProof
    firstFalsum <-
        countedNegationEliminationProof
            withProposition leftGoalProof nestedNegatedGoalProof
    negationProof <-
        countedNegationIntroductionProof
            withNegatedGoal proposition firstFalsum
    rightGoalProof <-
        countedDisjunctionRightProof
            withNegatedGoal propositionTerm negationProof
    secondFalsum <-
        countedNegationEliminationProof
            withNegatedGoal rightGoalProof negatedGoalProof
    doubleNegation <-
        countedNegationIntroductionProof
            context negatedGoal secondFalsum
    countedDoubleNegationEliminationProof
        context goal doubleNegation

countedExistentialIntroductionProof
    :: Eq global
    => ProofContext global
    -> CoreType
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedExistentialIntroductionProof context binderType body witness premise = do
    consumeProofEntry
    case scopedCoreContext body of
        actualBinder : outerContext -> do
            sameBinder <- countedTypeIdentityAction actualBinder binderType
            unless sameBinder (proofOperationFailure ProofExpectedUnaryBinder)
            sameContext <- countedContextIdentityAction outerContext (proofContextTypes context)
            unless sameContext (proofOperationFailure ProofExpectedUnaryBinder)
        [] -> proofOperationFailure ProofExpectedUnaryBinder
    conclusion <- liftProofSemantics (\work ->
        Semantics.countedExistentialIntroduction
            (proofContextGlobalTyping context) work body witness (builtProofStatement premise))
    pure (BuiltProof conclusion
        (existentialIntroductionDerivation body witness (builtProofDerivation premise)))

-- The caller prepares and charges the branch's fresh binder and body
-- hypothesis before search. This operation discharges that retained branch;
-- it neither opens another scope nor calls back into search.
countedPreparedExistentialEliminationProof
    :: Eq global
    => ProofContext global
    -> CoreType
    -> CanonicalTerm global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedPreparedExistentialEliminationProof context binderType body existential result branch = do
    consumeProofEntry
    expected <- countedScopedTerm context (CExists binderType body)
    matches <- countedScopedIdentityAction (builtProofStatement existential) expected
    unless matches (proofOperationFailure
        (ProofStructuralCompositionMismatch
            "existential elimination received a different binder body"))
    conclusion <- liftProofSemantics (\work ->
        Semantics.countedExistentialElimination (proofContextGlobalTyping context) work
            (builtProofStatement existential) result (builtProofStatement branch))
    pure (BuiltProof conclusion
        (existentialEliminationDerivation
            (builtProofDerivation existential) result (builtProofDerivation branch)))

countedForallEliminationProof
    :: ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> CountedProof global (BuiltProof global)
countedForallEliminationProof _context quantified argument = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedForallElimination
                    structural
                    (builtProofStatement quantified)
                    argument)
    pure
        (BuiltProof
            conclusion
            (forallEliminationDerivation
                (builtProofDerivation quantified) argument))

countedForallIntroductionProof
    :: ProofContext global
    -> CoreType
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedForallIntroductionProof context binderType body = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedForallIntroduction
                    (proofContextGlobalTyping context)
                    structural binderType
                    (builtProofStatement body))
    pure
        (BuiltProof
            conclusion
            (forallIntroductionDerivation
                binderType (builtProofDerivation body)))

countedFalsumEliminationProof
    :: ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> CountedProof global (BuiltProof global)
countedFalsumEliminationProof context falsum target = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedFalsumElimination
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement falsum)
                    target)
    pure
        (BuiltProof
            conclusion
            (falsumEliminationDerivation
                (builtProofDerivation falsum) target))

countedEqualityReflexivityProof
    :: ProofContext global
    -> ScopedCheckedCore global
    -> CountedProof global (BuiltProof global)
countedEqualityReflexivityProof context operand = do
    consumeProofEntry
    equality <-
        liftProofSemantics
            (\structural ->
                Semantics.countedEqualityReflexivity
                    (proofContextGlobalTyping context)
                    structural operand)
    pure
        (BuiltProof equality
            (scopedEqualityReflexivityDerivation operand))

countedEqualityCongruenceApplicationProof
    :: ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedEqualityCongruenceApplicationProof
        context functionEquality argumentEquality = do
    consumeProofEntry
    equality <-
        liftProofSemantics
            (\structural ->
                Semantics.countedEqualityCongruenceApplication
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement functionEquality)
                    (builtProofStatement argumentEquality))
    pure
        (BuiltProof
            equality
            (equalityCongruenceApplicationDerivation
                (builtProofDerivation functionEquality)
                (builtProofDerivation argumentEquality)))

countedComposeEqualityProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedComposeEqualityProof context firstEquality secondEquality = do
    consumeProofEntry
    (firstType, source, middle) <-
        countedEqualityPartsAction
            (builtProofStatement firstEquality)
    (secondType, middle', target) <-
        countedEqualityPartsAction
            (builtProofStatement secondEquality)
    sameType <- countedTypeIdentityAction firstType secondType
    sameMiddle <-
        liftProofExact
            (\remaining ->
                countedCanonicalIdentity
                    remaining middle middle')
    unless (sameType && sameMiddle)
        (proofOperationFailure
            (ProofStructuralCompositionMismatch
                "equality composition has mismatched middle operands"))
    shiftedSource <-
        liftProofExact
            (\remaining ->
                countedShiftCanonical
                    remaining 1 0 source)
    predicate <-
        countedScopedTerm context
            (CLam firstType
                (CEq firstType shiftedSource (CBound 0)))
    composed <-
        countedEqualityTransportProof
            context secondEquality predicate firstEquality
    expected <-
        countedScopedTerm context
            (CEq firstType source target)
    countedConversionProof context composed expected

countedEqualityModusPonensProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedEqualityModusPonensProof context equality premise = do
    consumeProofEntry
    conclusion <-
        liftProofSemantics
            (\structural ->
                Semantics.countedEqualityModusPonens
                    (proofContextGlobalTyping context)
                    structural
                    (builtProofStatement equality)
                    (builtProofStatement premise))
    pure
        (BuiltProof
            conclusion
            (equalityModusPonensDerivation
                (builtProofDerivation equality)
                (builtProofDerivation premise)))

countedConversionProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> CountedProof global (BuiltProof global)
countedConversionProof context source target = do
    consumeProofEntry
    account <- proofGets proofConversionAccount
    pool <- case account of
        DedicatedConversionPool remaining -> pure remaining
        SharedProofWork -> Conversion.conversionPool <$> proofGets proofRemainingStructural
    let (result, remaining) =
            runProofConversion
                (aggregateConversionLimitOwner pool) pool context source target
    case account of
        DedicatedConversionPool _ -> do
            modifyProofState (\state -> state {proofConversionAccount = DedicatedConversionPool remaining})
            either proofOperationFailure pure result
        SharedProofWork -> do
            modifyProofState (\state -> state {proofRemainingStructural = Conversion.conversionPoolAmount remaining})
            case result of
                Left (ProofConversionLimitExhausted ProofConversionAggregatePool _) ->
                    throwCountedFailure CountedCoreStructuralWorkExhausted
                Left failure -> proofOperationFailure failure
                Right proof -> pure proof

countedEqualityPartsAction
    :: ScopedCheckedCore global
    -> CountedProof
        global
        (CoreType, CanonicalTerm global, CanonicalTerm global)
countedEqualityPartsAction equality =
    case scopedCoreTerm equality of
        CEq operandType left right -> pure (operandType, left, right)
        _ -> proofOperationFailure ProofExpectedEquality

countedEqualityTransportProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedEqualityTransportProof context equality predicate premise = do
    consumeProofEntry
    (operandType, left, right) <-
        countedEqualityPartsAction (builtProofStatement equality)
    predicateTypeMatches <-
        countedTypeIdentityAction
            (scopedCoreType predicate)
            (TyArrow operandType TyProp)
    unless predicateTypeMatches
        (proofOperationFailure
            (ProofStructuralCompositionMismatch
                "equality transport predicate has the wrong type"))
    predicateReflexivity <-
        countedEqualityReflexivityProof context predicate
    propositionEquality <-
        countedEqualityCongruenceApplicationProof
            context predicateReflexivity equality
    leftApplication <-
        countedScopedTerm context
            (CApp (scopedCoreTerm predicate) left)
    rightApplication <-
        countedScopedTerm context
            (CApp (scopedCoreTerm predicate) right)
    premise' <-
        countedConversionProof
            context premise leftApplication
    transported <-
        countedEqualityModusPonensProof
            context propositionEquality premise'
    countedConversionProof
        context transported rightApplication

-- | Transport a proved proposition through an actual equality. Structural
-- construction and the required beta conversions debit one work account;
-- the existing per-conversion operation cap still applies. The supplied target
-- is checked at the end, and every retained conversion is replayed normally.
transportEqualityWithinWork
    :: Eq global
    => Word -> ProofContext global -> EqualityTransportDirection
    -> BuiltProof global -> ScopedCheckedCore global -> BuiltProof global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelProofBuildError) (BuiltProof global), Word)
transportEqualityWithinWork work context direction equality predicate premise target =
    let action = do
            directed <- case direction of
                EqualityLeftToRight -> pure equality
                EqualityRightToLeft -> countedEqualityReverseProof context equality
            transported <- countedEqualityTransportProof context directed predicate premise
            countedConversionProof context transported target
    in runSharedProofWork work action

-- | Apply an equality under a checked abstraction and retain the direct
-- endpoints. Congruence and beta conversion share one bounded work account.
congruenceEqualityWithinWork
    :: Eq global
    => Word -> ProofContext global -> BuiltProof global
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelProofBuildError) (BuiltProof global), Word)
congruenceEqualityWithinWork work context equality abstraction before after =
    let action = do
            beforeContext <- countedContextIdentityAction (proofContextTypes context) (scopedCoreContext before)
            afterContext <- countedContextIdentityAction (proofContextTypes context) (scopedCoreContext after)
            sameType <- countedTypeIdentityAction (scopedCoreType before) (scopedCoreType after)
            unless (beforeContext && afterContext && sameType)
                (proofOperationFailure (ProofStructuralCompositionMismatch
                    "congruence endpoints have different types or lexical contexts"))
            function <- countedEqualityReflexivityProof context abstraction
            applied <- countedEqualityCongruenceApplicationProof context function equality
            expected <- countedScopedTerm context
                (CEq (scopedCoreType before) (scopedCoreTerm before) (scopedCoreTerm after))
            countedConversionProof context applied expected
    in runSharedProofWork work action

countedEqualityReverseProof
    :: Eq global
    => ProofContext global
    -> BuiltProof global
    -> CountedProof global (BuiltProof global)
countedEqualityReverseProof context equality = do
    consumeProofEntry
    (operandType, left, right) <-
        countedEqualityPartsAction (builtProofStatement equality)
    leftOperand <- countedScopedTerm context left
    weakenedLeft <-
        liftProofCore ProofTermIllTyped
            (\remaining ->
                countedWeakenScopedCore
                    (proofContextGlobalTyping context)
                    remaining operandType leftOperand)
    function <-
        countedScopedTerm context
            (CLam operandType
                (CEq
                    operandType
                    (CBound 0)
                    (scopedCoreTerm weakenedLeft)))
    functionReflexivity <-
        countedEqualityReflexivityProof context function
    appliedEquality <-
        countedEqualityCongruenceApplicationProof
            context functionReflexivity equality
    leftReflexivity <-
        countedEqualityReflexivityProof context leftOperand
    appliedLeft <-
        countedScopedTerm context
            (CApp (scopedCoreTerm function) left)
    expected <-
        countedScopedTerm context
            (CEq operandType right left)
    appliedLeftReflexivity <-
        countedConversionProof
            context leftReflexivity appliedLeft
    reversedApplication <-
        countedEqualityModusPonensProof
            context appliedEquality appliedLeftReflexivity
    countedConversionProof
        context reversedApplication expected
