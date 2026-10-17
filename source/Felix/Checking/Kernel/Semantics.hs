{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked logical inference over scoped canonical HOL terms.
module Felix.Checking.Kernel.Semantics
    ( truthIntroduction
    , negationIntroduction
    , negationElimination
    , conjunctionIntroduction
    , conjunctionLeftElimination
    , conjunctionRightElimination
    , disjunctionLeftIntroduction
    , disjunctionRightIntroduction
    , disjunctionElimination
    , existentialIntroduction
    , existentialElimination
    , implicationElimination
    , implicationIntroduction
    , forallElimination
    , forallIntroduction
    , falsumElimination
    , equalityReflexivity
    , equalityCongruenceApplication
    , equalityCongruenceLambda
    , equalityModusPonens
    , countedTruthIntroduction
    , countedNegationIntroduction
    , countedNegationElimination
    , countedConjunctionIntroduction
    , countedConjunctionLeftElimination
    , countedConjunctionRightElimination
    , countedDisjunctionLeftIntroduction
    , countedDisjunctionRightIntroduction
    , countedDisjunctionElimination
    , countedExistentialIntroduction
    , countedExistentialElimination
    , countedImplicationElimination
    , countedImplicationIntroduction
    , countedComposeImplication
    , countedProjectConjunction
    , countedComposeReflexivity
    , countedComposeApplicationEquality
    , countedComposeEqualityModusPonens
    , countedForallElimination
    , countedForallIntroduction
    , countedFalsumElimination
    , countedEqualityReflexivity
    , countedEqualityCongruenceApplication
    , countedEqualityCongruenceLambda
    , countedEqualityModusPonens
    , KernelSemanticsError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)

import Control.Monad (unless)
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Word (Word)


data KernelSemanticsError
    = KernelContextMismatch
        ![CoreType]
        ![CoreType]
    | KernelBinderContextMismatch
        !CoreType
        ![CoreType]
    | KernelExpectedProposition !CoreType
    | KernelExpectedImplication
    | KernelImplicationPremiseMismatch
    | KernelExpectedForall
    | KernelForallArgumentTypeMismatch
        !CoreType
        !CoreType
    | KernelExpectedFalsum
    | KernelExpectedNegation
    | KernelNegationPremiseMismatch
    | KernelExpectedConjunction
    | KernelExpectedDisjunction
    | KernelDisjunctionBranchMismatch
    | KernelExpectedExists
    | KernelExistentialWitnessTypeMismatch
        !CoreType
        !CoreType
    | KernelExistentialPremiseMismatch
    | KernelExistentialResultMismatch
    | KernelExpectedEquality
    | KernelEqualityOperandTypeMismatch
        !CoreType
        !CoreType
    | KernelExpectedFunctionEquality !CoreType
    | KernelEqualityPremiseMismatch
    | KernelConclusionIllTyped !CoreCheckError
    | KernelScopedInstantiationFailed !ScopedInstantiationError
    | KernelCheckedCompositionFailed !Text
    deriving stock (Show, Eq)

truthIntroduction
    :: GlobalTyping global
    -> [CoreType]
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
truthIntroduction globalType context =
    checkConclusion globalType context CTruth

negationIntroduction
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
negationIntroduction globalType = negationIntroductionWith ordinaryChecks (checkConclusion globalType)

negationElimination
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
negationElimination globalType = negationEliminationWith ordinaryChecks
    (\left right -> pure (left == right)) (checkConclusion globalType)

conjunctionIntroduction
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
conjunctionIntroduction left right = do
    propositionPair ordinaryChecks left right
    checkedComposition "conjunction introduction" (conjoinExactScopedCore left right)

conjunctionLeftElimination
    :: ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
conjunctionLeftElimination = conjunctionEliminationWith ordinaryChecks pure fst

conjunctionRightElimination
    :: ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
conjunctionRightElimination = conjunctionEliminationWith ordinaryChecks pure snd

disjunctionLeftIntroduction
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
disjunctionLeftIntroduction globalType left right =
    binaryIntroductionWith ordinaryChecks (checkConclusion globalType) COr (scopedCoreContext left) left right

disjunctionRightIntroduction
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
disjunctionRightIntroduction globalType left right =
    binaryIntroductionWith ordinaryChecks (checkConclusion globalType) COr (scopedCoreContext right) left right

disjunctionElimination
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
disjunctionElimination globalType = disjunctionEliminationWith ordinaryChecks
    (\left right -> pure (left == right)) (checkConclusion globalType)

existentialIntroduction
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
existentialIntroduction globalType = existentialIntroductionWith ordinaryChecks
    (\witness body -> pure (instantiateCanonical (scopedCoreTerm witness) (scopedCoreTerm body)))
    (\left right -> pure (left == right)) (checkConclusion globalType)

existentialElimination
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
existentialElimination globalType = existentialEliminationWith ordinaryChecks
    (pure . shiftCanonical 1 0) (\left right -> pure (left == right)) (checkConclusion globalType)

implicationElimination
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
implicationElimination = implicationEliminationWith ordinaryChecks
    (\expected premise -> pure (premise == expected))

implicationIntroduction
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
implicationIntroduction premise conclusion = do
    propositionPair ordinaryChecks premise conclusion
    checkedComposition "implication introduction" (implyScopedCore premise conclusion)

forallElimination
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
forallElimination = forallEliminationWith ordinaryChecks
    (\argument body -> first KernelScopedInstantiationFailed (instantiateScopedCore argument body))

forallIntroduction
    :: GlobalTyping global
    -> CoreType
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
forallIntroduction globalType = forallIntroductionWith ordinaryChecks (checkConclusion globalType)

falsumElimination
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
falsumElimination _globalType = falsumEliminationWith ordinaryChecks

equalityReflexivity
    :: ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
equalityReflexivity operand =
    checkedComposition "equality reflexivity" (equalScopedCore operand operand)

equalityCongruenceApplication
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
equalityCongruenceApplication = equalityApplicationWith ordinaryChecks \_result leftFunction rightFunction leftArgument rightArgument ->
    checkedComposition "application congruence" do
        left <- applyScopedCore leftFunction leftArgument
        right <- applyScopedCore rightFunction rightArgument
        equalScopedCore left right

equalityCongruenceLambda
    :: CoreType
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
equalityCongruenceLambda = equalityLambdaWith ordinaryChecks
    (\binder body -> pure (abstractScopedCore binder body))
    (\left right -> pure (equalScopedCore left right))

countedEqualityCongruenceLambda
    :: Word -> CoreType -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedEqualityCongruenceLambda structural binder body = runCountedSemantics structural
    (equalityLambdaWith countedChecks
        (\ty value -> liftExactStructuralOperation (\work -> countedAbstractScopedCore work ty value))
        (\left right -> liftExactStructuralOperation (\work -> countedEqualScopedCore work left right)) binder body)

equalityModusPonens
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
equalityModusPonens = equalityModusPonensWith ordinaryChecks (\left right -> pure (left == right)) pure

checkedComposition
    :: Text
    -> Maybe (ScopedCheckedCore global)
    -> Either KernelSemanticsError (ScopedCheckedCore global)
checkedComposition label = maybe (Left (KernelCheckedCompositionFailed label)) Right

checkConclusion
    :: GlobalTyping global
    -> [CoreType]
    -> CanonicalTerm global
    -> Either
        KernelSemanticsError
        (ScopedCheckedCore global)
checkConclusion globalType context =
    first KernelConclusionIllTyped
        . checkScopedCanonicalCore globalType context


-- Counted kernel semantics ---------------------------------------------------

-- These policy-free variants consume structural work only. Conversion evidence
-- and its accounting belong to the proof construction boundary.
type CountedSemantics error =
    Except.ExceptT
        (CountedCoreFailure error)
        (State Word)

runCountedSemantics
    :: Word
    -> CountedSemantics error value
    -> (Either (CountedCoreFailure error) value, Word)
runCountedSemantics structural operation =
    State.runState (Except.runExceptT operation) structural

liftStructuralOperation
    :: (failure -> error)
    -> ( Word
         -> (Either (CountedCoreFailure failure) value, Word)
       )
    -> CountedSemantics error value
liftStructuralOperation mapFailure operation = do
    remaining <- State.get
    let (result, afterOperation) = operation remaining
    State.put $! afterOperation
    either (Except.throwE . fmap mapFailure) pure result

liftExactStructuralOperation
    :: ( Word
         -> (Either (CountedCoreFailure Void) value, Word)
       )
    -> CountedSemantics error value
liftExactStructuralOperation =
    liftStructuralOperation absurd

semanticFailure
    :: error
    -> CountedSemantics error value
semanticFailure =
    Except.throwE . CountedCoreOperationFailed

countedRequireType
    :: CoreType
    -> CoreType
    -> (CoreType -> KernelSemanticsError)
    -> CountedSemantics KernelSemanticsError ()
countedRequireType expected actual mismatch = do
    same <-
        liftExactStructuralOperation
            (\remaining ->
                countedCoreTypeIdentity remaining expected actual)
    unless same (semanticFailure (mismatch actual))

countedExactTerm
    :: Eq global
    => CanonicalTerm global
    -> CanonicalTerm global
    -> CountedSemantics KernelSemanticsError Bool
countedExactTerm left right =
    liftExactStructuralOperation
        (\remaining -> countedCanonicalIdentity remaining left right)

countedCheckConclusion
    :: GlobalTyping global
    -> [CoreType]
    -> CanonicalTerm global
    -> CountedSemantics
        KernelSemanticsError
        (ScopedCheckedCore global)
countedCheckConclusion globalType context term =
    liftStructuralOperation
        KernelConclusionIllTyped
        (\remaining ->
            countedCheckScopedCanonicalCore
                globalType remaining context term)

countedTruthIntroduction
    :: GlobalTyping global
    -> Word
    -> [CoreType]
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedTruthIntroduction globalType structural context =
    runCountedSemantics structural
        (countedCheckConclusion globalType context CTruth)

countedNegationIntroduction
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedNegationIntroduction globalType structural premise falsum = runCountedSemantics structural
    (negationIntroductionWith countedChecks (countedCheckConclusion globalType) premise falsum)

countedNegationElimination
    :: Eq global
    => GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedNegationElimination globalType structural premise negation = runCountedSemantics structural
    (negationEliminationWith countedChecks countedExactTerm (countedCheckConclusion globalType) premise negation)

-- | Checked composition within an admitting consumer. Like the uncounted
-- rule, this establishes typing only, not visibility in a destination snapshot.
countedConjunctionIntroduction
    :: Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedConjunctionIntroduction structural left right =
    let (result, remaining) = countedConjoinExactScopedCore structural left right
    in (first (fmap failure) result, remaining)
  where
    failure = \case
        ScopedConjunctionContextMismatch leftContext rightContext ->
            KernelContextMismatch leftContext rightContext
        ScopedConjunctionExpectedProposition actual -> KernelExpectedProposition actual

countedDisjunctionLeftIntroduction
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedDisjunctionLeftIntroduction globalType structural left right = runCountedSemantics structural
    (binaryIntroductionWith countedChecks (countedCheckConclusion globalType) COr (scopedCoreContext left) left right)

countedDisjunctionRightIntroduction
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedDisjunctionRightIntroduction globalType structural left right = runCountedSemantics structural
    (binaryIntroductionWith countedChecks (countedCheckConclusion globalType) COr (scopedCoreContext right) left right)

countedDisjunctionElimination
    :: Eq global
    => GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedDisjunctionElimination globalType structural disjunction left right = runCountedSemantics structural
    (disjunctionEliminationWith countedChecks countedExactTerm (countedCheckConclusion globalType) disjunction left right)

countedConjunctionLeftElimination
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedConjunctionLeftElimination globalType structural conjunction = runCountedSemantics structural
    (conjunctionEliminationWith countedChecks
        (countedCheckConclusion globalType (scopedCoreContext conjunction) . scopedCoreTerm) fst conjunction)

countedConjunctionRightElimination
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedConjunctionRightElimination globalType structural conjunction = runCountedSemantics structural
    (conjunctionEliminationWith countedChecks
        (countedCheckConclusion globalType (scopedCoreContext conjunction) . scopedCoreTerm) snd conjunction)

countedImplicationElimination
    :: Eq global
    => Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedImplicationElimination structural implication premise = runCountedSemantics structural
    (implicationEliminationWith countedChecks countedExactTerm implication premise)

countedImplicationIntroduction
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedImplicationIntroduction globalType structural premise conclusion = runCountedSemantics structural
    (binaryIntroductionWith countedChecks (countedCheckConclusion globalType) CImp
        (scopedCoreContext premise) premise conclusion)

countedExistentialIntroduction
    :: Eq global
    => GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedExistentialIntroduction globalType structural body witness premise = runCountedSemantics structural
    (existentialIntroductionWith countedChecks
        (\argument target -> scopedCoreTerm <$> liftStructuralOperation KernelScopedInstantiationFailed
            (\work -> countedInstantiateScopedCore work argument target))
        countedExactTerm (countedCheckConclusion globalType) body witness premise)

countedExistentialElimination
    :: Eq global
    => GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedExistentialElimination globalType structural existential result branch = runCountedSemantics structural
    (existentialEliminationWith countedChecks
        (\term -> liftExactStructuralOperation (\work -> countedShiftCanonical work 1 0 term))
        countedExactTerm (countedCheckConclusion globalType) existential result branch)

countedForallElimination
    :: Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedForallElimination structural quantified argument = runCountedSemantics structural
    (forallEliminationWith countedChecks
        (\value body -> liftStructuralOperation KernelScopedInstantiationFailed
            (\work -> countedInstantiateScopedCore work value body)) quantified argument)

countedForallIntroduction
    :: GlobalTyping global
    -> Word
    -> CoreType
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedForallIntroduction globalType structural binder body = runCountedSemantics structural
    (forallIntroductionWith countedChecks (countedCheckConclusion globalType) binder body)

countedFalsumElimination
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedFalsumElimination _globalType structural falsum target = runCountedSemantics structural
    (falsumEliminationWith countedChecks falsum target)

countedEqualityReflexivity
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedEqualityReflexivity globalType structural operand =
    runCountedSemantics structural
        (countedCheckConclusion
            globalType
            (scopedCoreContext operand)
            (CEq
                (scopedCoreType operand)
                (scopedCoreTerm operand)
                (scopedCoreTerm operand)))

countedEqualityCongruenceApplication
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedEqualityCongruenceApplication globalType structural functionEquality argumentEquality = runCountedSemantics structural
    (equalityApplicationWith countedChecks
        (\result leftFunction rightFunction leftArgument rightArgument ->
            countedCheckConclusion globalType (scopedCoreContext functionEquality)
                (CEq result (CApp (scopedCoreTerm leftFunction) (scopedCoreTerm leftArgument))
                    (CApp (scopedCoreTerm rightFunction) (scopedCoreTerm rightArgument)))) functionEquality argumentEquality)

countedEqualityModusPonens
    :: Eq global
    => GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure KernelSemanticsError)
            (ScopedCheckedCore global)
       , Word
       )
countedEqualityModusPonens globalType structural equality premise = runCountedSemantics structural
    (equalityModusPonensWith countedChecks countedExactTerm
        (countedCheckConclusion globalType (scopedCoreContext premise) . scopedCoreTerm) equality premise)

-- These mirror the ordinary rules over already checked operands. Unlike the
-- snapshot-admitting variants above, composition introduces no new globals
-- and does not repeat operand typing. Keep the older admission work policy
-- for its existing bounded callers; measuring formation must not change their
-- allowances or count an extra validation that ordinary replay never does.
countedComposeImplication
    :: Word -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedComposeImplication work premise conclusion = runCountedSemantics work do
    propositionPair countedChecks premise conclusion
    composed <- liftExactStructuralOperation (\remaining -> countedImplyScopedCore remaining premise conclusion)
    countedComposition "implication introduction" composed

countedProjectConjunction
    :: Bool -> Word -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedProjectConjunction leftSide work conjunction = runCountedSemantics work
    (conjunctionEliminationWith countedChecks pure (if leftSide then fst else snd) conjunction)

countedComposeReflexivity
    :: Word -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedComposeReflexivity work operand = runCountedSemantics work do
    composed <- liftExactStructuralOperation (\remaining -> countedEqualScopedCore remaining operand operand)
    countedComposition "equality reflexivity" composed

countedComposeApplicationEquality
    :: Word -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedComposeApplicationEquality work functionEquality argumentEquality = runCountedSemantics work
    (equalityApplicationWith countedChecks construct functionEquality argumentEquality)
  where
    construct _ leftFunction rightFunction leftArgument rightArgument = do
        left <- apply leftFunction leftArgument
        right <- apply rightFunction rightArgument
        composed <- liftExactStructuralOperation (\remaining -> countedEqualScopedCore remaining left right)
        countedComposition "application congruence" composed
    apply function argument = do
        composed <- liftExactStructuralOperation (\remaining -> countedApplyScopedCore remaining function argument)
        countedComposition "application congruence" composed

countedComposeEqualityModusPonens
    :: Eq global => Word -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure KernelSemanticsError) (ScopedCheckedCore global), Word)
countedComposeEqualityModusPonens work equality premise = runCountedSemantics work
    (equalityModusPonensWith countedChecks countedExactTerm pure equality premise)

countedComposition
    :: Text -> Maybe (ScopedCheckedCore global) -> CountedSemantics KernelSemanticsError (ScopedCheckedCore global)
countedComposition label = maybe (semanticFailure (KernelCheckedCompositionFailed label)) pure


-- Rule checks carry only the operations whose work policy differs. Logical
-- shape and error ordering live in the shared rule bodies below.
data RuleChecks m = RuleChecks
    { ruleContext :: [CoreType] -> [CoreType] -> m ()
    , ruleType :: CoreType -> CoreType -> (CoreType -> KernelSemanticsError) -> m ()
    , ruleFailure :: forall value. KernelSemanticsError -> m value
    }

ordinaryChecks :: RuleChecks (Either KernelSemanticsError)
ordinaryChecks = RuleChecks
    (\expected actual -> unless (expected == actual) (Left (KernelContextMismatch expected actual)))
    (\expected actual mismatch -> unless (expected == actual) (Left (mismatch actual)))
    Left

countedChecks :: RuleChecks (CountedSemantics KernelSemanticsError)
countedChecks = RuleChecks context countedRequireType semanticFailure
  where
    context expected actual = do
        same <- liftExactStructuralOperation (\work -> countedCoreTypeListIdentity work expected actual)
        unless same (semanticFailure (KernelContextMismatch expected actual))

sameContext :: RuleChecks m -> ScopedCheckedCore global -> ScopedCheckedCore global -> m ()
sameContext checks left right = ruleContext checks (scopedCoreContext left) (scopedCoreContext right)

proposition :: RuleChecks m -> ScopedCheckedCore global -> m ()
proposition checks value = ruleType checks TyProp (scopedCoreType value) KernelExpectedProposition

propositionPair :: Monad m => RuleChecks m -> ScopedCheckedCore global -> ScopedCheckedCore global -> m ()
propositionPair checks left right = do
    sameContext checks left right
    proposition checks left
    proposition checks right

exact :: Monad m => RuleChecks m -> (value -> value -> m Bool)
    -> KernelSemanticsError -> value -> value -> m ()
exact checks equal failure left right = do
    matched <- equal left right
    unless matched (ruleFailure checks failure)

negationIntroductionWith
    :: Monad m => RuleChecks m -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
negationIntroductionWith checks conclude premise falsum = do
    propositionPair checks premise falsum
    case scopedCoreTerm falsum of
        CFalsum -> conclude (scopedCoreContext premise) (CNot (scopedCoreTerm premise))
        _ -> ruleFailure checks KernelExpectedFalsum

negationEliminationWith
    :: Monad m => RuleChecks m -> (CanonicalTerm global -> CanonicalTerm global -> m Bool)
    -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
negationEliminationWith checks equal conclude premise negation = do
    propositionPair checks premise negation
    case scopedCoreTerm negation of
        CNot expected -> do
            exact checks equal KernelNegationPremiseMismatch expected (scopedCoreTerm premise)
            conclude (scopedCoreContext premise) CFalsum
        _ -> ruleFailure checks KernelExpectedNegation

binaryIntroductionWith
    :: Monad m => RuleChecks m -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> (CanonicalTerm global -> CanonicalTerm global -> CanonicalTerm global)
    -> [CoreType] -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
binaryIntroductionWith checks conclude construct context left right = do
    propositionPair checks left right
    conclude context (construct (scopedCoreTerm left) (scopedCoreTerm right))

conjunctionEliminationWith
    :: Monad m => RuleChecks m -> (ScopedCheckedCore global -> m (ScopedCheckedCore global))
    -> ((ScopedCheckedCore global, ScopedCheckedCore global) -> ScopedCheckedCore global)
    -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
conjunctionEliminationWith checks retain select conjunction = do
    proposition checks conjunction
    case splitScopedConjunction conjunction of
        Just operands -> retain (select operands)
        Nothing -> ruleFailure checks KernelExpectedConjunction

disjunctionEliminationWith
    :: Monad m => RuleChecks m -> (CanonicalTerm global -> CanonicalTerm global -> m Bool)
    -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
disjunctionEliminationWith checks equal conclude disjunction left right = do
    sameContext checks disjunction left
    sameContext checks disjunction right
    proposition checks disjunction
    proposition checks left
    proposition checks right
    case scopedCoreTerm disjunction of
        COr{} -> do
            exact checks equal KernelDisjunctionBranchMismatch (scopedCoreTerm left) (scopedCoreTerm right)
            conclude (scopedCoreContext disjunction) (scopedCoreTerm left)
        _ -> ruleFailure checks KernelExpectedDisjunction

implicationEliminationWith
    :: Monad m => RuleChecks m -> (CanonicalTerm global -> CanonicalTerm global -> m Bool)
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
implicationEliminationWith checks equal implication premise = do
    propositionPair checks implication premise
    case openScopedImplication implication of
        Just (expected, conclusion) -> do
            exact checks equal KernelImplicationPremiseMismatch (scopedCoreTerm expected) (scopedCoreTerm premise)
            pure conclusion
        Nothing -> ruleFailure checks KernelExpectedImplication

forallIntroductionWith
    :: Monad m => RuleChecks m -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> CoreType -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
forallIntroductionWith checks conclude binder body = do
    proposition checks body
    outer <- case scopedCoreContext body of
        actual : context -> do
            ruleType checks binder actual (const (KernelBinderContextMismatch binder (scopedCoreContext body)))
            pure context
        [] -> ruleFailure checks (KernelBinderContextMismatch binder [])
    conclude outer (CForall binder (scopedCoreTerm body))

forallEliminationWith
    :: Monad m => RuleChecks m
    -> (ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
forallEliminationWith checks instantiate quantified argument = do
    sameContext checks quantified argument
    proposition checks quantified
    case openScopedForall quantified of
        Just (binder, body) -> do
            ruleType checks binder (scopedCoreType argument) (KernelForallArgumentTypeMismatch binder)
            instantiate argument body
        Nothing -> ruleFailure checks KernelExpectedForall

existentialIntroductionWith
    :: Monad m => RuleChecks m
    -> (ScopedCheckedCore global -> ScopedCheckedCore global -> m (CanonicalTerm global))
    -> (CanonicalTerm global -> CanonicalTerm global -> m Bool)
    -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
existentialIntroductionWith checks instantiate equal conclude body witness premise = do
    sameContext checks witness premise
    proposition checks body
    proposition checks premise
    (binder, outer) <- case scopedCoreContext body of
        actual : context -> pure (actual, context)
        [] -> ruleFailure checks (KernelBinderContextMismatch (scopedCoreType witness) [])
    ruleContext checks outer (scopedCoreContext witness)
    ruleType checks binder (scopedCoreType witness) (KernelExistentialWitnessTypeMismatch binder)
    instantiated <- instantiate witness body
    exact checks equal KernelExistentialPremiseMismatch instantiated (scopedCoreTerm premise)
    conclude outer (CExists binder (scopedCoreTerm body))

existentialEliminationWith
    :: Monad m => RuleChecks m -> (CanonicalTerm global -> m (CanonicalTerm global))
    -> (CanonicalTerm global -> CanonicalTerm global -> m Bool)
    -> ([CoreType] -> CanonicalTerm global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
existentialEliminationWith checks shift equal conclude existential result branch = do
    sameContext checks existential result
    proposition checks existential
    proposition checks result
    proposition checks branch
    case scopedCoreTerm existential of
        CExists binder _ -> do
            ruleContext checks (binder : scopedCoreContext existential) (scopedCoreContext branch)
            shifted <- shift (scopedCoreTerm result)
            exact checks equal KernelExistentialResultMismatch (scopedCoreTerm branch) shifted
            conclude (scopedCoreContext existential) (scopedCoreTerm result)
        _ -> ruleFailure checks KernelExpectedExists

falsumEliminationWith
    :: Monad m => RuleChecks m -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
falsumEliminationWith checks falsum target = do
    propositionPair checks falsum target
    case scopedCoreTerm falsum of
        CFalsum -> pure target
        _ -> ruleFailure checks KernelExpectedFalsum

equalityOperandsWith
    :: Monad m => RuleChecks m -> ScopedCheckedCore global
    -> m (CoreType, ScopedCheckedCore global, ScopedCheckedCore global)
equalityOperandsWith checks equality = do
    proposition checks equality
    maybe (ruleFailure checks KernelExpectedEquality) pure (splitScopedEquality equality)

equalityApplicationWith
    :: Monad m => RuleChecks m
    -> (CoreType -> ScopedCheckedCore global -> ScopedCheckedCore global
        -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
equalityApplicationWith checks construct functionEquality argumentEquality = do
    sameContext checks functionEquality argumentEquality
    (functionType, leftFunction, rightFunction) <- equalityOperandsWith checks functionEquality
    (argumentType, leftArgument, rightArgument) <- equalityOperandsWith checks argumentEquality
    case functionType of
        TyArrow expected result -> do
            ruleType checks expected argumentType (KernelEqualityOperandTypeMismatch expected)
            construct result leftFunction rightFunction leftArgument rightArgument
        other -> ruleFailure checks (KernelExpectedFunctionEquality other)

equalityLambdaWith
    :: Monad m => RuleChecks m
    -> (CoreType -> ScopedCheckedCore global -> m (Maybe (ScopedCheckedCore global)))
    -> (ScopedCheckedCore global -> ScopedCheckedCore global -> m (Maybe (ScopedCheckedCore global)))
    -> CoreType -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
equalityLambdaWith checks abstract equal binder equality = do
    (_, leftBody, rightBody) <- equalityOperandsWith checks equality
    let close body = abstract binder body >>= maybe
            (ruleFailure checks (KernelBinderContextMismatch binder (scopedCoreContext equality))) pure
    left <- close leftBody
    right <- close rightBody
    result <- equal left right
    maybe (ruleFailure checks (KernelCheckedCompositionFailed "lambda congruence")) pure result

equalityModusPonensWith
    :: Monad m => RuleChecks m -> (CanonicalTerm global -> CanonicalTerm global -> m Bool)
    -> (ScopedCheckedCore global -> m (ScopedCheckedCore global))
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> m (ScopedCheckedCore global)
equalityModusPonensWith checks equal retain equality premise = do
    sameContext checks equality premise
    proposition checks premise
    (operandType, left, right) <- equalityOperandsWith checks equality
    ruleType checks TyProp operandType (KernelEqualityOperandTypeMismatch TyProp)
    exact checks equal KernelEqualityPremiseMismatch (scopedCoreTerm left) (scopedCoreTerm premise)
    retain right
