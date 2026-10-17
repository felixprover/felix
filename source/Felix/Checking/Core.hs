{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ViewPatterns #-}

-- | Checked monomorphic HOL canonical syntax and its preserving operations.
module Felix.Checking.Core
    ( CoreType(..)
    , firstOrderSymbolShape
    , CoreIntrinsicTag(..)
    , coreIntrinsicType
    , CoreCheckError(..)
    , CountedCoreFailure(..)
    , CanonicalTerm(..)
    , canonicalApplicationSpine
    , canonicalConjunction
    , canonicalSetInsert
    , canonicalDefinitionEquationTarget
    , logicalSelectionType
    , logicalSelectionWitness
    , FrozenCheckedCore
    , frozenCoreType
    , frozenCoreTerm
    , frozenCoreGlobals
    , admitFrozenCheckedCore
    , eliminateFrozenVoid
    , ScopedCheckedCore
    , scopedCoreContext
    , scopedCoreType
    , scopedCoreTerm
    , admitScopedCheckedCore
    , countedAdmitScopedCheckedCore
    , eliminateScopedVoid
    , ScopedOccurrenceReplacementError(..)
    , ScopedCoreReplacement
    , replaceScopedCoreOccurrence
    , countedReplaceScopedCoreOccurrence
    , scopedCoreReplacementAbstraction
    , scopedCoreReplacementResult
    , checkScopedCanonicalCore
    , countedCoreTypeIdentity
    , countedCoreTypeListIdentity
    , CountedIdentityResult(..)
    , CoreIdentityDifference(..)
    , CoreDifferenceKind(..)
    , CoreDifferenceStep(..)
    , countedCanonicalIdentity
    , countedCanonicalOrdering
    , countedScopedLevelKey
    , compareCanonicalWith
    , canonicalClosedWith
    , countedCanonicalIdentityDetailed
    , countedScopedCoreIdentity
    , countedScopedCoreIdentityDetailed
    , countedCheckScopedCanonicalCore
    , CheckedOccurrence
    , CheckedOccurrenceView(..)
    , checkedOccurrenceView
    , checkedOccurrenceScopedCore
    , checkedOccurrenceType
    , checkedOccurrenceDependsOnBinderPrefix
    , analyseCanonicalOccurrences
    , countedAnalyseCanonicalOccurrences
    , CheckedOccurrenceAnalysisError(..)
    , countedAnalyseScopedOccurrencesUnderBinders
    , CheckedOccurrenceRebaseError(..)
    , countedRebaseCheckedOccurrence
    , embedClosedCore
    , weakenCheckedScopedCore
    , weakenCheckedScopedCoreAt
    , weakenScopedCore
    , countedWeakenScopedCore
    , countedWeakenCheckedScopedCore
    , countedAlignScopedCore
    , countedAlignScopedCoreAt
    , ScopedInstantiationError(..)
    , ScopedInstantiationResult(..)
    , instantiateScopedCore
    , countedInstantiateScopedCore
    , countedInstantiateScopedPrefix
    , scopedBound
    , applyScopedCore
    , countedApplyScopedCore
    , pointwiseBodyScopedCore
    , countedPointwiseBodyScopedCore
    , abstractScopedCore
    , countedAbstractScopedCore
    , scopedDefinition
    , scopedSetDefinition
    , scopedCharacteristicDefinition
    , scopedReplacementGraph
    , implyScopedCore
    , countedImplyScopedCore
    , equalScopedCore
    , countedEqualScopedCore
    , memberScopedCore
    , conjoinScopedCore
    , conjoinExactScopedCore
    , ScopedConjunctionError(..)
    , countedConjoinExactScopedCore
    , disjoinScopedCore
    , negateScopedCore
    , falsumScopedCore
    , splitScopedSetEquality
    , scopedSetInductionInstance
    , closeScopedForall
    , closeScopedExists
    , openScopedForall
    , openScopedExists
    , openScopedImplication
    , splitScopedEquality
    , splitScopedMembership
    , splitScopedConjunction
    , splitScopedDisjunction
    , splitScopedNegation
    , closeScopedCore
    , betaNormalizeCanonical
    , instantiateCanonical
    , instantiateCanonicalAt
    , countedInstantiateCanonical
    , countedInstantiateCanonicalPrefix
    , countedInstantiateCanonicalSlots
    , instantiateCanonicalPrefixWith
    , traverseCanonicalBindings
    , canonicalFreeIndicesWith
    , shiftCanonical, shiftCanonicalWith
    , countedShiftCanonical
    , mapCanonicalGlobals
    , canonicalTermGlobals
    , countedCanonicalGlobals
    , checkCanonicalCore
    ) where

import Base hiding (Empty)
import Felix.Checking.Core.Representation.Internal
    ( CanonicalTerm(..)
    , CoreCheckError(..)
    , CoreIntrinsicTag(..)
    , CoreType(..)
    , FrozenCheckedCore
    , ScopedCheckedCore
    , frozenCoreTerm
    , frozenCoreType
    , scopedCoreContext
    , scopedCoreTerm
    , scopedCoreType
    )
import Felix.Checking.Core.Representation.Internal qualified as Representation
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , emptyGlobalTyping
    , lookupGlobalType
    )

import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Bifunctor (first)
import Data.Functor.Identity (runIdentity)
import Data.Word (Word)
import Numeric.Natural (Natural)
import Control.Monad (foldM, unless, when)
import Control.Monad.Except qualified as Except
import Control.Monad.State.Strict qualified as State


-- Private trusted patterns keep Core's checkedness-preserving canonical
-- operations readable without exposing the wrapper constructors. Every
-- construction through these patterns delegates to the representation
-- owner's conspicuously unsafe seals.
pattern FrozenCheckedCore
    :: CoreType
    -> CanonicalTerm global
    -> FrozenCheckedCore global
pattern FrozenCheckedCore coreType term <-
    (frozenCheckedCoreView -> (coreType, term))
  where
    FrozenCheckedCore coreType term =
        Representation.unsafeSealFrozenCheckedCore coreType term

{-# COMPLETE FrozenCheckedCore #-}

frozenCheckedCoreView
    :: FrozenCheckedCore global
    -> (CoreType, CanonicalTerm global)
frozenCheckedCoreView checked =
    (frozenCoreType checked, frozenCoreTerm checked)

pattern ScopedCheckedCore
    :: [CoreType]
    -> CoreType
    -> CanonicalTerm global
    -> ScopedCheckedCore global
pattern ScopedCheckedCore context coreType term <-
    (scopedCheckedCoreView -> (context, coreType, term))
  where
    ScopedCheckedCore context coreType term =
        Representation.unsafeSealScopedCheckedCore context coreType term

{-# COMPLETE ScopedCheckedCore #-}

scopedCheckedCoreView
    :: ScopedCheckedCore global
    -> ([CoreType], CoreType, CanonicalTerm global)
scopedCheckedCoreView checked =
    ( scopedCoreContext checked
    , scopedCoreType checked
    , scopedCoreTerm checked
    )


data ScopedOccurrenceReplacementError
    = ScopedOccurrenceReplacementContextMismatch
    | ScopedOccurrenceReplacementTypeMismatch !CoreType !CoreType
    deriving stock (Show, Eq)

-- | Checked capture-safe abstraction of every exact target occurrence and
-- its direct beta contractum at one same-typed replacement.
data ScopedCoreReplacement global = ScopedCoreReplacement
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)

scopedCoreReplacementAbstraction
    :: ScopedCoreReplacement global
    -> ScopedCheckedCore global
scopedCoreReplacementAbstraction
        (ScopedCoreReplacement abstraction _result) =
    abstraction

scopedCoreReplacementResult
    :: ScopedCoreReplacement global
    -> ScopedCheckedCore global
scopedCoreReplacementResult
        (ScopedCoreReplacement _abstraction result) =
    result


-- | Replace every exact occurrence of one checked term in a checked
-- term. Checkedness is preserved by same-context, same-type
-- capture-safe substitution; unrelated subterms are left untouched.
replaceScopedCoreOccurrence
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        ScopedOccurrenceReplacementError
        (Maybe (ScopedCoreReplacement global))
replaceScopedCoreOccurrence
        (ScopedCheckedCore targetContext targetType target)
        (ScopedCheckedCore replacementContext replacementType replacement)
        (ScopedCheckedCore termContext termType term)
    | targetContext /= replacementContext
        || targetContext /= termContext =
        Left ScopedOccurrenceReplacementContextMismatch
    | targetType /= replacementType =
        Left
            (ScopedOccurrenceReplacementTypeMismatch
                targetType replacementType)
    | otherwise =
        let (found, abstracted) =
                abstractCanonicalOccurrence target 0 term
        in if found then
            Right
                (Just
                    (ScopedCoreReplacement
                        (ScopedCheckedCore
                            targetContext
                            (TyArrow targetType termType)
                            (CLam targetType abstracted))
                        (ScopedCheckedCore
                            targetContext
                            termType
                            (instantiateCanonical replacement abstracted))))
        else
            Right Nothing


-- | Counted counterpart of 'replaceScopedCoreOccurrence'. Context/type
-- comparisons, abstraction, shifted endpoint comparisons, and substitution
-- share one allowance. No partial replacement escapes on exhaustion.
countedReplaceScopedCoreOccurrence
    :: Eq global
    => Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure ScopedOccurrenceReplacementError)
            (Maybe (ScopedCoreReplacement global)), Word)
countedReplaceScopedCoreOccurrence available target replacement original =
    State.runState (Except.runExceptT action) available
  where
    step operation = do
        remaining <- State.get
        let (result, after) = operation remaining
        State.put after
        either (Except.throwError . fmap absurd) pure result
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwError CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    require failure operation = do
        valid <- step operation
        unless valid (Except.throwError (CountedCoreOperationFailed failure))
    action = do
        require ScopedOccurrenceReplacementContextMismatch (\work ->
            countedCoreTypeListIdentity work (scopedCoreContext target) (scopedCoreContext replacement))
        require ScopedOccurrenceReplacementContextMismatch (\work ->
            countedCoreTypeListIdentity work (scopedCoreContext target) (scopedCoreContext original))
        require (ScopedOccurrenceReplacementTypeMismatch (scopedCoreType target) (scopedCoreType replacement))
            (\work -> countedCoreTypeIdentity work (scopedCoreType target) (scopedCoreType replacement))
        (found, abstracted) <- abstract 0 (scopedCoreTerm target) (scopedCoreTerm original)
        if not found then pure Nothing else do
            result <- step (\work -> countedInstantiateCanonical work (scopedCoreTerm replacement) abstracted)
            charge
            let context = scopedCoreContext original
                resultType = scopedCoreType original
            pure (Just (ScopedCoreReplacement
                (ScopedCheckedCore context (TyArrow (scopedCoreType target) resultType)
                    (CLam (scopedCoreType target) abstracted))
                (ScopedCheckedCore context resultType result)))
    -- Carry the shifted endpoint down each binder once. Comparing it with a
    -- subtree must not mistake that subtree's private variable for an alias.
    abstract depth endpoint term = do
        charge
        same <- step (\work -> countedCanonicalIdentity work endpoint term)
        if same then pure (True, CBound depth) else case term of
            CBound index -> pure (False, CBound (if index < depth then index else index + 1))
            CGlobal{} -> pure (False, term)
            CIntrinsic{} -> pure (False, term)
            CLogicalSelect{} -> pure (False, term)
            COpaqueInteger{} -> pure (False, term)
            CTruth -> pure (False, term)
            CFalsum -> pure (False, term)
            CApp left right -> binary CApp left right
            CNot child -> unary CNot child
            CAnd left right -> binary CAnd left right
            COr left right -> binary COr left right
            CImp left right -> binary CImp left right
            CEq coreType left right -> binary (CEq coreType) left right
            CLam coreType child -> binder (CLam coreType) child
            CForall coreType child -> binder (CForall coreType) child
            CExists coreType child -> binder (CExists coreType) child
      where
        unary constructor child = do
            (found, result) <- abstract depth endpoint child
            pure (found, constructor result)
        binary constructor left right = do
            (leftFound, l) <- abstract depth endpoint left
            (rightFound, r) <- abstract depth endpoint right
            pure (leftFound || rightFound, constructor l r)
        binder constructor child = do
            shifted <- step (\work -> countedShiftCanonical work 1 0 endpoint)
            (found, result) <- abstract (depth + 1) shifted child
            pure (found, constructor result)

-- | Recognize a first-order symbol type, returning its set-argument arity and
-- its set- or proposition-valued result type.
firstOrderSymbolShape :: CoreType -> Maybe (Int, CoreType)
firstOrderSymbolShape =
    go 0
  where
    go arity = \case
        TyArrow TySet result ->
            go (arity + 1) result
        result@TySet ->
            Just (arity, result)
        result@TyProp ->
            Just (arity, result)
        _ ->
            Nothing


coreIntrinsicType :: CoreIntrinsicTag -> CoreType
coreIntrinsicType = \case
    Member ->
        TySet `TyArrow` (TySet `TyArrow` TyProp)
    Empty ->
        TySet
    PairSet ->
        TySet `TyArrow` (TySet `TyArrow` TySet)
    FamilyUnion ->
        TySet `TyArrow` TySet
    PowerSet ->
        TySet `TyArrow` TySet
    Sep ->
        TySet
            `TyArrow`
                ((TySet `TyArrow` TyProp) `TyArrow` TySet)
    Repl ->
        TySet
            `TyArrow`
                ((TySet `TyArrow` TySet) `TyArrow` TySet)
    UnivOf ->
        TySet `TyArrow` TySet
    ISetLfp ->
        TySet
            `TyArrow`
                ((TySet `TyArrow` TySet) `TyArrow` TySet)
    GlobalChoice ->
        TySet `TyArrow` TySet
    OrderedPair ->
        TySet `TyArrow` (TySet `TyArrow` TySet)
    FirstProjection ->
        TySet `TyArrow` TySet
    SecondProjection ->
        TySet `TyArrow` TySet


-- | Failure from a policy-free counted Core operation.  Structural and beta
-- exhaustion are distinct because proof search assigns them to different
-- public limits.  A semantic operation may additionally report its ordinary
-- domain error without losing the remaining allowances.
data CountedCoreFailure error
    = CountedCoreStructuralWorkExhausted
    | CountedCoreOperationFailed !error
    deriving stock (Show, Eq, Functor)

-- | One row of a bottom-up checked occurrence analysis.  The constructor is
-- private: consumers may inspect the already computed shallow metadata and
-- recover its original checked scope or rebase a ground row, but cannot
-- manufacture checked evidence. The original context shares the binder stack
-- used by inference; the ambient context omits the removable binder prefix.
data CheckedOccurrence global = CheckedOccurrence
    !(CanonicalTerm global)
    !CoreType
    !OccurrenceScope
    !Bool
    !(CheckedOccurrenceView global)

-- Shared by every occurrence in one lexical scope. Entering a binder creates
-- one new scope and shares both context tails with its parent.
data OccurrenceScope = OccurrenceScope
    ![CoreType] -- Original lexical context.
    ![CoreType] -- Ambient context after removing the binder prefix.
    !Natural

type role CheckedOccurrence nominal

-- | The exact constructor and already checked immediate children of one
-- occurrence.  Constructor identity and child roles are exposed together so
-- clients cannot observe or repair an impossible disagreement between them.
data CheckedOccurrenceView global
    = OccurrenceBound !Natural
    | OccurrenceGlobal !global
    | OccurrenceIntrinsic !CoreIntrinsicTag
    | OccurrenceLogicalSelect !CoreType
    | OccurrenceOpaqueInteger !Integer
    | OccurrenceApplication
        !(CheckedOccurrence global)
        !(CheckedOccurrence global)
    | OccurrenceLambda !CoreType !(CheckedOccurrence global)
    | OccurrenceFalsum
    | OccurrenceTruth
    | OccurrenceNegation !(CheckedOccurrence global)
    | OccurrenceConjunction
        !(CheckedOccurrence global)
        !(CheckedOccurrence global)
    | OccurrenceDisjunction
        !(CheckedOccurrence global)
        !(CheckedOccurrence global)
    | OccurrenceImplication
        !(CheckedOccurrence global)
        !(CheckedOccurrence global)
    | OccurrenceEquality
        !CoreType
        !(CheckedOccurrence global)
        !(CheckedOccurrence global)
    | OccurrenceUniversal !CoreType !(CheckedOccurrence global)
    | OccurrenceExistential !CoreType !(CheckedOccurrence global)

type role CheckedOccurrenceView nominal

checkedOccurrenceView
    :: CheckedOccurrence global
    -> CheckedOccurrenceView global
checkedOccurrenceView
        (CheckedOccurrence _term _type _scope _depends view) =
    view

-- | Preserve the exact term, inferred type and full lexical context of one
-- occurrence. Unlike rebasing, this projection retains surrounding binders even
-- when the occurrence does not depend on them; it performs no inference.
checkedOccurrenceScopedCore
    :: CheckedOccurrence global
    -> ScopedCheckedCore global
checkedOccurrenceScopedCore
        (CheckedOccurrence term coreType
            (OccurrenceScope context _ambient _depth) _depends _view) =
    ScopedCheckedCore context coreType term

checkedOccurrenceType :: CheckedOccurrence global -> CoreType
checkedOccurrenceType
        (CheckedOccurrence _term coreType _scope _depends _view) =
    coreType

checkedOccurrenceDependsOnBinderPrefix
    :: CheckedOccurrence global
    -> Bool
checkedOccurrenceDependsOnBinderPrefix
        (CheckedOccurrence _term _type _scope depends _view) =
    depends

data CheckedOccurrenceRebaseError
    = CheckedOccurrenceRebaseInvariant
    deriving stock (Show, Eq)

-- | Failure while relating a checked occurrence tree to an already checked
-- logical-binder scope. The binder depth is supplied by the owner of that
-- scope; exceeding the checked context is therefore an internal invariant
-- failure rather than ordinary ill-typed user syntax.
data CheckedOccurrenceAnalysisError
    = CheckedOccurrenceBinderDepthOutOfScope
    | CheckedOccurrenceAnalysisCheckFailed !CoreCheckError
    | CheckedOccurrenceRootTypeMismatch !CoreType !CoreType
    deriving stock (Show, Eq)


-- | Split a canonical application into its head and arguments in application
-- order.
canonicalApplicationSpine
    :: CanonicalTerm global
    -> (CanonicalTerm global, [CanonicalTerm global])
canonicalApplicationSpine =
    go []
  where
    go arguments = \case
        CApp function argument ->
            go (argument : arguments) function
        headTerm ->
            (headTerm, arguments)

-- | Build a right-associated conjunction in input order, omitting logical
-- truth operands.
canonicalConjunction
    :: Foldable collection
    => collection (CanonicalTerm global)
    -> CanonicalTerm global
canonicalConjunction =
    foldr combine CTruth
  where
    combine CTruth remaining = remaining
    combine proposition CTruth = proposition
    combine proposition remaining = CAnd proposition remaining

-- | The fixed checked-core interpretation of set insertion.
--
-- Finite-set notation uses this intrinsic HOTG adjunction directly.  The
-- ordinary source-owned @cons@ function is not consulted during lowering.
canonicalSetInsert
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
canonicalSetInsert element set =
    CApp
        (CIntrinsic FamilyUnion)
        (CApp
            (CApp
                (CIntrinsic PairSet)
                (CApp
                    (CApp
                        (CIntrinsic PairSet)
                        element)
                    element))
            set)

-- | The canonical equation exposed for a transparent definition.  Ordinary
-- first-order symbols are presented pointwise; definitions with a
-- higher-order argument retain their exact object equation.
canonicalDefinitionEquationTarget
    :: global
    -> CoreType
    -> CanonicalTerm global
    -> CanonicalTerm global
canonicalDefinitionEquationTarget identity coreType body =
    fromMaybe exact
        (firstOrderDefinitionTarget identity coreType body)
  where
    exact = CEq coreType (CGlobal identity) body

    firstOrderDefinitionTarget object objectType objectBody = do
        (arity, resultType) <- firstOrderSymbolShape objectType
        let arguments =
                CBound
                    <$> reverse
                        (take arity [0 ..])
            left = foldl' CApp (CGlobal object) arguments
            right = foldl' applyArgument objectBody arguments
            equation = CEq resultType left right
        pure
            (foldr CForall equation
                (replicate arity TySet))

    applyArgument function argument =
        case function of
            CLam TySet lambdaBody ->
                instantiateCanonical argument lambdaBody
            _ ->
                CApp function argument

-- | The monomorphic logical-selection operator at one concrete type.
logicalSelectionType :: CoreType -> CoreType
logicalSelectionType coreType =
    (coreType `TyArrow` TyProp) `TyArrow` coreType

-- | The checked witness principle supplied by the selection-augmented
-- logical calculus.  It is not a set-theoretic foundation axiom.
logicalSelectionWitness :: CoreType -> FrozenCheckedCore Void
logicalSelectionWitness coreType =
    case checkCanonicalCore emptyGlobalTyping witness of
        Right checked -> checked
        Left failure ->
            impossible
                ("invalid logical-selection witness: " <> show failure)
  where
    predicateType = coreType `TyArrow` TyProp
    predicate = CBound 1
    witness =
        CForall predicateType
            (CForall coreType
                (CImp
                    (CApp predicate (CBound 0))
                    (CApp
                        predicate
                        (CApp
                            (CLogicalSelect coreType)
                            predicate))))

-- | Collect references under the caller's structural allowance. Repeated
-- references still charge their visits; type annotations contain no globals.
countedCanonicalGlobals
    :: Ord global => Word -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) (Set.Set global), Word)
countedCanonicalGlobals allowance root =
    State.runState (Except.runExceptT (go root)) allowance
  where
    go term = do
        remaining <- State.get
        case consumeCoreStructuralWork remaining of
            Left failure -> Except.throwError failure
            Right after -> State.put after
        case term of
            CGlobal global -> pure (Set.singleton global)
            CApp left right -> both left right
            CLam _ body -> go body
            CNot body -> go body
            CAnd left right -> both left right
            COr left right -> both left right
            CImp left right -> both left right
            CEq _ left right -> both left right
            CForall _ body -> go body
            CExists _ body -> go body
            CBound{} -> pure Set.empty
            CIntrinsic{} -> pure Set.empty
            CLogicalSelect{} -> pure Set.empty
            COpaqueInteger{} -> pure Set.empty
            CFalsum -> pure Set.empty
            CTruth -> pure Set.empty
    both left right = (<>) <$> go left <*> go right

-- | Eliminate an impossible global namespace without changing checked
-- evidence.  This is the only cross-namespace transport supported for a
-- checked closed term.
eliminateFrozenVoid
    :: FrozenCheckedCore Void
    -> FrozenCheckedCore global
eliminateFrozenVoid (FrozenCheckedCore coreType term) =
    FrozenCheckedCore
        coreType
        (mapCanonicalGlobals absurd term)

frozenCoreGlobals
    :: Ord global
    => FrozenCheckedCore global
    -> Set.Set global
frozenCoreGlobals =
    canonicalTermGlobals . frozenCoreTerm

-- | Admit an already checked closed term into another visible snapshot of the
-- same nominal universe.  The universe owner guarantees that a shared global
-- identity has one stable type, so admission need only establish visibility.
admitFrozenCheckedCore
    :: Ord global
    => GlobalTyping global
    -> FrozenCheckedCore global
    -> Either CoreCheckError (FrozenCheckedCore global)
admitFrozenCheckedCore globalTyping checked
    | all visible (frozenCoreGlobals checked) = Right checked
    | otherwise = Left UnknownCoreGlobal
  where
    visible global = isJust (lookupGlobalType globalTyping global)

canonicalTermGlobals
    :: Ord global
    => CanonicalTerm global
    -> Set.Set global
canonicalTermGlobals = \case
    CBound{} ->
        mempty
    CGlobal global ->
        Set.singleton global
    CIntrinsic{} ->
        mempty
    CLogicalSelect{} ->
        mempty
    COpaqueInteger{} ->
        mempty
    CApp function argument ->
        canonicalTermGlobals function
            <> canonicalTermGlobals argument
    CLam _binderType body ->
        canonicalTermGlobals body
    CFalsum ->
        mempty
    CTruth ->
        mempty
    CNot proposition ->
        canonicalTermGlobals proposition
    CAnd left right ->
        canonicalTermGlobals left
            <> canonicalTermGlobals right
    COr left right ->
        canonicalTermGlobals left
            <> canonicalTermGlobals right
    CImp premise conclusion ->
        canonicalTermGlobals premise
            <> canonicalTermGlobals conclusion
    CEq _operandType left right ->
        canonicalTermGlobals left
            <> canonicalTermGlobals right
    CForall _binderType body ->
        canonicalTermGlobals body
    CExists _binderType body ->
        canonicalTermGlobals body

-- | Eliminate an impossible global namespace without changing checked
-- evidence.  This is the only cross-namespace transport supported for a
-- checked scoped term.
eliminateScopedVoid
    :: ScopedCheckedCore Void
    -> ScopedCheckedCore global
eliminateScopedVoid (ScopedCheckedCore context coreType term) =
    ScopedCheckedCore
        context
        coreType
        (mapCanonicalGlobals absurd term)

-- | Admit an already checked scoped term into another visible snapshot of the
-- same nominal universe.  Local binders are unaffected; every global
-- reference must be visible in the destination snapshot.
admitScopedCheckedCore
    :: Ord global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> Either CoreCheckError (ScopedCheckedCore global)
admitScopedCheckedCore globalTyping checked
    | all visible (canonicalTermGlobals (scopedCoreTerm checked)) =
        Right checked
    | otherwise = Left UnknownCoreGlobal
  where
    visible global = isJust (lookupGlobalType globalTyping global)

-- | Admit checked scoped evidence while charging one unit for every visited
-- canonical constructor.  This operation checks visibility only: the checked
-- wrapper already owns its context and type evidence.
countedAdmitScopedCheckedCore
    :: GlobalTyping global
    -> Word
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure CoreCheckError)
            (ScopedCheckedCore global)
       , Word
       )
countedAdmitScopedCheckedCore globalTyping remaining checked =
    case visit remaining (scopedCoreTerm checked) of
        (Left failure, remaining') ->
            (Left failure, remaining')
        (Right (), remaining') ->
            (Right checked, remaining')
  where
    visit available term =
        case consumeCoreStructuralWork available of
            Left failure ->
                (Left failure, 0)
            Right afterNode ->
                case term of
                    CBound{} ->
                        complete afterNode
                    CGlobal global
                        | isJust (lookupGlobalType globalTyping global) ->
                            complete afterNode
                        | otherwise ->
                            ( Left
                                (CountedCoreOperationFailed
                                    UnknownCoreGlobal)
                            , afterNode
                            )
                    CIntrinsic{} ->
                        complete afterNode
                    CLogicalSelect{} ->
                        complete afterNode
                    COpaqueInteger{} ->
                        complete afterNode
                    CApp function argument ->
                        visitBinary afterNode function argument
                    CLam _binderType body ->
                        visit afterNode body
                    CFalsum ->
                        complete afterNode
                    CTruth ->
                        complete afterNode
                    CNot proposition ->
                        visit afterNode proposition
                    CAnd left right ->
                        visitBinary afterNode left right
                    COr left right ->
                        visitBinary afterNode left right
                    CImp premise conclusion ->
                        visitBinary afterNode premise conclusion
                    CEq _operandType left right ->
                        visitBinary afterNode left right
                    CForall _binderType body ->
                        visit afterNode body
                    CExists _binderType body ->
                        visit afterNode body

    visitBinary available left right =
        case visit available left of
            (Left failure, afterLeft) ->
                (Left failure, afterLeft)
            (Right (), afterLeft) ->
                visit afterLeft right

    complete available =
        (Right (), available)

-- | Infer in the supplied context while retaining that exact context and raw
-- term. No normalization or substitution occurs. Successful inference checks
-- every child and every global, including syntax that reduction could discard.
checkScopedCanonicalCore
    :: GlobalTyping global
    -> [CoreType]
    -> CanonicalTerm global
    -> Either CoreCheckError (ScopedCheckedCore global)
checkScopedCanonicalCore globalTyping context term =
    ScopedCheckedCore context
        <$> inferCanonicalCore
            (lookupGlobalType globalTyping)
            context
            term
        <*> pure term

-- | Compare checked types under explicit structural work.  One unit is
-- charged before inspecting each pair of type constructors.
countedCoreTypeIdentity
    :: Word
    -> CoreType
    -> CoreType
    -> (Either (CountedCoreFailure Void) Bool, Word)
countedCoreTypeIdentity =
    go
  where
    go remaining left right =
        case consumeCoreStructuralWork remaining of
            Left failure -> (Left failure, remaining)
            Right afterNode ->
                case (left, right) of
                    (TyProp, TyProp) ->
                        (Right True, afterNode)
                    (TySet, TySet) ->
                        (Right True, afterNode)
                    (TyArrow leftDomain leftCodomain,
                     TyArrow rightDomain rightCodomain) ->
                        case go afterNode leftDomain rightDomain of
                            (Left failure, afterDomain) ->
                                (Left failure, afterDomain)
                            (Right False, afterDomain) ->
                                (Right False, afterDomain)
                            (Right True, afterDomain) ->
                                go afterDomain leftCodomain rightCodomain
                    _ ->
                        (Right False, afterNode)

-- | Compare nearest-first checked contexts.  Each shared list row and every
-- recursive type constructor consumes structural work.
countedCoreTypeListIdentity
    :: Word
    -> [CoreType]
    -> [CoreType]
    -> (Either (CountedCoreFailure Void) Bool, Word)
countedCoreTypeListIdentity =
    go
  where
    go remaining [] [] =
        (Right True, remaining)
    go remaining (left : leftRest) (right : rightRest) =
        case consumeCoreStructuralWork remaining of
            Left failure -> (Left failure, remaining)
            Right afterRow ->
                case countedCoreTypeIdentity afterRow left right of
                    (Left failure, afterType) ->
                        (Left failure, afterType)
                    (Right False, afterType) ->
                        (Right False, afterType)
                    (Right True, afterType) ->
                        go afterType leftRest rightRest
    go remaining _left _right =
        (Right False, remaining)

data CountedIdentityResult
    = CountedIdentical
    | CountedDifferent !CoreIdentityDifference
    deriving stock (Show, Eq)

data CoreIdentityDifference = CoreIdentityDifference
    !CoreDifferenceKind
    ![CoreDifferenceStep]
    !Bool
    deriving stock (Show, Eq)

data CoreDifferenceKind
    = CoreConstructorDifference
    | CoreAtomDifference
    | CoreTypeDifference
    deriving stock (Show, Eq, Ord)

data CoreDifferenceStep
    = CoreFirstChild
    | CoreSecondChild
    | CoreBodyChild
    deriving stock (Show, Eq, Ord)

coreDifferencePathLimit :: Int
coreDifferencePathLimit = 12

data IdentityResultMode result where
    BooleanIdentityResult :: IdentityResultMode Bool
    DetailedIdentityResult :: IdentityResultMode CountedIdentityResult

-- | Exact structural identity without the uncounted derived-'Eq' shortcut.
-- One worker owns both the semantic-only and bounded-difference modes.
-- Entering one checked Core-node pair consumes one structural unit. Stored
-- type payloads use the counted type comparison above.
countedCanonicalIdentity
    :: Eq global
    => Word
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) Bool, Word)
countedCanonicalIdentity =
    countedCanonicalIdentityWith BooleanIdentityResult
{-# INLINE countedCanonicalIdentity #-}

-- | Lexicographic ordering matching the derived 'Ord' instance. Charge before
-- each term/type pair and stop at the first difference. Atomic identifiers and
-- integers have the same unit-cost convention as counted identity.
countedCanonicalOrdering
    :: Ord global => Word -> CanonicalTerm global -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) Ordering, Word)
countedCanonicalOrdering allowance left right =
    State.runState (Except.runExceptT (compareCanonicalWith charge left right)) allowance
  where
    charge = do
        remaining <- State.get
        case consumeCoreStructuralWork remaining of
            Left failure -> Except.throwError failure
            Right after -> State.put after

-- | The same structural comparison under a caller-owned aborting account.
-- Interning can share its account with surrounding preparation and lookup;
-- no fresh allowance is assigned to a large closed mathematical value.
compareCanonicalWith
    :: (Monad m, Ord global) => m () -> CanonicalTerm global -> CanonicalTerm global -> m Ordering
compareCanonicalWith charge = term
  where
    thenCompare action next = action >>= \case
        EQ -> next
        difference -> pure difference
    coreType lhs rhs = do
        charge
        case (lhs, rhs) of
            (TyArrow a b, TyArrow c d) -> thenCompare (coreType a c) (coreType b d)
            _ -> pure (compare (typeTag lhs) (typeTag rhs))
    typeTag :: CoreType -> Int
    typeTag = \case
        TyProp -> 0
        TySet -> 1
        TyArrow{} -> 2
    term lhs rhs = do
        charge
        case (lhs, rhs) of
            (CBound a, CBound b) -> pure (compare a b)
            (CGlobal a, CGlobal b) -> pure (compare a b)
            (CIntrinsic a, CIntrinsic b) -> pure (compare a b)
            (CLogicalSelect a, CLogicalSelect b) -> coreType a b
            (COpaqueInteger a, COpaqueInteger b) -> pure (compare a b)
            (CApp a b, CApp c d) -> pair a b c d
            (CLam a b, CLam c d) -> typed a b c d
            (CFalsum, CFalsum) -> pure EQ
            (CTruth, CTruth) -> pure EQ
            (CNot a, CNot b) -> term a b
            (CAnd a b, CAnd c d) -> pair a b c d
            (COr a b, COr c d) -> pair a b c d
            (CImp a b, CImp c d) -> pair a b c d
            (CEq a b c, CEq d e f) -> thenCompare (coreType a d) (pair b c e f)
            (CForall a b, CForall c d) -> typed a b c d
            (CExists a b, CExists c d) -> typed a b c d
            _ -> pure (compare (tag lhs) (tag rhs))
    pair a b c d = thenCompare (term a c) (term b d)
    typed a b c d = thenCompare (coreType a c) (term b d)
    -- Constructor declaration order, not cache wire codes.
    tag :: CanonicalTerm global -> Int
    tag = \case
        CBound{} -> 0
        CGlobal{} -> 1
        CIntrinsic{} -> 2
        CLogicalSelect{} -> 3
        COpaqueInteger{} -> 4
        CApp{} -> 5
        CLam{} -> 6
        CFalsum -> 7
        CTruth -> 8
        CNot{} -> 9
        CAnd{} -> 10
        COr{} -> 11
        CImp{} -> 12
        CEq{} -> 13
        CForall{} -> 14
        CExists{} -> 15

-- | Closedness concerns free de Bruijn indices, not the absence of binders.
-- In particular an internal comprehension binder is allowed, and unused
-- surrounding source binders do not change a closed term's identity.
canonicalClosedWith :: Monad m => m () -> CanonicalTerm global -> m Bool
canonicalClosedWith charge = visit 0
  where
    visit depth value = do
        charge
        case value of
            CBound index -> pure (index < depth)
            CApp left right -> both depth left right
            CLam _ body -> visit (depth + 1) body
            CNot body -> visit depth body
            CAnd left right -> both depth left right
            COr left right -> both depth left right
            CImp left right -> both depth left right
            CEq _ left right -> both depth left right
            CForall _ body -> visit (depth + 1) body
            CExists _ body -> visit (depth + 1) body
            _ -> pure True
    both depth left right = do
        closed <- visit depth left
        if closed then visit depth right else pure False

countedCanonicalIdentityDetailed
    :: Eq global
    => Word
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) CountedIdentityResult, Word)
countedCanonicalIdentityDetailed =
    countedCanonicalIdentityWith DetailedIdentityResult
{-# INLINE countedCanonicalIdentityDetailed #-}

countedCanonicalIdentityWith
    :: Eq global
    => IdentityResultMode result
    -> Word
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) result, Word)
countedCanonicalIdentityWith mode =
    go
  where
    go remaining left right =
        case consumeCoreStructuralWork remaining of
            Left failure -> (Left failure, remaining)
            Right afterNode ->
                compareNode afterNode left right

    compareNode remaining left right =
        case (left, right) of
            (CBound leftIndex, CBound rightIndex) ->
                atomicIdentity (leftIndex == rightIndex) remaining
            (CGlobal leftGlobal, CGlobal rightGlobal) ->
                atomicIdentity (leftGlobal == rightGlobal) remaining
            (CIntrinsic leftIntrinsic, CIntrinsic rightIntrinsic) ->
                atomicIdentity (leftIntrinsic == rightIntrinsic) remaining
            (CLogicalSelect leftType, CLogicalSelect rightType) ->
                typeIdentity remaining leftType rightType
            (COpaqueInteger leftInteger, COpaqueInteger rightInteger) ->
                atomicIdentity (leftInteger == rightInteger) remaining
            (CApp leftFunction leftArgument,
             CApp rightFunction rightArgument) ->
                comparePair remaining
                    leftFunction rightFunction
                    leftArgument rightArgument
            (CLam leftType leftBody, CLam rightType rightBody) ->
                compareTypedBody remaining
                    leftType rightType leftBody rightBody
            (CFalsum, CFalsum) ->
                (Right (identicalResult mode), remaining)
            (CTruth, CTruth) ->
                (Right (identicalResult mode), remaining)
            (CNot leftProposition, CNot rightProposition) ->
                atStep CoreBodyChild
                    (go remaining leftProposition rightProposition)
            (CAnd leftFirst leftSecond,
             CAnd rightFirst rightSecond) ->
                comparePair remaining
                    leftFirst rightFirst leftSecond rightSecond
            (COr leftFirst leftSecond,
             COr rightFirst rightSecond) ->
                comparePair remaining
                    leftFirst rightFirst leftSecond rightSecond
            (CImp leftFirst leftSecond,
             CImp rightFirst rightSecond) ->
                comparePair remaining
                    leftFirst rightFirst leftSecond rightSecond
            (CEq leftType leftFirst leftSecond,
             CEq rightType rightFirst rightSecond) ->
                case countedCoreTypeIdentity remaining leftType rightType of
                    (Left failure, afterType) ->
                        (Left failure, afterType)
                    (Right False, afterType) ->
                        (Right (differentResult mode CoreTypeDifference), afterType)
                    (Right True, afterType) ->
                        comparePair afterType
                            leftFirst rightFirst leftSecond rightSecond
            (CForall leftType leftBody, CForall rightType rightBody) ->
                compareTypedBody remaining
                    leftType rightType leftBody rightBody
            (CExists leftType leftBody, CExists rightType rightBody) ->
                compareTypedBody remaining
                    leftType rightType leftBody rightBody
            _ ->
                ( Right
                    (differentResult mode CoreConstructorDifference)
                , remaining
                )

    compareTypedBody remaining leftType rightType leftBody rightBody =
        case countedCoreTypeIdentity remaining leftType rightType of
            (Left failure, afterType) ->
                (Left failure, afterType)
            (Right False, afterType) ->
                (Right (differentResult mode CoreTypeDifference), afterType)
            (Right True, afterType) ->
                atStep CoreBodyChild (go afterType leftBody rightBody)

    comparePair remaining
            leftFirst rightFirst leftSecond rightSecond =
        case go remaining leftFirst rightFirst of
            (Left failure, afterFirst) ->
                (Left failure, afterFirst)
            (Right result, afterFirst)
                | identityResultMatches mode result ->
                    atStep CoreSecondChild
                        (go afterFirst leftSecond rightSecond)
                | otherwise ->
                    ( Right
                        (prependDifference mode CoreFirstChild result)
                    , afterFirst
                    )

    atomicIdentity matches remaining =
        ( Right
            (if matches
                then identicalResult mode
                else differentResult mode CoreAtomDifference)
        , remaining
        )

    typeIdentity remaining left right =
        case countedCoreTypeIdentity remaining left right of
            (Left failure, after) -> (Left failure, after)
            (Right True, after) -> (Right (identicalResult mode), after)
            (Right False, after) ->
                (Right (differentResult mode CoreTypeDifference), after)

    atStep step (Right result, remaining) =
        (Right (prependDifference mode step result), remaining)
    atStep _step (Left failure, remaining) =
        (Left failure, remaining)
{-# INLINE countedCanonicalIdentityWith #-}

identicalResult :: IdentityResultMode result -> result
identicalResult BooleanIdentityResult = True
identicalResult DetailedIdentityResult = CountedIdentical

differentResult
    :: IdentityResultMode result
    -> CoreDifferenceKind
    -> result
differentResult BooleanIdentityResult _kind = False
differentResult DetailedIdentityResult kind =
    CountedDifferent (CoreIdentityDifference kind [] False)

prependDifference
    :: IdentityResultMode result
    -> CoreDifferenceStep
    -> result
    -> result
prependDifference BooleanIdentityResult _step result = result
prependDifference DetailedIdentityResult _step CountedIdentical =
    CountedIdentical
prependDifference DetailedIdentityResult step (CountedDifferent difference) =
    CountedDifferent (prependCoreDifference step difference)

prependCoreDifference
    :: CoreDifferenceStep
    -> CoreIdentityDifference
    -> CoreIdentityDifference
prependCoreDifference step (CoreIdentityDifference kind path truncated)
    | length path < coreDifferencePathLimit =
        CoreIdentityDifference kind (step : path) truncated
    | otherwise =
        CoreIdentityDifference kind path True

identityResultMatches :: IdentityResultMode result -> result -> Bool
identityResultMatches BooleanIdentityResult = id
identityResultMatches DetailedIdentityResult = \case
    CountedIdentical -> True
    CountedDifferent{} -> False

-- | Exact identity for a complete checked scoped value.  The wrapper itself
-- is fixed metadata; its context rows, type, and term are all counted.
countedScopedCoreIdentity
    :: Eq global
    => Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) Bool, Word)
countedScopedCoreIdentity =
    countedScopedCoreIdentityWith BooleanIdentityResult
{-# INLINE countedScopedCoreIdentity #-}

countedScopedCoreIdentityDetailed
    :: Eq global
    => Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) CountedIdentityResult, Word)
countedScopedCoreIdentityDetailed =
    countedScopedCoreIdentityWith DetailedIdentityResult
{-# INLINE countedScopedCoreIdentityDetailed #-}

countedScopedCoreIdentityWith
    :: Eq global
    => IdentityResultMode result
    -> Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) result, Word)
countedScopedCoreIdentityWith mode remaining left right =
    case countedCoreTypeListIdentity remaining
            (scopedCoreContext left) (scopedCoreContext right) of
        (Left failure, afterContext) ->
            (Left failure, afterContext)
        (Right False, afterContext) ->
            (Right (differentResult mode CoreTypeDifference), afterContext)
        (Right True, afterContext) ->
            case countedCoreTypeIdentity afterContext
                    (scopedCoreType left) (scopedCoreType right) of
                (Left failure, afterType) ->
                    (Left failure, afterType)
                (Right False, afterType) ->
                    (Right (differentResult mode CoreTypeDifference), afterType)
                (Right True, afterType) ->
                    countedCanonicalIdentityWith mode afterType
                        (scopedCoreTerm left) (scopedCoreTerm right)
{-# INLINE countedScopedCoreIdentityWith #-}

-- | Recheck a canonical term while charging every visited term constructor,
-- context row, and compared type constructor.  The original uncounted entry
-- point remains available to non-search callers.
countedCheckScopedCanonicalCore
    :: GlobalTyping global
    -> Word
    -> [CoreType]
    -> CanonicalTerm global
    -> ( Either
            (CountedCoreFailure CoreCheckError)
            (ScopedCheckedCore global)
       , Word
       )
countedCheckScopedCanonicalCore globalTyping remaining context term =
    case inferCanonicalCoreCounted
            (lookupGlobalType globalTyping)
            remaining
            context
            term of
        (Left failure, remaining') ->
            (Left failure, remaining')
        (Right coreType, remaining') ->
            (Right (ScopedCheckedCore context coreType term), remaining')

-- | Regard a closed term under a larger lexical context. Closed canonical
-- terms contain no indices, so this does not shift the term.
embedClosedCore
    :: [CoreType]
    -> FrozenCheckedCore global
    -> ScopedCheckedCore global
embedClosedCore context
        (FrozenCheckedCore coreType term) =
    ScopedCheckedCore context coreType term

-- | Add one nearest binder to an already checked lexical context.
weakenCheckedScopedCore
    :: CoreType
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
weakenCheckedScopedCore binderType scoped =
    ScopedCheckedCore
        (binderType : scopedCoreContext scoped)
        (scopedCoreType scoped)
        (shiftCanonical 1 0 (scopedCoreTerm scoped))

-- | Insert one checked binder at a specified depth in the nearest-first
-- lexical context.  This is a structural same-universe operation: shifting
-- bound indices cannot change any established global typing evidence.
weakenCheckedScopedCoreAt
    :: Natural
    -> CoreType
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
weakenCheckedScopedCoreAt depth binderType scoped = do
    let context = scopedCoreContext scoped
    guard (depth <= fromIntegral (length context))
    let boundedDepth = fromIntegral depth
        (inner, outer) = splitAt boundedDepth context
    pure
        (ScopedCheckedCore
            (inner <> (binderType : outer))
            (scopedCoreType scoped)
            (shiftCanonical 1 depth (scopedCoreTerm scoped)))

-- | Add one nearest binder to a checked lexical context.
weakenScopedCore
    :: GlobalTyping global
    -> CoreType
    -> ScopedCheckedCore global
    -> Either CoreCheckError (ScopedCheckedCore global)
weakenScopedCore globalType binderType scoped =
    checkScopedCanonicalCore
        globalType
        (binderType : scopedCoreContext scoped)
        (shiftCanonical 1 0
            (scopedCoreTerm scoped))

-- | Counted counterpart of 'weakenScopedCore'.  Shifting and checked recovery
-- share one structural allowance and no partially weakened value is returned
-- when either traversal exhausts it.
countedWeakenScopedCore
    :: GlobalTyping global
    -> Word
    -> CoreType
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure CoreCheckError)
            (ScopedCheckedCore global)
       , Word
       )
countedWeakenScopedCore globalType remaining binderType scoped =
    case countedShiftCanonical
            remaining 1 0 (scopedCoreTerm scoped) of
        (Left failure, afterShift) ->
            (Left (absurd <$> failure), afterShift)
        (Right shifted, afterShift) ->
            countedCheckScopedCanonicalCore
                globalType
                afterShift
                (binderType : scopedCoreContext scoped)
                shifted

-- | Shift a checked term under one binder, retaining its established type.
-- This same-universe operation makes no destination visibility claim.
countedWeakenCheckedScopedCore
    :: Word
    -> CoreType
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (ScopedCheckedCore global), Word)
countedWeakenCheckedScopedCore remaining binderType scoped =
    case countedShiftCanonical remaining 1 0 (scopedCoreTerm scoped) of
        (result, afterShift) ->
            ( ScopedCheckedCore
                (binderType : scopedCoreContext scoped)
                (scopedCoreType scoped)
                <$> result
            , afterShift
            )

-- | Align a checked term to an exact context extension. Validate the suffix
-- under the same account, then shift once by the complete new prefix. Nothing
-- denotes an incompatible scope; exhaustion never publishes a partial shift.
countedAlignScopedCore
    :: Word -> [CoreType] -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedAlignScopedCore allowance = countedAlignScopedCoreAt allowance 0

-- | Extend the ambient context while retaining a local binder prefix.
countedAlignScopedCoreAt
    :: Word -> Natural -> [CoreType] -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedAlignScopedCoreAt allowance depth target scoped =
    State.runState (Except.runExceptT action) allowance
  where
    charge = do
        remaining <- State.get
        case consumeCoreStructuralWork remaining of
            Left failure -> Except.throwError failure
            Right after -> State.put after
    step operation = do
        remaining <- State.get
        let (result, after) = operation remaining
        State.put after
        either Except.throwError pure result
    size = foldM (\count _ -> charge >> pure (count + 1 :: Natural)) 0
    suffix 0 context = pure context
    suffix count (_ : rest) = charge >> suffix (count - 1) rest
    suffix _ [] = impossible "a measured context prefix exceeds its list"
    action = do
        targetSize <- size target
        sourceSize <- size (scopedCoreContext scoped)
        if targetSize < sourceSize || depth > sourceSize then pure Nothing else do
            let difference = targetSize - sourceSize
            afterPrefix <- suffix depth target
            ambient <- suffix difference afterPrefix
            let original = take (fromIntegral depth) target <> ambient
            matches <- step (\work -> countedCoreTypeListIdentity work original (scopedCoreContext scoped))
            if not matches then pure Nothing
            else if difference == 0 then pure (Just scoped)
            else do
                shifted <- step (\work -> countedShiftCanonical work difference depth (scopedCoreTerm scoped))
                pure (Just (ScopedCheckedCore target (scopedCoreType scoped) shifted))

data ScopedInstantiationError
    = ScopedInstantiationPrefixTooLong !Natural !Natural
    | ScopedInstantiationContextMismatch !Natural ![CoreType] ![CoreType]
    | ScopedInstantiationTypeMismatch !Natural !CoreType !CoreType
    deriving stock (Show, Eq)

-- | Missing assignments expose only their source-order slots, never a
-- partially instantiated checked term.
data ScopedInstantiationResult global
    = ScopedInstantiationOpen !(Set Natural)
    | ScopedInstantiationClosed !(ScopedCheckedCore global)
    deriving stock (Show, Eq)

type role ScopedInstantiationResult nominal

-- | Eliminate the nearest binder using an already checked ambient argument.
-- Typing is preserved; callers own admission before discarding unused syntax.
instantiateScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either ScopedInstantiationError (ScopedCheckedCore global)
instantiateScopedCore argument body =
    case scopedCoreContext body of
        [] -> Left (ScopedInstantiationPrefixTooLong 1 0)
        binderType : ambient
            | scopedCoreContext argument /= ambient ->
                Left (ScopedInstantiationContextMismatch
                    0 ambient (scopedCoreContext argument))
            | scopedCoreType argument /= binderType ->
                Left (ScopedInstantiationTypeMismatch
                    0 binderType (scopedCoreType argument))
            | otherwise ->
                Right (ScopedCheckedCore ambient (scopedCoreType body)
                    (instantiateCanonical
                        (scopedCoreTerm argument) (scopedCoreTerm body)))

-- | Complete counted instantiation: unlike a partial prefix assignment this
-- operation cannot leave an unresolved slot. No result inference is repeated.
countedInstantiateScopedCore
    :: Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure ScopedInstantiationError)
            (ScopedCheckedCore global), Word)
countedInstantiateScopedCore remaining argument body =
    case consumeCoreStructuralWork remaining of
        Left failure -> (Left failure, remaining)
        Right afterEntry ->
            case scopedCoreContext body of
                [] ->
                    ( Left (CountedCoreOperationFailed
                        (ScopedInstantiationPrefixTooLong 1 0))
                    , afterEntry
                    )
                binderType : ambient ->
                    case countedValidateScopedReplacement
                            afterEntry 0 binderType ambient argument of
                        (Left failure, afterValidation) ->
                            (Left failure, afterValidation)
                        (Right (), afterValidation) ->
                            case countedInstantiateCanonical afterValidation
                                    (scopedCoreTerm argument) (scopedCoreTerm body) of
                                (result, afterSubstitution) ->
                                    ( first (fmap absurd)
                                        (ScopedCheckedCore ambient
                                            (scopedCoreType body) <$> result)
                                    , afterSubstitution
                                    )

countedValidateScopedReplacement
    :: Word
    -> Natural
    -> CoreType
    -> [CoreType]
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure ScopedInstantiationError) (), Word)
countedValidateScopedReplacement available slot binderType ambient replacement =
    case countedCoreTypeListIdentity available
            ambient (scopedCoreContext replacement) of
        (Left failure, afterContext) ->
            (Left (absurd <$> failure), afterContext)
        (Right False, afterContext) ->
            failed afterContext (ScopedInstantiationContextMismatch
                slot ambient (scopedCoreContext replacement))
        (Right True, afterContext) ->
            case countedCoreTypeIdentity afterContext
                    binderType (scopedCoreType replacement) of
                (Left failure, afterType) ->
                    (Left (absurd <$> failure), afterType)
                (Right False, afterType) ->
                    failed afterType (ScopedInstantiationTypeMismatch
                        slot binderType (scopedCoreType replacement))
                (Right True, afterType) -> (Right (), afterType)
  where
    failed remaining failure =
        (Left (CountedCoreOperationFailed failure), remaining)

-- | Simultaneously remove a nearest-first lexical prefix. Assignments use
-- source-order slots: slot zero denotes the outermost removed binder. Every
-- present assignment in this prefix must have its binder's type and the
-- remaining ambient context; later slots are ignored without scanning the map.
-- Each prefix row and compared metadata constructor, body constructor, and
-- shifted replacement constructor consumes structural work, including failure.
countedInstantiateScopedPrefix
    :: Word
    -> Natural
    -> Map Natural (ScopedCheckedCore global)
    -> ScopedCheckedCore global
    -> ( Either (CountedCoreFailure ScopedInstantiationError)
            (ScopedInstantiationResult global)
       , Word
       )
countedInstantiateScopedPrefix remaining binderCount replacements body =
    case validatePrefix remaining binderCount (scopedCoreContext body) of
        (Left failure, afterValidation) ->
            (Left failure, afterValidation)
        (Right ambient, afterValidation) ->
            case transform afterValidation 0 (scopedCoreTerm body) of
                (Left failure, afterTransform) ->
                    (Left failure, afterTransform)
                (Right (term, unresolved), afterTransform) ->
                    ( Right
                        (if Set.null unresolved
                            then ScopedInstantiationClosed
                                (ScopedCheckedCore ambient
                                    (scopedCoreType body) term)
                            else ScopedInstantiationOpen unresolved)
                    , afterTransform
                    )
  where
    -- Unwinding visits source-order slots once, with the ambient tail already
    -- known. No copy of the substitution or lexical context is needed.
    validatePrefix available 0 context = (Right context, available)
    validatePrefix available count context =
        case consumeCoreStructuralWork available of
            Left failure -> (Left failure, available)
            Right afterRow ->
                case context of
                    [] ->
                        failed afterRow
                            (ScopedInstantiationPrefixTooLong
                                binderCount (binderCount - count))
                    binderType : rest ->
                        case validatePrefix afterRow (count - 1) rest of
                            (Left failure, afterTail) ->
                                (Left failure, afterTail)
                            (Right ambient, afterTail) ->
                                case Map.lookup (count - 1) replacements of
                                    Nothing -> (Right ambient, afterTail)
                                    Just replacement ->
                                        case countedValidateScopedReplacement
                                                afterTail (count - 1)
                                                binderType ambient replacement of
                                            (result, afterReplacement) ->
                                                (ambient <$ result, afterReplacement)

    transform available depth term =
        case consumeCoreStructuralWork available of
            Left failure -> (Left failure, available)
            Right afterNode ->
                case term of
                    CBound index
                        | index < depth -> complete afterNode (CBound index)
                        | index < depth + binderCount ->
                            let slot = binderCount - (index - depth) - 1
                            in case Map.lookup slot replacements of
                                Nothing ->
                                    ( Right (CBound index, Set.singleton slot)
                                    , afterNode
                                    )
                                Just replacement ->
                                    case countedShiftCanonical afterNode depth 0
                                            (scopedCoreTerm replacement) of
                                        (Left failure, afterCopy) ->
                                            (Left (absurd <$> failure), afterCopy)
                                        (Right shifted, afterCopy) ->
                                            complete afterCopy shifted
                        | otherwise ->
                            complete afterNode (CBound (index - binderCount))
                    CGlobal global -> complete afterNode (CGlobal global)
                    CIntrinsic intrinsic ->
                        complete afterNode (CIntrinsic intrinsic)
                    CLogicalSelect coreType ->
                        complete afterNode (CLogicalSelect coreType)
                    COpaqueInteger integer ->
                        complete afterNode (COpaqueInteger integer)
                    CFalsum -> complete afterNode CFalsum
                    CTruth -> complete afterNode CTruth
                    CApp function argument ->
                        binary afterNode depth CApp function argument
                    CLam binderType termBody ->
                        unary afterNode (depth + 1) (CLam binderType) termBody
                    CNot proposition -> unary afterNode depth CNot proposition
                    CAnd left right -> binary afterNode depth CAnd left right
                    COr left right -> binary afterNode depth COr left right
                    CImp premise conclusion ->
                        binary afterNode depth CImp premise conclusion
                    CEq operandType left right ->
                        binary afterNode depth (CEq operandType) left right
                    CForall binderType termBody ->
                        unary afterNode (depth + 1) (CForall binderType) termBody
                    CExists binderType termBody ->
                        unary afterNode (depth + 1) (CExists binderType) termBody

    unary available depth constructor term =
        case transform available depth term of
            (Left failure, afterBody) -> (Left failure, afterBody)
            (Right (result, unresolved), afterBody) ->
                (Right (constructor result, unresolved), afterBody)

    binary available depth constructor left right =
        case transform available depth left of
            (Left failure, afterLeft) -> (Left failure, afterLeft)
            (Right (leftResult, leftUnresolved), afterLeft) ->
                case transform afterLeft depth right of
                    (Left failure, afterRight) -> (Left failure, afterRight)
                    (Right (rightResult, rightUnresolved), afterRight) ->
                        ( Right
                            ( constructor leftResult rightResult
                            , leftUnresolved <> rightUnresolved
                            )
                        , afterRight
                        )

    complete available result = (Right (result, Set.empty), available)
    failed available failure =
        (Left (CountedCoreOperationFailed failure), available)

-- | The nearest checked bound variable over one explicit outer context.
scopedBound
    :: [CoreType]
    -> CoreType
    -> ScopedCheckedCore global
scopedBound context binderType =
    ScopedCheckedCore (binderType : context) binderType (CBound 0)

-- | Apply two already checked terms in the same lexical context.
applyScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
applyScopedCore
        (ScopedCheckedCore functionContext functionType function)
        (ScopedCheckedCore argumentContext argumentType argument)
    | functionContext == argumentContext
    , TyArrow expected resultType <- functionType
    , expected == argumentType =
        Just
            (ScopedCheckedCore
                functionContext
                resultType
                (CApp function argument))
applyScopedCore _function _argument = Nothing

countedApplyScopedCore
    :: Word -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedApplyScopedCore available function argument =
    case consumeCoreStructuralWork available of
        Left failure -> (Left failure, available)
        Right afterEntry -> case countedCoreTypeListIdentity afterEntry
                (scopedCoreContext function) (scopedCoreContext argument) of
            (Left failure, remaining) -> (Left failure, remaining)
            (Right False, remaining) -> (Right Nothing, remaining)
            (Right True, afterContext) -> case scopedCoreType function of
                TyArrow expected resultType ->
                    let (result, remaining) = countedCoreTypeIdentity afterContext expected (scopedCoreType argument)
                    in ((\same -> if same then Just (ScopedCheckedCore (scopedCoreContext function)
                            resultType (CApp (scopedCoreTerm function) (scopedCoreTerm argument))) else Nothing) <$> result, remaining)
                _ -> (Right Nothing, afterContext)

-- | Apply a checked function to a fresh nearest binder. Weakening preserves
-- its typing evidence; both operands have the context constructed here.
pointwiseBodyScopedCore
    :: ScopedCheckedCore global -> Maybe (ScopedCheckedCore global)
pointwiseBodyScopedCore operand = case scopedCoreType operand of
    TyArrow domain result ->
        let function = weakenCheckedScopedCore domain operand
            argument = scopedBound (scopedCoreContext operand) domain
        in Just (ScopedCheckedCore (scopedCoreContext function) result
            (CApp (scopedCoreTerm function) (scopedCoreTerm argument)))
    _ -> Nothing

countedPointwiseBodyScopedCore
    :: Word -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedPointwiseBodyScopedCore available operand =
    case consumeCoreStructuralWork available of
        Left failure -> (Left failure, available)
        Right afterEntry -> case scopedCoreType operand of
            TyArrow domain result ->
                case countedWeakenCheckedScopedCore afterEntry domain operand of
                    (Left failure, remaining) -> (Left failure, remaining)
                    (Right function, remaining) -> case consumeCoreStructuralWork remaining of
                        Left failure -> (Left failure, remaining)
                        Right afterArgument ->
                            let argument = scopedBound (scopedCoreContext operand) domain
                            in (Right (Just (ScopedCheckedCore (scopedCoreContext function) result
                                (CApp (scopedCoreTerm function) (scopedCoreTerm argument)))), afterArgument)
            _ -> (Right Nothing, afterEntry)

-- | Close the nearest checked binder as a lambda.
abstractScopedCore
    :: CoreType
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
abstractScopedCore binderType
        (ScopedCheckedCore (actual : context) bodyType body)
    | actual == binderType =
        Just
            (ScopedCheckedCore
                context
                (TyArrow binderType bodyType)
                (CLam binderType body))
abstractScopedCore _binderType _body = Nothing

countedAbstractScopedCore
    :: Word -> CoreType -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedAbstractScopedCore available binderType body =
    case consumeCoreStructuralWork available of
        Left failure -> (Left failure, available)
        Right afterEntry -> case scopedCoreContext body of
            [] -> (Right Nothing, afterEntry)
            actual : context ->
                case countedCoreTypeIdentity afterEntry binderType actual of
                    (result, remaining) ->
                        ( (\same -> if same then Just (ScopedCheckedCore context
                            (TyArrow binderType (scopedCoreType body))
                            (CLam binderType (scopedCoreTerm body))) else Nothing) <$> result
                        , remaining)

-- | Introduce a fresh set-valued local definition. Separation specializes
-- the checked foundation characteristic so its local premise remains
-- first-order.
scopedSetDefinition
    :: Eq global
    => FrozenCheckedCore Void
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
scopedSetDefinition
        characteristic
        expression@(ScopedCheckedCore context TySet term) =
    case term of
        CApp
                (CApp (CIntrinsic Sep) bound)
                predicate@(CLam TySet _body) ->
            scopedCharacteristicDefinition
                characteristic
                expression
                ( ScopedCheckedCore context TySet bound
                    :| [ ScopedCheckedCore
                            context
                            (TySet `TyArrow` TyProp)
                            predicate
                       ]
                )
        _ ->
            Just (scopedDefinition expression)
scopedSetDefinition _characteristic _expression =
    Nothing

-- | Introduce a fresh local constant at the exact type of a checked value.
scopedDefinition
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
scopedDefinition (ScopedCheckedCore context coreType term) =
    ScopedCheckedCore
        (coreType : context)
        TyProp
        (CEq
            coreType
            (CBound 0)
            (shiftCanonical 1 0 term))

-- | Specialize a checked characteristic and abstract its set-valued target
-- into one fresh nearest binder. Checked substitution and beta reduction
-- preserve the foundation row's proposition type.
scopedCharacteristicDefinition
    :: Eq global
    => FrozenCheckedCore Void
    -> ScopedCheckedCore global
    -> NonEmpty (ScopedCheckedCore global)
    -> Maybe (ScopedCheckedCore global)
scopedCharacteristicDefinition
        (FrozenCheckedCore TyProp frozen)
        (ScopedCheckedCore context TySet target)
        arguments
    | all ((== context) . scopedCoreContext) arguments = do
        specialized <-
            specialize
                (mapCanonicalGlobals absurd frozen)
                (toList arguments)
        let normalized = betaNormalizeCanonical specialized
            (found, abstracted) =
                abstractCanonicalOccurrence target 0 normalized
        guard found
        pure
            (ScopedCheckedCore
                (TySet : context)
                TyProp
                abstracted)
  where
    specialize term [] =
        Just term
    specialize (CForall binderType body)
            (ScopedCheckedCore _ argumentType argument : rest)
        | binderType == argumentType =
            specialize
                (instantiateCanonical argument body)
                rest
    specialize _term _arguments =
        Nothing

scopedCharacteristicDefinition _characteristic _target _arguments =
    Nothing

-- | Insert one fresh outer binder and capture every occurrence equal to the
-- supplied target at the current depth.  Existing free indices are shifted
-- around that binder, while indices owned by intervening binders are stable.
abstractCanonicalOccurrence
    :: Eq global
    => CanonicalTerm global
    -> Natural
    -> CanonicalTerm global
    -> (Bool, CanonicalTerm global)
abstractCanonicalOccurrence target depth term
    | term == shiftCanonical depth 0 target =
        (True, CBound depth)
    | otherwise =
        case term of
            CBound index
                | index < depth ->
                    (False, CBound index)
                | otherwise ->
                    (False, CBound (index + 1))
            CGlobal global ->
                (False, CGlobal global)
            CIntrinsic intrinsic ->
                (False, CIntrinsic intrinsic)
            CLogicalSelect coreType ->
                (False, CLogicalSelect coreType)
            COpaqueInteger integer ->
                (False, COpaqueInteger integer)
            CApp function argument ->
                combine CApp
                    (abstractCanonicalOccurrence target depth function)
                    (abstractCanonicalOccurrence target depth argument)
            CLam binderType body ->
                let (found, abstracted) =
                        abstractCanonicalOccurrence target (depth + 1) body
                in (found, CLam binderType abstracted)
            CFalsum ->
                (False, CFalsum)
            CTruth ->
                (False, CTruth)
            CNot proposition ->
                let (found, abstracted) =
                        abstractCanonicalOccurrence target depth proposition
                in (found, CNot abstracted)
            CAnd left right ->
                combine CAnd
                    (abstractCanonicalOccurrence target depth left)
                    (abstractCanonicalOccurrence target depth right)
            COr left right ->
                combine COr
                    (abstractCanonicalOccurrence target depth left)
                    (abstractCanonicalOccurrence target depth right)
            CImp premise conclusion ->
                combine CImp
                    (abstractCanonicalOccurrence target depth premise)
                    (abstractCanonicalOccurrence target depth conclusion)
            CEq operandType left right ->
                combine (CEq operandType)
                    (abstractCanonicalOccurrence target depth left)
                    (abstractCanonicalOccurrence target depth right)
            CForall binderType body ->
                let (found, abstracted) =
                        abstractCanonicalOccurrence target (depth + 1) body
                in (found, CForall binderType abstracted)
            CExists binderType body ->
                let (found, abstracted) =
                        abstractCanonicalOccurrence target (depth + 1) body
                in (found, CExists binderType abstracted)
  where
    combine constructor (leftFound, left) (rightFound, right) =
        (leftFound || rightFound, constructor left right)

-- | Build the replacement graph of one checked set-valued local function.
-- The ordered-pair constructor is an ordinary checked source object.
scopedReplacementGraph
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        , ScopedCheckedCore global
        )
scopedReplacementGraph
        (ScopedCheckedCore context pairType pair)
        domain@(ScopedCheckedCore domainContext TySet domainTerm)
        (ScopedCheckedCore valueContext TySet value)
    | pairType == TySet `TyArrow` (TySet `TyArrow` TySet)
    , domainContext == context
    , valueContext == TySet : context =
        let pairValue =
                CApp
                    (CApp
                        (shiftCanonical 1 0 pair)
                        (CBound 0))
                    value
            function = CLam TySet pairValue
            graph =
                CApp
                    (CApp (CIntrinsic Repl) domainTerm)
                    function
        in Just
            ( ScopedCheckedCore context TySet graph
            , domain
            , ScopedCheckedCore
                context
                (TySet `TyArrow` TySet)
                function
            )
scopedReplacementGraph _pair _domain _value =
    Nothing

betaNormalizeCanonical
    :: CanonicalTerm global
    -> CanonicalTerm global
betaNormalizeCanonical = \case
    CApp function argument ->
        case betaNormalizeCanonical function of
            CLam _binderType body ->
                betaNormalizeCanonical
                    (instantiateCanonical
                        (betaNormalizeCanonical argument)
                        body)
            normalizedFunction ->
                CApp
                    normalizedFunction
                    (betaNormalizeCanonical argument)
    CLam binderType body ->
        CLam binderType (betaNormalizeCanonical body)
    CNot proposition ->
        CNot (betaNormalizeCanonical proposition)
    CAnd left right ->
        CAnd
            (betaNormalizeCanonical left)
            (betaNormalizeCanonical right)
    COr left right ->
        COr
            (betaNormalizeCanonical left)
            (betaNormalizeCanonical right)
    CImp premise conclusion ->
        CImp
            (betaNormalizeCanonical premise)
            (betaNormalizeCanonical conclusion)
    CEq operandType left right ->
        CEq operandType
            (betaNormalizeCanonical left)
            (betaNormalizeCanonical right)
    CForall binderType body ->
        CForall binderType (betaNormalizeCanonical body)
    CExists binderType body ->
        CExists binderType (betaNormalizeCanonical body)
    term -> term

-- | Combine two checked propositions under the same lexical context.
implyScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
implyScopedCore
        (ScopedCheckedCore premiseContext TyProp premise)
        (ScopedCheckedCore conclusionContext TyProp conclusion)
    | premiseContext == conclusionContext =
        Just
            (ScopedCheckedCore
                premiseContext
                TyProp
                (CImp premise conclusion))
implyScopedCore _premise _conclusion =
    Nothing

countedImplyScopedCore
    :: Word -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedImplyScopedCore available left right =
    case consumeCoreStructuralWork available of
        Left failure -> (Left failure, available)
        Right afterEntry -> case (scopedCoreType left, scopedCoreType right) of
            (TyProp, TyProp) -> case countedCoreTypeListIdentity afterEntry
                    (scopedCoreContext left) (scopedCoreContext right) of
                (result, remaining) ->
                    ((\same -> if same then Just (ScopedCheckedCore (scopedCoreContext left)
                        TyProp (CImp (scopedCoreTerm left) (scopedCoreTerm right))) else Nothing) <$> result, remaining)
            _ -> (Right Nothing, afterEntry)

-- | Form an equality between checked operands under the same lexical
-- context.  This preserves the checked-core invariant without requiring a
-- caller to recover global types merely to combine already checked terms.
equalScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
equalScopedCore
        (ScopedCheckedCore leftContext leftType left)
        (ScopedCheckedCore rightContext rightType right)
    | leftContext == rightContext
    , leftType == rightType =
        Just
            (ScopedCheckedCore
                leftContext
                TyProp
                (CEq leftType left right))
equalScopedCore _left _right =
    Nothing

countedEqualScopedCore
    :: Word -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void) (Maybe (ScopedCheckedCore global)), Word)
countedEqualScopedCore available left right =
    case consumeCoreStructuralWork available of
        Left failure -> (Left failure, available)
        Right afterEntry -> case countedCoreTypeListIdentity afterEntry
                (scopedCoreContext left) (scopedCoreContext right) of
            (Left failure, remaining) -> (Left failure, remaining)
            (Right False, remaining) -> (Right Nothing, remaining)
            (Right True, afterContext) -> case countedCoreTypeIdentity afterContext
                    (scopedCoreType left) (scopedCoreType right) of
                (result, remaining) ->
                    ( (\same -> if same then Just (ScopedCheckedCore (scopedCoreContext left)
                        TyProp (CEq (scopedCoreType left) (scopedCoreTerm left)
                            (scopedCoreTerm right))) else Nothing) <$> result
                    , remaining)

-- | Form checked set membership from checked operands in the same lexical
-- context.
memberScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
memberScopedCore
        (ScopedCheckedCore elementContext TySet element)
        (ScopedCheckedCore setContext TySet set)
    | elementContext == setContext =
        Just
            (ScopedCheckedCore
                elementContext
                TyProp
                (CApp (CApp (CIntrinsic Member) element) set))
memberScopedCore _element _set =
    Nothing

-- | Construct the exact ordinary conjunction, retaining truth operands.
conjoinExactScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
conjoinExactScopedCore
        (ScopedCheckedCore leftContext TyProp left)
        (ScopedCheckedCore rightContext TyProp right)
    | leftContext == rightContext =
        Just (ScopedCheckedCore leftContext TyProp (CAnd left right))
conjoinExactScopedCore _left _right = Nothing

data ScopedConjunctionError
    = ScopedConjunctionContextMismatch ![CoreType] ![CoreType]
    | ScopedConjunctionExpectedProposition !CoreType
    deriving stock (Show, Eq)

-- | Preserve checked operands without recovering their types or admitting
-- their globals. The consumer owns admission before entering this operation.
-- Charge the constructed node and each context/type comparison, including
-- failures; the constructor below relies on precisely those checked premises.
countedConjoinExactScopedCore
    :: Word
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure ScopedConjunctionError)
            (ScopedCheckedCore global), Word)
countedConjoinExactScopedCore available left right =
    case consumeCoreStructuralWork available of
        Left failure -> (Left failure, available)
        Right afterEntry ->
            case countedCoreTypeListIdentity afterEntry
                    (scopedCoreContext left) (scopedCoreContext right) of
                (Left failure, remaining) -> (Left (fmap absurd failure), remaining)
                (Right False, remaining) ->
                    failed remaining (ScopedConjunctionContextMismatch
                        (scopedCoreContext left) (scopedCoreContext right))
                (Right True, afterContext) ->
                    case proposition afterContext left of
                        (Left failure, remaining) -> (Left failure, remaining)
                        (Right (), afterLeft) ->
                            case proposition afterLeft right of
                                (Left failure, remaining) -> (Left failure, remaining)
                                (Right (), remaining) ->
                                    ( Right (ScopedCheckedCore
                                        (scopedCoreContext left) TyProp
                                        (CAnd (scopedCoreTerm left) (scopedCoreTerm right)))
                                    , remaining
                                    )
  where
    proposition remaining operand =
        case countedCoreTypeIdentity remaining TyProp (scopedCoreType operand) of
            (Left failure, afterType) -> (Left (fmap absurd failure), afterType)
            (Right False, afterType) ->
                failed afterType (ScopedConjunctionExpectedProposition
                    (scopedCoreType operand))
            (Right True, afterType) -> (Right (), afterType)
    failed remaining failure = (Left (CountedCoreOperationFailed failure), remaining)

-- | Conjoin two checked propositions under the same lexical context. Truth is
-- normalized away so callers can build an optional generated guard without
-- retaining an inert conjunct.
conjoinScopedCore
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
conjoinScopedCore
        left@(ScopedCheckedCore leftContext TyProp leftTerm)
        right@(ScopedCheckedCore rightContext TyProp rightTerm)
    | leftContext == rightContext
    , leftTerm == CTruth = Just right
    | leftContext == rightContext
    , rightTerm == CTruth = Just left
    | leftContext == rightContext =
        Just
            (ScopedCheckedCore
                leftContext
                TyProp
                (CAnd leftTerm rightTerm))
conjoinScopedCore _left _right =
    Nothing

-- | Disjoin two checked propositions under the same lexical context.
disjoinScopedCore
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
disjoinScopedCore
        (ScopedCheckedCore leftContext TyProp left)
        (ScopedCheckedCore rightContext TyProp right)
    | leftContext == rightContext =
        Just
            (ScopedCheckedCore
                leftContext
                TyProp
                (COr left right))
disjoinScopedCore _left _right =
    Nothing

-- | Negate a checked proposition without changing its lexical context.
negateScopedCore
    :: ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
negateScopedCore (ScopedCheckedCore context TyProp proposition) =
    Just
        (ScopedCheckedCore
            context
            TyProp
            (CNot proposition))
negateScopedCore _proposition =
    Nothing

-- | Checked falsum at an already established lexical context.
falsumScopedCore :: [CoreType] -> ScopedCheckedCore global
falsumScopedCore context =
    ScopedCheckedCore context TyProp CFalsum

-- | Split a checked set equality into its two extensionality directions.
splitScopedSetEquality
    :: ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        )
splitScopedSetEquality
        (ScopedCheckedCore context TyProp (CEq TySet left right)) =
    Just (subset left right, subset right left)
  where
    subset source target =
        ScopedCheckedCore
            context
            TyProp
            (CForall
                TySet
                (CImp
                    (memberOf (shiftCanonical 1 0 source))
                    (memberOf (shiftCanonical 1 0 target))))

    memberOf set =
        CApp
            (CApp
                (CIntrinsic Member)
                (CBound 0))
            set
splitScopedSetEquality _proposition =
    Nothing

-- | Derive the exact predicate, member-wise hypothesis, induction step, and
-- binder-level result for one set-valued ambient binder. The selected binder
-- is replaced by the newly introduced set variable; every other ambient
-- binder remains a parameter.
scopedSetInductionInstance
    :: Natural
    -> ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        , ScopedCheckedCore global
        , ScopedCheckedCore global
        )
scopedSetInductionInstance selected
        (ScopedCheckedCore context TyProp property)
    | nth selected context == Just TySet =
        Just (predicate, hypothesis, step, result)
  where
    abstractedProperty = abstractSelected 0 property
    predicate =
        ScopedCheckedCore
            context
            (TySet `TyArrow` TyProp)
            (CLam TySet abstractedProperty)
    hypothesis =
        ScopedCheckedCore
            context
            TyProp
            (CForall
                TySet
                (CImp
                    (CApp
                        (CApp
                            (CIntrinsic Member)
                            (CBound 0))
                        (CBound (selected + 1)))
                    abstractedProperty))
    step =
        ScopedCheckedCore
            context
            TyProp
            (CForall
                TySet
                (CImp
                    (abstractSelected
                        0
                        (scopedCoreTerm hypothesis))
                    abstractedProperty))
    result =
        ScopedCheckedCore
            context
            TyProp
            (CForall TySet abstractedProperty)

    abstractSelected depth = \case
        CBound index
            | index == depth + selected ->
                CBound depth
            | index >= depth ->
                CBound (index + 1)
            | otherwise ->
                CBound index
        CGlobal global ->
            CGlobal global
        CIntrinsic intrinsic ->
            CIntrinsic intrinsic
        CLogicalSelect coreType ->
            CLogicalSelect coreType
        COpaqueInteger integer ->
            COpaqueInteger integer
        CApp function argument ->
            CApp
                (abstractSelected depth function)
                (abstractSelected depth argument)
        CLam binderType body ->
            CLam binderType
                (abstractSelected (depth + 1) body)
        CFalsum ->
            CFalsum
        CTruth ->
            CTruth
        CNot proposition ->
            CNot (abstractSelected depth proposition)
        CAnd left right ->
            CAnd
                (abstractSelected depth left)
                (abstractSelected depth right)
        COr left right ->
            COr
                (abstractSelected depth left)
                (abstractSelected depth right)
        CImp premise conclusion ->
            CImp
                (abstractSelected depth premise)
                (abstractSelected depth conclusion)
        CEq operandType left right ->
            CEq operandType
                (abstractSelected depth left)
                (abstractSelected depth right)
        CForall binderType body ->
            CForall binderType
                (abstractSelected (depth + 1) body)
        CExists binderType body ->
            CExists binderType
                (abstractSelected (depth + 1) body)
scopedSetInductionInstance _selected _property =
    Nothing

-- | Close the nearest checked binder as one leading universal.
closeScopedForall
    :: ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
closeScopedForall
        (ScopedCheckedCore (binderType : context) TyProp body) =
    Just
        (ScopedCheckedCore
            context
            TyProp
            (CForall binderType body))
closeScopedForall _scoped =
    Nothing

-- | Close the nearest checked binder as one leading existential.
closeScopedExists
    :: ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
closeScopedExists
        (ScopedCheckedCore (binderType : context) TyProp body) =
    Just
        (ScopedCheckedCore
            context
            TyProp
            (CExists binderType body))
closeScopedExists _scoped =
    Nothing

-- | Open one checked leading universal without rechecking its body.
openScopedForall
    :: ScopedCheckedCore global
    -> Maybe (CoreType, ScopedCheckedCore global)
openScopedForall
        (ScopedCheckedCore context TyProp
            (CForall binderType body)) =
    Just
        ( binderType
        , ScopedCheckedCore
            (binderType : context)
            TyProp
            body
        )
openScopedForall _scoped =
    Nothing

-- | Open one checked leading existential without rechecking its body.
openScopedExists
    :: ScopedCheckedCore global
    -> Maybe (CoreType, ScopedCheckedCore global)
openScopedExists
        (ScopedCheckedCore context TyProp
            (CExists binderType body)) =
    Just
        ( binderType
        , ScopedCheckedCore
            (binderType : context)
            TyProp
            body
        )
openScopedExists _scoped =
    Nothing

-- | Split one checked implication under its unchanged ambient context.
openScopedImplication
    :: ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        )
openScopedImplication
        (ScopedCheckedCore context TyProp
            (CImp premise conclusion)) =
    Just
        ( ScopedCheckedCore context TyProp premise
        , ScopedCheckedCore context TyProp conclusion
        )
openScopedImplication _scoped =
    Nothing

-- | Split a checked equality without reducing its operands or changing scope.
splitScopedEquality
    :: ScopedCheckedCore global
    -> Maybe
        ( CoreType
        , ScopedCheckedCore global
        , ScopedCheckedCore global
        )
splitScopedEquality
        (ScopedCheckedCore context TyProp (CEq operandType left right)) =
    Just
        ( operandType
        , ScopedCheckedCore context operandType left
        , ScopedCheckedCore context operandType right
        )
splitScopedEquality _scoped =
    Nothing

-- | Project a checked membership's element and set without reducing either.
splitScopedMembership
    :: ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global, ScopedCheckedCore global)
splitScopedMembership
        (ScopedCheckedCore context TyProp
            (CApp (CApp (CIntrinsic Member) element) set)) =
    Just
        ( ScopedCheckedCore context TySet element
        , ScopedCheckedCore context TySet set
        )
splitScopedMembership _scoped =
    Nothing

splitScopedConjunction
    :: ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        )
splitScopedConjunction
        (ScopedCheckedCore context TyProp
            (CAnd left right)) =
    Just
        ( ScopedCheckedCore context TyProp left
        , ScopedCheckedCore context TyProp right
        )
splitScopedConjunction _scoped =
    Nothing

splitScopedDisjunction
    :: ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        )
splitScopedDisjunction
        (ScopedCheckedCore context TyProp
            (COr left right)) =
    Just
        ( ScopedCheckedCore context TyProp left
        , ScopedCheckedCore context TyProp right
        )
splitScopedDisjunction _scoped =
    Nothing

splitScopedNegation
    :: ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
splitScopedNegation
        (ScopedCheckedCore context TyProp (CNot proposition)) =
    Just (ScopedCheckedCore context TyProp proposition)
splitScopedNegation _scoped =
    Nothing

closeScopedCore
    :: ScopedCheckedCore global
    -> Maybe (FrozenCheckedCore global)
closeScopedCore
        (ScopedCheckedCore [] coreType term) =
    Just (FrozenCheckedCore coreType term)
closeScopedCore ScopedCheckedCore{} =
    Nothing

-- | Substitute an outer-context term for index zero and remove that binder.
instantiateCanonical
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
instantiateCanonical = instantiateCanonicalAt 0

-- | Instantiate a selected surrounding binder beneath a retained telescope.
-- The replacement belongs to the context outside that telescope.
instantiateCanonicalAt
    :: Natural -> CanonicalTerm global -> CanonicalTerm global -> CanonicalTerm global
instantiateCanonicalAt depth argument term =
    runIdentity (instantiateCanonicalWith (pure ()) depth argument term)

instantiateCanonicalWith
    :: Monad m => m () -> Natural -> CanonicalTerm global
    -> CanonicalTerm global -> m (CanonicalTerm global)
instantiateCanonicalWith visit initialDepth argument =
    traverseCanonicalBindings visit replace initialDepth
  where
    replace depth index
        | index == depth = shiftCanonicalWith visit depth 0 argument
        | index > depth = pure (CBound (index - 1))
        | otherwise = pure (CBound index)
{-# INLINE instantiateCanonicalWith #-}

-- Each body constructor is charged, including every shifted replacement copy.
countedInstantiateCanonical
    :: Word -> CanonicalTerm global -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) (CanonicalTerm global), Word)
countedInstantiateCanonical available argument body =
    State.runState (Except.runExceptT
        (instantiateCanonicalWith visitCoreConstructor 0 argument body)) available

-- | Simultaneously substitute a nearest-first binder prefix. Replacement
-- occurrences live outside that prefix; inner binders remain untouched and
-- remaining outer indices lose the removed prefix. Expanded abbreviations use
-- this operation for both their logical body and construction-free subterms.
-- Repeated formals at one body depth share their capture-safe weakening.
countedInstantiateCanonicalPrefix
    :: Word -> Vector (CanonicalTerm global) -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) (CanonicalTerm global), Word)
countedInstantiateCanonicalPrefix available arguments =
    countedInstantiateCanonicalParameters available (fromIntegral (Vector.length arguments))
        (Right . (arguments Vector.!) . fromIntegral)

-- A component substitutes only its referenced formal slots. The removed
-- prefix is still explicit, so unused holes never shift a surviving capture.
-- Report an actually referenced missing slot rather than guessing a value.
countedInstantiateCanonicalSlots
    :: Word -> Natural -> Map Natural (CanonicalTerm global) -> CanonicalTerm global
    -> (Either (CountedCoreFailure Natural) (CanonicalTerm global), Word)
countedInstantiateCanonicalSlots available arity arguments =
    countedInstantiateCanonicalParameters available arity
        (\slot -> maybe (Left slot) Right (Map.lookup slot arguments))

countedInstantiateCanonicalParameters
    :: Word -> Natural -> (Natural -> Either failure (CanonicalTerm global)) -> CanonicalTerm global
    -> (Either (CountedCoreFailure failure) (CanonicalTerm global), Word)
countedInstantiateCanonicalParameters available arity argumentAt body =
    State.runState (Except.runExceptT
        (State.evalStateT (instantiateCanonicalPrefixWith visit arity replace 0 body) Map.empty)) available
  where
    visit = State.lift visitCoreConstructor
    replace depth formal = do
        let key = (formal, depth)
        visit
        known <- State.get
        case Map.lookup key known of
            Just shifted -> pure shifted
            Nothing -> do
                argument <- either (State.lift . Except.throwError . CountedCoreOperationFailed) pure (argumentAt formal)
                shifted <- if depth == 0 then pure argument
                    else shiftCanonicalWith visit depth 0 argument
                visit
                State.modify' (Map.insert key shifted)
                pure shifted

-- The expansion owner shares the same formal/depth memo between logical Core
-- and rich source occurrences. The callback supplies a replacement already
-- weakened beneath the indicated number of body binders.
instantiateCanonicalPrefixWith
    :: Monad m => m () -> Natural
    -> (Natural -> Natural -> m (CanonicalTerm global))
    -> Natural -> CanonicalTerm global -> m (CanonicalTerm global)
instantiateCanonicalPrefixWith visit arity formal = traverseCanonicalBindings visit replace
  where
    replace depth index
        | index < depth = pure (CBound index)
        | index >= depth + arity = pure (CBound (index - arity))
        | otherwise = formal depth (index - depth)

-- | Outer de Bruijn slots, excluding binders internal to this term. The
-- admission owner supplies the same bounded visitor used for other Core work.
canonicalFreeIndicesWith
    :: Monad m => m () -> CanonicalTerm global -> m (Set Natural)
canonicalFreeIndicesWith visit term = State.execStateT
    (traverseCanonicalBindings (State.lift visit) record 0 term) Set.empty
  where
    record depth index = do
        when (index >= depth) (State.modify' (Set.insert (index - depth)))
        pure (CBound index)

mapCanonicalGlobals
    :: (global -> global')
    -> CanonicalTerm global
    -> CanonicalTerm global'
mapCanonicalGlobals transform = \case
    CBound index ->
        CBound index
    CGlobal global ->
        CGlobal (transform global)
    CIntrinsic intrinsic ->
        CIntrinsic intrinsic
    CLogicalSelect coreType ->
        CLogicalSelect coreType
    COpaqueInteger integer ->
        COpaqueInteger integer
    CApp function argument ->
        CApp
            (mapCanonicalGlobals transform function)
            (mapCanonicalGlobals transform argument)
    CLam binderType body ->
        CLam binderType
            (mapCanonicalGlobals transform body)
    CFalsum ->
        CFalsum
    CTruth ->
        CTruth
    CNot proposition ->
        CNot (mapCanonicalGlobals transform proposition)
    CAnd left right ->
        CAnd
            (mapCanonicalGlobals transform left)
            (mapCanonicalGlobals transform right)
    COr left right ->
        COr
            (mapCanonicalGlobals transform left)
            (mapCanonicalGlobals transform right)
    CImp premise conclusion ->
        CImp
            (mapCanonicalGlobals transform premise)
            (mapCanonicalGlobals transform conclusion)
    CEq operandType left right ->
        CEq operandType
            (mapCanonicalGlobals transform left)
            (mapCanonicalGlobals transform right)
    CForall binderType body ->
        CForall binderType
            (mapCanonicalGlobals transform body)
    CExists binderType body ->
        CExists binderType
            (mapCanonicalGlobals transform body)

-- | Recheck a nameless term without exposing the checked wrapper constructor.
checkCanonicalCore
    :: GlobalTyping global
    -> CanonicalTerm global
    -> Either CoreCheckError (FrozenCheckedCore global)
checkCanonicalCore globalTyping term =
    FrozenCheckedCore
        <$> inferCanonicalCore (lookupGlobalType globalTyping) [] term
        <*> pure term

inferCanonicalCore
    :: (global -> Maybe CoreType)
    -> [CoreType]
    -> CanonicalTerm global
    -> Either CoreCheckError CoreType
inferCanonicalCore globalType binders term =
    inferCanonicalCoreWith id (pure ())
        (\index context -> maybe (Left (UnboundCoreIndex index)) Right (nth index context))
        (\left right -> pure (left == right))
        (\_ _ -> ()) (\_ _ coreType _ -> coreType) id globalType binders () term

data InferenceNode global child
    = InferenceBound !Natural
    | InferenceGlobal !global
    | InferenceIntrinsic !CoreIntrinsicTag
    | InferenceLogicalSelect !CoreType
    | InferenceOpaqueInteger !Integer
    | InferenceApplication !child !child
    | InferenceLambda !CoreType !child
    | InferenceFalsum
    | InferenceTruth
    | InferenceNegation !child
    | InferenceConjunction !child !child
    | InferenceDisjunction !child !child
    | InferenceImplication !child !child
    | InferenceEquality !CoreType !child !child
    | InferenceUniversal !CoreType !child
    | InferenceExistential !CoreType !child

inferCanonicalCoreWith
    :: Except.MonadError failure m
    => (CoreCheckError -> failure)
    -> m ()
    -> (Natural -> [CoreType] -> m CoreType)
    -> (CoreType -> CoreType -> m Bool)
    -> ([CoreType] -> scope -> scope)
    -> (scope -> CanonicalTerm global -> CoreType -> InferenceNode global payload -> payload)
    -> (payload -> CoreType)
    -> (global -> Maybe CoreType)
    -> [CoreType] -> scope -> CanonicalTerm global -> m payload
inferCanonicalCoreWith failure visit binderAt sameType enterScope build typeOf globalType = infer
  where
    requireType expected actual mismatch = do
        same <- sameType expected actual
        unless same (Except.throwError (failure mismatch))

    infer binders scope term = do
        visit
        let complete coreType children = pure (build scope term coreType children)
            beneath binder body =
                let inner = binder : binders
                in infer inner (enterScope inner scope) body
            binary expected mismatch construct left right = do
                leftResult <- infer binders scope left
                requireType expected (typeOf leftResult) (mismatch (typeOf leftResult))
                rightResult <- infer binders scope right
                requireType expected (typeOf rightResult) (mismatch (typeOf rightResult))
                complete TyProp (construct leftResult rightResult)
            quantified construct binder body = do
                result <- beneath binder body
                requireType TyProp (typeOf result) (QuantifierBodyTypeMismatch (typeOf result))
                complete TyProp (construct binder result)
        case term of
            CBound index -> do
                coreType <- binderAt index binders
                complete coreType (InferenceBound index)
            CGlobal global -> do
                coreType <- maybe (Except.throwError (failure UnknownCoreGlobal)) pure (globalType global)
                complete coreType (InferenceGlobal global)
            CIntrinsic intrinsic -> complete (coreIntrinsicType intrinsic) (InferenceIntrinsic intrinsic)
            CLogicalSelect coreType -> complete (logicalSelectionType coreType) (InferenceLogicalSelect coreType)
            COpaqueInteger integer -> complete TySet (InferenceOpaqueInteger integer)
            CApp function argument -> do
                functionResult <- infer binders scope function
                argumentResult <- infer binders scope argument
                case typeOf functionResult of
                    TyArrow expected result -> do
                        let actual = typeOf argumentResult
                        requireType expected actual (ApplicationArgumentTypeMismatch expected actual)
                        complete result (InferenceApplication functionResult argumentResult)
                    other -> Except.throwError (failure (AppliedNonFunction other))
            CLam binder body -> do
                result <- beneath binder body
                complete (TyArrow binder (typeOf result)) (InferenceLambda binder result)
            CFalsum -> complete TyProp InferenceFalsum
            CTruth -> complete TyProp InferenceTruth
            CNot proposition -> do
                result <- infer binders scope proposition
                requireType TyProp (typeOf result) (ExpectedCoreType TyProp (typeOf result))
                complete TyProp (InferenceNegation result)
            CAnd left right -> binary TyProp (ExpectedCoreType TyProp) InferenceConjunction left right
            COr left right -> binary TyProp (ExpectedCoreType TyProp) InferenceDisjunction left right
            CImp left right -> binary TyProp ImplicationOperandTypeMismatch InferenceImplication left right
            CEq operand left right -> binary operand (EqualityOperandTypeMismatch operand) (InferenceEquality operand) left right
            CForall binder body -> quantified InferenceUniversal binder body
            CExists binder body -> quantified InferenceExistential binder body
{-# INLINE inferCanonicalCoreWith #-}

inferCanonicalCoreCountedWith
    :: ([CoreType] -> scope -> scope)
    -> (scope -> CanonicalTerm global -> CoreType -> InferenceNode global payload -> payload)
    -> (payload -> CoreType)
    -> (global -> Maybe CoreType)
    -> Word -> [CoreType] -> scope -> CanonicalTerm global
    -> (Either (CountedCoreFailure CoreCheckError) payload, Word)
inferCanonicalCoreCountedWith enterScope build typeOf globalType available binders scope term =
    State.runState (Except.runExceptT
        (inferCanonicalCoreWith CountedCoreOperationFailed visitCoreConstructor binderAt sameType
            enterScope build typeOf globalType binders scope term)) available
  where
    binderAt index = \case
        [] -> Except.throwError (CountedCoreOperationFailed (UnboundCoreIndex index))
        binder : rest -> do
            visitCoreConstructor
            if index == 0 then pure binder else binderAt (index - 1) rest
    sameType left right = do
        beforeComparison <- State.get
        let (result, remaining) = countedCoreTypeIdentity beforeComparison left right
        State.put remaining
        either (Except.throwError . fmap absurd) pure result
{-# INLINE inferCanonicalCoreCountedWith #-}

inferCanonicalCoreCounted
    :: (global -> Maybe CoreType)
    -> Word
    -> [CoreType]
    -> CanonicalTerm global
    -> (Either (CountedCoreFailure CoreCheckError) CoreType, Word)
inferCanonicalCoreCounted globalType remaining context term =
    inferCanonicalCoreCountedWith
        (\_binders _scope -> ())
        (\_scope _term coreType _children -> coreType)
        id globalType remaining context () term

-- The scalar is the least absolute binder level, measured from the analysed
-- root, referenced anywhere below the row. A row at depth d depends on its
-- removable prefix exactly when that level is below d. Unlike a free-index
-- collection, this summary combines in constant time at every constructor.
data RetainedOccurrence global = RetainedOccurrence
    !(CheckedOccurrence global)
    !(Maybe Natural)

-- | Ordinary elaboration's occurrence analysis. It shares the inference and
-- retention engine with the resource-bounded query operation below.
analyseCanonicalOccurrences
    :: GlobalTyping global
    -> [CoreType]
    -> CanonicalTerm global
    -> Either CoreCheckError (CheckedOccurrence global)
analyseCanonicalOccurrences globalTyping context term = do
    RetainedOccurrence root _ <- inferCanonicalCoreWith id (pure ())
        (\index binders -> maybe (Left (UnboundCoreIndex index)) Right (nth index binders))
        (\left right -> pure (left == right))
        enterOccurrenceScope retainOccurrence
        (\(RetainedOccurrence row _) -> checkedOccurrenceType row)
        (lookupGlobalType globalTyping) context (OccurrenceScope context context 0) term
    pure root

-- | Check a complete canonical tree once while retaining the inferred type,
-- exact constructor view, and removable-binder dependency of every occurrence.
-- The returned row spine and shallow metadata are fully built before the exact
-- structural remainder is returned; recursive Core payloads remain shared.
countedAnalyseCanonicalOccurrences
    :: GlobalTyping global
    -> Word
    -> [CoreType]
    -> CanonicalTerm global
    -> ( Either
            (CountedCoreFailure CoreCheckError)
            (CheckedOccurrence global)
       , Word
       )
countedAnalyseCanonicalOccurrences globalTyping remaining ambient term =
    case analyseCanonicalOccurrencesAt
            (lookupGlobalType globalTyping)
            remaining
            ambient
            ambient
            0
            term of
        (Left failure, remaining') ->
            (Left failure, remaining')
        (Right (root, _coreType), remaining') ->
            (Right root, remaining')

-- | Analyse an already checked term beneath a known removable logical-binder
-- prefix. Deriving the fixed ambient suffix and checking the retained root
-- type are both counted; the occurrence tree itself is built by the same
-- inference/retention engine as the depth-zero operation above.
countedAnalyseScopedOccurrencesUnderBinders
    :: GlobalTyping global
    -> Word
    -> Natural
    -> ScopedCheckedCore global
    -> ( Either
            (CountedCoreFailure CheckedOccurrenceAnalysisError)
            (CheckedOccurrence global)
       , Word
       )
countedAnalyseScopedOccurrencesUnderBinders
        globalTyping remaining binderDepth checked =
    case countedAmbientSuffix
            remaining binderDepth (scopedCoreContext checked) of
        (Left failure, afterPrefix) ->
            (Left failure, afterPrefix)
        (Right ambient, afterPrefix) ->
            case analyseCanonicalOccurrencesAt
                    (lookupGlobalType globalTyping) afterPrefix ambient
                    (scopedCoreContext checked) binderDepth
                    (scopedCoreTerm checked) of
                (Left failure, afterAnalysis) ->
                    ( Left
                        (CheckedOccurrenceAnalysisCheckFailed <$> failure)
                    , afterAnalysis
                    )
                (Right (root, rootType), afterAnalysis) ->
                    case countedCoreTypeIdentity
                            afterAnalysis rootType
                            (scopedCoreType checked) of
                        (Left failure, afterType) ->
                            (Left (absurd <$> failure), afterType)
                        (Right False, afterType) ->
                            ( Left
                                (CountedCoreOperationFailed
                                    (CheckedOccurrenceRootTypeMismatch
                                        rootType
                                        (scopedCoreType checked)))
                            , afterType
                            )
                        (Right True, afterType) ->
                            (Right root, afterType)
  where
    countedAmbientSuffix available 0 context =
        (Right context, available)
    countedAmbientSuffix 0 _depth _context =
        (Left CountedCoreStructuralWorkExhausted, 0)
    countedAmbientSuffix available _depth [] =
        ( Left
            (CountedCoreOperationFailed
                CheckedOccurrenceBinderDepthOutOfScope)
        , available
        )
    countedAmbientSuffix available depth (_binder : context) =
        countedAmbientSuffix (available - 1) (depth - 1) context

analyseCanonicalOccurrencesAt
    :: (global -> Maybe CoreType)
    -> Word
    -> [CoreType]
    -> [CoreType]
    -> Natural
    -> CanonicalTerm global
    -> ( Either
            (CountedCoreFailure CoreCheckError)
            (CheckedOccurrence global, CoreType)
       , Word
       )
analyseCanonicalOccurrencesAt
        globalType remaining ambient context initialBinderDepth term =
    case inferCanonicalCoreCountedWith
            enterOccurrenceScope retainOccurrence (\(RetainedOccurrence row _) -> checkedOccurrenceType row) globalType remaining context
            (OccurrenceScope context ambient initialBinderDepth) term of
        (Left failure, remaining') ->
            (Left failure, remaining')
        (Right (RetainedOccurrence root _minimumBinderLevel), remaining') ->
            (Right (root, checkedOccurrenceType root), remaining')

enterOccurrenceScope :: [CoreType] -> OccurrenceScope -> OccurrenceScope
enterOccurrenceScope childContext (OccurrenceScope _context ambient binderDepth) =
    OccurrenceScope childContext ambient (binderDepth + 1)

retainOccurrence
    :: OccurrenceScope -> CanonicalTerm global -> CoreType
    -> InferenceNode global (RetainedOccurrence global) -> RetainedOccurrence global
retainOccurrence scope@(OccurrenceScope _context _ambient binderDepth)
        source coreType node =
    let (view, minimumBinderLevel) = retainNode binderDepth node
        depends = maybe False (< binderDepth) minimumBinderLevel
    in RetainedOccurrence (CheckedOccurrence source coreType scope depends view) minimumBinderLevel
  where
    retainNode binderDepth = \case
        InferenceBound index ->
            ( OccurrenceBound index
            , if index < binderDepth
                then Just (binderDepth - index - 1)
                else Nothing
            )
        InferenceGlobal global ->
            (OccurrenceGlobal global, Nothing)
        InferenceIntrinsic intrinsic ->
            (OccurrenceIntrinsic intrinsic, Nothing)
        InferenceLogicalSelect coreType ->
            (OccurrenceLogicalSelect coreType, Nothing)
        InferenceOpaqueInteger integer ->
            (OccurrenceOpaqueInteger integer, Nothing)
        InferenceApplication left right ->
            retainBinary OccurrenceApplication left right
        InferenceLambda binderType child ->
            retainUnary (OccurrenceLambda binderType) child
        InferenceFalsum ->
            (OccurrenceFalsum, Nothing)
        InferenceTruth ->
            (OccurrenceTruth, Nothing)
        InferenceNegation child ->
            retainUnary OccurrenceNegation child
        InferenceConjunction left right ->
            retainBinary OccurrenceConjunction left right
        InferenceDisjunction left right ->
            retainBinary OccurrenceDisjunction left right
        InferenceImplication left right ->
            retainBinary OccurrenceImplication left right
        InferenceEquality operandType left right ->
            retainBinary (OccurrenceEquality operandType) left right
        InferenceUniversal binderType child ->
            retainUnary (OccurrenceUniversal binderType) child
        InferenceExistential binderType child ->
            retainUnary (OccurrenceExistential binderType) child

    retainUnary construct (RetainedOccurrence child childMinimum) =
        (construct child, childMinimum)

    retainBinary construct
            (RetainedOccurrence left leftMinimum)
            (RetainedOccurrence right rightMinimum) =
        ( construct left right
        , minimumLevel leftMinimum rightMinimum
        )

    minimumLevel Nothing right = right
    minimumLevel left Nothing = left
    minimumLevel (Just left) (Just right) = Just (min left right)

-- | Remove the surrounding logical-binder prefix from one retained occurrence
-- without rechecking it.  The analysis has already established its type and
-- whether the prefix occurs; Core keeps construction of the resulting checked
-- value behind this evidence-preserving boundary.
countedRebaseCheckedOccurrence
    :: Word
    -> CheckedOccurrence global
    -> ( Either
            (CountedCoreFailure CheckedOccurrenceRebaseError)
            (Maybe (ScopedCheckedCore global))
       , Word
       )
countedRebaseCheckedOccurrence remaining
        (CheckedOccurrence term coreType
            (OccurrenceScope _context ambient binderDepth) depends _view)
        | depends = (Right Nothing, remaining)
        | binderDepth == 0 =
            (Right (Just (ScopedCheckedCore ambient coreType term)), remaining)
        | otherwise =
            case remove remaining 0 term of
                (Left failure, remaining') ->
                    (Left failure, remaining')
                (Right Nothing, remaining') ->
                    ( Left
                        (CountedCoreOperationFailed
                            CheckedOccurrenceRebaseInvariant)
                    , remaining'
                    )
                (Right (Just rebased), remaining') ->
                    ( Right
                        (Just
                            (ScopedCheckedCore ambient coreType rebased))
                    , remaining'
                    )
  where
    remove available localDepth candidate =
        case consumeCoreStructuralWork available of
            Left failure -> (Left failure, available)
            Right afterNode ->
                case candidate of
                    CBound index
                        | index < localDepth ->
                            complete afterNode (CBound index)
                        | index < localDepth + binderDepth ->
                            (Right Nothing, afterNode)
                        | otherwise ->
                            complete afterNode
                                (CBound (index - binderDepth))
                    CGlobal global ->
                        complete afterNode (CGlobal global)
                    CIntrinsic intrinsic ->
                        complete afterNode (CIntrinsic intrinsic)
                    CLogicalSelect selectedType ->
                        complete afterNode (CLogicalSelect selectedType)
                    COpaqueInteger integer ->
                        complete afterNode (COpaqueInteger integer)
                    CApp function argument ->
                        binary afterNode localDepth CApp function argument
                    CLam binderType body ->
                        unary afterNode (localDepth + 1)
                            (CLam binderType) body
                    CFalsum -> complete afterNode CFalsum
                    CTruth -> complete afterNode CTruth
                    CNot proposition ->
                        unary afterNode localDepth CNot proposition
                    CAnd left right ->
                        binary afterNode localDepth CAnd left right
                    COr left right ->
                        binary afterNode localDepth COr left right
                    CImp premise conclusion ->
                        binary afterNode localDepth CImp premise conclusion
                    CEq operandType left right ->
                        binary afterNode localDepth
                            (CEq operandType) left right
                    CForall binderType body ->
                        unary afterNode (localDepth + 1)
                            (CForall binderType) body
                    CExists binderType body ->
                        unary afterNode (localDepth + 1)
                            (CExists binderType) body

    unary available depth constructor candidate =
        case remove available depth candidate of
            (Left failure, remaining') ->
                (Left failure, remaining')
            (Right result, remaining') ->
                (Right (constructor <$> result), remaining')

    binary available depth constructor left right =
        case remove available depth left of
            (Left failure, afterLeft) ->
                (Left failure, afterLeft)
            (Right Nothing, afterLeft) ->
                (Right Nothing, afterLeft)
            (Right (Just leftResult), afterLeft) ->
                case remove afterLeft depth right of
                    (Left failure, afterRight) ->
                        (Left failure, afterRight)
                    (Right rightResult, afterRight) ->
                        (Right (constructor leftResult <$> rightResult), afterRight)

    complete available result = (Right (Just result), available)

consumeCoreStructuralWork
    :: Word
    -> Either (CountedCoreFailure error) Word
consumeCoreStructuralWork 0 =
    Left CountedCoreStructuralWorkExhausted
consumeCoreStructuralWork remaining =
    Right (remaining - 1)

shiftCanonical
    :: Natural -> Natural -> CanonicalTerm global -> CanonicalTerm global
shiftCanonical amount cutoff term =
    runIdentity (shiftCanonicalWith (pure ()) amount cutoff term)

shiftCanonicalWith
    :: Monad m => m () -> Natural -> Natural -> CanonicalTerm global
    -> m (CanonicalTerm global)
shiftCanonicalWith visit amount = traverseCanonicalBindings visit \cutoff index ->
    pure (CBound (if index >= cutoff then index + amount else index))
{-# INLINE shiftCanonicalWith #-}

-- Counted traversal publishes only a complete result and retains spent work
-- on failure. Identity preserves the ordinary transformation's demand.
countedShiftCanonical
    :: Word -> Natural -> Natural -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) (CanonicalTerm global), Word)
countedShiftCanonical available amount cutoff term =
    State.runState (Except.runExceptT
        (shiftCanonicalWith visitCoreConstructor amount cutoff term)) available

-- | Syntax identity under extension of one nominal lexical scope. Internal
-- indices remain indices; free variables become levels in a separate namespace
-- from real globals. The owning scope establishes nominal prefix identity.
-- This is an index key, never a term to admit to the kernel.
countedScopedLevelKey
    :: Word -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure Void)
        (CanonicalTerm (Either Natural global)), Word)
countedScopedLevelKey available scoped = State.runState (Except.runExceptT do
    ambient <- foldM (\depth _ -> visitCoreConstructor >> pure (depth + 1))
        0 (scopedCoreContext scoped)
    traverseCanonicalScope visitCoreConstructor (pure . CGlobal . Right)
        (\depth index -> pure
            (if index < depth then CBound index
             else CGlobal (Left (ambient - (index - depth) - 1))))
        0 (scopedCoreTerm scoped)) available

visitCoreConstructor :: Except.ExceptT (CountedCoreFailure error) (State.State Word) ()
visitCoreConstructor = do
    remaining <- State.get
    either Except.throwError State.put (consumeCoreStructuralWork remaining)

-- The visit precedes each constructor; replacement decides how an index
-- changes at its lexical depth and may perform further charged traversal.
traverseCanonicalBindings
    :: Monad m => m () -> (Natural -> Natural -> m (CanonicalTerm global))
    -> Natural -> CanonicalTerm global -> m (CanonicalTerm global)
traverseCanonicalBindings visit = traverseCanonicalScope visit (pure . CGlobal)
{-# INLINE traverseCanonicalBindings #-}

traverseCanonicalScope
    :: Monad m => m () -> (global -> m (CanonicalTerm target))
    -> (Natural -> Natural -> m (CanonicalTerm target))
    -> Natural -> CanonicalTerm global -> m (CanonicalTerm target)
traverseCanonicalScope visit global replace = go
  where
    go depth term = visit >> case term of
        CBound index -> replace depth index
        CGlobal value -> global value
        CIntrinsic intrinsic -> pure (CIntrinsic intrinsic)
        CLogicalSelect coreType -> pure (CLogicalSelect coreType)
        COpaqueInteger integer -> pure (COpaqueInteger integer)
        CApp function argument -> CApp <$> go depth function <*> go depth argument
        CLam binder body -> CLam binder <$> go (depth + 1) body
        CFalsum -> pure CFalsum
        CTruth -> pure CTruth
        CNot body -> CNot <$> go depth body
        CAnd left right -> CAnd <$> go depth left <*> go depth right
        COr left right -> COr <$> go depth left <*> go depth right
        CImp left right -> CImp <$> go depth left <*> go depth right
        CEq operand left right -> CEq operand <$> go depth left <*> go depth right
        CForall binder body -> CForall binder <$> go (depth + 1) body
        CExists binder body -> CExists binder <$> go (depth + 1) body
{-# INLINE traverseCanonicalScope #-}
