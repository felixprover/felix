{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Transient owner-preserving source terms.  The checked Core denotation is
-- authoritative; construction metadata records only eligible written source
-- applications and is erased before logical proof locals or persistent proof
-- syntax.  Constructors stay private.  Smart constructors establish the
-- small construction-specific type invariants; elaboration remains responsible
-- for supplying the matching checked Core term and recursive source arguments.
module Felix.Checking.SourceTerm
    ( SourceTermOccurrence
    , SourceTermProvider
    , sourceTermOccurrence
    , sourceGlobalProviderTermOccurrence
    , sourceStructureFieldProviderTermOccurrence
    , sourceIntrinsicProviderTermOccurrence
    , sourceFiniteSetLiteralTermOccurrence
    , sourceOrderedPairTermOccurrence
    , sourceTermOccurrenceCore
    , sourceTermOccurrenceType
    , sourceTermOccurrencePresentation
    , sourceTermOccurrenceProvider
    , sourceTermOccurrenceOrderedPair
    , sourceTermProviderHead
    , sourceTermProviderArguments
    , weakenScopedSourceTermOccurrence
    , alignScopedSourceTermOccurrence
    , countedAlignScopedSourceTermOccurrence
    , countedAlignScopedSourceTermOccurrenceAt
    , replaceScopedSourceTermOccurrence
    , countedReplaceScopedSourceTermOccurrence
    , SourceTermCheckingContext(..)
    , SourceTermSealError(..)
    , checkCanonicalSourceTerm
    , countedSealCanonicalSourceTermOccurrence
    , sealCanonicalSourceTermOccurrence
    , shiftCanonicalSourceTermOccurrence
    , countedShiftCanonicalSourceTermOccurrence
    , instantiateCanonicalSourceTermOccurrence
    , instantiateCanonicalSourceTermOccurrenceAt
    , normalizeCanonicalSourceTermOccurrence
    , forgetScopedSourceTermOccurrence
    , SourceTemplateFailure(..)
    , encodeScopedSourceTemplate
    , sourceSupportTemplate
    ) where

import Base
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity (FieldId, ObjectId)
import Felix.Checking.Semantic

import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Maybe qualified as Maybe
import Data.Word (Word)
import Data.Bifunctor (first)
import Data.Functor.Identity (Identity(..))
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


data SourceTermOccurrence presentation term = SourceTermOccurrence
    { sourceTermOccurrenceCore :: !term
    , sourceTermOccurrenceType :: !CoreType
    , sourceTermOccurrencePresentation :: presentation
    , sourceTermOccurrenceConstruction
        :: !(Maybe (SourceTermConstruction presentation term))
    }

data SourceTermConstruction presentation term
    = SourceProviderConstruction
        !(SourceTermProvider presentation term)
    | SourceOrderedPairConstruction
        !(SourceTermOccurrence presentation term)
        !(SourceTermOccurrence presentation term)

data SourceTermProvider presentation term = SourceTermProvider
    { sourceTermProviderHead :: !SourceProviderHead
    , sourceTermProviderArguments
        :: !(Vector (SourceTermOccurrence presentation term))
    }

sourceSupportTemplate
    :: (term -> CanonicalTerm ObjectId) -> SourceTermOccurrence presentation term -> SupportTermTemplate
sourceSupportTemplate core source = case sourceTermOccurrenceConstruction source of
    Just (SourceProviderConstruction provider) -> TemplateProvider (sourceTermProviderHead provider)
        (sourceSupportTemplate core <$> sourceTermProviderArguments provider)
    Just (SourceOrderedPairConstruction a b) -> TemplateOrderedPair (sourceSupportTemplate core a) (sourceSupportTemplate core b)
    Nothing -> TemplateVariable (core (sourceTermOccurrenceCore source))

sourceTermOccurrence
    :: term
    -> CoreType
    -> presentation
    -> SourceTermOccurrence presentation term
sourceTermOccurrence core coreType presentation =
    SourceTermOccurrence core coreType presentation Nothing

sourceGlobalProviderTermOccurrence
    :: GlobalBindingRef
    -> Vector (SourceTermOccurrence presentation term)
    -> term
    -> presentation
    -> Maybe (SourceTermOccurrence presentation term)
sourceGlobalProviderTermOccurrence reference arguments core presentation = do
    providerType <- semanticGlobalKeyType (globalBindingRefKey reference)
    (arity, resultType) <- firstOrderSymbolShape providerType
    guard
        ( resultType == TySet
          && arity == Vector.length arguments
          && all ((== TySet) . sourceTermOccurrenceType) arguments
        )
    pure
        (providerTermOccurrence
            (GlobalSourceProvider reference)
            arguments core presentation)

sourceStructureFieldProviderTermOccurrence
    :: FieldId
    -> ObjectId
    -> SourceTermOccurrence presentation (CanonicalTerm ObjectId)
    -> presentation
    -> Maybe
        (SourceTermOccurrence presentation (CanonicalTerm ObjectId))
sourceStructureFieldProviderTermOccurrence identity projection receiver presentation
    | sourceTermOccurrenceType receiver == TySet =
        Just
            (providerTermOccurrence
                (StructureFieldSourceProvider identity projection)
                (Vector.singleton receiver)
                (CApp (CGlobal projection) (sourceTermOccurrenceCore receiver))
                presentation)
    | otherwise = Nothing

sourceIntrinsicProviderTermOccurrence
    :: IntrinsicProviderId
    -> Vector
        (SourceTermOccurrence presentation (CanonicalTerm global))
    -> presentation
    -> Maybe
        (SourceTermOccurrence presentation (CanonicalTerm global))
sourceIntrinsicProviderTermOccurrence provider arguments presentation = do
    guard (all ((== TySet) . sourceTermOccurrenceType) arguments)
    core <- intrinsicProviderApplication
        provider
        (sourceTermOccurrenceCore <$> arguments)
    pure
        (providerTermOccurrence
            (IntrinsicSourceProvider provider)
            arguments core presentation)

-- | Mint or reconstruct the exact rich identity of one written nonempty
-- finite-set literal.  The checked Core is derived from the retained spine;
-- callers cannot attach the identity to an arbitrary equal Core term.
sourceFiniteSetLiteralTermOccurrence
    :: NonEmpty
        (SourceTermOccurrence presentation (CanonicalTerm global))
    -> presentation
    -> Maybe
        (SourceTermOccurrence presentation (CanonicalTerm global))
sourceFiniteSetLiteralTermOccurrence elements presentation = do
    let arguments = Vector.fromList (toList elements)
    guard (all ((== TySet) . sourceTermOccurrenceType) arguments)
    let core = finiteSetLiteralProviderApplication
            (sourceTermOccurrenceCore <$> elements)
    pure
        (providerTermOccurrence
            FiniteSetLiteralSourceProvider
            arguments core presentation)

providerTermOccurrence
    :: SourceProviderHead
    -> Vector (SourceTermOccurrence presentation term)
    -> term
    -> presentation
    -> SourceTermOccurrence presentation term
providerTermOccurrence providerHead arguments core presentation =
    SourceTermOccurrence core TySet presentation
        (Just
            (SourceProviderConstruction
                (SourceTermProvider providerHead arguments)))

-- | Retain the dedicated written ordered-pair construction.  Pair identity is
-- available only when both checked arguments are sets; an ill-typed caller
-- cannot mint rich pair metadata independently of ordinary Core checking.
sourceOrderedPairTermOccurrence
    :: SourceTermOccurrence presentation term
    -> SourceTermOccurrence presentation term
    -> term
    -> presentation
    -> Maybe (SourceTermOccurrence presentation term)
sourceOrderedPairTermOccurrence left right core presentation
    | sourceTermOccurrenceType left == TySet
    , sourceTermOccurrenceType right == TySet =
        Just
            (SourceTermOccurrence
                core
                TySet
                presentation
                (Just (SourceOrderedPairConstruction left right)))
    | otherwise = Nothing

sourceTermOccurrenceProvider
    :: SourceTermOccurrence presentation term
    -> Maybe (SourceTermProvider presentation term)
sourceTermOccurrenceProvider occurrence =
    case sourceTermOccurrenceConstruction occurrence of
        Just (SourceProviderConstruction provider) -> Just provider
        _ -> Nothing

sourceTermOccurrenceOrderedPair
    :: SourceTermOccurrence presentation term
    -> Maybe
        ( SourceTermOccurrence presentation term
        , SourceTermOccurrence presentation term
        )
sourceTermOccurrenceOrderedPair occurrence =
    case sourceTermOccurrenceConstruction occurrence of
        Just (SourceOrderedPairConstruction left right) ->
            Just (left, right)
        _ -> Nothing

-- The recursive transformation primitive stays private.  Public operations
-- below name the checked scope transformation they perform, so a caller cannot
-- casually change Core while retaining unrelated provider evidence.
mapSourceTermOccurrenceCore
    :: (left -> right)
    -> SourceTermOccurrence presentation left
    -> SourceTermOccurrence presentation right
mapSourceTermOccurrenceCore transform =
    runIdentity . traverseSourceTermOccurrenceCore
        (\_coreType -> Identity . transform)

-- | Check or transform every retained Core in root-before-argument order.
-- Construction arguments are recursively transformed under their own recorded
-- source types; no provider or ordered-pair identity is reconstructed from the
-- transformed Core.
traverseSourceTermOccurrenceCore
    :: Applicative effect
    => (CoreType -> left -> effect right)
    -> SourceTermOccurrence presentation left
    -> effect (SourceTermOccurrence presentation right)
traverseSourceTermOccurrenceCore transform occurrence =
    SourceTermOccurrence
        <$> transform
            (sourceTermOccurrenceType occurrence)
            (sourceTermOccurrenceCore occurrence)
        <*> pure (sourceTermOccurrenceType occurrence)
        <*> pure (sourceTermOccurrencePresentation occurrence)
        <*> traverse
            traverseConstruction
            (sourceTermOccurrenceConstruction occurrence)
  where
    traverseConstruction = \case
        SourceProviderConstruction provider ->
            SourceProviderConstruction
                <$> (SourceTermProvider
                    (sourceTermProviderHead provider)
                    <$> traverse
                        (traverseSourceTermOccurrenceCore transform)
                        (sourceTermProviderArguments provider))
        SourceOrderedPairConstruction left right ->
            SourceOrderedPairConstruction
                <$> traverseSourceTermOccurrenceCore transform left
                <*> traverseSourceTermOccurrenceCore transform right

-- | Substitute a complete source occurrence when a node denotes the selected
-- binder; otherwise transform its Core and recurse through provider arguments.
-- This preserves the provider of an actual replacement term instead of
-- retaining the provider-free metadata of the abstracted binder.
substituteSourceTermOccurrenceCore
    :: (term -> Maybe (SourceTermOccurrence presentation term))
    -> (term -> term)
    -> SourceTermOccurrence presentation term
    -> SourceTermOccurrence presentation term
substituteSourceTermOccurrenceCore selectReplacement transform occurrence =
    case selectReplacement (sourceTermOccurrenceCore occurrence) of
        Just replacement -> replacement
        Nothing ->
            SourceTermOccurrence
                (transform (sourceTermOccurrenceCore occurrence))
                (sourceTermOccurrenceType occurrence)
                (sourceTermOccurrencePresentation occurrence)
                (substituteConstruction
                    <$> sourceTermOccurrenceConstruction occurrence)
  where
    substituteConstruction = \case
        SourceProviderConstruction provider ->
            SourceProviderConstruction
                (SourceTermProvider
                    (sourceTermProviderHead provider)
                    (substituteSourceTermOccurrenceCore
                        selectReplacement
                        transform
                        <$> sourceTermProviderArguments provider))
        SourceOrderedPairConstruction left right ->
            SourceOrderedPairConstruction
                (substituteSourceTermOccurrenceCore
                    selectReplacement transform left)
                (substituteSourceTermOccurrenceCore
                    selectReplacement transform right)

-- | Enter one checked binder while retaining every recursive provider argument.
weakenScopedSourceTermOccurrence
    :: CoreType
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
weakenScopedSourceTermOccurrence binderType =
    mapSourceTermOccurrenceCore (weakenCheckedScopedCore binderType)

-- | Align all checked nodes of one occurrence to a longer lexical prefix.
-- Every node must have its recorded source type, and its checked context must
-- be an exact suffix of the target context.  The only transformation is the
-- corresponding sequence of checked weakenings.
alignScopedSourceTermOccurrence
    :: [CoreType]
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> Maybe
        (SourceTermOccurrence presentation (ScopedCheckedCore global))
alignScopedSourceTermOccurrence targetContext =
    traverseSourceTermOccurrenceCore align
  where
    align expectedType scoped = do
        guard (scopedCoreType scoped == expectedType)
        let sourceContext = scopedCoreContext scoped
            difference = length targetContext - length sourceContext
        guard
            ( difference >= 0
              && drop difference targetContext == sourceContext
            )
        pure
            (foldr weakenCheckedScopedCore scoped
                (take difference targetContext))

-- | Count source nodes, recorded type checks, context alignment, and shifting
-- in one account. A rejected node rejects the whole occurrence; provider and
-- presentation metadata are retained by the existing source-tree traversal.
countedAlignScopedSourceTermOccurrence
    :: Word -> [CoreType]
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> (Either (CountedCoreFailure Void)
        (Maybe (SourceTermOccurrence presentation (ScopedCheckedCore global))), Word)
countedAlignScopedSourceTermOccurrence allowance = countedAlignScopedSourceTermOccurrenceAt allowance 0

-- | As above, retaining the innermost source-bound variables at their slots.
countedAlignScopedSourceTermOccurrenceAt
    :: Word -> Natural -> [CoreType]
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> (Either (CountedCoreFailure Void)
        (Maybe (SourceTermOccurrence presentation (ScopedCheckedCore global))), Word)
countedAlignScopedSourceTermOccurrenceAt allowance depth target occurrence =
    State.runState (Except.runExceptT (Maybe.runMaybeT
        (traverseSourceTermOccurrenceCore align occurrence))) allowance
  where
    step operation = State.lift do
        remaining <- State.get
        let (result, after) = operation remaining
        State.put after
        either Except.throwE pure result
    align expected scoped = do
        remaining <- State.get
        if remaining == 0 then State.lift (Except.throwE CountedCoreStructuralWorkExhausted)
            else State.put (remaining - 1)
        matches <- step (\work -> countedCoreTypeIdentity work expected (scopedCoreType scoped))
        guard matches
        aligned <- step (\work -> countedAlignScopedCoreAt work depth target scoped)
        Maybe.MaybeT (pure aligned)

-- | Apply one checked, same-context replacement to a retained source tree.
-- An opaque occurrence of the selected term inherits the replacement's source
-- metadata. An existing written provider/pair keeps its own identity, even if
-- its Core happens to equal the target (for example a transparent identity).
-- Replacements beneath opaque Core binders are capture-safe but do not expose
-- new source children. A changed erased argument still counts as a source
-- change, even when the enclosing Core is unchanged.
replaceScopedSourceTermOccurrence
    :: Eq global
    => ScopedCheckedCore global
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> Either ScopedOccurrenceReplacementError
        (Maybe (SourceTermOccurrence presentation (ScopedCheckedCore global)))
replaceScopedSourceTermOccurrence target replacement =
    replaceScopedSourceTermUsing (pure ())
        (replaceScopedCoreOccurrence target (sourceTermOccurrenceCore replacement))
        (pure . (== target)) replacement

countedReplaceScopedSourceTermOccurrence
    :: Eq global
    => Word -> ScopedCheckedCore global
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> (Either (CountedCoreFailure ScopedOccurrenceReplacementError)
        (Maybe (SourceTermOccurrence presentation (ScopedCheckedCore global))), Word)
countedReplaceScopedSourceTermOccurrence allowance target replacement occurrence =
    State.runState (Except.runExceptT
        (replaceScopedSourceTermUsing charge replace same replacement occurrence)) allowance
  where
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwE CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    step operation = do
        remaining <- State.get
        let (result, after) = operation remaining
        State.put after
        either Except.throwE pure result
    replace current = step (\available -> countedReplaceScopedCoreOccurrence available
        target (sourceTermOccurrenceCore replacement) current)
    same current = step (\available -> first (first (fmap absurd))
        (countedScopedCoreIdentity available current target))

-- Both entry points use the same source-tree traversal and ownership rules.
replaceScopedSourceTermUsing
    :: Monad m
    => m ()
    -> (ScopedCheckedCore global -> m (Maybe (ScopedCoreReplacement global)))
    -> (ScopedCheckedCore global -> m Bool)
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> m (Maybe (SourceTermOccurrence presentation (ScopedCheckedCore global)))
replaceScopedSourceTermUsing charge replaceCore same replacement = go
  where
    go occurrence = do
        charge
        changedCore <- replaceCore (sourceTermOccurrenceCore occurrence)
        replaceWhole <- case sourceTermOccurrenceConstruction occurrence of
            Nothing -> same (sourceTermOccurrenceCore occurrence)
            Just{} -> pure False
        case sourceTermOccurrenceConstruction occurrence of
            Nothing | replaceWhole -> pure (Just replacement)
            construction -> do
                (changedChildren, construction') <- case construction of
                    Nothing -> pure (False, Nothing)
                    Just (SourceProviderConstruction provider) -> do
                        children <- traverse replaceChild (sourceTermProviderArguments provider)
                        pure (any fst children, Just (SourceProviderConstruction provider
                            {sourceTermProviderArguments = snd <$> children}))
                    Just (SourceOrderedPairConstruction left right) -> do
                        (changedLeft, left') <- replaceChild left
                        (changedRight, right') <- replaceChild right
                        pure (changedLeft || changedRight, Just (SourceOrderedPairConstruction left' right'))
                pure if isJust changedCore || changedChildren
                    then Just occurrence
                        { sourceTermOccurrenceCore = maybe (sourceTermOccurrenceCore occurrence)
                            scopedCoreReplacementResult changedCore
                        , sourceTermOccurrenceConstruction = construction'
                        }
                    else Nothing
    replaceChild child = maybe (False, child) (\changed -> (True, changed)) <$> go child

-- | One immutable checking snapshot for a complete sealing transaction.
-- It contains no mutable elaboration state and grants no checking authority.
data SourceTermCheckingContext global = SourceTermCheckingContext
    { sourceTermGlobalTyping :: !(GlobalTyping global)
    , sourceTermBinderTypes :: ![CoreType]
    }

data SourceTermSealError global
    = SourceTermSealCoreCheckFailed !(CanonicalTerm global) !CoreCheckError
    | SourceTermSealTypeMismatch !CoreType !CoreType
    deriving stock (Show, Eq)

-- | Check the exact raw term, without normalization or substitution. Successful
-- Core inference visits every child, including syntax a later reduction could
-- discard. A failure retains the input so the caller can report all missing
-- globals even when inference stopped at an earlier type error.
checkCanonicalSourceTerm
    :: SourceTermCheckingContext global
    -> CoreType
    -> CanonicalTerm global
    -> Either (SourceTermSealError global) (ScopedCheckedCore global)
checkCanonicalSourceTerm context expectedType term = do
    scoped <- first (SourceTermSealCoreCheckFailed term)
        (checkScopedCanonicalCore
            (sourceTermGlobalTyping context)
            (sourceTermBinderTypes context)
            term)
    unless (scopedCoreType scoped == expectedType)
        (Left (SourceTermSealTypeMismatch expectedType (scopedCoreType scoped)))
    pure scoped

-- | Seal every retained node with the same fixed checking operation and
-- snapshot. The safe Core constructor retains the identical term and context;
-- no caller-supplied evidence can be substituted beneath source metadata.
sealCanonicalSourceTermOccurrence
    :: SourceTermCheckingContext global
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> Either
        (SourceTermSealError global)
        (SourceTermOccurrence presentation (ScopedCheckedCore global))
sealCanonicalSourceTermOccurrence context =
    traverseSourceTermOccurrenceCore (checkCanonicalSourceTerm context)

-- Seal the same retained source tree under one structural allowance.
countedSealCanonicalSourceTermOccurrence
    :: Word -> SourceTermCheckingContext global
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> (Either (CountedCoreFailure (SourceTermSealError global))
        (SourceTermOccurrence presentation (ScopedCheckedCore global)), Word)
countedSealCanonicalSourceTermOccurrence allowance context occurrence =
    State.runState (Except.runExceptT (traverseSourceTermOccurrenceCore check occurrence)) allowance
  where
    step :: (Word -> (Either (CountedCoreFailure failure) value, Word))
        -> Except.ExceptT (CountedCoreFailure failure) (State.State Word) value
    step operation = do
        available <- State.get
        let (result, remaining) = operation available
        State.put remaining
        either Except.throwE pure result
    check expected term = do
        step (\work -> if work == 0 then (Left CountedCoreStructuralWorkExhausted, 0)
            else (Right (), work - 1))
        scoped <- step (\work -> first (first (fmap (SourceTermSealCoreCheckFailed term)))
            (countedCheckScopedCanonicalCore (sourceTermGlobalTyping context) work
                (sourceTermBinderTypes context) term))
        matches <- step (\work -> first (first (fmap absurd))
            (countedCoreTypeIdentity work expected (scopedCoreType scoped)))
        unless matches (Except.throwE (CountedCoreOperationFailed
            (SourceTermSealTypeMismatch expected (scopedCoreType scoped))))
        pure scoped

-- | Apply one capture-avoiding de Bruijn shift to the complete rich tree.
shiftCanonicalSourceTermOccurrence
    :: Natural
    -> Natural
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> SourceTermOccurrence presentation (CanonicalTerm global)
shiftCanonicalSourceTermOccurrence amount cutoff =
    mapSourceTermOccurrenceCore (shiftCanonical amount cutoff)

countedShiftCanonicalSourceTermOccurrence
    :: Word -> Natural -> Natural
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> (Either (CountedCoreFailure Void)
        (SourceTermOccurrence presentation (CanonicalTerm global)), Word)
countedShiftCanonicalSourceTermOccurrence allowance amount cutoff occurrence =
    State.runState (Except.runExceptT (traverseSourceTermOccurrenceCore shift occurrence)) allowance
  where
    shift _ term = do
        remaining <- State.get
        if remaining == 0 then Except.throwE CountedCoreStructuralWorkExhausted else do
            let (result, after) = countedShiftCanonical (remaining - 1) amount cutoff term
            State.put after
            either Except.throwE pure result

-- | Instantiate the nearest binder, replacing a matching source node by the
-- complete supplied occurrence and preserving its presentation and provider.
instantiateCanonicalSourceTermOccurrence
    :: SourceTermOccurrence presentation (CanonicalTerm global)
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> SourceTermOccurrence presentation (CanonicalTerm global)
instantiateCanonicalSourceTermOccurrence = instantiateCanonicalSourceTermOccurrenceAt 0

instantiateCanonicalSourceTermOccurrenceAt
    :: Natural
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> SourceTermOccurrence presentation (CanonicalTerm global)
    -> SourceTermOccurrence presentation (CanonicalTerm global)
instantiateCanonicalSourceTermOccurrenceAt depth replacement =
    substituteSourceTermOccurrenceCore
        (\core -> case core of
            CBound index | index == depth ->
                Just (shiftCanonicalSourceTermOccurrence depth 0 replacement)
            _ -> Nothing)
        (instantiateCanonicalAt depth (sourceTermOccurrenceCore replacement))

-- | Erase checked scope evidence while preserving the exact source/provider
-- construction tree.  This is used only when returning to canonical Core in a
-- scope whose alignment has already been validated.
forgetScopedSourceTermOccurrence
    :: SourceTermOccurrence presentation (ScopedCheckedCore global)
    -> SourceTermOccurrence presentation (CanonicalTerm global)
forgetScopedSourceTermOccurrence =
    mapSourceTermOccurrenceCore scopedCoreTerm

-- Scoped source abstraction for formation. The owner has checked nominal
-- source eligibility and supplies bounded context comparison and local leaf interning. Core beneath an opaque leaf is
-- never inspected to recover a provider, pair, or binder-local seed.
data SourceTemplateFailure = SourceTemplateScopeMismatch | SourceTemplateNotSet
    deriving stock (Show, Eq)

encodeScopedSourceTemplate
    :: Monad m => (Natural -> m ()) -> ([CoreType] -> [CoreType] -> m Bool)
    -> [CoreType] -> (ScopedCheckedCore ObjectId -> m variable)
    -> SourceTermOccurrence presentation (ScopedCheckedCore ObjectId)
    -> m (Either SourceTemplateFailure (SetTermTemplate variable))
encodeScopedSourceTemplate charge equalContexts context internLeaf = Except.runExceptT . encode
  where
    encode occurrence = do
        lift (charge 1)
        let core = sourceTermOccurrenceCore occurrence
        same <- lift (equalContexts context (scopedCoreContext core))
        unless same (Except.throwE SourceTemplateScopeMismatch)
        unless (scopedCoreType core == TySet && sourceTermOccurrenceType occurrence == TySet)
            (Except.throwE SourceTemplateNotSet)
        case (sourceTermOccurrenceProvider occurrence, sourceTermOccurrenceOrderedPair occurrence) of
            (Just provider, _) -> TemplateProvider (sourceTermProviderHead provider)
                <$> traverse encode (sourceTermProviderArguments provider)
            (_, Just (left,right)) -> TemplateOrderedPair <$> encode left <*> encode right
            _ -> lift (closedSetValueWith (charge 1) core) >>= \case
                Just value -> pure (TemplateClosed value)
                Nothing -> TemplateVariable <$> lift (internLeaf core)

-- Beta normalization preserves each written construction and its denotation.
-- Keep the unrestricted payload traversal private: callers cannot replace a
-- Core value while silently retaining an unrelated provider description.
normalizeCanonicalSourceTermOccurrence
    :: Monad m => SourceTermCheckingContext ObjectId
    -> SourceTermOccurrence presentation (CanonicalTerm ObjectId)
    -> ExpansionWork m (SourceTermOccurrence presentation (CanonicalTerm ObjectId))
normalizeCanonicalSourceTermOccurrence context = traverseSourceTermOccurrenceCore normalize
  where
    typing = sourceTermGlobalTyping context
    normalize expected term = do
        checked <- expansionCoreWork (\work -> countedCheckScopedCanonicalCore typing work (sourceTermBinderTypes context) term)
        same <- expansionCoreWork (\work -> countedCoreTypeIdentity work expected (scopedCoreType checked))
        unless same (Except.throwE (ExpansionInvalid "a retained source operand changed type"))
        remaining <- State.get
        let report = Conversion.betaNormalizeChecked (Conversion.ConversionRecoveryTyping typing typing)
                (Conversion.conversionLimit remaining) checked
        State.put (remaining - Conversion.conversionCostAmount (Conversion.conversionCost report))
        case Conversion.conversionResult report of
            Right value -> pure (scopedCoreTerm value)
            Left Conversion.ConversionLimitExhausted{} -> Except.throwE (ExpansionWorkExhausted 1)
            Left failure -> Except.throwE (ExpansionInvalid (fromString (show failure)))
