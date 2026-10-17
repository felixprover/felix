{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representations shared by canonical checking and resolved
-- construction. Checked-wrapper sealing is deliberately unsafe: callers must
-- already have established the type and local-context invariants.
module Felix.Checking.Core.Representation.Internal
    ( CoreType(..)
    , CoreIntrinsicTag(..)
    , CoreCheckError(..)
    , expectCoreType
    , applicationResultType
    , propositionResultType
    , propositionalOperandsResultType
    , checkImplicationOperand
    , implicationResultType
    , checkEqualityOperand
    , equalityResultType
    , quantifierResultType
    , CanonicalTerm(..)
    , FrozenCheckedCore
    , frozenCoreType
    , frozenCoreTerm
    , unsafeSealFrozenCheckedCore
    , ScopedCheckedCore
    , scopedCoreContext
    , scopedCoreType
    , scopedCoreTerm
    , unsafeSealScopedCheckedCore
    ) where

import Base hiding (Empty)

import Control.DeepSeq (NFData(..))
import Numeric.Natural (Natural)


-- | The complete monomorphic type grammar of the checked core.
data CoreType
    = TyProp
    | TySet
    | TyArrow !CoreType !CoreType
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | The complete set-forming primitive inventory.
data CoreIntrinsicTag
    = Member
    | Empty
    | PairSet
    | FamilyUnion
    | PowerSet
    | Sep
    | Repl
    | UnivOf
    -- | The bounded set-valued least fixed point. It denotes the elements of
    -- its bound that belong to every bounded pre-fixed point of its operator.
    | ISetLfp
    -- | Set-theoretic global choice from an inhabited set.
    | GlobalChoice
    -- | A foundation-level ordered pair. Unlike 'PairSet', this operation is
    -- ordered and is governed by injectivity and projection laws.
    | OrderedPair
    | FirstProjection
    | SecondProjection
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Syntax-independent checked-Core typing failures. Keeping the premise
-- vocabulary beside 'CoreType' lets canonical and resolved checking share one
-- rule owner without introducing an upward dependency into this module.
data CoreCheckError
    = UnknownCoreGlobal
    | UnboundCoreIndex !Natural
    | AppliedNonFunction !CoreType
    | ApplicationArgumentTypeMismatch
        !CoreType
        !CoreType
    | ImplicationOperandTypeMismatch
        !CoreType
    | EqualityOperandTypeMismatch
        !CoreType
        !CoreType
    | QuantifierBodyTypeMismatch
        !CoreType
    | ExpectedCoreType
        !CoreType
        !CoreType
    deriving stock (Show, Eq)

expectCoreType
    :: CoreType
    -> CoreType
    -> Either CoreCheckError ()
expectCoreType expected actual
    | expected == actual =
        Right ()
    | otherwise =
        Left (ExpectedCoreType expected actual)

applicationResultType
    :: CoreType
    -> CoreType
    -> Either CoreCheckError CoreType
applicationResultType functionType argumentType =
    case functionType of
        TyArrow expectedArgument resultType
            | expectedArgument == argumentType ->
                Right resultType
            | otherwise ->
                Left
                    (ApplicationArgumentTypeMismatch
                        expectedArgument
                        argumentType)
        other ->
            Left (AppliedNonFunction other)

propositionResultType
    :: CoreType
    -> Either CoreCheckError CoreType
propositionResultType actual = do
    expectCoreType TyProp actual
    pure TyProp

propositionalOperandsResultType
    :: CoreType
    -> CoreType
    -> Either CoreCheckError CoreType
propositionalOperandsResultType left right = do
    _ <- propositionResultType left
    propositionResultType right

implicationResultType
    :: CoreType
    -> CoreType
    -> Either CoreCheckError CoreType
implicationResultType premise conclusion = do
    checkImplicationOperand premise
    checkImplicationOperand conclusion
    pure TyProp

checkImplicationOperand
    :: CoreType
    -> Either CoreCheckError ()
checkImplicationOperand actual
    | actual == TyProp =
        Right ()
    | otherwise =
        Left (ImplicationOperandTypeMismatch actual)

equalityResultType
    :: CoreType
    -> CoreType
    -> CoreType
    -> Either CoreCheckError CoreType
equalityResultType operandType left right = do
    checkEqualityOperand operandType left
    checkEqualityOperand operandType right
    pure TyProp

checkEqualityOperand
    :: CoreType
    -> CoreType
    -> Either CoreCheckError ()
checkEqualityOperand operandType actual
    | actual == operandType =
        Right ()
    | otherwise =
        Left
            (EqualityOperandTypeMismatch
                operandType
                actual)

quantifierResultType
    :: CoreType
    -> Either CoreCheckError CoreType
quantifierResultType bodyType
    | bodyType == TyProp =
        Right TyProp
    | otherwise =
        Left (QuantifierBodyTypeMismatch bodyType)

-- | Felix-owned explicit-index syntax. Index zero denotes the nearest
-- enclosing binder.
data CanonicalTerm global
    = CBound !Natural
    | CGlobal !global
    | CIntrinsic !CoreIntrinsicTag
    | CLogicalSelect !CoreType
    | COpaqueInteger !Integer
    | CApp
        !(CanonicalTerm global)
        !(CanonicalTerm global)
    | CLam
        !CoreType
        !(CanonicalTerm global)
    | CFalsum
    | CTruth
    | CNot
        !(CanonicalTerm global)
    | CAnd
        !(CanonicalTerm global)
        !(CanonicalTerm global)
    | COr
        !(CanonicalTerm global)
        !(CanonicalTerm global)
    | CImp
        !(CanonicalTerm global)
        !(CanonicalTerm global)
    | CEq
        !CoreType
        !(CanonicalTerm global)
        !(CanonicalTerm global)
    | CForall
        !CoreType
        !(CanonicalTerm global)
    | CExists
        !CoreType
        !(CanonicalTerm global)
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

type role FrozenCheckedCore nominal
data FrozenCheckedCore global = FrozenCheckedCore
    !CoreType
    !(CanonicalTerm global)
    deriving stock (Show, Eq, Ord)

instance NFData global => NFData (FrozenCheckedCore global) where
    rnf (FrozenCheckedCore coreType term) =
        rnf coreType `seq` rnf term

frozenCoreType :: FrozenCheckedCore global -> CoreType
frozenCoreType (FrozenCheckedCore coreType _term) =
    coreType

frozenCoreTerm :: FrozenCheckedCore global -> CanonicalTerm global
frozenCoreTerm (FrozenCheckedCore _coreType term) =
    term

unsafeSealFrozenCheckedCore
    :: CoreType
    -> CanonicalTerm global
    -> FrozenCheckedCore global
unsafeSealFrozenCheckedCore =
    FrozenCheckedCore

-- | A checked canonical term relative to the listed nearest-first binders.
-- This is the construction boundary used by kernel replay; it carries no fact
-- authority.
type role ScopedCheckedCore nominal
data ScopedCheckedCore global = ScopedCheckedCore
    ![CoreType]
    !CoreType
    !(CanonicalTerm global)
    deriving stock (Show, Eq, Ord)

instance NFData global => NFData (ScopedCheckedCore global) where
    rnf (ScopedCheckedCore context coreType term) =
        rnf context `seq` rnf coreType `seq` rnf term

scopedCoreContext
    :: ScopedCheckedCore global
    -> [CoreType]
scopedCoreContext
        (ScopedCheckedCore context _coreType _term) =
    context

scopedCoreType
    :: ScopedCheckedCore global
    -> CoreType
scopedCoreType
        (ScopedCheckedCore _context coreType _term) =
    coreType

scopedCoreTerm
    :: ScopedCheckedCore global
    -> CanonicalTerm global
scopedCoreTerm
        (ScopedCheckedCore _context _coreType term) =
    term

unsafeSealScopedCheckedCore
    :: [CoreType]
    -> CoreType
    -> CanonicalTerm global
    -> ScopedCheckedCore global
unsafeSealScopedCheckedCore =
    ScopedCheckedCore
