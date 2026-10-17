{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Package-hidden stable-local syntax, checked assembly, and closed freezing.
-- Lifecycle controllers establish scope activity before calling this module.
module Felix.Checking.Core.Resolved.Substrate.Internal
    ( LocalId
    , ScopeId
    , LocalRef
    , CheckedExpr
    , ResolvedFreezeError
    , localIdFromOrdinalInternal
    , localOrdinalInternal
    , scopeIdFromOrdinalInternal
    , scopeOrdinalInternal
    , makeLocalRefInternal
    , localRefScopeInternal
    , localRefType
    , checkedExprOwnerInternal
    , checkedExprType
    , makeLocalExprInternal
    , makeGlobalExprInternal
    , makeEmbeddedExprInternal
    , makeIntrinsicExprInternal
    , makeFalsumExprInternal
    , makeApplicationExprInternal
    , makeLambdaExprInternal
    , makeNegationExprInternal
    , makeConjunctionExprInternal
    , makeDisjunctionExprInternal
    , makeImplicationExprInternal
    , makeEqualityExprInternal
    , makeForallExprInternal
    , makeExistsExprInternal
    , freezeClosedExprInternal
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
    ( CanonicalTerm(..)
    , CoreCheckError
    , CoreIntrinsicTag
    , CoreType(..)
    , FrozenCheckedCore
    , coreIntrinsicType
    , frozenCoreTerm
    , frozenCoreType
    )
import Felix.Checking.Core.Representation.Internal
    ( applicationResultType
    , equalityResultType
    , implicationResultType
    , propositionResultType
    , propositionalOperandsResultType
    , quantifierResultType
    )
import Felix.Checking.Core.Representation.Internal qualified as Representation
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , lookupGlobalType
    )

import Data.IntMap.Strict qualified as IntMap
import Numeric.Natural (Natural)


type role LocalId nominal
newtype LocalId region = LocalId Int
    deriving stock (Eq)

type role ScopeId nominal
newtype ScopeId region = ScopeId Int
    deriving stock (Eq)

type role LocalRef nominal
data LocalRef region = LocalRef
    !(ScopeId region)
    !(LocalId region)
    !CoreType

type role ResolvedTerm nominal nominal
data ResolvedTerm region global
    = RLocal !(LocalId region)
    | RGlobal !global
    | RIntrinsic !CoreIntrinsicTag
    | REmbedClosed !(FrozenCheckedCore global)
    | RApp
        !(ResolvedTerm region global)
        !(ResolvedTerm region global)
    | RLam
        !(LocalId region)
        !CoreType
        !(ResolvedTerm region global)
    | RFalsum
    | RNot !(ResolvedTerm region global)
    | RAnd
        !(ResolvedTerm region global)
        !(ResolvedTerm region global)
    | ROr
        !(ResolvedTerm region global)
        !(ResolvedTerm region global)
    | RImp
        !(ResolvedTerm region global)
        !(ResolvedTerm region global)
    | REq
        !CoreType
        !(ResolvedTerm region global)
        !(ResolvedTerm region global)
    | RForall
        !(LocalId region)
        !CoreType
        !(ResolvedTerm region global)
    | RExists
        !(LocalId region)
        !CoreType
        !(ResolvedTerm region global)

type role CheckedExpr nominal nominal
data CheckedExpr region global = CheckedExpr
    !(ScopeId region)
    !CoreType
    !(ResolvedTerm region global)

data ResolvedFreezeError
    = ResolvedLocalMissing !Int !Natural
    | ResolvedBinderDuplicate !Int
    | ResolvedLevelOutOfScope !Int !Natural !Natural

localIdFromOrdinalInternal :: Int -> LocalId region
localIdFromOrdinalInternal =
    LocalId

localOrdinalInternal :: LocalId region -> Int
localOrdinalInternal (LocalId identity) =
    identity

scopeIdFromOrdinalInternal :: Int -> ScopeId region
scopeIdFromOrdinalInternal =
    ScopeId

scopeOrdinalInternal :: ScopeId region -> Int
scopeOrdinalInternal (ScopeId identity) =
    identity

makeLocalRefInternal
    :: ScopeId region
    -> LocalId region
    -> CoreType
    -> LocalRef region
makeLocalRefInternal =
    LocalRef

localRefScopeInternal :: LocalRef region -> ScopeId region
localRefScopeInternal (LocalRef scope _local _coreType) =
    scope

localRefType :: LocalRef region -> CoreType
localRefType (LocalRef _scope _local coreType) =
    coreType

localRefIdentity :: LocalRef region -> LocalId region
localRefIdentity (LocalRef _scope local _coreType) =
    local

checkedExprOwnerInternal
    :: CheckedExpr region global
    -> ScopeId region
checkedExprOwnerInternal (CheckedExpr owner _coreType _term) =
    owner

checkedExprType :: CheckedExpr region global -> CoreType
checkedExprType (CheckedExpr _owner coreType _term) =
    coreType

checkedExprTerm
    :: CheckedExpr region global
    -> ResolvedTerm region global
checkedExprTerm (CheckedExpr _owner _coreType term) =
    term

makeLocalExprInternal
    :: ScopeId region
    -> LocalRef region
    -> CheckedExpr region global
makeLocalExprInternal owner localRef =
    CheckedExpr
        owner
        (localRefType localRef)
        (RLocal (localRefIdentity localRef))

makeGlobalExprInternal
    :: GlobalTyping global
    -> ScopeId region
    -> global
    -> Maybe (CheckedExpr region global)
makeGlobalExprInternal globalTyping owner global = do
    coreType <- lookupGlobalType globalTyping global
    pure (CheckedExpr owner coreType (RGlobal global))

makeEmbeddedExprInternal
    :: ScopeId region
    -> FrozenCheckedCore global
    -> CheckedExpr region global
makeEmbeddedExprInternal owner frozen =
    CheckedExpr
        owner
        (frozenCoreType frozen)
        (REmbedClosed frozen)

makeIntrinsicExprInternal
    :: ScopeId region
    -> CoreIntrinsicTag
    -> CheckedExpr region global
makeIntrinsicExprInternal owner intrinsic =
    CheckedExpr
        owner
        (coreIntrinsicType intrinsic)
        (RIntrinsic intrinsic)

makeFalsumExprInternal
    :: ScopeId region
    -> CheckedExpr region global
makeFalsumExprInternal owner =
    CheckedExpr owner TyProp RFalsum

makeApplicationExprInternal
    :: ScopeId region
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeApplicationExprInternal owner function argument = do
    resultType <-
        applicationResultType
            (checkedExprType function)
            (checkedExprType argument)
    pure
        (CheckedExpr
            owner
            resultType
            (RApp
                (checkedExprTerm function)
                (checkedExprTerm argument)))

makeLambdaExprInternal
    :: ScopeId region
    -> LocalRef region
    -> CheckedExpr region global
    -> CheckedExpr region global
makeLambdaExprInternal owner localRef body =
    CheckedExpr
        owner
        (TyArrow (localRefType localRef) (checkedExprType body))
        (RLam
            (localRefIdentity localRef)
            (localRefType localRef)
            (checkedExprTerm body))

makeNegationExprInternal
    :: ScopeId region
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeNegationExprInternal owner proposition = do
    resultType <- propositionResultType (checkedExprType proposition)
    pure
        (CheckedExpr
            owner
            resultType
            (RNot (checkedExprTerm proposition)))

makeConjunctionExprInternal
    :: ScopeId region
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeConjunctionExprInternal =
    makePropositionalBinaryExpr RAnd

makeDisjunctionExprInternal
    :: ScopeId region
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeDisjunctionExprInternal =
    makePropositionalBinaryExpr ROr

makeImplicationExprInternal
    :: ScopeId region
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeImplicationExprInternal owner premise conclusion = do
    resultType <-
        implicationResultType
            (checkedExprType premise)
            (checkedExprType conclusion)
    pure
        (CheckedExpr
            owner
            resultType
            (RImp
                (checkedExprTerm premise)
                (checkedExprTerm conclusion)))

makeEqualityExprInternal
    :: ScopeId region
    -> CoreType
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeEqualityExprInternal owner operandType left right = do
    resultType <-
        equalityResultType
            operandType
            (checkedExprType left)
            (checkedExprType right)
    pure
        (CheckedExpr
            owner
            resultType
            (REq
                operandType
                (checkedExprTerm left)
                (checkedExprTerm right)))

makeForallExprInternal
    :: ScopeId region
    -> LocalRef region
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeForallExprInternal =
    makeQuantifierExpr RForall

makeExistsExprInternal
    :: ScopeId region
    -> LocalRef region
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeExistsExprInternal =
    makeQuantifierExpr RExists

makePropositionalBinaryExpr
    :: (ResolvedTerm region global
        -> ResolvedTerm region global
        -> ResolvedTerm region global)
    -> ScopeId region
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makePropositionalBinaryExpr construct owner left right = do
    resultType <-
        propositionalOperandsResultType
            (checkedExprType left)
            (checkedExprType right)
    pure
        (CheckedExpr
            owner
            resultType
            (construct
                (checkedExprTerm left)
                (checkedExprTerm right)))

makeQuantifierExpr
    :: (LocalId region
        -> CoreType
        -> ResolvedTerm region global
        -> ResolvedTerm region global)
    -> ScopeId region
    -> LocalRef region
    -> CheckedExpr region global
    -> Either CoreCheckError (CheckedExpr region global)
makeQuantifierExpr construct owner localRef body = do
    resultType <- quantifierResultType (checkedExprType body)
    pure
        (CheckedExpr
            owner
            resultType
            (construct
                (localRefIdentity localRef)
                (localRefType localRef)
                (checkedExprTerm body)))

freezeClosedExprInternal
    :: CheckedExpr region global
    -> Either ResolvedFreezeError (FrozenCheckedCore global)
freezeClosedExprInternal checked = do
    term <- freezeResolved (Depth 0) IntMap.empty (checkedExprTerm checked)
    pure
        (Representation.unsafeSealFrozenCheckedCore
            (checkedExprType checked)
            term)

newtype Depth = Depth Natural
newtype Lvl = Lvl Natural

nextDepth :: Depth -> Depth
nextDepth (Depth depth) =
    Depth (depth + 1)

lvlToIndex :: Depth -> Lvl -> Maybe Natural
lvlToIndex (Depth depth) (Lvl level)
    | level < depth =
        Just (depth - level - 1)
    | otherwise =
        Nothing

freezeResolved
    :: Depth
    -> IntMap.IntMap Lvl
    -> ResolvedTerm region global
    -> Either ResolvedFreezeError (CanonicalTerm global)
freezeResolved depth binders = \case
    RLocal local ->
        case IntMap.lookup (localOrdinalInternal local) binders of
            Nothing ->
                Left
                    (ResolvedLocalMissing
                        (localOrdinalInternal local)
                        (depthNatural depth))
            Just level ->
                case lvlToIndex depth level of
                    Just index ->
                        pure (CBound index)
                    Nothing ->
                        Left
                            (ResolvedLevelOutOfScope
                                (localOrdinalInternal local)
                                (lvlNatural level)
                                (depthNatural depth))
    RGlobal global ->
        pure (CGlobal global)
    RIntrinsic intrinsic ->
        pure (CIntrinsic intrinsic)
    REmbedClosed frozen ->
        pure (frozenCoreTerm frozen)
    RApp function argument ->
        CApp
            <$> freezeResolved depth binders function
            <*> freezeResolved depth binders argument
    RLam local binderType body ->
        freezeBinder CLam depth binders local binderType body
    RFalsum ->
        pure CFalsum
    RNot proposition ->
        CNot <$> freezeResolved depth binders proposition
    RAnd left right ->
        CAnd
            <$> freezeResolved depth binders left
            <*> freezeResolved depth binders right
    ROr left right ->
        COr
            <$> freezeResolved depth binders left
            <*> freezeResolved depth binders right
    RImp premise conclusion ->
        CImp
            <$> freezeResolved depth binders premise
            <*> freezeResolved depth binders conclusion
    REq operandType left right ->
        CEq operandType
            <$> freezeResolved depth binders left
            <*> freezeResolved depth binders right
    RForall local binderType body ->
        freezeBinder CForall depth binders local binderType body
    RExists local binderType body ->
        freezeBinder CExists depth binders local binderType body

freezeBinder
    :: (CoreType
        -> CanonicalTerm global
        -> CanonicalTerm global)
    -> Depth
    -> IntMap.IntMap Lvl
    -> LocalId region
    -> CoreType
    -> ResolvedTerm region global
    -> Either ResolvedFreezeError (CanonicalTerm global)
freezeBinder construct depth binders local binderType body
    | localOrdinalInternal local `IntMap.member` binders =
        Left (ResolvedBinderDuplicate (localOrdinalInternal local))
    | otherwise =
        construct binderType
            <$> freezeResolved
                (nextDepth depth)
                (IntMap.insert
                    (localOrdinalInternal local)
                    (Lvl (depthNatural depth))
                    binders)
                body

depthNatural :: Depth -> Natural
depthNatural (Depth depth) =
    depth

lvlNatural :: Lvl -> Natural
lvlNatural (Lvl level) =
    level
