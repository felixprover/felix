{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Deliberately independent test oracle for the stable-local builder. The
-- direct fold below does not call Core's checker, freezer, or shared premise
-- rules. Production interpretation uses only the exposed safe builder API.
module Felix.Test.Support.BindingReference
    ( SymbolicKey(..)
    , SymbolicTerm(..)
    , BindingReferenceError(..)
    , BindingBuildError(..)
    , referenceClosed
    , buildClosed
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.Resolved qualified as Resolved

import Data.Bifunctor (first)
import Data.List qualified as List
import Numeric.Natural (Natural)


data SymbolicKey = SymbolicKey !String !Int
    deriving stock (Show, Eq, Ord)

data SymbolicTerm
    = SymbolicLocal !SymbolicKey
    | SymbolicIntrinsic !CoreIntrinsicTag
    | SymbolicApply !SymbolicTerm !SymbolicTerm
    | SymbolicLambda !SymbolicKey !CoreType !SymbolicTerm
    | SymbolicFalsum
    | SymbolicNot !SymbolicTerm
    | SymbolicAnd !SymbolicTerm !SymbolicTerm
    | SymbolicOr !SymbolicTerm !SymbolicTerm
    | SymbolicEquality !CoreType !SymbolicTerm !SymbolicTerm
    | SymbolicForAll !SymbolicKey !CoreType !SymbolicTerm
    | SymbolicExists !SymbolicKey !CoreType !SymbolicTerm
    | SymbolicImply !SymbolicTerm !SymbolicTerm
    deriving stock (Show, Eq)

data BindingReferenceError
    = ReferenceUnboundLocal !SymbolicKey
    | ReferenceAppliedNonFunction !CoreType
    | ReferenceApplicationArgumentMismatch !CoreType !CoreType
    | ReferencePropositionOperandMismatch !CoreType
    | ReferenceEqualityOperandMismatch !CoreType !CoreType
    | ReferenceQuantifierBodyMismatch !CoreType
    deriving stock (Show, Eq)

data BindingBuildError
    = BindingReferenceRejected !BindingReferenceError
    | BindingProductionRejected !(Resolved.CoreBuilderError Void)
    deriving stock (Show, Eq)

referenceClosed
    :: SymbolicTerm
    -> Either
        BindingReferenceError
        (CoreType, CanonicalTerm Void)
referenceClosed =
    inferReference []

buildClosed
    :: SymbolicTerm
    -> Either BindingBuildError (FrozenCheckedCore Void)
buildClosed term = do
    _ <- first BindingReferenceRejected (referenceClosed term)
    first BindingProductionRejected
        (Resolved.runClosedBuilderVoid
            (interpretReference [] term))

type ReferenceContext = [(SymbolicKey, CoreType)]

inferReference
    :: ReferenceContext
    -> SymbolicTerm
    -> Either
        BindingReferenceError
        (CoreType, CanonicalTerm Void)
inferReference context = \case
    SymbolicLocal key ->
        case referenceLocal key context of
            Nothing ->
                Left (ReferenceUnboundLocal key)
            Just (index, coreType) ->
                Right (coreType, CBound index)
    SymbolicIntrinsic intrinsic ->
        Right
            ( referenceIntrinsicType intrinsic
            , CIntrinsic intrinsic
            )
    SymbolicApply function argument -> do
        (functionType, functionTerm) <-
            inferReference context function
        (argumentType, argumentTerm) <-
            inferReference context argument
        case functionType of
            TyArrow expectedArgument resultType
                | expectedArgument == argumentType ->
                    Right
                        ( resultType
                        , CApp functionTerm argumentTerm
                        )
                | otherwise ->
                    Left
                        (ReferenceApplicationArgumentMismatch
                            expectedArgument
                            argumentType)
            other ->
                Left (ReferenceAppliedNonFunction other)
    SymbolicLambda key binderType body -> do
        (bodyType, bodyTerm) <-
            inferReference ((key, binderType) : context) body
        Right
            ( TyArrow binderType bodyType
            , CLam binderType bodyTerm
            )
    SymbolicFalsum ->
        Right (TyProp, CFalsum)
    SymbolicNot proposition -> do
        (propositionType, propositionTerm) <-
            inferReference context proposition
        requireProposition propositionType
        Right (TyProp, CNot propositionTerm)
    SymbolicAnd left right ->
        inferPropositionalBinary CAnd context left right
    SymbolicOr left right ->
        inferPropositionalBinary COr context left right
    SymbolicEquality operandType left right -> do
        (leftType, leftTerm) <-
            inferReference context left
        requireEqualityOperand operandType leftType
        (rightType, rightTerm) <-
            inferReference context right
        requireEqualityOperand operandType rightType
        Right (TyProp, CEq operandType leftTerm rightTerm)
    SymbolicForAll key binderType body -> do
        (bodyType, bodyTerm) <-
            inferReference ((key, binderType) : context) body
        if bodyType == TyProp
            then
                Right (TyProp, CForall binderType bodyTerm)
            else
                Left (ReferenceQuantifierBodyMismatch bodyType)
    SymbolicExists key binderType body -> do
        (bodyType, bodyTerm) <-
            inferReference ((key, binderType) : context) body
        if bodyType == TyProp
            then
                Right (TyProp, CExists binderType bodyTerm)
            else
                Left (ReferenceQuantifierBodyMismatch bodyType)
    SymbolicImply premise conclusion -> do
        (premiseType, premiseTerm) <-
            inferReference context premise
        requireProposition premiseType
        (conclusionType, conclusionTerm) <-
            inferReference context conclusion
        requireProposition conclusionType
        Right (TyProp, CImp premiseTerm conclusionTerm)

inferPropositionalBinary
    :: (CanonicalTerm Void
        -> CanonicalTerm Void
        -> CanonicalTerm Void)
    -> ReferenceContext
    -> SymbolicTerm
    -> SymbolicTerm
    -> Either
        BindingReferenceError
        (CoreType, CanonicalTerm Void)
inferPropositionalBinary construct context left right = do
    (leftType, leftTerm) <- inferReference context left
    requireProposition leftType
    (rightType, rightTerm) <- inferReference context right
    requireProposition rightType
    Right (TyProp, construct leftTerm rightTerm)

requireProposition
    :: CoreType
    -> Either BindingReferenceError ()
requireProposition coreType
    | coreType == TyProp =
        Right ()
    | otherwise =
        Left (ReferencePropositionOperandMismatch coreType)

requireEqualityOperand
    :: CoreType
    -> CoreType
    -> Either BindingReferenceError ()
requireEqualityOperand expected actual
    | actual == expected =
        Right ()
    | otherwise =
        Left (ReferenceEqualityOperandMismatch expected actual)

referenceLocal
    :: SymbolicKey
    -> ReferenceContext
    -> Maybe (Natural, CoreType)
referenceLocal wanted =
    go 0
  where
    go _index [] =
        Nothing
    go index ((key, coreType) : remaining)
        | key == wanted =
            Just (index, coreType)
        | otherwise =
            go (index + 1) remaining

-- Kept independent of 'coreIntrinsicType' on purpose. Adding an intrinsic to
-- Core must make this test oracle non-exhaustive until its test rule is added.
referenceIntrinsicType :: CoreIntrinsicTag -> CoreType
referenceIntrinsicType = \case
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

type BuilderContext region =
    [(SymbolicKey, Resolved.LocalRef region)]

interpretReference
    :: BuilderContext region
    -> SymbolicTerm
    -> Resolved.CoreBuilder region Void
        (Resolved.CheckedExpr region Void)
interpretReference context = \case
    SymbolicLocal key ->
        Resolved.useLocal (resolvedLocal key context)
    SymbolicIntrinsic intrinsic ->
        Resolved.intrinsic intrinsic
    SymbolicApply function argument -> do
        functionExpr <- interpretReference context function
        argumentExpr <- interpretReference context argument
        Resolved.apply functionExpr argumentExpr
    SymbolicLambda key binderType body ->
        Resolved.lambda binderType \local ->
            interpretReference ((key, local) : context) body
    SymbolicFalsum ->
        Resolved.falsum
    SymbolicNot proposition -> do
        propositionExpr <- interpretReference context proposition
        Resolved.negation propositionExpr
    SymbolicAnd left right -> do
        leftExpr <- interpretReference context left
        rightExpr <- interpretReference context right
        Resolved.conjunction leftExpr rightExpr
    SymbolicOr left right -> do
        leftExpr <- interpretReference context left
        rightExpr <- interpretReference context right
        Resolved.disjunction leftExpr rightExpr
    SymbolicEquality operandType left right -> do
        leftExpr <- interpretReference context left
        rightExpr <- interpretReference context right
        Resolved.equality operandType leftExpr rightExpr
    SymbolicForAll key binderType body ->
        Resolved.forAll binderType \local ->
            interpretReference ((key, local) : context) body
    SymbolicExists key binderType body ->
        Resolved.exists binderType \local ->
            interpretReference ((key, local) : context) body
    SymbolicImply premise conclusion -> do
        premiseExpr <- interpretReference context premise
        conclusionExpr <- interpretReference context conclusion
        Resolved.imply premiseExpr conclusionExpr

resolvedLocal
    :: SymbolicKey
    -> BuilderContext region
    -> Resolved.LocalRef region
resolvedLocal wanted context =
    case List.lookup wanted context of
        Just local ->
            local
        Nothing ->
            impossible
                "validated symbolic binding disappeared during interpretation"
