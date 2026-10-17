{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The four checked rules for the bounded set-valued least fixed point.
module Felix.Checking.Kernel.SetLfp
    ( setLfpBound
    , setLfpLeast
    , setLfpFixed
    , setLfpInduct
    , setLfpTerm
    , memberProposition
    , subsetProposition
    , boundedMonoProposition
    , inductionClosureProposition
    , SetLfpRuleError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)

import Data.Bifunctor (first)
import Numeric.Natural (Natural)


data SetLfpRuleError
    = SetLfpRuleSignatureMismatch
        !KernelRuleTag
        !KernelRuleSignature
        !KernelRuleSignature
    | SetLfpRuleContextMismatch
        !KernelRuleTag
        ![CoreType]
        ![CoreType]
    | SetLfpRuleArgumentTypeMismatch
        !KernelRuleTag
        !Natural
        !CoreType
        !CoreType
    | SetLfpRulePremiseIsNotProposition
        !KernelRuleTag
        !Natural
        !CoreType
    | SetLfpRulePremiseMismatch
        !KernelRuleTag
        !Natural
    | SetLfpRuleConstructionIllTyped
        !KernelRuleTag
        !CoreCheckError
    deriving stock (Show, Eq)

setLfpBound
    :: CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
setLfpBound foundation globalType domain operator = do
    validateApplication
        foundation
        SetLfpBound
        [domain, operator]
        []
    fixedPoint <-
        setLfpTermFor
            SetLfpBound
            globalType
            domain
            operator
    subsetFor
        SetLfpBound
        globalType
        fixedPoint
        domain

setLfpLeast
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
setLfpLeast
        foundation
        globalType
        domain
        operator
        candidate
        closedPremise
        boundedPremise = do
    validateApplication
        foundation
        SetLfpLeast
        [domain, operator, candidate]
        [closedPremise, boundedPremise]
    operatorCandidate <-
        applyFor
            SetLfpLeast
            globalType
            operator
            candidate
    expectedClosed <-
        subsetFor
            SetLfpLeast
            globalType
            operatorCandidate
            candidate
    expectedBounded <-
        subsetFor
            SetLfpLeast
            globalType
            candidate
            domain
    requirePremise
        SetLfpLeast
        0
        expectedClosed
        closedPremise
    requirePremise
        SetLfpLeast
        1
        expectedBounded
        boundedPremise
    fixedPoint <-
        setLfpTermFor
            SetLfpLeast
            globalType
            domain
            operator
    subsetFor
        SetLfpLeast
        globalType
        fixedPoint
        candidate

setLfpFixed
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
setLfpFixed
        foundation
        globalType
        domain
        operator
        monotonePremise = do
    validateApplication
        foundation
        SetLfpFixed
        [domain, operator]
        [monotonePremise]
    expectedMonotone <-
        boundedMonoFor
            SetLfpFixed
            globalType
            domain
            operator
    requirePremise
        SetLfpFixed
        0
        expectedMonotone
        monotonePremise
    fixedPoint <-
        setLfpTermFor
            SetLfpFixed
            globalType
            domain
            operator
    unfolded <-
        applyFor
            SetLfpFixed
            globalType
            operator
            fixedPoint
    checkedFor
        SetLfpFixed
        globalType
        (scopedCoreContext domain)
        (CEq
            TySet
            (scopedCoreTerm fixedPoint)
            (scopedCoreTerm unfolded))

setLfpInduct
    :: Eq global
    => CheckedFoundation
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
setLfpInduct
        foundation
        globalType
        domain
        operator
        predicate
        element
        monotonePremise
        memberPremise
        closurePremise = do
    validateApplication
        foundation
        SetLfpInduct
        [domain, operator, predicate, element]
        [monotonePremise, memberPremise, closurePremise]
    expectedMonotone <-
        boundedMonoFor
            SetLfpInduct
            globalType
            domain
            operator
    requirePremise
        SetLfpInduct
        0
        expectedMonotone
        monotonePremise
    fixedPoint <-
        setLfpTermFor
            SetLfpInduct
            globalType
            domain
            operator
    expectedMember <-
        memberFor
            SetLfpInduct
            globalType
            element
            fixedPoint
    requirePremise
        SetLfpInduct
        1
        expectedMember
        memberPremise
    expectedClosure <-
        inductionClosureFor
            SetLfpInduct
            globalType
            fixedPoint
            operator
            predicate
    requirePremise
        SetLfpInduct
        2
        expectedClosure
        closurePremise
    applyFor
        SetLfpInduct
        globalType
        predicate
        element

setLfpTerm
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
setLfpTerm =
    setLfpTermFor SetLfpBound

memberProposition
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
memberProposition =
    memberFor SetLfpInduct

subsetProposition
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
subsetProposition =
    subsetFor SetLfpBound

boundedMonoProposition
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
boundedMonoProposition =
    boundedMonoFor SetLfpFixed

inductionClosureProposition
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
inductionClosureProposition globalType domain operator predicate = do
    fixedPoint <-
        setLfpTermFor
            SetLfpInduct
            globalType
            domain
            operator
    inductionClosureFor
        SetLfpInduct
        globalType
        fixedPoint
        operator
        predicate

validateApplication
    :: CheckedFoundation
    -> KernelRuleTag
    -> [ScopedCheckedCore global]
    -> [ScopedCheckedCore global]
    -> Either SetLfpRuleError ()
validateApplication foundation tag arguments premises = do
    let expected =
            expectedSignature tag
        actual =
            foundationRuleSignature foundation tag
    if actual == expected
        then pure ()
        else
            Left
                (SetLfpRuleSignatureMismatch
                    tag
                    expected
                    actual)
    case arguments of
        [] ->
            pure ()
        firstArgument : remainingArguments -> do
            traverse_
                (requireContext tag firstArgument)
                remainingArguments
            traverse_
                (requireContext tag firstArgument)
                premises
    traverse_
        (uncurry
            (requireArgumentType tag))
        (zip [0 ..] arguments)
    traverse_
        (uncurry
            (requireProposition tag))
        (zip [0 ..] premises)

expectedSignature :: KernelRuleTag -> KernelRuleSignature
expectedSignature = \case
    SetLfpBound ->
        KernelRuleSignature
            [TySet, TySet `TyArrow` TySet]
            0
    SetLfpLeast ->
        KernelRuleSignature
            [TySet, TySet `TyArrow` TySet, TySet]
            2
    SetLfpFixed ->
        KernelRuleSignature
            [TySet, TySet `TyArrow` TySet]
            1
    SetLfpInduct ->
        KernelRuleSignature
            [ TySet
            , TySet `TyArrow` TySet
            , TySet `TyArrow` TyProp
            , TySet
            ]
            3

expectedArgumentTypes
    :: KernelRuleTag
    -> [CoreType]
expectedArgumentTypes tag =
    case expectedSignature tag of
        KernelRuleSignature argumentTypes _premiseCount ->
            argumentTypes

requireContext
    :: KernelRuleTag
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either SetLfpRuleError ()
requireContext tag expected actual
    | scopedCoreContext expected
        == scopedCoreContext actual =
            Right ()
    | otherwise =
        Left
            (SetLfpRuleContextMismatch
                tag
                (scopedCoreContext expected)
                (scopedCoreContext actual))

requireArgumentType
    :: KernelRuleTag
    -> Natural
    -> ScopedCheckedCore global
    -> Either SetLfpRuleError ()
requireArgumentType tag index argument =
    case nth index (expectedArgumentTypes tag) of
        Nothing ->
            impossible
                "fixed-point rule argument inventory is inconsistent"
        Just expected
            | scopedCoreType argument == expected ->
                Right ()
            | otherwise ->
                Left
                    (SetLfpRuleArgumentTypeMismatch
                        tag
                        index
                        expected
                        (scopedCoreType argument))

requireProposition
    :: KernelRuleTag
    -> Natural
    -> ScopedCheckedCore global
    -> Either SetLfpRuleError ()
requireProposition tag index premise
    | scopedCoreType premise == TyProp =
        Right ()
    | otherwise =
        Left
            (SetLfpRulePremiseIsNotProposition
                tag
                index
                (scopedCoreType premise))

requirePremise
    :: Eq global
    => KernelRuleTag
    -> Natural
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either SetLfpRuleError ()
requirePremise tag index expected actual
    | expected == actual =
        Right ()
    | otherwise =
        Left
            (SetLfpRulePremiseMismatch
                tag
                index)

setLfpTermFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
setLfpTermFor tag globalType domain operator =
    checkedFor tag globalType
        (scopedCoreContext domain)
        (CApp
            (CApp
                (CIntrinsic ISetLfp)
                (scopedCoreTerm domain))
            (scopedCoreTerm operator))

applyFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
applyFor tag globalType function argument = do
    requireContext tag function argument
    checkedFor tag globalType
        (scopedCoreContext function)
        (CApp
            (scopedCoreTerm function)
            (scopedCoreTerm argument))

memberFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
memberFor tag globalType element set = do
    requireContext tag element set
    checkedFor tag globalType
        (scopedCoreContext element)
        (CApp
            (CApp
                (CIntrinsic Member)
                (scopedCoreTerm element))
            (scopedCoreTerm set))

subsetFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
subsetFor tag globalType left right = do
    requireContext tag left right
    left' <- weakenFor tag globalType TySet left
    right' <- weakenFor tag globalType TySet right
    element <-
        checkedFor tag globalType
            (TySet : scopedCoreContext left)
            (CBound 0)
    inLeft <-
        memberFor tag globalType element left'
    inRight <-
        memberFor tag globalType element right'
    checkedFor tag globalType
        (scopedCoreContext left)
        (CForall
            TySet
            (CImp
                (scopedCoreTerm inLeft)
                (scopedCoreTerm inRight)))

boundedMonoFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
boundedMonoFor tag globalType domain operator = do
    requireContext tag domain operator
    operatorDomain <-
        applyFor tag globalType operator domain
    bounded <-
        subsetFor tag globalType operatorDomain domain

    domainX <-
        weakenFor tag globalType TySet domain
    operatorX <-
        weakenFor tag globalType TySet operator
    domainXY <-
        weakenFor tag globalType TySet domainX
    operatorXY <-
        weakenFor tag globalType TySet operatorX
    let xyContext =
            TySet : TySet : scopedCoreContext domain
    x <-
        checkedFor tag globalType
            xyContext
            (CBound 1)
    y <-
        checkedFor tag globalType
            xyContext
            (CBound 0)
    xSubsetY <-
        subsetFor tag globalType x y
    ySubsetDomain <-
        subsetFor tag globalType y domainXY
    antecedent <-
        conjunctionFor
            tag
            globalType
            xSubsetY
            ySubsetDomain
    operatorXValue <-
        applyFor tag globalType operatorXY x
    operatorYValue <-
        applyFor tag globalType operatorXY y
    imageSubset <-
        subsetFor
            tag
            globalType
            operatorXValue
            operatorYValue
    monotoneBody <-
        implicationFor
            tag
            globalType
            antecedent
            imageSubset
    quantifiedY <-
        closeForallFor tag globalType TySet monotoneBody
    quantifiedXY <-
        closeForallFor tag globalType TySet quantifiedY
    conjunctionFor
        tag
        globalType
        bounded
        quantifiedXY

inductionClosureFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
inductionClosureFor
        tag
        globalType
        fixedPoint
        operator
        predicate = do
    fixedPoint' <-
        weakenFor tag globalType TySet fixedPoint
    operator' <-
        weakenFor tag globalType TySet operator
    predicate' <-
        weakenFor tag globalType TySet predicate
    element <-
        checkedFor tag globalType
            (TySet : scopedCoreContext fixedPoint)
            (CBound 0)
    separated <-
        checkedFor tag globalType
            (scopedCoreContext fixedPoint')
            (CApp
                (CApp
                    (CIntrinsic Sep)
                    (scopedCoreTerm fixedPoint'))
                (scopedCoreTerm predicate'))
    unfolded <-
        applyFor tag globalType operator' separated
    memberUnfolded <-
        memberFor tag globalType element unfolded
    predicateElement <-
        applyFor tag globalType predicate' element
    body <-
        implicationFor
            tag
            globalType
            memberUnfolded
            predicateElement
    closeForallFor tag globalType TySet body

conjunctionFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
conjunctionFor tag globalType left right = do
    requireContext tag left right
    checkedFor tag globalType
        (scopedCoreContext left)
        (CAnd
            (scopedCoreTerm left)
            (scopedCoreTerm right))

implicationFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
implicationFor tag globalType premise conclusion = do
    requireContext tag premise conclusion
    checkedFor tag globalType
        (scopedCoreContext premise)
        (CImp
            (scopedCoreTerm premise)
            (scopedCoreTerm conclusion))

closeForallFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> CoreType
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
closeForallFor tag globalType binderType body =
    case scopedCoreContext body of
        actualBinder : outerContext
            | actualBinder == binderType ->
                checkedFor tag globalType
                    outerContext
                    (CForall
                        binderType
                        (scopedCoreTerm body))
        _ ->
            Left
                (SetLfpRuleContextMismatch
                    tag
                    (binderType : drop 1
                        (scopedCoreContext body))
                    (scopedCoreContext body))

weakenFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> CoreType
    -> ScopedCheckedCore global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
weakenFor tag globalType binderType =
    first
        (SetLfpRuleConstructionIllTyped tag)
        . weakenScopedCore
            globalType
            binderType

checkedFor
    :: KernelRuleTag
    -> GlobalTyping global
    -> [CoreType]
    -> CanonicalTerm global
    -> Either
        SetLfpRuleError
        (ScopedCheckedCore global)
checkedFor tag globalType context =
    first
        (SetLfpRuleConstructionIllTyped tag)
        . checkScopedCanonicalCore
            globalType
            context
