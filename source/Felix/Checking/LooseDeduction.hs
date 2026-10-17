{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The bounded, source-oriented part of loose deduction used by proof
-- assumption steps. This module only decides which checked conjunction leaves
-- may be consumed and how the residual goal keeps its source shape. Kernel
-- composition is deliberately owned by Felix.Checking.Kernel.Proof.
module Felix.Checking.LooseDeduction
    ( ConjunctionSide(..)
    , ConjunctionLeafPath
    , ConjunctionView(..)
    , FrontierPremise(..)
    , FrontierRemainder(..)
    , AssumptionFrontier(..)
    , FrontierOccurrence(..)
    , SelectedFrontierLeaf(..)
    , ResidualPositivePremise(..)
    , AssumptionOpeningKind(..)
    , DetailedAssumptionOpening(..)
    , AssumptionOpening(..)
    , AssumptionOpeningReplayError(..)
    , AssumptionOpeningInputError(..)
    , AssumptionOpeningMismatch(..)
    , AssumptionOpeningFailure(..)
    , findAssumptionOpening
    , compactAssumptionOpening
    , validateAssumptionOpening
    , deleteSelectedLeaves
    , conjunctionViewCore
    ) where

import Base
import Felix.Checking.Core

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)


data ConjunctionSide
    = ConjunctionLeft
    | ConjunctionRight
    deriving stock (Show, Eq, Ord)

type ConjunctionLeafPath = [ConjunctionSide]

data ConjunctionView a
    = ConjunctionLeaf a
    | ConjunctionBranch
        (ConjunctionView a)
        (ConjunctionView a)
    deriving stock (Show, Eq, Ord)

data FrontierPremise a = FrontierPremise
    { frontierPremiseTree :: !(ConjunctionView a)
    }
    deriving stock (Show, Eq, Ord)

data FrontierRemainder a
    = OrdinaryRemainder a
    | TerminalNegationRemainder
    deriving stock (Show, Eq, Ord)

data AssumptionFrontier a = AssumptionFrontier
    { frontierPositivePremises :: ![FrontierPremise a]
    , frontierNegativePremise :: !(Maybe (ConjunctionView a))
    , frontierRemainder :: !(FrontierRemainder a)
    }
    deriving stock (Show, Eq, Ord)

data FrontierOccurrence
    = PositiveFrontierOccurrence !Natural !ConjunctionLeafPath
    | NegativeFrontierOccurrence !ConjunctionLeafPath
    deriving stock (Show, Eq, Ord)

data SelectedFrontierLeaf a = SelectedFrontierLeaf
    { selectedSuppliedPath :: !ConjunctionLeafPath
    , selectedFrontierOccurrence :: !FrontierOccurrence
    , selectedLeafValue :: !a
    }
    deriving stock (Show, Eq, Ord)

data ResidualPositivePremise a = ResidualPositivePremise
    { residualPositiveIndex :: !Natural
    , residualPositiveTree :: !(Maybe (ConjunctionView a))
    }
    deriving stock (Show, Eq, Ord)

data AssumptionOpeningKind
    = DirectImplicationOpening
    | DirectNegationOpening
    | ClassicalDisjunctionOpening
    | ConjunctiveFrontierOpening
    deriving stock (Show, Eq, Ord, Enum, Bounded)

data DetailedAssumptionOpening global = DetailedAssumptionOpening
    { detailedOpeningKind :: !AssumptionOpeningKind
    , detailedOpeningGoal :: !(ScopedCheckedCore global)
    , detailedOpeningSupplied :: !(ScopedCheckedCore global)
    , detailedOpeningResidual :: !(ScopedCheckedCore global)
    , detailedSuppliedTree :: !(ConjunctionView (ScopedCheckedCore global))
    , detailedOpeningFrontier
        :: !(AssumptionFrontier (ScopedCheckedCore global))
    , detailedSelectedLeaves
        :: ![SelectedFrontierLeaf (ScopedCheckedCore global)]
    , detailedResidualPositivePremises
        :: ![ResidualPositivePremise (ScopedCheckedCore global)]
    , detailedResidualNegativePremise
        :: !(Maybe (ConjunctionView (ScopedCheckedCore global)))
    }
    deriving stock (Show, Eq, Ord)

data AssumptionOpening global = AssumptionOpening
    { assumptionOpeningKind :: !AssumptionOpeningKind
    , assumptionOpeningGoal :: !(ScopedCheckedCore global)
    , assumptionOpeningSupplied :: !(ScopedCheckedCore global)
    , assumptionOpeningResidual :: !(ScopedCheckedCore global)
    }
    deriving stock (Show, Eq, Ord)

data AssumptionOpeningReplayError
    = AssumptionOpeningReplayMismatch
    deriving stock (Show, Eq, Ord)

data AssumptionOpeningInputError
    = AssumptionGoalNotProposition !CoreType
    | AssumptionSuppliedNotProposition !CoreType
    | AssumptionContextMismatch
    deriving stock (Show, Eq, Ord)

data AssumptionOpeningMismatch global
    = AssumptionNoSupportedFrontier
    | AssumptionClassicalDisjunctionMismatch
        { requiredClassicalAssumption
            :: !(ScopedCheckedCore global)
        }
    | AssumptionPartUnavailable
        { unavailableAssumptionPart
            :: !(ScopedCheckedCore global)
        , availableAssumptionParts
            :: !(NonEmpty (ScopedCheckedCore global))
        }
    | AssumptionInsufficientMultiplicity
        { repeatedAssumptionPart
            :: !(ScopedCheckedCore global)
        , requiredOccurrences :: !Natural
        , availableOccurrences :: !Natural
        }
    deriving stock (Show, Eq, Ord)

data AssumptionOpeningFailure global
    = AssumptionOpeningInvalidInput
        !AssumptionOpeningInputError
    | AssumptionOpeningDoesNotMatch
        !(AssumptionOpeningMismatch global)
    deriving stock (Show, Eq, Ord)

findAssumptionOpening
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        (AssumptionOpeningFailure global)
        (DetailedAssumptionOpening global)
findAssumptionOpening supplied goal =
    case assumptionOpeningInputError supplied goal of
        Just failure ->
            Left (AssumptionOpeningInvalidInput failure)
        Nothing ->
            case directOpening supplied goal of
                Just opening ->
                    Right opening
                Nothing ->
                    case classicalDisjunctionOpening supplied goal of
                        Just opening ->
                            Right opening
                        Nothing ->
                            case classicalDisjunctionExpected goal of
                                Just expected ->
                                    Left
                                        (AssumptionOpeningDoesNotMatch
                                            (AssumptionClassicalDisjunctionMismatch
                                                expected))
                                Nothing ->
                                    case frontierOpening supplied goal of
                                        Left mismatch ->
                                            Left
                                                (AssumptionOpeningDoesNotMatch
                                                    mismatch)
                                        Right opening ->
                                            Right opening

assumptionOpeningInputError
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe AssumptionOpeningInputError
assumptionOpeningInputError supplied goal
    | scopedCoreType goal /= TyProp =
        Just (AssumptionGoalNotProposition (scopedCoreType goal))
    | scopedCoreType supplied /= TyProp =
        Just (AssumptionSuppliedNotProposition (scopedCoreType supplied))
    | scopedCoreContext supplied /= scopedCoreContext goal =
        Just AssumptionContextMismatch
    | otherwise =
        Nothing

compactAssumptionOpening
    :: DetailedAssumptionOpening global
    -> AssumptionOpening global
compactAssumptionOpening detailed =
    AssumptionOpening
        { assumptionOpeningKind = detailedOpeningKind detailed
        , assumptionOpeningGoal = detailedOpeningGoal detailed
        , assumptionOpeningSupplied = detailedOpeningSupplied detailed
        , assumptionOpeningResidual = detailedOpeningResidual detailed
        }

validateAssumptionOpening
    :: Eq global
    => AssumptionOpening global
    -> Either AssumptionOpeningReplayError ()
validateAssumptionOpening opening =
    case findAssumptionOpening
            (assumptionOpeningSupplied opening)
            (assumptionOpeningGoal opening) of
        Right detailed
            | compactAssumptionOpening detailed == opening ->
                Right ()
        _ -> Left AssumptionOpeningReplayMismatch

deleteSelectedLeaves
    :: Set.Set ConjunctionLeafPath
    -> ConjunctionView a
    -> Maybe (ConjunctionView a)
deleteSelectedLeaves selected =
    go []
  where
    go path (ConjunctionLeaf value)
        | Set.member path selected =
            Nothing
        | otherwise =
            Just (ConjunctionLeaf value)
    go path (ConjunctionBranch left right) =
        case
            ( go (path <> [ConjunctionLeft]) left
            , go (path <> [ConjunctionRight]) right
            ) of
            (Nothing, Nothing) -> Nothing
            (Just remaining, Nothing) -> Just remaining
            (Nothing, Just remaining) -> Just remaining
            (Just remainingLeft, Just remainingRight) ->
                Just (ConjunctionBranch remainingLeft remainingRight)

conjunctionViewCore
    :: Eq global
    => ConjunctionView (ScopedCheckedCore global)
    -> Maybe (ScopedCheckedCore global)
conjunctionViewCore (ConjunctionLeaf value) =
    Just value
conjunctionViewCore (ConjunctionBranch left right) = do
    leftCore <- conjunctionViewCore left
    rightCore <- conjunctionViewCore right
    conjoinScopedCore leftCore rightCore

directOpening
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (DetailedAssumptionOpening global)
directOpening supplied goal = do
    frontier <- makeFrontier goal
    case scopedCoreTerm goal of
        CImp{} -> do
            (antecedent, conclusion) <- openScopedImplication goal
            guard (supplied == antecedent)
            pure
                (direct
                    DirectImplicationOpening
                    supplied
                    goal
                    frontier
                    conclusion)
        CNot{} -> do
            proposition <- splitScopedNegation goal
            guard (supplied == proposition)
            pure
                (direct
                    DirectNegationOpening
                    supplied
                    goal
                    frontier
                    (falsumScopedCore (scopedCoreContext goal)))
        _ ->
            Nothing
  where
    direct kind supplied' goal' frontier' residual =
        directOpeningResult kind supplied' goal' frontier' residual

classicalDisjunctionOpening
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (DetailedAssumptionOpening global)
classicalDisjunctionOpening supplied goal = do
    frontier <- makeFrontier goal
    (left, right) <- splitScopedDisjunction goal
    expected <- negateScopedCore left
    guard (supplied == expected)
    pure
        (directOpeningResult
            ClassicalDisjunctionOpening
            supplied
            goal
            frontier
            right)

classicalDisjunctionExpected
    :: ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
classicalDisjunctionExpected goal = do
    (left, _right) <- splitScopedDisjunction goal
    negateScopedCore left

directOpeningResult
    :: AssumptionOpeningKind
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> AssumptionFrontier (ScopedCheckedCore global)
    -> ScopedCheckedCore global
    -> DetailedAssumptionOpening global
directOpeningResult kind supplied goal frontier residual =
    DetailedAssumptionOpening
        { detailedOpeningKind = kind
        , detailedOpeningGoal = goal
        , detailedOpeningSupplied = supplied
        , detailedOpeningResidual = residual
        , detailedSuppliedTree = conjunctionTree supplied
        , detailedOpeningFrontier = frontier
        , detailedSelectedLeaves = []
        , detailedResidualPositivePremises = []
        , detailedResidualNegativePremise = Nothing
        }

frontierOpening
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        (AssumptionOpeningMismatch global)
        (DetailedAssumptionOpening global)
frontierOpening supplied goal =
    case makeFrontier goal of
        Nothing ->
            Left AssumptionNoSupportedFrontier
        Just frontier ->
            let suppliedTree = conjunctionTree supplied
                suppliedLeaves = leafOccurrences suppliedTree
                candidates = frontierOccurrences frontier
            in if null candidates
                then Left AssumptionNoSupportedFrontier
                else do
                    selected <- matchLeaves suppliedLeaves candidates
                    let positiveSelections =
                            Map.fromListWith Set.union
                                [ (index, Set.singleton path)
                                | SelectedFrontierLeaf
                                        _suppliedPath
                                        (PositiveFrontierOccurrence index path)
                                        _value <- selected
                                ]
                        negativeSelections =
                            Set.fromList
                                [ path
                                | SelectedFrontierLeaf
                                        _suppliedPath
                                        (NegativeFrontierOccurrence path)
                                        _value <- selected
                                ]
                        residualPositive =
                            [ ResidualPositivePremise index
                                ( deleteSelectedLeaves
                                    (Map.findWithDefault Set.empty index positiveSelections)
                                    (frontierPremiseTree premise))
                            | (index, premise) <-
                                zip [0 :: Natural ..] (frontierPositivePremises frontier)
                            ]
                        residualNegative =
                            case frontierNegativePremise frontier of
                                Nothing ->
                                    Nothing
                                Just tree ->
                                    deleteSelectedLeaves negativeSelections tree
                    case rebuildResidual
                            frontier
                            residualPositive
                            residualNegative of
                        Nothing ->
                            Left AssumptionNoSupportedFrontier
                        Just residual ->
                            Right
                                (DetailedAssumptionOpening
                                    { detailedOpeningKind =
                                        ConjunctiveFrontierOpening
                                    , detailedOpeningGoal = goal
                                    , detailedOpeningSupplied = supplied
                                    , detailedOpeningResidual = residual
                                    , detailedSuppliedTree = suppliedTree
                                    , detailedOpeningFrontier = frontier
                                    , detailedSelectedLeaves = selected
                                    , detailedResidualPositivePremises =
                                        residualPositive
                                    , detailedResidualNegativePremise =
                                        residualNegative
                                    })

makeFrontier
    :: ScopedCheckedCore global
    -> Maybe (AssumptionFrontier (ScopedCheckedCore global))
makeFrontier goal = do
    (positive, remainder) <- stripImplications [] goal
    case splitScopedNegation remainder of
        Just negated ->
            pure
                (AssumptionFrontier
                    (FrontierPremise . conjunctionTree <$> positive)
                    (Just (conjunctionTree negated))
                    TerminalNegationRemainder)
        Nothing ->
            pure
                (AssumptionFrontier
                    (FrontierPremise . conjunctionTree <$> positive)
                    Nothing
                    (OrdinaryRemainder remainder))
  where
    stripImplications reversed current =
        case openScopedImplication current of
            Just (premise, conclusion) ->
                stripImplications (premise : reversed) conclusion
            Nothing ->
                Just (reverse reversed, current)

rebuildResidual
    :: Eq global
    => AssumptionFrontier (ScopedCheckedCore global)
    -> [ResidualPositivePremise (ScopedCheckedCore global)]
    -> Maybe (ConjunctionView (ScopedCheckedCore global))
    -> Maybe (ScopedCheckedCore global)
rebuildResidual frontier residualPositive residualNegative = do
    remainder <-
        case frontierRemainder frontier of
            OrdinaryRemainder proposition ->
                Just proposition
            TerminalNegationRemainder ->
                case residualNegative of
                    Nothing ->
                        Just
                            (falsumScopedCore
                                (frontierContext frontier))
                    Just tree -> do
                        proposition <- conjunctionViewCore tree
                        negateScopedCore proposition
    foldrM addRemainder remainder residualPositive
  where
    addRemainder
            (ResidualPositivePremise _index maybeTree)
            continuation =
        case maybeTree of
            Nothing ->
                Just continuation
            Just tree -> do
                premise <- conjunctionViewCore tree
                implyScopedCore premise continuation

frontierContext
    :: AssumptionFrontier (ScopedCheckedCore global)
    -> [CoreType]
frontierContext frontier =
    case frontierPositivePremises frontier of
        FrontierPremise tree : _ ->
            conjunctionViewContext tree
        [] ->
            case frontierNegativePremise frontier of
                Just tree ->
                    conjunctionViewContext tree
                Nothing ->
                    case frontierRemainder frontier of
                        OrdinaryRemainder proposition ->
                            scopedCoreContext proposition
                        TerminalNegationRemainder ->
                            []
  where
    conjunctionViewContext (ConjunctionLeaf proposition) =
        scopedCoreContext proposition
    conjunctionViewContext (ConjunctionBranch left _right) =
        conjunctionViewContext left

frontierOccurrences
    :: AssumptionFrontier (ScopedCheckedCore global)
    -> [(FrontierOccurrence, ScopedCheckedCore global)]
frontierOccurrences frontier =
    positive <> negative
  where
    positive =
        [ (PositiveFrontierOccurrence index path, proposition)
        | (index, FrontierPremise tree) <-
            zip [0 :: Natural ..] (frontierPositivePremises frontier)
        , (path, proposition) <- leafOccurrences tree
        ]
    negative =
        [ (NegativeFrontierOccurrence path, proposition)
        | Just tree <- [frontierNegativePremise frontier]
        , (path, proposition) <- leafOccurrences tree
        ]

matchLeaves
    :: Eq global
    => [(ConjunctionLeafPath, ScopedCheckedCore global)]
    -> [(FrontierOccurrence, ScopedCheckedCore global)]
    -> Either
        (AssumptionOpeningMismatch global)
        [SelectedFrontierLeaf (ScopedCheckedCore global)]
matchLeaves _supplied [] =
    Left AssumptionNoSupportedFrontier
matchLeaves supplied candidates =
    go Set.empty supplied []
  where
    go _used [] selected =
        Right (reverse selected)
    go used ((suppliedPath, suppliedValue) : rest) selected = do
        let matching =
                [ (occurrence, candidateValue)
                | (occurrence, candidateValue) <- candidates
                , candidateValue == suppliedValue
                ]
            available =
                [ (occurrence, candidateValue)
                | (occurrence, candidateValue) <- matching
                , Set.notMember occurrence used
                ]
            required =
                1 + fromIntegral
                    (length
                        [ ()
                        | SelectedFrontierLeaf
                                _previousPath
                                _previousOccurrence
                                previousValue <- selected
                        , previousValue == suppliedValue
                        ])
        case (matching, available) of
            ([], _) ->
                Left
                    (AssumptionPartUnavailable
                        suppliedValue
                        (candidateValues candidates))
            (_ : _, []) ->
                Left
                    (AssumptionInsufficientMultiplicity
                        suppliedValue
                        required
                        (fromIntegral (length matching)))
            (candidate : _, _ : _) -> do
                let (occurrence, _value) = candidate
                go
                    (Set.insert occurrence used)
                    rest
                    ( SelectedFrontierLeaf
                        suppliedPath occurrence suppliedValue
                        : selected)

    candidateValues [] =
        impossible "a nonempty frontier lost all candidate values"
    candidateValues ((_, value) : rest) =
        value :| [candidateValue | (_, candidateValue) <- rest]

leafOccurrences
    :: ConjunctionView a
    -> [(ConjunctionLeafPath, a)]
leafOccurrences =
    go []
  where
    go path (ConjunctionLeaf value) =
        [(path, value)]
    go path (ConjunctionBranch left right) =
        go (path <> [ConjunctionLeft]) left
            <> go (path <> [ConjunctionRight]) right

conjunctionTree
    :: ScopedCheckedCore global
    -> ConjunctionView (ScopedCheckedCore global)
conjunctionTree proposition =
    case splitScopedConjunction proposition of
        Nothing ->
            ConjunctionLeaf proposition
        Just (left, right) ->
            ConjunctionBranch
                (conjunctionTree left)
                (conjunctionTree right)
