{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Immutable, branch-local equality reference engine over the frozen search
-- catalogue.  It retains only shallow IDs and generic proof labels; the
-- refutation coordinator owns proof-reason construction and scheduling.
module Felix.Checking.Obvious.Equality
    ( EqualityFailure(..)
    , EqualityDirection(..)
    , EqualityStep(..)
    , EqualityPath(..)
    , equalityPathSource
    , equalityPathTarget
    , equalityPathSteps
    , EqualityClash(..)
    , CongruenceRequest(..)
    , EqualityState
    , initializeEqualityState
    , makeTermVisible
    , recordEquality
    , recordEqualityWithSupport
    , recordDisequality
    , recordPolarity
    , equalityPath
    , equalitySupportedPath
    , equalityRefreshPending
    , refreshCongruence
    ) where

import Base
import Felix.Checking.Obvious.Search

import Control.Monad (foldM, unless)
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Word (Word)


data EqualityFailure
    = EqualityWorkExhausted
    | EqualityUnknownTerm !TermId
    | EqualityTypeMismatch !TermId !TermId
    | EqualityMalformedApplication !TermId
    deriving stock (Show, Eq)

data EqualityDirection
    = EqualityForward
    | EqualityReverse
    deriving stock (Show, Eq, Ord)

data EqualityStep reason = EqualityStep
    !reason
    !EqualityDirection

data EqualityPath reason = EqualityPath
    !TermId
    !TermId
    ![EqualityStep reason]

equalityPathSteps :: EqualityPath reason -> [EqualityStep reason]
equalityPathSteps (EqualityPath _source _target steps) = steps

equalityPathSource :: EqualityPath reason -> TermId
equalityPathSource (EqualityPath source _target _steps) = source

equalityPathTarget :: EqualityPath reason -> TermId
equalityPathTarget (EqualityPath _source target _steps) = target

data EqualityClash reason
    = EqualityDisequalityClash
        !(EqualityPath reason)
        !reason
    | EqualityPropositionClash
        !reason
        !reason
        !(EqualityPath reason)

data CongruenceRequest reason = CongruenceRequest
    !TermId
    !TermId
    !(EqualityPath reason)
    !(EqualityPath reason)

data EqualityNeighbor reason = EqualityNeighbor
    !TermId
    !(EqualityStep reason)

data Disequality reason = Disequality
    !TermId
    !TermId
    !reason

data PolarityWitness reason = PolarityWitness
    !TermId
    !FormulaId
    !reason

data EqualityState reason = EqualityState
    { equalityVisibleTerms :: !(Set TermId)
    , equalityEdgePairs :: !(Set (TermId, TermId))
    , equalityAdjacency :: !(Map TermId (Seq (EqualityNeighbor reason)))
    -- Nothing means the ordinary map already contains every explanation.
    -- The first alternate derives a full view by persistent sharing; later
    -- insertions maintain both views without changing ordinary predecessors.
    , equalityExplanationAdjacency :: !(Maybe (Map TermId (Seq (EqualityNeighbor reason))))
    , equalityDisequalities :: !(Seq (Disequality reason))
    , equalityDisequalityPairs :: !(Set (TermId, TermId))
    , equalityTrueWitnesses :: !(Seq (PolarityWitness reason))
    , equalityFalseWitnesses :: !(Seq (PolarityWitness reason))
    , equalityTrueTerms :: !(Set TermId)
    , equalityFalseTerms :: !(Set TermId)
    , equalityCongruencePairs :: !(Set (TermId, TermId))
    , equalityHasPendingRefresh :: !Bool
    }

emptyEqualityState :: EqualityState reason
emptyEqualityState =
    EqualityState
        { equalityVisibleTerms = Set.empty
        , equalityEdgePairs = Set.empty
        , equalityAdjacency = Map.empty
        , equalityExplanationAdjacency = Nothing
        , equalityDisequalities = Seq.empty
        , equalityDisequalityPairs = Set.empty
        , equalityTrueWitnesses = Seq.empty
        , equalityFalseWitnesses = Seq.empty
        , equalityTrueTerms = Set.empty
        , equalityFalseTerms = Set.empty
        , equalityCongruencePairs = Set.empty
        , equalityHasPendingRefresh = False
        }

type Counted value = Except.ExceptT EqualityFailure (State Word) value

runCounted
    :: Word
    -> Counted value
    -> (Either EqualityFailure value, Word)
runCounted available action =
    State.runState (Except.runExceptT action) available

charge :: Counted ()
charge = do
    remaining <- State.get
    if remaining == 0
        then Except.throwE EqualityWorkExhausted
        else State.put (remaining - 1)

-- Both traversals see incident edges in their original admission order.
-- Index lookup and each visited entry have separate structural charges.
neighborsC :: EqualityState reason -> TermId -> Counted (Seq (EqualityNeighbor reason))
neighborsC state term = do
    charge
    pure (Map.findWithDefault Seq.empty term (equalityAdjacency state))

lookupTermC
    :: Catalogue global
    -> TermId
    -> Counted (CatalogueTerm global)
lookupTermC catalogue termId = do
    charge
    maybe
        (Except.throwE (EqualityUnknownTerm termId))
        pure
        (catalogueTerm catalogue termId)

orderedPair :: TermId -> TermId -> (TermId, TermId)
orderedPair left right
    | left <= right = (left, right)
    | otherwise = (right, left)

initializeEqualityState
    :: Word
    -> Catalogue global
    -> (Either EqualityFailure (EqualityState reason), Word)
initializeEqualityState available catalogue =
    runCounted available do
        foldM admit emptyEqualityState termIds
  where
    termIds =
        [ TermId position
        | position <- [0 .. fromIntegral (catalogueTermCount catalogue) - 1]
        ]

    admit state termId = do
        term <- lookupTermC catalogue termId
        charge
        pure
            state
                { equalityVisibleTerms =
                    Set.insert termId (equalityVisibleTerms state)
                , equalityHasPendingRefresh =
                    equalityHasPendingRefresh state
                        || isJust (catalogueTermApplication term)
                }

makeTermVisible
    :: Word
    -> Catalogue global
    -> TermId
    -> EqualityState reason
    -> (Either EqualityFailure (EqualityState reason), Word)
makeTermVisible available catalogue termId state =
    runCounted available do
        charge
        if termId `Set.member` equalityVisibleTerms state
            then pure state
            else do
                term <- lookupTermC catalogue termId
                pure
                    state
                        { equalityVisibleTerms =
                            Set.insert termId (equalityVisibleTerms state)
                        , equalityHasPendingRefresh =
                            equalityHasPendingRefresh state
                                || isJust (catalogueTermApplication term)
                        }

equalityPath
    :: Word
    -> Catalogue global
    -> EqualityState reason
    -> TermId
    -> TermId
    -> (Either EqualityFailure (Maybe (EqualityPath reason)), Word)
equalityPath available catalogue state source target =
    runCounted available (pathC catalogue state source target)

pathC
    :: Catalogue global
    -> EqualityState reason
    -> TermId
    -> TermId
    -> Counted (Maybe (EqualityPath reason))
pathC catalogue state source target = do
    sourceTerm <- lookupTermC catalogue source
    targetTerm <- lookupTermC catalogue target
    unless
        (catalogueTermTypeId sourceTerm == catalogueTermTypeId targetTerm)
        (Except.throwE (EqualityTypeMismatch source target))
    if source == target
        then pure (Just (EqualityPath source target []))
        else
            search
                (Set.singleton source)
                Map.empty
                (Seq.singleton source)
  where
    search visited predecessors queue = do
        charge
        case Seq.viewl queue of
            Seq.EmptyL -> pure Nothing
            current Seq.:< rest -> do
                adjacent <- neighborsC state current
                (updatedVisited, updatedPredecessors, updatedQueue) <-
                    scanEdges
                        current visited predecessors rest
                        (Seq.viewl adjacent)
                if target `Set.member` updatedVisited
                    then
                        Just . EqualityPath source target
                            <$> rebuild updatedPredecessors target []
                    else
                        search
                            updatedVisited updatedPredecessors updatedQueue

    scanEdges _current visited predecessors queue Seq.EmptyL =
        pure (visited, predecessors, queue)
    scanEdges current visited predecessors queue
            (EqualityNeighbor next step Seq.:< rest) = do
        charge
        let (nextVisited, nextPredecessors, nextQueue) =
                admitNeighbor current
                    (visited, predecessors, queue)
                    (next, step)
        scanEdges
            current nextVisited nextPredecessors nextQueue
            (Seq.viewl rest)

    admitNeighbor previous (visited, predecessors, queue)
            (next, step)
        | next `Set.member` visited = (visited, predecessors, queue)
        | otherwise =
            ( Set.insert next visited
            , Map.insert next (previous, step) predecessors
            , queue Seq.|> next
            )

    rebuild predecessors current steps
        | current == source = pure steps
        | otherwise = do
            charge
            case Map.lookup current predecessors of
                Nothing ->
                    Except.throwE (EqualityUnknownTerm current)
                Just (previous, step) ->
                    rebuild predecessors previous (step : steps)

-- The resolver supplies an already completed supported certificate for the
-- same oriented edge. It is read only during this counted query, never retained
-- by the equality state. Visiting (term, support-seen) preserves supported loops
-- without assigning support to an unused reflexivity proof.
equalitySupportedPath
    :: Word -> Catalogue global -> (reason -> Maybe reason)
    -> EqualityState reason -> TermId -> TermId
    -> (Either EqualityFailure (Maybe (EqualityPath reason)), Word)
equalitySupportedPath available catalogue supported state source target = runCounted available do
    sourceTerm <- lookupTermC catalogue source
    targetTerm <- lookupTermC catalogue target
    unless (catalogueTermTypeId sourceTerm == catalogueTermTypeId targetTerm)
        (Except.throwE (EqualityTypeMismatch source target))
    search (Set.singleton (source, False)) Map.empty (Seq.singleton (source, False))
  where
    destination = (target, True)
    search visited predecessors queue = do
        charge
        case Seq.viewl queue of
            Seq.EmptyL -> pure Nothing
            current Seq.:< rest -> do
                charge
                let incident = Map.findWithDefault Seq.empty (fst current)
                        (fromMaybe (equalityAdjacency state) (equalityExplanationAdjacency state))
                (seen, paths, pending) <- scanEdges current visited predecessors rest (Seq.viewl incident)
                if Set.member destination seen
                    then Just . EqualityPath source target <$> rebuild paths destination []
                    else search seen paths pending
    scanEdges _ visited predecessors queue Seq.EmptyL = pure (visited, predecessors, queue)
    scanEdges current@(_, seenSupport) visited predecessors queue
            (EqualityNeighbor neighbor (EqualityStep reason direction) Seq.:< rest) = do
        charge
        let canonical = supported reason
            selected = fromMaybe reason canonical
            withSupport = seenSupport || isJust canonical
            (seen, paths, pending) = admit current (visited, predecessors, queue)
                ((neighbor, withSupport), EqualityStep selected direction)
        scanEdges current seen paths pending (Seq.viewl rest)
    admit previous (visited, predecessors, queue) (next, step)
        | Set.member next visited = (visited, predecessors, queue)
        | otherwise = (Set.insert next visited, Map.insert next (previous, step) predecessors, queue Seq.|> next)
    rebuild predecessors current steps
        | current == (source, False) = pure steps
        | otherwise = do
            charge
            case Map.lookup current predecessors of
                Nothing -> Except.throwE (EqualityUnknownTerm (fst current))
                Just (previous, step) -> rebuild predecessors previous (step : steps)

recordEquality
    :: Word
    -> Catalogue global
    -> TermId
    -> TermId
    -> reason
    -> EqualityState reason
    -> ( Either
            EqualityFailure
            (EqualityState reason, Maybe (EqualityClash reason), Bool)
       , Word
       )
recordEquality = recordEqualityC False

-- A supported request retains alternate explanations of an already connected
-- pair. This changes neither its equality merge count nor its retry generation.
recordEqualityWithSupport
    :: Word -> Catalogue global -> TermId -> TermId -> reason -> EqualityState reason
    -> (Either EqualityFailure (EqualityState reason, Maybe (EqualityClash reason), Bool), Word)
recordEqualityWithSupport = recordEqualityC True

recordEqualityC
    :: Bool -> Word -> Catalogue global -> TermId -> TermId -> reason -> EqualityState reason
    -> (Either EqualityFailure (EqualityState reason, Maybe (EqualityClash reason), Bool), Word)
recordEqualityC keepAlternatives available catalogue left right reason state =
    runCounted available do
        leftTerm <- lookupTermC catalogue left
        rightTerm <- lookupTermC catalogue right
        unless
            (catalogueTermTypeId leftTerm == catalogueTermTypeId rightTerm)
            (Except.throwE (EqualityTypeMismatch left right))
        let pair = orderedPair left right
        charge
        if pair `Set.member` equalityEdgePairs state
            then if keepAlternatives
                then do
                    explanations <- appendIncident
                        (fromMaybe (equalityAdjacency state) (equalityExplanationAdjacency state))
                    pure (state {equalityExplanationAdjacency = Just explanations}, Nothing, False)
                else pure (state, Nothing, False)
            else do
                previousPath <- pathC catalogue state left right
                adjacency <- appendIncident (equalityAdjacency state)
                explanations <- traverse appendIncident (equalityExplanationAdjacency state)
                let merged = isNothing previousPath
                    updated =
                        state
                            { equalityEdgePairs =
                                Set.insert pair (equalityEdgePairs state)
                            , equalityAdjacency = adjacency
                            , equalityExplanationAdjacency = explanations
                            , equalityHasPendingRefresh =
                                equalityHasPendingRefresh state || merged
                            }
                clash <-
                    if merged
                        then firstClashC catalogue updated
                        else pure Nothing
                pure (updated, clash, merged)
  where
    -- Charge every endpoint insertion before publishing either view. A shared
    -- view needs no second update; self-edges have only a forward explanation.
    appendIncident adjacency = do
        charge
        unless (left == right) charge
        let forward = appendNeighbor left right EqualityForward adjacency
        -- The full view sits inside Maybe; forcing only Just would retain a
        -- chain of pending Map updates across alternate admissions.
        pure $! (if left == right then forward
            else appendNeighbor right left EqualityReverse forward)
    appendNeighbor owner neighbor direction = Map.alter
        (\existing -> Just
            (fromMaybe Seq.empty existing Seq.|> EqualityNeighbor neighbor (EqualityStep reason direction)))
        owner

recordDisequality
    :: Word
    -> Catalogue global
    -> TermId
    -> TermId
    -> reason
    -> EqualityState reason
    -> ( Either
            EqualityFailure
            (EqualityState reason, Maybe (EqualityClash reason), Bool)
       , Word
       )
recordDisequality available catalogue left right reason state =
    runCounted available do
        leftTerm <- lookupTermC catalogue left
        rightTerm <- lookupTermC catalogue right
        unless
            (catalogueTermTypeId leftTerm == catalogueTermTypeId rightTerm)
            (Except.throwE (EqualityTypeMismatch left right))
        let pair = orderedPair left right
        charge
        if pair `Set.member` equalityDisequalityPairs state
            then pure (state, Nothing, False)
            else do
                let updated =
                        state
                            { equalityDisequalities =
                                equalityDisequalities state
                                    Seq.|> Disequality left right reason
                            , equalityDisequalityPairs =
                                Set.insert pair
                                    (equalityDisequalityPairs state)
                            }
                path <- pathC catalogue updated left right
                pure
                    ( updated
                    , (\selected ->
                        EqualityDisequalityClash selected reason)
                        <$> path
                    , True
                    )

recordPolarity
    :: Word
    -> Catalogue global
    -> Bool
    -> TermId
    -> FormulaId
    -> reason
    -> EqualityState reason
    -> ( Either
            EqualityFailure
            (EqualityState reason, Maybe (EqualityClash reason), Bool)
       , Word
       )
recordPolarity available catalogue positive termId formulaId reason state =
    runCounted available do
        _term <- lookupTermC catalogue termId
        charge
        let seenTerms =
                if positive
                    then equalityTrueTerms state
                    else equalityFalseTerms state
        if termId `Set.member` seenTerms
            then pure (state, Nothing, False)
            else do
                let witness = PolarityWitness termId formulaId reason
                    updated =
                        if positive
                            then
                                state
                                    { equalityTrueWitnesses =
                                        equalityTrueWitnesses state
                                            Seq.|> witness
                                    , equalityTrueTerms =
                                        Set.insert termId
                                            (equalityTrueTerms state)
                                    }
                            else
                                state
                                    { equalityFalseWitnesses =
                                        equalityFalseWitnesses state
                                            Seq.|> witness
                                    , equalityFalseTerms =
                                        Set.insert termId
                                            (equalityFalseTerms state)
                                    }
                clash <- firstPropositionClashC catalogue updated
                pure (updated, clash, True)

firstClashC
    :: Catalogue global
    -> EqualityState reason
    -> Counted (Maybe (EqualityClash reason))
firstClashC catalogue state = do
    disequality <- scanDisequalities (Seq.viewl (equalityDisequalities state))
    case disequality of
        Just clash -> pure (Just clash)
        Nothing -> firstPropositionClashC catalogue state
  where
    scanDisequalities Seq.EmptyL = pure Nothing
    scanDisequalities
            (Disequality left right reason Seq.:< rest) = do
        charge
        path <- pathC catalogue state left right
        case path of
            Just selected ->
                pure (Just (EqualityDisequalityClash selected reason))
            Nothing -> scanDisequalities (Seq.viewl rest)

firstPropositionClashC
    :: Catalogue global
    -> EqualityState reason
    -> Counted (Maybe (EqualityClash reason))
firstPropositionClashC catalogue state =
    scanTrue (Seq.viewl (equalityTrueWitnesses state))
  where
    scanTrue Seq.EmptyL = pure Nothing
    scanTrue (trueWitness Seq.:< rest) = do
        clash <-
            scanFalse trueWitness
                (Seq.viewl (equalityFalseWitnesses state))
        maybe (scanTrue (Seq.viewl rest)) (pure . Just) clash

    scanFalse _trueWitness Seq.EmptyL = pure Nothing
    scanFalse
            trueWitness@(PolarityWitness
                trueTerm _trueFormula trueReason)
            (PolarityWitness falseTerm _falseFormula falseReason
                Seq.:< rest) = do
        charge
        path <- pathC catalogue state trueTerm falseTerm
        case path of
            Just selected ->
                pure
                    (Just
                        (EqualityPropositionClash
                            trueReason falseReason selected))
            Nothing ->
                scanFalse trueWitness (Seq.viewl rest)

equalityRefreshPending :: EqualityState reason -> Bool
equalityRefreshPending = equalityHasPendingRefresh

refreshCongruence
    :: Word
    -> Catalogue global
    -> EqualityState reason
    -> ( Either
            EqualityFailure
            (EqualityState reason, Seq (CongruenceRequest reason))
       , Word
       )
refreshCongruence available catalogue state =
    runCounted available do
        if not (equalityHasPendingRefresh state)
            then pure (state, Seq.empty)
            else do
                let started = state {equalityHasPendingRefresh = False}
                scanApplications
                    started Map.empty Seq.empty
                    (Set.toAscList (equalityVisibleTerms started))
  where
    -- Requests are appended in the visible-term scan order.  Returning the
    -- sequence directly avoids a second unmetered pass over semantic rows.
    scanApplications current _signatures requests [] =
        pure (current, requests)
    scanApplications current signatures requests
            (termId : rest) = do
        charge
        term <- lookupTermC catalogue termId
        case catalogueTermApplication term of
            Nothing ->
                scanApplications
                    current signatures requests rest
            Just (functionId, argumentId)
                | functionId
                    `Set.notMember` equalityVisibleTerms current
                  || argumentId
                    `Set.notMember` equalityVisibleTerms current ->
                    scanApplications
                        current signatures requests rest
                | otherwise -> do
                    functionRepresentative <-
                        representativeC catalogue current functionId
                    argumentRepresentative <-
                        representativeC catalogue current argumentId
                    let signature =
                            ( catalogueTermTypeId term
                            , functionRepresentative
                            , argumentRepresentative
                            )
                    case Map.lookup signature signatures of
                        Nothing ->
                            scanApplications
                                current
                                (Map.insert signature termId signatures)
                                requests rest
                        Just anchor -> do
                            let pair = orderedPair anchor termId
                            alreadyEqual <-
                                isJust
                                    <$> pathC catalogue current anchor termId
                            if pair
                                    `Set.member`
                                        equalityCongruencePairs current
                                    || alreadyEqual
                                then
                                    scanApplications
                                        current signatures requests rest
                                else do
                                    anchorTerm <- lookupTermC catalogue anchor
                                    (anchorFunction, anchorArgument) <-
                                        maybe
                                            (Except.throwE
                                                (EqualityMalformedApplication
                                                    anchor))
                                            pure
                                            (catalogueTermApplication anchorTerm)
                                    functionPath <-
                                        requirePath
                                            anchorFunction functionId
                                    argumentPath <-
                                        requirePath
                                            anchorArgument argumentId
                                    let updated =
                                            current
                                                { equalityCongruencePairs =
                                                    Set.insert pair
                                                        (equalityCongruencePairs
                                                            current)
                                                }
                                        request =
                                            CongruenceRequest
                                                anchor termId
                                                functionPath argumentPath
                                    scanApplications
                                        updated signatures
                                        (requests Seq.|> request) rest

    requirePath source target = do
        selected <- pathC catalogue state source target
        maybe
            (Except.throwE (EqualityTypeMismatch source target))
            pure
            selected

representativeC
    :: Catalogue global
    -> EqualityState reason
    -> TermId
    -> Counted TermId
representativeC _catalogue state source =
    flood (Set.singleton source) (Seq.singleton source)
  where
    flood visited queue = do
        charge
        case Seq.viewl queue of
            Seq.EmptyL -> pure (Set.findMin visited)
            current Seq.:< rest -> do
                adjacent <- neighborsC state current
                (nextVisited, nextQueue) <-
                    scan visited rest (Seq.viewl adjacent)
                flood nextVisited nextQueue

    scan visited queue Seq.EmptyL = pure (visited, queue)
    scan visited queue
            (EqualityNeighbor next _step Seq.:< rest) = do
        charge
        let (nextVisited, nextQueue)
                | next `Set.member` visited = (visited, queue)
                | otherwise = (Set.insert next visited, queue Seq.|> next)
        scan nextVisited nextQueue (Seq.viewl rest)
