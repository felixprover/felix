{-# LANGUAGE NoImplicitPrelude #-}

-- | Request/answer scheduling for the finite formation calculus. Logical
-- matching, joins, support admission, and proof construction belong
-- to the caller. This driver never turns a request into an assumed answer.
module Felix.Checking.Notion.Relational
    ( AnswerMatch(..)
    , RelationalStep(..)
    , RelationalEvaluator(..)
    , RelationalResult(..)
    , RelationalSession, RelationalStatus(..)
    , initializeRelational, advanceRelational, deliverRelational, relationalStatus, finishRelational
    , focusRelational, queryRelational
    , relationalRootAnswer
    , evaluateRelational
    , solveRelational
    ) where

import Base
import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Numeric.Natural (Natural)

-- A checked conversion publishes a distinct answer through the ordinary queue;
-- it never delivers the original row as if its source shape had matched.
data AnswerMatch answer work = NoMatch | DirectMatch | DerivedMatch !answer | DeferredMatch !work

data RelationalStep request answer continuation work = RelationalStep
    { relationalEmissions :: ![answer]
    , relationalSubscriptions :: ![(request, continuation)]
    -- Each continuation names the demand whose progress postpones it. This
    -- can be a chosen join prerequisite, not just the expanded parent query.
    -- Nothing denotes forward work without such an owner. Postponement is
    -- only a priority: idle/saturating evaluation still drains every item.
    , relationalDeferred :: ![(Maybe request, work)]
    }

-- Keys must be finite request-local identities, not derivation histories.
-- An answer key retains every eligibility distinction a consumer observes;
-- equal keys permit the first founded representative to serve all consumers.
-- A continuation retains its original full-pattern filter and join state.
-- Each request chooses one posting; answers may enter several. Buckets are
-- only an index: every compatible pair must share the requested bucket.
data RelationalEvaluator m request answer key continuation work bucket = RelationalEvaluator
    { relationalCharge :: m ()
    , relationalRequestBucket :: request -> m bucket
    , relationalAnswerBuckets :: answer -> m [bucket]
    , relationalAnswerKey :: answer -> key
    , relationalMatches :: request -> answer -> m (AnswerMatch answer work)
    , relationalObserve :: answer -> m (RelationalStep request answer continuation work)
    , relationalExpand :: request -> m (RelationalStep request answer continuation work)
    , relationalResume :: continuation -> answer -> m (RelationalStep request answer continuation work)
    , relationalContinue :: work -> m (RelationalStep request answer continuation work)
    -- Work extending an evidence-producing request shares the new-request
    -- queue. Speculative alternatives stay behind available prerequisites.
    , relationalDiscovery :: work -> Bool
    -- Exact truth needs one founded witness. A partial relation or component
    -- still needs alternative rows even after its first answer.
    , relationalNeedsMoreAnswers :: request -> m Bool
    }

data RelationalResult request answer key = RelationalResult
    { relationalSaturated :: !Bool
    , relationalRequests :: !(Set request)
    , relationalAnswers :: !(Map key answer)
    , relationalRootAnswers :: !(Set key)
    , relationalUnansweredRequests :: !(Set request)
    -- Unique scheduled continuation/answer pairs; solve mode may leave some
    -- alternate deliveries unvisited after the root has been answered.
    , relationalDeliveryCount :: !Int
    }
    deriving (Show, Eq)

data Event request answer key continuation work bucket
    = OpenRequest !request
    | ExpandRequest !request
    | PublishAnswer !key
    | Deliver !continuation !key
    | ContinueWork !(Maybe request) !work
    | ApplyStep !(RelationalStep request answer continuation work)
    | MatchAnswers !request !(Set key)
    | MatchRequests !key !(Set request)
    | DeliverKeys !continuation !(Set key)
    | DeliverWaiters !key !(Set continuation)
    | PublishBuckets !key ![bucket]
    | ObserveAnswer !key

data Table request answer key continuation work bucket = Table
    { requests :: !(Map request (bucket, Set continuation, Set key))
    , answers :: !(Map key (answer, [bucket]))
    , requestBuckets :: !(Map bucket (Set request))
    , answerBuckets :: !(Map bucket (Set key))
    , deliveries :: !(Map continuation (Set key))
    , deliveryCount :: !Int
    , pendingAlternatives :: !(Seq.Seq (Event request answer key continuation work bucket))
    , pendingRequests :: !(Seq.Seq (Event request answer key continuation work bucket))
    , pendingAnswered :: !(Seq.Seq (Event request answer key continuation work bucket))
    , pending :: !(Seq.Seq (Event request answer key continuation work bucket))
    , evidenceBatch :: !Int
    }

-- A session has one immutable problem owner. Quiescence describes only this
-- table: the owner must also finish external producers before declaring absence.
data RelationalSession request answer key continuation work bucket = RelationalSession
    !Bool !request ![answer] !(Table request answer key continuation work bucket)

data RelationalStatus = RelationalRunnable | RelationalAnswered | RelationalQuiescent
    deriving (Show, Eq)

relationalStatus :: Ord request => RelationalSession request answer key continuation work bucket -> RelationalStatus
relationalStatus (RelationalSession stop root seeds table)
    | stop && not (Set.null found) = RelationalAnswered
    | null seeds && Seq.null (pendingAlternatives table) && Seq.null (pending table) && Seq.null (pendingRequests table)
        && Seq.null (pendingAnswered table) = RelationalQuiescent
    | otherwise = RelationalRunnable
  where
    (_,_,found) = requests table Map.! root

-- Selecting a proof must not copy the owner's entire answer map for each
-- sibling goal. Full enumeration remains available to saturation/debug callers.
relationalRootAnswer
    :: (Monad m, Ord request, Ord key)
    => RelationalEvaluator m request answer key continuation work bucket
    -> RelationalSession request answer key continuation work bucket -> m (Maybe answer)
relationalRootAnswer evaluator (RelationalSession _ root _ table) = do
    relationalCharge evaluator
    let (_,_,found) = requests table Map.! root
    pure (Set.lookupMin found >>= fmap fst . (`Map.lookup` answers table))

initializeRelational
    :: (Monad m, Ord request)
    => Bool -> RelationalEvaluator m request answer key continuation work bucket
    -> [answer] -> request -> m (RelationalSession request answer key continuation work bucket)
initializeRelational stop evaluator facts root = do
    relationalCharge evaluator
    bucket <- relationalRequestBucket evaluator root
    pure (RelationalSession stop root facts (Table
        (Map.singleton root (bucket,Set.empty,Set.empty)) Map.empty Map.empty Map.empty Map.empty 0
        Seq.empty Seq.empty Seq.empty (Seq.singleton (OpenRequest root)) 0))

-- Select another obligation in the same owner. Existing answers and pending
-- work survive; a new root is enrolled through ordinary indexed lookup.
focusRelational
    :: (Monad m, Ord request)
    => RelationalEvaluator m request answer key continuation work bucket -> request
    -> RelationalSession request answer key continuation work bucket
    -> m (RelationalSession request answer key continuation work bucket)
focusRelational evaluator root (RelationalSession stop _ seeds table) = do
    relationalCharge evaluator
    updated <- if Map.member root (requests table) then pure table else do
        bucket <- relationalRequestBucket evaluator root
        pure table { requests = Map.insert root (bucket,Set.empty,Set.empty) (requests table)
            , pending = pending table Seq.|> OpenRequest root }
    pure (RelationalSession stop root seeds updated)

-- Enroll an additional obligation in this owner without changing its root.
-- A pending lookup returns no answer while preserving the newly queued work.
queryRelational
    :: (Monad m, Ord request, Ord key)
    => RelationalEvaluator m request answer key continuation work bucket -> request
    -> RelationalSession request answer key continuation work bucket
    -> m (Maybe answer, RelationalSession request answer key continuation work bucket)
queryRelational evaluator requested original@(RelationalSession _ root _ _) = do
    focused <- focusRelational evaluator requested original
    found <- relationalRootAnswer evaluator focused
    let RelationalSession stop _ seeds table = focused
    pure (found,RelationalSession stop root seeds table)

-- External results enter the same publication/subscription queue. This cannot
-- mark an unanswered request false or replace a previously founded witness.
deliverRelational
    :: Monad m => RelationalEvaluator m request answer key continuation work bucket
    -> RelationalStep request answer continuation work
    -> RelationalSession request answer key continuation work bucket
    -> m (RelationalSession request answer key continuation work bucket)
deliverRelational evaluator step (RelationalSession stop root seeds table) = do
    relationalCharge evaluator
    pure (RelationalSession stop root seeds table
        {pending = pending table Seq.|> ApplyStep step})

finishRelational
    :: (Monad m, Ord request)
    => RelationalEvaluator m request answer key continuation work bucket
    -> RelationalSession request answer key continuation work bucket
    -> m (RelationalResult request answer key)
finishRelational evaluator session@(RelationalSession _ root _ table) = do
    (requested,unanswered) <- foldM (\(known,missing) (request,(_,_,found)) -> do
        relationalCharge evaluator
        pure (Set.insert request known,if Set.null found then Set.insert request missing else missing))
        (Set.empty,Set.empty) (Map.toAscList (requests table))
    let (_,_,found) = requests table Map.! root
    pure (RelationalResult (relationalStatus session == RelationalQuiescent)
        requested (fst <$> answers table) found unanswered (deliveryCount table))

-- The ordinary wrappers drain the same bounded machine used by scoped owners.
-- Small determined searches finish within the first batch. Every producer,
-- candidate, and delivery cursor yields after one item; an external owner can
-- interleave child work without copying or reconstructing this table.
evaluateRelational
    :: (Monad m, Ord request, Ord key, Ord continuation, Ord bucket)
    => RelationalEvaluator m request answer key continuation work bucket
    -> [answer] -> request -> m (RelationalResult request answer key)
evaluateRelational = runRelational False

-- | Answer one existential root query. A checked answer suffices for success;
-- absence still requires saturation. The returned flag distinguishes a solved
-- query from a complete enumeration of all answers.
solveRelational
    :: (Monad m, Ord request, Ord key, Ord continuation, Ord bucket)
    => RelationalEvaluator m request answer key continuation work bucket
    -> [answer] -> request -> m (RelationalResult request answer key)
solveRelational = runRelational True

runRelational
    :: (Monad m, Ord request, Ord key, Ord continuation, Ord bucket)
    => Bool -> RelationalEvaluator m request answer key continuation work bucket
    -> [answer] -> request -> m (RelationalResult request answer key)
runRelational stopOnAnswer evaluator facts root =
    initializeRelational stopOnAnswer evaluator facts root >>= drain
  where
    drain session = case relationalStatus session of
        RelationalRunnable -> advanceRelational 64 evaluator session >>= drain
        _ -> finishRelational evaluator session

advanceRelational
    :: (Monad m, Ord request, Ord key, Ord continuation, Ord bucket)
    => Natural -> RelationalEvaluator m request answer key continuation work bucket
    -> RelationalSession request answer key continuation work bucket
    -> m (RelationalSession request answer key continuation work bucket)
advanceRelational quantum evaluator (RelationalSession stopOnAnswer root facts initial) = do
    (remaining,final) <- drain quantum facts initial
    pure (RelationalSession stopOnAnswer root remaining final)
  where
    charge = relationalCharge evaluator
    open request table = do
        charge
        if Map.member request (requests table) then pure table else do
            bucket <- relationalRequestBucket evaluator request
            pure table
                { requests = Map.insert request (bucket, Set.empty, Set.empty) (requests table)
                , pending = pending table Seq.|> OpenRequest request }
    emit table answer = do
        charge
        let key = relationalAnswerKey evaluator answer
        if Map.member key (answers table) then pure table else do
            buckets <- relationalAnswerBuckets evaluator answer
            for_ buckets (const charge)
            let postings = Set.toAscList (Set.fromList buckets)
                inserted = table
                    { answers = Map.insert key (answer, postings) (answers table)
                    , pending = pending table Seq.|> PublishAnswer key }
                (rootBucket, _, _) = requests table Map.! root
            if stopOnAnswer && rootBucket `elem` postings
                then match inserted root key
                else pure inserted
    deliver table continuation key = do
        charge
        let known = Map.findWithDefault Set.empty continuation (deliveries table)
        if Set.member key known then pure table else do
            charge
            let event = Deliver continuation key
                updated = table {deliveries = Map.insert continuation (Set.insert key known) (deliveries table)
                    , deliveryCount = deliveryCount table + 1}
            -- One witness gets to expose its next demand before another
            -- witness resumes this same continuation. Merely prioritizing
            -- immediate emissions is insufficient: that demand may need
            -- producer expansion, which otherwise waits behind all siblings.
            -- Retain every alternate delivery in the existing idle queue;
            -- partial outputs and distinct eligibility may need them later.
            pure if stopOnAnswer && not (Set.null known)
                then updated {pendingAnswered = pendingAnswered updated Seq.|> event}
                else updated {pending = pending updated Seq.|> event}
    subscribe table (request, continuation) = do
        enrolled <- open request table
        let (bucket, waiting, known) = requests enrolled Map.! request
        if Set.member continuation waiting then pure enrolled else do
            let updated = enrolled {requests = Map.insert request (bucket, Set.insert continuation waiting, known)
                    (requests enrolled)}
            pure updated {pending = pending updated Seq.|> DeliverKeys continuation known}
    apply table (RelationalStep [] [] []) = pure table
    apply table step = pure table {pending = pending table Seq.|> ApplyStep step}
    applyNext table = \case
        RelationalStep (answer:rest) subscriptions deferred ->
            emit table answer >>= (\next -> apply next (RelationalStep rest subscriptions deferred))
        RelationalStep [] (subscription:rest) deferred ->
            subscribe table subscription >>= (\next -> apply next (RelationalStep [] rest deferred))
        RelationalStep [] [] ((owner,work):rest) -> do
            charge
            let next = case owner of
                    Nothing -> table {pending = pending table Seq.|> ContinueWork Nothing work}
                    Just _ | relationalDiscovery evaluator work ->
                        table {pendingRequests = pendingRequests table Seq.|> ContinueWork owner work}
                    Just _ -> table {pendingAlternatives = pendingAlternatives table Seq.|> ContinueWork owner work}
            apply next (RelationalStep [] [] rest)
        RelationalStep [] [] [] -> pure table
    -- A focused root may have changed since emission. Only an already matched
    -- pair can skip this check; older answers still serve newly focused roots.
    matchPublished table request key
        | Set.member key (matchedKeys request table) = pure table
        | otherwise = match table request key
    match table request key = do
        charge
        relationalMatches evaluator request (fst (answers table Map.! key)) >>= \case
            NoMatch -> pure table
            DerivedMatch answer -> emit table answer
            DeferredMatch work -> do
                charge
                pure table {pendingAlternatives = pendingAlternatives table Seq.|> ContinueWork (Just request) work}
            DirectMatch -> do
                let (bucket, waiting, known) = requests table Map.! request
                    updated = table {requests = Map.insert request (bucket, waiting, Set.insert key known) (requests table)}
                pure updated {pending = pending updated Seq.|> DeliverWaiters key waiting}
    matchedKeys request table = let (_, _, found) = requests table Map.! request in found
    solved table = stopOnAnswer && not (Set.null (matchedKeys root table))
    -- An answered request need not immediately enumerate more witnesses.
    -- Partial outputs retain their alternatives until outstanding demands
    -- cannot progress. The owner may close an exact truth request after its
    -- first proof; already instantiated clauses and answer deliveries remain
    -- independent work. This is witness selection, not negative memoization.
    answeredOwner table event = stopOnAnswer && case event of
        ExpandRequest request -> answered request
        ContinueWork (Just request) _ -> answered request
        _ -> False
      where
        answered request = not (Set.null (matchedKeys request table))
    drain 0 seeds table = pure (seeds,table)
    drain remaining seeds table
        | solved table = pure (seeds,table)
        | otherwise = case seeds of
            answer:rest -> emit table answer >>= drain (remaining-1) rest
            [] -> nextEvent remaining table
    -- Bound uninterrupted evidence delivery, then give a discovery alternative
    -- a turn. The counter survives suspension; smaller external quanta cannot
    -- accidentally starve this owner's deferred queue.
    nextEvent remaining table
        | evidenceBatch table >= 64 = case Seq.viewl (pendingAlternatives table) of
            event Seq.:< rest -> stepEvent remaining table
                {pendingAlternatives = rest,pending = event Seq.<| pending table,evidenceBatch = 0}
            Seq.EmptyL -> stepEvent remaining table
        | otherwise = stepEvent remaining table
    stepEvent remaining table = case Seq.viewl (pending table) of
        Seq.EmptyL -> case Seq.viewl (pendingRequests table) of
            event Seq.:< rest -> choose remaining table {pendingRequests = rest} event
            Seq.EmptyL -> case Seq.viewl (pendingAlternatives table) of
                event Seq.:< rest -> choose remaining table {pendingAlternatives = rest,evidenceBatch = 0} event
                Seq.EmptyL -> case Seq.viewl (pendingAnswered table) of
                    Seq.EmptyL -> pure ([],table)
                    event Seq.:< rest -> stepEvent remaining table
                        {pendingAnswered = rest,pending = Seq.singleton event,evidenceBatch = 0}
        event Seq.:< rest -> do
            -- Cursor items perform their original candidate/publication charges
            -- below. Reifying the walk adds no fictitious semantic operation.
            case event of
                OpenRequest{} -> charge
                ExpandRequest{} -> charge
                ContinueWork{} -> charge
                PublishAnswer{} -> charge
                Deliver{} -> charge
                _ -> pure ()
            let current = table {pending = Seq.empty,evidenceBatch = evidenceBatch table + 1}
            next <- case event of
                OpenRequest request -> do
                    let (bucket,_,_) = requests current Map.! request
                    pure current
                        {requestBuckets = Map.insertWith Set.union bucket (Set.singleton request) (requestBuckets current)
                        ,pending = Seq.singleton (MatchAnswers request
                            (Map.findWithDefault Set.empty bucket (answerBuckets current)))
                        ,pendingRequests = pendingRequests current Seq.|> ExpandRequest request}
                ExpandRequest request -> relationalExpand evaluator request >>= apply current
                ContinueWork _ work -> relationalContinue evaluator work >>= apply current
                ApplyStep step -> applyNext current step
                PublishAnswer key -> pure current
                    {pending = Seq.singleton (PublishBuckets key (snd (answers current Map.! key)))}
                PublishBuckets key buckets -> do
                    case buckets of
                        [] -> pure current {pending = Seq.singleton (ObserveAnswer key)}
                        bucket:restBuckets -> do
                            charge
                            pure current
                                {answerBuckets = Map.insertWith Set.union bucket (Set.singleton key) (answerBuckets current)
                                ,pending = Seq.fromList
                                    [MatchRequests key (Map.findWithDefault Set.empty bucket (requestBuckets current)),
                                     PublishBuckets key restBuckets]}
                ObserveAnswer key -> relationalObserve evaluator (fst (answers current Map.! key)) >>= apply current
                MatchAnswers request keys -> case Set.minView keys of
                    Nothing -> pure current
                    Just (key,keys') -> do
                        next <- matchPublished current request key
                        pure next {pending = pending next Seq.|> MatchAnswers request keys'}
                MatchRequests key requested -> case Set.minView requested of
                    Nothing -> pure current
                    Just (request,requested') -> do
                        next <- matchPublished current request key
                        pure next {pending = pending next Seq.|> MatchRequests key requested'}
                DeliverKeys continuation keys -> case Set.minView keys of
                    Nothing -> pure current
                    Just (key,keys') -> do
                        next <- deliver current continuation key
                        pure next {pending = pending next Seq.|> DeliverKeys continuation keys'}
                DeliverWaiters key waiting -> case Set.minView waiting of
                    Nothing -> pure current
                    Just (continuation,waiting') -> do
                        next <- deliver current continuation key
                        pure next {pending = pending next Seq.|> DeliverWaiters key waiting'}
                Deliver continuation key ->
                    relationalResume evaluator continuation (fst (answers current Map.! key)) >>= apply current
            drain (remaining-1) [] next {pending = pending next Seq.>< rest}

    -- First attempts on newly opened prerequisites precede alternate producers.
    -- Keep both queues FIFO so a new descendant cannot overtake an older sibling.
    -- The shared batch counter still gives alternatives bounded service.
    choose remaining table event
        | answeredOwner table event = do
            charge
            needed <- case event of
                ExpandRequest request -> relationalNeedsMoreAnswers evaluator request
                ContinueWork (Just request) _ -> relationalNeedsMoreAnswers evaluator request
                _ -> pure True
            drain (remaining-1) [] (if needed then table
                {pendingAnswered = pendingAnswered table Seq.|> event} else table)
        | otherwise = nextEvent remaining table {pending = Seq.singleton event}
