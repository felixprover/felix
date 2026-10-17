{-# LANGUAGE NoImplicitPrelude #-}

-- | A ground clause needs one founded proof of each distinct proposition.
-- Bindings and conclusion views are already fixed. Alternative proofs cannot
-- change the instance, so they never form a Cartesian product here.
module Felix.Checking.Notion.Ground
    ( GroundInstance, prepareInstance, deliverInstance
    , instanceRule, instanceRequests, instanceReady, instanceWitnesses
    ) where

import Base
import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Felix.Checking.Notion.Request (RequestId)
import Felix.Checking.Notion.Rule (GroundRule)
import Felix.Checking.Notion.TermIndex (indexWork)
import Numeric.Natural (Natural)

data GroundInstance variable witness = GroundInstance
    { instanceRule :: !(GroundRule variable)
    , instanceRequests :: !(Map RequestId [Natural])
    , positionRequests :: !(Map Natural RequestId)
    , requestWitnesses :: !(Map RequestId witness)
    , unfilledRequests :: !Int
    }

prepareInstance
    :: Monad m => (Natural -> m ()) -> GroundRule variable -> Map Natural RequestId
    -> m (GroundInstance variable witness)
prepareInstance charge rule positions = do
    grouped <- foldM (\known (position,request) -> do
        charge (indexWork (Map.size known) 1)
        pure (Map.insertWith (<>) request [position] known)) Map.empty (Map.toAscList positions)
    charge (fromIntegral (Map.size positions))
    pure (GroundInstance rule (reverse <$> grouped) positions Map.empty (Map.size grouped))

instanceReady :: GroundInstance variable witness -> Bool
instanceReady = (== 0) . unfilledRequests

-- True denotes the single transition to readiness. The evaluator schedules
-- proof construction once, after this immutable selection has been retained.
deliverInstance
    :: Monad m => (Natural -> m ()) -> RequestId -> witness -> GroundInstance variable witness
    -> m (GroundInstance variable witness, Bool)
deliverInstance charge request witness current = do
    charge (indexWork (Map.size (requestWitnesses current)) 1)
    if Map.member request (requestWitnesses current) then pure (current,False) else do
        charge (indexWork (Map.size (requestWitnesses current)) 1)
        let updated = current
                {requestWitnesses = Map.insert request witness (requestWitnesses current)
                ,unfilledRequests = unfilledRequests current - 1}
        pure (updated,instanceReady updated)

-- Repeated premises retain their original positions and therefore their
-- distinct uses in replay, while sharing the selected proof of that request.
instanceWitnesses
    :: Monad m => (Natural -> m ()) -> GroundInstance variable witness -> m (Map Natural witness)
instanceWitnesses charge current = traverse (\request -> do
    charge (indexWork (Map.size (requestWitnesses current)) 1)
    pure (requestWitnesses current Map.! request)) (positionRequests current)
