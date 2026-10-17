{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}

-- | Choice ownership within one focused scheduler. Shared producers are roots;
-- their consumer relation is deliberately separate from this forest.
module Felix.Checking.Obvious.Choice
    ( Owner(..)
    , Forest
    , Choice
    , empty
    , lookup
    , ownerProducer
    , live
    , parent
    , producer
    , payload
    , rows
    , insert
    , insertProducer
    , adjust
    , retire
    ) where

import Base hiding (empty)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)

data Owner = RootContinuation | OwnedChoice !Natural
    deriving stock (Eq, Ord, Show)

newtype Forest producer value = Forest (Map.Map Natural (Choice producer value))

-- Constructors stay private so payload updates cannot detach a child or forge
-- its inherited producer. Retiring a choice removes every owned descendant.
data Choice producer value = Choice
    { choiceParent :: !Owner
    , choiceProducer :: !(Maybe producer)
    , children :: !(Set Natural)
    , choicePayload :: !value
    }

parent :: Choice producer value -> Owner
parent = choiceParent

producer :: Choice producer value -> Maybe producer
producer = choiceProducer

payload :: Choice producer value -> value
payload = choicePayload

empty :: Forest producer value
empty = Forest Map.empty

lookup :: Natural -> Forest producer value -> Maybe (Choice producer value)
lookup identifier (Forest choices) = Map.lookup identifier choices

ownerProducer :: Owner -> Forest producer value -> Maybe (Maybe producer)
ownerProducer RootContinuation _ = Just Nothing
ownerProducer (OwnedChoice identifier) choices = producer <$> lookup identifier choices

live :: Owner -> Forest producer value -> Bool
live RootContinuation _ = True
live (OwnedChoice identifier) (Forest choices) = Map.member identifier choices

rows :: Forest producer value -> [(Natural, Choice producer value)]
rows (Forest choices) = Map.toAscList choices

insert :: Natural -> Owner -> value -> Forest producer value -> Maybe (Forest producer value)
insert identifier owner value forest = do
    enclosing <- ownerProducer owner forest
    insertOwned identifier owner enclosing value forest

insertProducer :: Natural -> producer -> value -> Forest producer value -> Maybe (Forest producer value)
insertProducer identifier enclosing = insertOwned identifier RootContinuation (Just enclosing)

insertOwned
    :: Natural -> Owner -> Maybe producer -> value -> Forest producer value
    -> Maybe (Forest producer value)
insertOwned identifier owner enclosing value (Forest choices)
    | Map.member identifier choices = Nothing
    | otherwise = Just (Forest (Map.insert identifier
        (Choice owner enclosing Set.empty value) attached))
  where
    attached = case owner of
        RootContinuation -> choices
        OwnedChoice ancestor -> Map.adjust
            (\choice -> choice {children = Set.insert identifier (children choice)}) ancestor choices

adjust :: (value -> value) -> Natural -> Forest producer value -> Forest producer value
adjust update identifier (Forest choices) = Forest (Map.adjust
    (\choice -> choice {choicePayload = update (payload choice)}) identifier choices)

-- The explicit frontier bounds the call stack even for deep choices. Unlink
-- once at the surviving parent; descendants are visited only through ownership
-- edges. Ready/dormant entries and consumer registrations become inert at once.
retire :: Natural -> Forest producer value -> Forest producer value
retire identifier forest@(Forest choices) = case lookup identifier forest of
    Nothing -> forest
    Just choice -> Forest (drain [identifier] detached)
      where
        detached = case parent choice of
            RootContinuation -> choices
            OwnedChoice ancestor -> Map.adjust
                (\ancestorChoice -> ancestorChoice
                    {children = Set.delete identifier (children ancestorChoice)}) ancestor choices
        drain [] !remaining = remaining
        drain (next : pending) !remaining = case Map.lookup next remaining of
            Nothing -> drain pending remaining
            Just current -> drain (Set.foldr (:) pending (children current))
                (Map.delete next remaining)
