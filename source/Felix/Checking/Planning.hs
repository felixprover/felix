{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Inert declaration-local coordinates. Admission checks dependency order.
module Felix.Checking.Planning
    ( PlannedCandidatePosition(..)
    , plannedEarlierCandidate
    , plannedCandidateStage
    , plannedCandidateIndex
    , PlannedFactReference(..)
    ) where

import Base
import Felix.Checking.Semantic (SemanticFactOccurrenceFingerprint)
import Numeric.Natural (Natural)

data PlannedCandidatePosition = PlannedCandidatePosition
    !Natural
    !Natural
    deriving stock (Show, Eq, Ord)

plannedEarlierCandidate :: Natural -> Natural -> PlannedCandidatePosition
plannedEarlierCandidate = PlannedCandidatePosition

plannedCandidateStage :: PlannedCandidatePosition -> Natural
plannedCandidateStage (PlannedCandidatePosition stage _) = stage

plannedCandidateIndex :: PlannedCandidatePosition -> Natural
plannedCandidateIndex (PlannedCandidatePosition _ index) = index

data PlannedFactReference
    = LocalCandidateReference !PlannedCandidatePosition
    | EnvironmentOccurrenceReference !SemanticFactOccurrenceFingerprint
    deriving stock (Show, Eq, Ord)
