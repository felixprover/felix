module AggregateAndObviousCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Obvious
    ( ObviousDefinitionView
    , ObviousFailure
    , ObviousImport
    , ObviousProof
    )
import Felix.Checking.SetConstruction
    ( CheckedRelationalSetConstruction
    , NamedSetConstruction
    )

newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badNamed
    :: NamedSetConstruction UniverseA
    -> NamedSetConstruction UniverseB
badNamed = coerce

badRelational
    :: CheckedRelationalSetConstruction UniverseA
    -> CheckedRelationalSetConstruction UniverseB
badRelational = coerce

badImport :: ObviousImport UniverseA -> ObviousImport UniverseB
badImport = coerce

badDefinitionView
    :: ObviousDefinitionView UniverseA
    -> ObviousDefinitionView UniverseB
badDefinitionView = coerce

badProof :: ObviousProof UniverseA -> ObviousProof UniverseB
badProof = coerce

badFailure :: ObviousFailure UniverseA -> ObviousFailure UniverseB
badFailure = coerce
