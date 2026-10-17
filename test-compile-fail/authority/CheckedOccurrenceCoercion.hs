module CheckedOccurrenceCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core (CheckedOccurrence)

newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badOccurrence
    :: CheckedOccurrence UniverseA
    -> CheckedOccurrence UniverseB
badOccurrence = coerce
