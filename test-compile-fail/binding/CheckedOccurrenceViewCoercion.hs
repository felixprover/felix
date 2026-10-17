module CheckedOccurrenceViewCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core (CheckedOccurrenceView)

newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badOccurrenceView
    :: CheckedOccurrenceView UniverseA
    -> CheckedOccurrenceView UniverseB
badOccurrenceView = coerce
