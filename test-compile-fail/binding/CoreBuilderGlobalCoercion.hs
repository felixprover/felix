module CoreBuilderGlobalCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core.Resolved (CoreBuilder)

data Region
newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badBuilderGlobal
    :: CoreBuilder Region UniverseA value
    -> CoreBuilder Region UniverseB value
badBuilderGlobal = coerce
