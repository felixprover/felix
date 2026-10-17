module CoreBuilderRegionCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core.Resolved (CoreBuilder)

data RegionA
data RegionB

badBuilderRegion
    :: CoreBuilder RegionA global value
    -> CoreBuilder RegionB global value
badBuilderRegion = coerce
