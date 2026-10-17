module LocalRefRegionCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core.Resolved (LocalRef)

data RegionA
data RegionB

badLocalRef :: LocalRef RegionA -> LocalRef RegionB
badLocalRef = coerce
