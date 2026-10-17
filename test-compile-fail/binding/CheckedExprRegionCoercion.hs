module CheckedExprRegionCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core.Resolved (CheckedExpr)

data RegionA
data RegionB

badCheckedExprRegion
    :: CheckedExpr RegionA global
    -> CheckedExpr RegionB global
badCheckedExprRegion = coerce
