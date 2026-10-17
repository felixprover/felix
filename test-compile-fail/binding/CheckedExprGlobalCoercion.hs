module CheckedExprGlobalCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core.Resolved (CheckedExpr)

data Region
newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badCheckedExprGlobal
    :: CheckedExpr Region UniverseA
    -> CheckedExpr Region UniverseB
badCheckedExprGlobal = coerce
