{-# LANGUAGE NoImplicitPrelude #-}

-- | Work permitted for one production conversion attempt.
module Felix.Checking.Kernel.Conversion.Policy
    ( productionConversionOperationLimit
    ) where

import Felix.Checking.Kernel.Conversion (ConversionLimit, conversionLimit)


-- Each evaluator transition or delegated Core work unit consumes one unit.
-- This is not a time or memory bound. Current allowances and historical
-- measurements are described in benchmark/readme.md#work-budgets.
productionConversionOperationLimit :: ConversionLimit
productionConversionOperationLimit = conversionLimit 2000000
