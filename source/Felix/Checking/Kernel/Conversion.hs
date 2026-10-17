{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked beta-eta conversion with deterministic work accounting.
module Felix.Checking.Kernel.Conversion
    ( ConversionLimit
    , ConversionPool
    , ConversionCost
    , conversionLimit
    , conversionLimitAmount
    , conversionPool
    , conversionPoolAmount
    , conversionCostAmount
    , capConversionLimit
    , debitConversionCost
    , ConversionRecoveryTyping(..)
    , ConversionDecision(..)
    , ConversionInputError(..)
    , ConversionInternalError(..)
    , ConversionFailure(..)
    , ConversionReport
    , conversionResult
    , conversionCost
    , convertibleChecked
    , betaNormalizeChecked
    , residualizeHeadChecked
    , PreparedSpine
    , PreparedSpineStep(..)
    , preparedSpineSteps
    , preparedSpineTerminal
    , prepareImplicationSpineChecked
    ) where

import Felix.Checking.Kernel.Conversion.Checked
