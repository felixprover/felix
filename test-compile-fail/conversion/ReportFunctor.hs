{-# LANGUAGE NoImplicitPrelude #-}

module ReportFunctor where

import Base
import Felix.Checking.Kernel.Conversion

bad
    :: ConversionReport ConversionDecision
    -> ConversionReport ConversionDecision
bad = fmap (const NotConvertible)
