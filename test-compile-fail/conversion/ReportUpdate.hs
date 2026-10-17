{-# LANGUAGE NoImplicitPrelude #-}

module ReportUpdate where

import Base
import Felix.Checking.Kernel.Conversion

bad
    :: ConversionReport ConversionDecision
    -> ConversionReport ConversionDecision
bad report = report { conversionResult = Right Convertible }
