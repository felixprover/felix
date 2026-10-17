{-# LANGUAGE NoImplicitPrelude #-}

module ReportConstruction where

import Base
import Felix.Checking.Kernel.Conversion

bad :: ConversionReport ConversionDecision
bad = ConversionReport (Right Convertible) (error "cost")
