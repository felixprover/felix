{-# LANGUAGE NoImplicitPrelude #-}

module RawIngress where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping
import Felix.Checking.Kernel.Conversion

bad = convertibleChecked emptyGlobalTyping (conversionLimit 1) CTruth CTruth
