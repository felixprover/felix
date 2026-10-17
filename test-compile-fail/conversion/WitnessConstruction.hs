{-# LANGUAGE NoImplicitPrelude #-}

module WitnessConstruction where

import Base
import Felix.Checking.Kernel.Conversion

bad :: SuccessfulConversion global
bad = SuccessfulConversion (error "left") (error "right") (error "cost")
