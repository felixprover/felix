{-# LANGUAGE NoImplicitPrelude #-}

-- | The sole bridge from pair-bound conversion evidence to a fresh proof node.
module Felix.Checking.Kernel.Derivation.Conversion
    ( ConversionSealError(..)
    , sealSuccessfulConversion
    ) where

import Base
import Felix.Checking.Core (ScopedCheckedCore)
import Felix.Checking.Kernel.Conversion.Checked
    ( SuccessfulConversion
    , eliminateSuccessfulConversion
    )
import Felix.Checking.Kernel.Derivation.Internal (KernelDerivation(..))


data ConversionSealError = ConversionSealSourceMismatch

sealSuccessfulConversion
    :: Eq global
    => SuccessfulConversion global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> Either
        ConversionSealError
        (ScopedCheckedCore global, KernelDerivation global)
sealSuccessfulConversion witness source derivation =
    eliminateSuccessfulConversion witness \witnessSource target cost ->
        if source == witnessSource
            then Right (target, ConvertJudgement derivation target cost)
            else Left ConversionSealSourceMismatch
