{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | One conversion operation against a caller-owned aggregate pool. Search
-- state and error classification remain with the focused or refutation caller.
module Felix.Checking.Obvious.Conversion
    ( ObviousConversionLimitOwner(..)
    , ObviousConversionRunError(..)
    , runObviousConversion
    , PreparationResult(..)
    , runPreparatoryConversion
    , runPreparatoryBuilder
    ) where

import Base
import Felix.Checking.Core (CountedCoreFailure(..))
import Felix.Checking.Kernel.Conversion
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Kernel.Conversion.Policy
    (productionConversionOperationLimit)
import Data.Word (Word)


data ObviousConversionLimitOwner
    = ObviousConversionOperationOwner
    | ObviousConversionPoolOwner
    deriving stock (Show, Eq)

data ObviousConversionRunError
    = ObviousConversionPoolAccountingInvariant !ConversionCost !ConversionPool

-- A policy stop retains the operation at its caller. It is neither a mismatch
-- nor exhaustion of the real owner, and permits only a larger-effort retry.
data PreparationResult failure value
    = PreparationFinished !(Either failure value)
    | NeedsMoreEffort !ConversionLimit
    deriving stock (Show, Eq)

runObviousConversion
    :: ConversionPool
    -> (ConversionLimit -> ConversionReport result)
    -> Either
        ObviousConversionRunError
        (ObviousConversionLimitOwner, ConversionPool, Either ConversionFailure result)
runObviousConversion pool operation =
    let limit = capConversionLimit pool productionConversionOperationLimit
        owner
            | conversionPoolAmount pool
                    <= conversionLimitAmount productionConversionOperationLimit =
                ObviousConversionPoolOwner
            | otherwise = ObviousConversionOperationOwner
    in fmap (\(remaining, result) -> (owner, remaining, result))
        (runConversionReport pool limit operation)

runConversionReport
    :: ConversionPool
    -> ConversionLimit
    -> (ConversionLimit -> ConversionReport result)
    -> Either ObviousConversionRunError (ConversionPool, Either ConversionFailure result)
runConversionReport pool limit operation =
    let report = operation limit
        result = conversionResult report
        cost = conversionCost report
    in result `seq` cost `seq`
        case debitConversionCost cost pool of
            Nothing -> Left (ObviousConversionPoolAccountingInvariant cost pool)
            Just remaining -> Right (remaining, result)

runPreparatoryConversion
    :: ConversionLimit
    -> ConversionPool
    -> (ConversionLimit -> ConversionReport result)
    -> Either ObviousConversionRunError
        (ObviousConversionLimitOwner, ConversionPool, PreparationResult ConversionFailure result)
runPreparatoryConversion preparation pool operation = do
    let full = capConversionLimit pool productionConversionOperationLimit
        offered = conversionLimit (min (conversionLimitAmount preparation) (conversionLimitAmount full))
        owner
            | conversionPoolAmount pool <= conversionLimitAmount productionConversionOperationLimit =
                ObviousConversionPoolOwner
            | otherwise = ObviousConversionOperationOwner
    (remaining, result) <- runConversionReport pool offered operation
    pure (owner, remaining, case result of
        Left ConversionLimitExhausted{}
            | conversionLimitAmount offered < conversionLimitAmount full -> NeedsMoreEffort offered
        _ -> PreparationFinished result)

-- Counted builders already have a compound conversion allowance. Lend only
-- the preparatory slice, then debit its actual consumption from the real pool.
-- The real pool is never replaced by the local remainder. Builders and their
-- stored proof costs are unchanged; failed structural work is retained too.
runPreparatoryBuilder
    :: ConversionLimit
    -> Word
    -> ConversionPool
    -> (Word -> ConversionPool
        -> (Either (CountedCoreFailure Proof.KernelProofBuildError) result, Word, ConversionPool))
    -> (PreparationResult (CountedCoreFailure Proof.KernelProofBuildError) result, Word, ConversionPool)
runPreparatoryBuilder preparation structural real operation =
    let offered = min (conversionLimitAmount preparation) (conversionPoolAmount real)
        (result, afterStructural, afterPool) = operation structural (conversionPool offered)
        returned = conversionPoolAmount afterPool
        invalid = PreparationFinished (Left (CountedCoreOperationFailed
            (Proof.ProofStructuralCompositionMismatch "preparatory builder replenished its allowance")))
    in if afterStructural > structural || returned > offered
        then (invalid, structural, real)
        else
            let remaining = conversionPool (conversionPoolAmount real - (offered - returned))
                outcome = case result of
                    Left (CountedCoreOperationFailed (Proof.ProofConversionLimitExhausted
                            Proof.ProofConversionAggregatePool limit))
                        | offered < conversionPoolAmount real ->
                            if conversionLimitAmount limit < conversionLimitAmount productionConversionOperationLimit
                                then NeedsMoreEffort (conversionLimit offered)
                                else PreparationFinished (Left (CountedCoreOperationFailed
                                    (Proof.ProofConversionLimitExhausted Proof.ProofConversionOperationLimit limit)))
                    _ -> PreparationFinished result
            in (outcome, afterStructural, remaining)
