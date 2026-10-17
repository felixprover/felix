module DecoderBudgetReset where

-- Nested consumers cannot reconstruct a fresh internal allowance.
import Felix.Codec.Admission (newDecoderBudget, standardDecoderLimits)

reset = newDecoderBudget standardDecoderLimits
