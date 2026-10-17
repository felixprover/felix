{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The small source-facing diagnostic value shared by batch reporting.
-- Domain modules retain their structured failures and convert only at the
-- presentation boundary; this type deliberately carries no generic metadata.
module Felix.Report.Diagnostic
    ( Diagnostic(..)
    , DiagnosticSeverity(..)
    , DiagnosticCode(..)
    , diagnosticCodeText
    , allDiagnosticCodes
    ) where

import Base
import Felix.Report.Location (Location)

import Prettyprinter (Doc)

data DiagnosticCode
    = DiagnosticAtpCountermodel
    | DiagnosticAtpContradictoryInput
    | DiagnosticAtpTimeout
    | DiagnosticAtpResourceOut
    | DiagnosticAtpGaveUp
    | DiagnosticAtpUnknown
    | DiagnosticAtpIndeterminate
    | DiagnosticAtpProtocol
    | DiagnosticAtpProcess
    | DiagnosticProofExpectedUniversal
    | DiagnosticProofExpectedImplication
    | DiagnosticProofExpectedAssumptiveGoal
    | DiagnosticProofAssumptionMismatch
    | DiagnosticProofSetInductionAmbiguous
    | DiagnosticProofTransfiniteInductionAmbiguous
    | DiagnosticProofUnknownReference
    | DiagnosticProofObviousNoMatch
    | DiagnosticProofObviousAntecedentUnavailable
    | DiagnosticProofObviousParameterUndetermined
    | DiagnosticProofObviousFalsityPairUnavailable
    | DiagnosticProofObviousHigherOrderUnsupported
    | DiagnosticProofObviousTermOutsideUniverse
    | DiagnosticProofObviousDefinitionEvidenceRequired
    | DiagnosticProofObviousSaturated
    | DiagnosticProofObviousResourceExhausted
    | DiagnosticProofObviousRepeatedState
    | DiagnosticProofObviousMalformed
    | DiagnosticProofObviousIntegrity
    | DiagnosticProofObviousDiagnosticIntegrity
    | DiagnosticParseUnconsumedInput
    | DiagnosticParseAmbiguous
    | DiagnosticHtmlMissingRenderHint
    | DiagnosticHtmlUnsupportedMarkup
    | DiagnosticHtmlSectionHierarchy
    deriving stock (Show, Eq, Ord, Enum, Bounded)

diagnosticCodeText :: DiagnosticCode -> Text
diagnosticCodeText = \case
    DiagnosticAtpCountermodel -> "FELIX-ATP-COUNTERMODEL"
    DiagnosticAtpContradictoryInput -> "FELIX-ATP-CONTRADICTORY-INPUT"
    DiagnosticAtpTimeout -> "FELIX-ATP-TIMEOUT"
    DiagnosticAtpResourceOut -> "FELIX-ATP-RESOURCE-OUT"
    DiagnosticAtpGaveUp -> "FELIX-ATP-GAVE-UP"
    DiagnosticAtpUnknown -> "FELIX-ATP-UNKNOWN"
    DiagnosticAtpIndeterminate -> "FELIX-ATP-INDETERMINATE"
    DiagnosticAtpProtocol -> "FELIX-ATP-PROTOCOL"
    DiagnosticAtpProcess -> "FELIX-ATP-PROCESS"
    DiagnosticProofExpectedUniversal ->
        "FELIX-PROOF-EXPECTED-UNIVERSAL"
    DiagnosticProofExpectedImplication ->
        "FELIX-PROOF-EXPECTED-IMPLICATION"
    DiagnosticProofExpectedAssumptiveGoal ->
        "FELIX-PROOF-EXPECTED-ASSUMPTIVE-GOAL"
    DiagnosticProofAssumptionMismatch ->
        "FELIX-PROOF-ASSUMPTION-MISMATCH"
    DiagnosticProofSetInductionAmbiguous ->
        "FELIX-PROOF-SET-INDUCTION-AMBIGUOUS"
    DiagnosticProofTransfiniteInductionAmbiguous ->
        "FELIX-PROOF-TRANSFINITE-INDUCTION-AMBIGUOUS"
    DiagnosticProofUnknownReference -> "FELIX-PROOF-UNKNOWN-REFERENCE"
    DiagnosticProofObviousNoMatch -> "FELIX-PROOF-OBVIOUS-NO-MATCH"
    DiagnosticProofObviousAntecedentUnavailable ->
        "FELIX-PROOF-OBVIOUS-ANTECEDENT-UNAVAILABLE"
    DiagnosticProofObviousParameterUndetermined ->
        "FELIX-PROOF-OBVIOUS-PARAMETER-UNDETERMINED"
    DiagnosticProofObviousFalsityPairUnavailable ->
        "FELIX-PROOF-OBVIOUS-FALSITY-PAIR-UNAVAILABLE"
    DiagnosticProofObviousHigherOrderUnsupported ->
        "FELIX-PROOF-OBVIOUS-HIGHER-ORDER-UNSUPPORTED"
    DiagnosticProofObviousTermOutsideUniverse ->
        "FELIX-PROOF-OBVIOUS-TERM-OUTSIDE-UNIVERSE"
    DiagnosticProofObviousDefinitionEvidenceRequired ->
        "FELIX-PROOF-OBVIOUS-DEFINITION-EVIDENCE-REQUIRED"
    DiagnosticProofObviousSaturated -> "FELIX-PROOF-OBVIOUS-SATURATED"
    DiagnosticProofObviousResourceExhausted ->
        "FELIX-PROOF-OBVIOUS-RESOURCE-EXHAUSTED"
    DiagnosticProofObviousRepeatedState ->
        "FELIX-PROOF-OBVIOUS-REPEATED-STATE"
    DiagnosticProofObviousMalformed -> "FELIX-PROOF-OBVIOUS-MALFORMED"
    DiagnosticProofObviousIntegrity -> "FELIX-PROOF-OBVIOUS-INTEGRITY"
    DiagnosticProofObviousDiagnosticIntegrity ->
        "FELIX-PROOF-OBVIOUS-DIAGNOSTIC-INTEGRITY"
    DiagnosticParseUnconsumedInput -> "FELIX-PARSE-UNCONSUMED-INPUT"
    DiagnosticParseAmbiguous -> "FELIX-PARSE-AMBIGUOUS"
    DiagnosticHtmlMissingRenderHint -> "FELIX-HTML-MISSING-RENDER-HINT"
    DiagnosticHtmlUnsupportedMarkup -> "FELIX-HTML-UNSUPPORTED-MARKUP"
    DiagnosticHtmlSectionHierarchy -> "FELIX-HTML-SECTION-HIERARCHY"

allDiagnosticCodes :: [DiagnosticCode]
allDiagnosticCodes = [minBound .. maxBound]

data Diagnostic = Diagnostic
    { diagnosticSeverity :: !DiagnosticSeverity
    , diagnosticCode :: !DiagnosticCode
    , diagnosticTitle :: !Text
    , diagnosticPrimary :: !(Maybe Location)
    , diagnosticMessage :: !(Doc ())
    , diagnosticNotes :: ![Doc ()]
    , diagnosticHelp :: ![Doc ()]
    }

data DiagnosticSeverity
    = DiagnosticError
    | DiagnosticWarning
    deriving stock (Show, Eq, Ord)
