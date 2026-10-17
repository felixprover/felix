#!/usr/bin/env bash
# Run through `make check-api`, which builds and supplies the Stack environment.
set -euo pipefail

repository=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
fixtures="$repository/test-compile-fail"
temporary=$(mktemp -d "${TMPDIR:-/tmp}/felix-api.XXXXXX")
trap 'rm -rf "$temporary"' EXIT
compiler=(ghc -v0 -i -fforce-recomp -fno-code -fmax-errors=100 -package felix -outputdir "$temporary")

# A valid client must compile before any rejection can count as evidence.
"${compiler[@]}" "$fixtures/authority/CheckedEvidenceProducers.hs"

reject() {
    local fixture=$1 diagnostic=$2
    if "${compiler[@]}" "$fixtures/$fixture.hs" >"$temporary/log" 2>&1; then
        printf '%s unexpectedly compiled\n' "$fixture" >&2
        exit 1
    fi
    if ! rg -q "$diagnostic" "$temporary/log"; then
        cat "$temporary/log" >&2
        printf '%s failed for an unexpected reason\n' "$fixture" >&2
        exit 1
    fi
    # Grouped coercion probes must reject every attempted escape independently.
    for binding in "${@:3}"; do
        if ! rg -q "In an equation for .$binding." "$temporary/log"; then
            cat "$temporary/log" >&2
            printf '%s did not reject %s\n' "$fixture" "$binding" >&2
            exit 1
        fi
    done
}

# Checked evidence cannot be forged or moved to another scope or universe.
reject authority/CarrierAndCoreCoercion 'Couldn.t match' badCarrier badFrozen badScoped
reject authority/ProofCoercion 'Couldn.t match' badContext badProof badImport badDerivation badReplay badScopedReplay
reject authority/AggregateAndObviousCoercion 'Couldn.t match' badNamed badRelational badImport badDefinitionView badProof badFailure
for file in "$fixtures"/authority/CheckedOccurrenceCoercion.hs \
        "$fixtures"/binding/*Coercion.hs \
        "$fixtures"/conversion/{PreparedSpine,ProofAction}Coercion.hs; do
    relative=${file#"$fixtures/"}
    reject "${relative%.hs}" "Couldn.t match"
done
for file in "$fixtures"/{authority,conversion}/Generic*.hs; do
    relative=${file#"$fixtures/"}
    reject "${relative%.hs}" 'No instance for.*Generic'
done

# Internal constructors and unchecked proof services stay package-private.
for fixture in authority/InternalCarrierImport authority/InternalStructuralProofAuthorizationImport \
        authority/DecoderBudgetReset binding/InternalResolvedSubstrateImport \
        conversion/HiddenCheckedImport conversion/HiddenDerivationImport \
        conversion/HiddenEngineImport conversion/HiddenSealerImport \
        conversion/HiddenFormationImport conversion/HiddenFormationProofImport; do
    reject "$fixture" 'hidden module'
done
reject authority/PublicCarrierConstructor 'does not export'
reject authority/ImportedEvidenceConstructor 'does not export'
reject authority/BareStructuralProof 'StructuralProofAuthorization'
reject authority/CacheDecoderRawGet 'Couldn.t match'
reject conversion/RawIngress 'ScopedCheckedCore'
reject conversion/CostConstruction 'Illegal term-level use|Data constructor not in scope'
reject conversion/PreparedSpineConstruction 'Illegal term-level use|Data constructor not in scope'
reject conversion/ReportConstruction 'Illegal term-level use|Data constructor not in scope'
reject conversion/WitnessConstruction 'Not in scope: type constructor|Data constructor not in scope'
reject conversion/ProofActionConstructor 'Illegal term-level use|Data constructor not in scope'
reject conversion/ProofActionState 'MonadState'
reject conversion/ProofActionCatch 'MonadError'
reject conversion/ReportFunctor 'Functor ConversionReport'
reject conversion/WitnessElimination 'does not export'
reject conversion/StoredPairReplay 'does not export'

# Public observations must not also permit updates to sealed evidence.
for fixture in authority/CalculationLawUpdate authority/ParsedArtefactPayloadUpdate \
        authority/DecodedParsedBlocksUpdate authority/IdentifiedParsedSyntaxUpdate \
        authority/ParsedSourceUpdate conversion/PreparedSpineUpdate conversion/ReportUpdate; do
    reject "$fixture" 'Not in scope: record field|not a record selector'
done
printf 'Public API boundary checks passed.\n'
