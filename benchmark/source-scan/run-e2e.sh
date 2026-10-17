#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
timed_command="$script_dir/../run-timed.sh"

if (( $# < 5 || $# > 6 )); then
    printf '%s\n' \
        'usage: run-e2e.sh BASELINE-FELIX CANDIDATE-FELIX BASELINE-HELPER CANDIDATE-HELPER ROOT [OUTPUT-DIRECTORY]' >&2
    exit 2
fi

: "${NAPROCHE_LIB:?NAPROCHE_LIB must name the absolute library root}"
: "${BASELINE_REVISION:?BASELINE_REVISION is required}"
: "${CANDIDATE_REVISION:?CANDIDATE_REVISION is required}"
: "${BASELINE_BUILD_COMMAND:?BASELINE_BUILD_COMMAND is required}"
: "${CANDIDATE_BUILD_COMMAND:?CANDIDATE_BUILD_COMMAND is required}"
if [[ $NAPROCHE_LIB != /* ]]; then
    printf 'NAPROCHE_LIB must be absolute: %s\n' "$NAPROCHE_LIB" >&2
    exit 2
fi

baseline_felix=$(realpath "$1")
candidate_felix=$(realpath "$2")
baseline_helper=$(realpath "$3")
candidate_helper=$(realpath "$4")
root=$(realpath "$5")
requested_output=${6:-}
repetitions=${SOURCE_SCAN_REPETITIONS:-5}
jobs=${FELIX_JOBS:-8}
time_limit=${SOURCE_SCAN_TIME_LIMIT:-20}
memory_limit=${SOURCE_SCAN_MEMORY_LIMIT:-}

for executable in \
    "$baseline_felix" "$candidate_felix" \
    "$baseline_helper" "$candidate_helper"
do
    if [[ ! -x $executable ]]; then
        printf 'executable is not runnable: %s\n' "$executable" >&2
        exit 2
    fi
done

if (( repetitions < 3 )); then
    printf 'SOURCE_SCAN_REPETITIONS must be at least 3\n' >&2
    exit 2
fi

if [[ -n $requested_output ]]; then
    output=$requested_output
else
    output="profiling/source-scan/$(date +%Y%m%d-%H%M%S)-e2e"
fi

if [[ -e $output ]]; then
    printf 'output path already exists: %s\n' "$output" >&2
    exit 2
fi

mkdir -p "$output"
output=$(realpath "$output")

write_executable_metadata() {
    local label=$1
    local executable=$2
    {
        printf '%s path: %s\n' "$label" "$executable"
        printf '%s sha256: ' "$label"
        sha256sum "$executable" | cut -d ' ' -f 1
    } >> "$output/metadata.txt"
}

{
    printf 'source-scan end-to-end run v1\n'
    printf 'root: %s\n' "$root"
    printf 'NAPROCHE_LIB: %s\n' "$NAPROCHE_LIB"
    printf 'repetitions: %s\n' "$repetitions"
    printf 'jobs: %s\n' "$jobs"
    printf 'time limit: %s\n' "$time_limit"
    printf 'memory limit: %s\n' "${memory_limit:-default}"
    printf 'baseline revision: %s\n' "$BASELINE_REVISION"
    printf 'candidate revision: %s\n' "$CANDIDATE_REVISION"
    printf 'baseline build: %s\n' "$BASELINE_BUILD_COMMAND"
    printf 'candidate build: %s\n' "$CANDIDATE_BUILD_COMMAND"
    printf 'helper optimization: %s\n' \
        "${SOURCE_SCAN_HELPER_OPTIMIZATION:-see recorded build configurations}"
    printf 'CLI/library optimization: %s\n' \
        "${SOURCE_SCAN_CLI_OPTIMIZATION:-Stack/Cabal configured default}"
    printf 'filesystem cache policy: %s\n' \
        "${SOURCE_SCAN_FILESYSTEM_CACHE_POLICY:-uncontrolled-warm-host-cache}"
    printf 'GHC: '
    ghc --numeric-version
    printf 'text: '
    ghc-pkg latest text --simple-output
    printf 'Stack: '
    stack --version
    printf 'system: '
    uname -srmo
    printf 'processors: '
    getconf _NPROCESSORS_ONLN
    printf 'GHC capabilities: default -N (%s)\n' \
        "$(getconf _NPROCESSORS_ONLN)"
    printf 'Vampire cores per process: 2\n'
    printf 'FELIX_VAMPIRE: %s\n' "${FELIX_VAMPIRE:-vampire}"
    printf 'hardware:\n'
    lscpu
    printf 'Vampire:\n'
    "${FELIX_VAMPIRE:-vampire}" --version
} > "$output/metadata.txt" 2>&1

write_executable_metadata baseline-felix "$baseline_felix"
write_executable_metadata candidate-felix "$candidate_felix"
write_executable_metadata baseline-helper "$baseline_helper"
write_executable_metadata candidate-helper "$candidate_helper"

preflight_work="$output/preflight-work"
mkdir -p "$preflight_work"
(
    cd "$preflight_work"
    NAPROCHE_LIB="$NAPROCHE_LIB" \
        "$baseline_helper" manifest "$root"
) > "$output/baseline.manifest"
(
    cd "$preflight_work"
    NAPROCHE_LIB="$NAPROCHE_LIB" \
        "$candidate_helper" manifest "$root"
) > "$output/candidate.manifest"

if ! cmp -s "$output/baseline.manifest" "$output/candidate.manifest"; then
    diff -u "$output/baseline.manifest" "$output/candidate.manifest" \
        > "$output/manifest.diff" || true
    printf 'baseline and candidate manifests differ; see %s\n' \
        "$output/manifest.diff" >&2
    exit 1
fi

warm_build_dir="$output/warm-build"
mkdir -p "$warm_build_dir/work" "$warm_build_dir/store"
warm_store="$warm_build_dir/store/felix.sqlite"
warm_args=("$root" --store "$warm_store" -t "$time_limit" --jobs "$jobs" --store-report)
if [[ -n $memory_limit ]]; then
    warm_args+=(--memlimit "$memory_limit")
fi
(
    cd "$warm_build_dir/work"
    "$timed_command" resources "$warm_build_dir/time.txt" -- \
        env NAPROCHE_LIB="$NAPROCHE_LIB" \
        "$baseline_felix" "${warm_args[@]}" \
        +RTS "-s$warm_build_dir/rts.txt" -RTS \
        > "$warm_build_dir/stdout.txt" \
        2> "$warm_build_dir/stderr.txt"
)

for suffix in -journal -wal -shm; do
    if [[ -e $warm_store$suffix ]]; then
        printf 'closed warm store retained SQLite sidecar: %s\n' \
            "$warm_store$suffix" >&2
        exit 1
    fi
done

warm_snapshot="$output/warm.snapshot.sqlite"
cp "$warm_store" "$warm_snapshot"
warm_digest=$(sha256sum "$warm_snapshot" | cut -d ' ' -f 1)
{
    printf 'warm creation command:'
    printf ' %q' "$baseline_felix" "${warm_args[@]}"
    printf '\n'
    printf 'warm snapshot sha256: %s\n' "$warm_digest"
    printf 'SQLite closed sidecars: absent\n'
    printf 'restore: byte-copy immutable snapshot into a new store directory\n'
} > "$output/warm-snapshot.txt"

run_variant() {
    local case_name=$1
    local variant=$2
    local executable=$3
    local state=$4
    local html_requested=$5
    local repetition=$6
    local ordinal=$7
    local run_name
    run_name=$(printf '%s-%02d-%s-%s' \
        "$case_name" "$repetition" "$ordinal" "$variant")
    local run_dir="$output/runs/$run_name"
    local work_dir="$run_dir/work"
    local store_dir="$run_dir/store"
    local store_path="$store_dir/felix.sqlite"
    mkdir -p "$work_dir" "$store_dir"

    if [[ $state == warm ]]; then
        cp "$warm_snapshot" "$store_path"
        local restored_digest
        restored_digest=$(sha256sum "$store_path" | cut -d ' ' -f 1)
        if [[ $restored_digest != "$warm_digest" ]]; then
            printf 'warm store restore digest mismatch for %s\n' "$run_name" >&2
            exit 1
        fi
    elif [[ -e $store_path ]]; then
        printf 'fresh store unexpectedly exists for %s\n' "$run_name" >&2
        exit 1
    fi

    local args=("$root" --store "$store_path" -t "$time_limit" --jobs "$jobs" --store-report)
    if [[ -n $memory_limit ]]; then
        args+=(--memlimit "$memory_limit")
    fi
    if [[ $html_requested == yes ]]; then
        args+=(--html)
    fi

    {
        printf 'variant: %s\n' "$variant"
        printf 'state: %s\n' "$state"
        printf 'html: %s\n' "$html_requested"
        printf 'repetition: %s\n' "$repetition"
        printf 'schedule ordinal: %s\n' "$ordinal"
        printf 'command:'
        printf ' %q' "$executable" "${args[@]}"
        printf ' +RTS -s%s -RTS\n' "$run_dir/rts.txt"
    } > "$run_dir/command.txt"

    (
        cd "$work_dir"
        "$timed_command" resources "$run_dir/time.txt" -- \
            env NAPROCHE_LIB="$NAPROCHE_LIB" \
            "$executable" "${args[@]}" \
            +RTS "-s$run_dir/rts.txt" -RTS \
            > "$run_dir/stdout.txt" \
            2> "$run_dir/stderr.txt"
    )
}

case_names=(fresh-no-html warm-no-html fresh-html warm-html)
case_index=0
mkdir -p "$output/runs"
for case_name in "${case_names[@]}"; do
    case "$case_name" in
        fresh-no-html) state=fresh; html_requested=no ;;
        warm-no-html) state=warm; html_requested=no ;;
        fresh-html) state=fresh; html_requested=yes ;;
        warm-html) state=warm; html_requested=yes ;;
    esac
    for (( repetition = 1; repetition <= repetitions; repetition++ )); do
        if (( (case_index + repetition) % 2 == 0 )); then
            run_variant "$case_name" baseline "$baseline_felix" \
                "$state" "$html_requested" "$repetition" 1
            run_variant "$case_name" candidate "$candidate_felix" \
                "$state" "$html_requested" "$repetition" 2
        else
            run_variant "$case_name" candidate "$candidate_felix" \
                "$state" "$html_requested" "$repetition" 1
            run_variant "$case_name" baseline "$baseline_felix" \
                "$state" "$html_requested" "$repetition" 2
        fi
    done
    (( case_index += 1 ))
done

printf 'source-scan end-to-end results: %s\n' "$output"
