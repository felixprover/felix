#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
timed_command="$script_dir/../run-timed.sh"

if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
    printf '%s\n' \
        'usage: run-space.sh SOURCE-SCAN-BENCH ROOT [OUTPUT-DIRECTORY]' >&2
    exit 2
fi

helper=$(realpath "$1")
root=$(realpath "$2")
requested_output=${3:-}
revision=${SOURCE_SCAN_REVISION:-}
if [ -z "$revision" ]; then
    revision=$(git rev-parse HEAD 2>/dev/null || printf 'unrecorded')
fi

if [ ! -x "$helper" ]; then
    printf 'source-scan helper is not executable: %s\n' "$helper" >&2
    exit 2
fi

if [ -n "$requested_output" ]; then
    output=$requested_output
else
    output="profiling/source-scan/$(date +%Y%m%d-%H%M%S)-space"
fi

if [ -e "$output" ]; then
    printf 'output path already exists: %s\n' "$output" >&2
    exit 2
fi

mkdir -p "$output"
output=$(realpath "$output")

{
    printf 'source-scan space run v1\n'
    printf 'helper: %s\n' "$helper"
    printf 'helper sha256: '
    sha256sum "$helper" | cut -d ' ' -f 1
    printf 'root: %s\n' "$root"
    printf 'command cwd: %s\n' "$(pwd)"
    printf 'NAPROCHE_LIB: %s\n' "${NAPROCHE_LIB:-unset}"
    printf 'revision: %s\n' "$revision"
    printf 'build: %s\n' \
        "${SOURCE_SCAN_BUILD_COMMAND:-stack build felix:bench:source-scan-bench --no-run-benchmarks}"
    printf 'optimization: %s\n' "${SOURCE_SCAN_OPTIMIZATION:-see recorded build configuration}"
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
    printf 'hardware:\n'
    lscpu
} > "$output/metadata.txt"

"$helper" manifest "$root" > "$output/manifest.txt"

for case_name in \
    prefix \
    verification-completion \
    presentation-decoded
do
    {
        printf '%q ' "$helper" space "$root" "$case_name"
        printf '%s\n' "+RTS -T -s$output/$case_name.rts -RTS"
    } > "$output/$case_name.command"
    "$timed_command" resources "$output/$case_name.time" -- \
        "$helper" space "$root" "$case_name" \
        +RTS -T "-s$output/$case_name.rts" -RTS \
        > "$output/$case_name.out" \
        2> "$output/$case_name.err"
done

printf 'source-scan space results: %s\n' "$output"
