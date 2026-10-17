#!/usr/bin/env bash
set -eo pipefail
cd -- "$(dirname -- "$0")/.."

mode=${1:?Pass a Make profiling target}
case $mode in
    profile|profileall|profilejson|profilewarm|profilemem|profileparser|profilebaseline) ;;
    *) printf 'Unknown profiling target: %s\n' "$mode" >&2; exit 2 ;;
esac
if [[ $mode == profilebaseline && ${PROFILE_CACHE_FLAGS:-} != '' && $PROFILE_CACHE_FLAGS != --refresh ]]; then
    printf 'PROFILE_CACHE_FLAGS must be --refresh or empty\n' >&2
    exit 2
fi
if [[ $mode == profilebaseline && -z $PROFILE_STORE ]]; then
    printf 'PROFILE_STORE must name a verification store\n' >&2
    exit 2
fi

# Validate before process substitution, whose exit status Bash does not propagate.
perl tools/verification-command.pl check "${FELIX_VERIFY_FLAGS:-}"
verify_flags=()
while IFS= read -r -d '' argument; do verify_flags+=("$argument"); done \
    < <(perl tools/verification-command.pl args "${FELIX_VERIFY_FLAGS:-}")
read -r -a build_flags <<< "${STACK_BUILD_FLAGS:-}"
read -r -a rts_flags <<< "${PROFILE_RTS_FLAGS:-}"

stack_command=(stack)
instrumentation=()
if [[ $mode == profilebaseline ]]; then
    stack build "${build_flags[@]}" felix:exe:felix felix:bench:source-scan-bench --no-run-benchmarks
else
    stack_command+=(--stack-yaml stack.yaml --work-dir .stack-work-profile-o2)
    "${stack_command[@]}" build "${build_flags[@]}" --profile \
        --ghc-options "$PROFILE_GHC_OPTIONS" felix:exe:felix
    instrumentation=(--profile)
fi
binary=$("${stack_command[@]}" exec "${instrumentation[@]}" -- which felix)
vampire=$(command -v "${FELIX_VAMPIRE:-vampire}")
stem="$PROFILE_DIR/$(date +%y%m%d_%H%M%S)-${mode#profile}"
stem=${stem%-}
mkdir -p -- "$PROFILE_DIR"

command=("$binary" "$LIBRARY_PROFILE" -t 20 --jobs "$FELIX_JOBS" --store-report)
profile_rts=("$PROFILE_RTS_OPTION" "-po$stem")
case $mode in
    profilebaseline)
        mkdir -p -- "$(dirname -- "$PROFILE_STORE")"
        command+=(--store "$PROFILE_STORE")
        [[ -z $PROFILE_CACHE_FLAGS ]] || command+=(--refresh)
        profile_rts=()
        dist=$(stack path --dist-dir)
        "$dist/build/source-scan-bench/source-scan-bench" manifest "$LIBRARY_PROFILE" > "$stem.inputs"
        ;;
    profilewarm) ;;
    profileparser) command=("$binary" "$LIBRARY_PROFILE" --parseonly) ;;
    *) command+=(--fresh) ;;
esac
command+=("${verify_flags[@]}")
if [[ $mode == profilemem ]]; then profile_rts=(-hc "-po$stem"); fi
measured=("${command[@]}" +RTS "-s$stem.rts" "${profile_rts[@]}" "${rts_flags[@]}" -RTS)

{
    printf 'target: make %s\n' "$mode"
    printf 'git revision: '; git rev-parse HEAD
    printf 'worktree status:\n'; git status --short
    printf 'command arguments:\n'; printf '<%s>\n' "${measured[@]}"
    printf 'source/build hashes:\n'
    git ls-files -z -- source cli cbits package.yaml stack.yaml tools/profile.sh \
        tools/verification-command.pl benchmark/run-timed.sh | xargs -0 shasum -a 256
    printf 'binary hashes:\n'; shasum -a 256 "$binary" "$vampire"
    printf 'input sha256:\n'; shasum -a 256 "$LIBRARY_PROFILE"
    printf 'resolved dependency hashes:\n'; shasum -a 256 stack.yaml.lock felix.cabal
    printf 'selected Stack configuration:\n'
    if [[ $mode == profilebaseline ]]; then
        shasum -a 256 "${STACK_YAML:-stack.yaml}"
        printf 'store before run:\n'
        for file in "$PROFILE_STORE" "$PROFILE_STORE-wal"; do
            if [[ -f $file ]]; then shasum -a 256 "$file"; else printf 'absent: %s\n' "$file"; fi
        done
    else
        shasum -a 256 stack.yaml
        printf 'profile GHC options: %s\n' "$PROFILE_GHC_OPTIONS"
    fi
    printf 'build flags: %s\n' "${STACK_BUILD_FLAGS:-}"
    printf 'GHC: '; "${stack_command[@]}" exec -- ghc --numeric-version
    printf 'Stack: '; stack --version
    printf 'Vampire:\n'; "$vampire" --version
    printf 'system: '; uname -a
    printf 'Vampire cores per process: 2\nfilesystem cache: uncontrolled\n'
} > "$stem.meta" 2>&1

if [[ $mode == profilewarm ]]; then
    printf 'Warming the default store for %s\n' "$LIBRARY_PROFILE"
    status=0
    "${command[@]}" +RTS "${rts_flags[@]}" -RTS > "$stem.warm.run.txt" 2>&1 || status=$?
    printf '%s\n' "$status" > "$stem.warm.status"
    sed -n '1,240p' "$stem.warm.run.txt" >&2
    if ((status != 0)); then exit "$status"; fi
fi

printf 'Writing profile to %s.*\n' "$stem"
status=0
benchmark/run-timed.sh resources "$stem.time" -- "${measured[@]}" > "$stem.run.txt" 2>&1 || status=$?
printf '%s\n' "$status" > "$stem.status"
sed -n '1,240p' "$stem.run.txt" >&2
if ((status != 0)); then exit "$status"; fi

case $mode in
    profilebaseline) ;;
    profilemem)
        (cd -- "$(dirname -- "$stem")" && hp2ps "$(basename -- "$stem").hp")
        gs -q -dNOPAUSE -dBATCH -sOutputFile="$stem.rotated.ps" -sDEVICE=ps2write \
            -c '<</Orientation 1>> setpagedevice' -- "$stem.ps"
        mv -- "$stem.rotated.ps" "$stem.ps"
        ;;
    *) icicle --strict --format "$PROFILE_FORMAT" --metric ticks --summary-min-share 0.04 "$stem.prof" ;;
esac
