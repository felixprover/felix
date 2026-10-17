#!/usr/bin/env bash
# Exercise the real executable startup hook and GHC's RTS option precedence.
set -euo pipefail
repository=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository"
unset GHCRTS
ghc=$(stack path --compiler-exe)
work=$(mktemp -d "${TMPDIR:-/tmp}/felix-runtime-defaults.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
cp cbits/runtime-defaults.c "$work/defaults.c"
cd "$work"
cat > Main.hs <<'HS'
import GHC.Conc
import GHC.RTS.Flags
main :: IO ()
main = do
    processors <- getNumProcessors
    capabilities <- getNumCapabilities
    flags <- getRTSFlags
    putStrLn (unwords (map show
        [fromIntegral processors, fromIntegral capabilities,
         minAllocAreaSize (gcFlags flags)]))
HS
"$ghc" -threaded -rtsopts -with-rtsopts=-A64m Main.hs defaults.c -o probe > build.log 2>&1 || {
    cat build.log >&2
    exit 1
}

check() {
    local inherited=$1 expected=$2 mib=$3 output processors capabilities blocks
    shift 3
    output=$(GHCRTS="$inherited" ./probe "$@" 2> rts.log) || {
        cat rts.log >&2
        exit 1
    }
    read -r processors capabilities blocks <<< "$output"
    case $expected in
        auto) expected=$((2 * processors / 3))
              ((expected >= 1)) || expected=1
              ((expected <= 16)) || expected=16 ;;
        all) expected=$processors ;;
        capped) expected=$((processors < 2 ? processors : 2)) ;;
    esac
    # GHC reports the allocation area in 4-KiB blocks.
    if [[ $capabilities != "$expected" || $blocks != "$((mib * 256))" ]]; then
        printf 'Unexpected RTS defaults: %s (expected N=%s, allocation=%s MiB)\n' \
            "$output" "$expected" "$mib" >&2
        exit 1
    fi
}

check '' auto 64
check '-N2' 2 64
check '-A16m' auto 16
check '-s' auto 64
check '-N2 -A16m' 3 32 +RTS -N3 -A32m -RTS
check '' 1 64 +RTS -N1 --RTS --jobs 3
check '' all 64 +RTS -N -RTS
check '' capped 64 +RTS -maxN2 -RTS
printf '%s\n' 'Runtime defaults and overrides passed.'
