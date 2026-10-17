#!/usr/bin/env bash
set -euo pipefail

repository=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
temporary=$(mktemp -d "${TMPDIR:-/tmp}/felix-imports.XXXXXX")
trap 'rm -rf "$temporary"' EXIT

reject() {
    if bash "$repository/test/check-imports.sh" "$1" >"$temporary/log" 2>&1; then
        printf 'Import check unexpectedly accepted %s\n' "$1" >&2
        exit 1
    fi
}

# Missing inputs must not turn into a successful empty inspection.
reject "$temporary/missing"
mkdir "$temporary/source"
reject "$temporary/source"

cat >"$temporary/source/Example.hs" <<'HS'
module Felix.Checking.Kernel.Example where
import Felix.Checking.Core
HS
bash "$repository/test/check-imports.sh" "$temporary/source"
printf 'import qualified Felix.Provers\n' >>"$temporary/source/Example.hs"
reject "$temporary/source"
rg -q 'forbidden import' "$temporary/log"

cat >"$temporary/source/Example.hs" <<'HS'
module Felix.Checking.Example where
import Felix.Checking.Core.Representation.Internal qualified as Representation
HS
reject "$temporary/source"
rg -q 'forbidden import' "$temporary/log"
