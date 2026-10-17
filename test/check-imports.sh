#!/usr/bin/env bash
set -euo pipefail

repository=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
source_directory=${1:-"$repository/source"}
sources=$(find "$source_directory" -type f -name '*.hs' -print)
test -n "$sources" || { printf 'No Haskell sources: %s\n' "$source_directory" >&2; exit 1; }

# Cabal hides these modules from clients, but not from other library modules.
# Restrict access to unchecked representations; removing an import is harmless.
find "$source_directory" -type f -name '*.hs' -exec awk '
    BEGIN {
        owners["Felix.Checking.Core.Representation.Internal"] = \
            "Felix.Checking.Core Felix.Checking.Core.Resolved.Substrate.Internal Felix.Checking.GlobalTyping.Internal"
        owners["Felix.Checking.Core.Resolved.Internal"] = "Felix.Checking.Core.Resolved"
        owners["Felix.Checking.Core.Resolved.Substrate.Internal"] = "Felix.Checking.Core.Resolved.Internal"
        owners["Felix.Checking.GlobalTyping.Internal"] = "Felix.Checking.GlobalTyping Felix.Checking.Identity"
        owners["Felix.Checking.Proof.Authorization.Internal"] = "Felix.Checking.Declaration Felix.Checking.Proof"
        owners["Felix.Checking.Kernel.Conversion.Checked"] = \
            "Felix.Checking.Kernel.Conversion Felix.Checking.Kernel.Derivation Felix.Checking.Kernel.Derivation.Conversion Felix.Checking.Kernel.Proof"
        owners["Felix.Checking.Kernel.Conversion.Pure"] = "Felix.Checking.Kernel.Conversion.Checked"
        owners["Felix.Checking.Kernel.Derivation.Internal"] = \
            "Felix.Checking.Kernel.Derivation Felix.Checking.Kernel.Derivation.Conversion"
        owners["Felix.Checking.Kernel.Derivation.Conversion"] = "Felix.Checking.Kernel.Proof"
        owners["Felix.Checking.Notion.Formation"] = "Felix.Checking.Notion Felix.Checking.Notion.FormationProof"
        owners["Felix.Checking.Notion.FormationProof"] = "Felix.Checking.Declaration"
        split("Felix.Cache.Codec Felix.Checking.Core Felix.Checking.Foundation Felix.Checking.GlobalTyping Felix.Checking.LooseDeduction", dependencies, " ")
        for (i in dependencies) kernel[dependencies[i]] = 1
    }

    FNR == 1 { owner = "" }
    /^[[:space:]]*module[[:space:]]/ {
        owner = $2
        sub(/\(.*/, "", owner)
    }
    /^[[:space:]]*import[[:space:]]/ {
        for (i = 2; i <= NF; i++) {
            dependency = $i
            sub(/\(.*/, "", dependency)
            if (dependency !~ /^Felix\./) continue
            if (owner == "" \
                    || (dependency in owners && !index(" " owners[dependency] " ", " " owner " ")) \
                    || (owner ~ /^Felix\.Checking\.Kernel\./ \
                        && dependency !~ /^Felix\.Checking\.Kernel(\.|$)/ \
                        && !(dependency in kernel))) {
                printf "%s:%d: forbidden import of %s by %s\n", FILENAME, FNR, dependency, owner > "/dev/stderr"
                failed = 1
            }
            break
        }
    }
    END { exit failed }
' {} +
