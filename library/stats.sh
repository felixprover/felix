#!/bin/sh

library_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)

rg --no-filename --only-matching \
    --replace '$1' \
    '^[[:space:]]*\\begin\{(definition|inductive|theorem|lemma|corollary|proposition|composition|claim)\}' \
    --glob '*.tex' "$library_dir" |
awk '
    $1 == "definition" || $1 == "inductive" { definitions++ }
    $1 != "definition" && $1 != "inductive" { theorems++ }
    END {
        printf "Definitions: %d\n", definitions
        printf "Theorems:    %d\n", theorems
    }
'
