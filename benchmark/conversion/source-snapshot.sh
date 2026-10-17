#!/bin/sh
set -eu

usage() {
    printf '%s\n' \
        'usage: source-snapshot.sh write OUTPUT' \
        '       source-snapshot.sh verify EXPECTED' >&2
    exit 2
}

test "$#" -eq 2 || usage
mode=$1
target=$2

repository=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
worktree_library=$(CDPATH= cd -- "$repository/library" && pwd -P)
configured_library=${NAPROCHE_LIB:-$worktree_library}
library_root=$(CDPATH= cd -- "$configured_library" && pwd -P)

if test "$library_root" != "$worktree_library"; then
    printf 'configured library root does not match worktree: %s != %s\n' \
        "$library_root" "$worktree_library" >&2
    exit 1
fi

digest_stream() {
    shasum -a 256 | awk '{ print $1 }'
}

write_snapshot() {
    printf 'conversion-source-snapshot-v3\n'
    printf 'library-root %s\n' "$library_root"
    printf 'head %s\n' "$(git -C "$repository" rev-parse HEAD)"
    printf 'tracked-diff '
    git -C "$repository" diff --binary --no-ext-diff HEAD | digest_stream
    printf 'package-yaml '
    shasum -a 256 "$repository/package.yaml" | awk '{ print $1 }'
    printf 'generated-package '
    shasum -a 256 "$repository/felix.cabal" | awk '{ print $1 }'
    printf 'stack-yaml '
    shasum -a 256 "$repository/stack.yaml" | awk '{ print $1 }'
    printf 'stack-lock '
    shasum -a 256 "$repository/stack.yaml.lock" | awk '{ print $1 }'
    printf 'driver-manifest '
    find "$repository/benchmark/conversion" -type f -print \
        | sort \
        | while IFS= read -r path; do
            relative=${path#"$repository/"}
            digest=$(shasum -a 256 "$path" | awk '{ print $1 }')
            printf '%s %s\n' "$relative" "$digest"
        done \
        | digest_stream
    printf 'suite-digest '
    shasum -a 256 "$repository/benchmark/conversion/Cases.hs" \
        | awk '{ print $1 }'
    printf 'library-manifest '
    find "$library_root" -type f -print \
        | sort \
        | while IFS= read -r path; do
            relative=${path#"$library_root/"}
            digest=$(shasum -a 256 "$path" | awk '{ print $1 }')
            printf '%s %s\n' "$relative" "$digest"
        done \
        | digest_stream
    printf 'untracked-begin\n'
    git -C "$repository" ls-files --others --exclude-standard \
        | sort \
        | while IFS= read -r relative; do
            path="$repository/$relative"
            if test -f "$path"; then
                digest=$(shasum -a 256 "$path" | awk '{ print $1 }')
                printf '%s %s\n' "$relative" "$digest"
            else
                printf '%s non-regular\n' "$relative"
            fi
        done
    printf 'untracked-end\n'
}

case "$mode" in
    write)
        temporary=$(mktemp "${TMPDIR:-/tmp}/felix-conversion-snapshot.XXXXXX")
        trap 'rm -f "$temporary"' EXIT HUP INT TERM
        write_snapshot > "$temporary"
        mv "$temporary" "$target"
        trap - EXIT HUP INT TERM
        ;;
    verify)
        test -f "$target" || {
            printf 'snapshot does not exist: %s\n' "$target" >&2
            exit 2
        }
        temporary=$(mktemp "${TMPDIR:-/tmp}/felix-conversion-snapshot.XXXXXX")
        trap 'rm -f "$temporary"' EXIT HUP INT TERM
        write_snapshot > "$temporary"
        if ! cmp -s "$target" "$temporary"; then
            diff -u "$target" "$temporary" >&2 || true
            printf '%s\n' 'conversion source snapshot changed' >&2
            exit 1
        fi
        ;;
    *) usage ;;
esac
