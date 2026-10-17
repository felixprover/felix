#!/usr/bin/env bash
set -euo pipefail

if (( $# > 1 )); then
    printf '%s\n' 'usage: record-production-surface.sh [GIT-REVISION]' >&2
    exit 2
fi

revision=${1:-HEAD}
repository=$(git rev-parse --show-toplevel)

paths=(
    source/Felix/Source.hs
    source/Felix/Source/Content.hs
    source/Felix/Source/Graph.hs
    source/Felix/Parsed/Module.hs
    source/Felix/Syntax/Token.hs
    source/Felix/Syntax/Pragma.hs
    source/Felix/Parse.hs
    source/Felix/Workspace.hs
    source/Felix/Render/Html.hs
    source/Felix/Render/Html/Export.hs
    source/Felix/Verification.hs
)

cd "$repository"
resolved_revision=$(git rev-parse "$revision^{commit}")

printf 'source-scan-production-surface-v1\n'
printf 'revision %s\n' "$resolved_revision"

for path in "${paths[@]}"; do
    if ! git cat-file -e "$resolved_revision:$path"; then
        printf 'missing %s\n' "$path" >&2
        exit 1
    fi
    printf 'file %s\n' "$path"
    printf 'lines '
    git show "$resolved_revision:$path" | wc -l
    printf 'sha256 '
    git show "$resolved_revision:$path" | sha256sum | cut -d ' ' -f 1
    printf 'exports-begin\n'
    git show "$resolved_revision:$path" | awk '
        /^module / { capture = 1 }
        capture { print }
        capture && (/^[[:space:]]*\) where$/ || /^module .* where$/) { exit }
    '
    printf 'exports-end\n'
done
