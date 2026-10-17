#!/usr/bin/env bash
# Check Make's store policy and literal arguments without building Felix.
set -euo pipefail
repository=$(cd -- "$(dirname -- "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/felix-library-command.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
mkdir -p "$work/bin" "$work/tools" "$work/benchmark"
cp "$repository/Makefile" "$work/"
cp "$repository/tools/verification-command.pl" "$work/tools/"
cp "$repository/benchmark/run-timed.sh" "$work/benchmark/"
cat > "$work/bin/stack" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ $1 == build ]]; then
    touch built
else
    [[ $1 == exec && $2 == -- && $3 == felix ]]
    shift 3
    printf '%s\0' "$@" > arguments
fi
SH
chmod +x "$work/bin/stack"
export PATH="$work/bin:$PATH"
unset FELIX_JOBS FELIX_STORE FELIX_VERIFY_FLAGS STACK_BUILD_FLAGS MAKEFLAGS MFLAGS MAKEOVERRIDES
cd "$work"

invoke() {
    rm -f built arguments
    make "$@" > make.log 2>&1 || return
    args=()
    while IFS= read -r -d '' argument; do args+=("$argument"); done < arguments
}
has() {
    local argument
    for argument in "${args[@]}"; do [[ $argument != "$1" ]] || return 0; done
    return 1
}
option() {
    local index
    for ((index=0; index + 1 < ${#args[@]}; index++)); do
        if [[ ${args[index]} == "$1" && ${args[index+1]} == "$2" ]]; then return 0; fi
    done
    printf 'Missing option: %s %s\n' "$1" "$2" >&2
    exit 1
}
suffix() {
    local count=$#
    printf '%s\0' "$@" > expected
    printf '%s\0' "${args[@]:${#args[@]}-count}" > actual
    cmp expected actual
}
reject() {
    if invoke "$@" || [[ -e built || -e arguments ]]; then
        printf 'Invalid invocation reached build or execution: %s\n' "$*" >&2
        cat make.log >&2
        exit 1
    fi
}

for target in lib lib-refresh spike spike-refresh; do
    root=library/everything.tex store=.cache/library.sqlite
    if [[ $target == spike* ]]; then
        root=library/topology/urysohn/chain.tex store=.cache/spike.sqlite
    fi
    invoke "$target"
    has "$root"
    option --store "$store"
    has --check-render-hints
    if has --fresh; then exit 1; fi
    if [[ $target == *-refresh ]]; then has --refresh
    elif has --refresh; then exit 1; fi
    if [[ $target == spike* ]]; then option --jobs 8
    elif has --jobs; then exit 1; fi
done

# A glob must not silently become a destructive store-policy flag.
touch -- --refresh
FELIX_STORE=environment.sqlite FELIX_JOBS=3 invoke lib \
    "FELIX_STORE=owner's path.sqlite" FELIX_JOBS=5 \
    'FELIX_VERIFY_FLAGS=--module-jobs 2 --dump "a path" --refres*'
option --store "owner's path.sqlite"
option --jobs 5
suffix --module-jobs 2 --dump 'a path' '--refres*'
if has --refresh; then exit 1; fi
FELIX_STORE=environment.sqlite FELIX_JOBS=3 invoke lib
option --store environment.sqlite
option --jobs 3

# Quoting and escaping preserve literal paths, concatenated fragments and empties.
invoke lib "FELIX_VERIFY_FLAGS=--dump 'a;b' pre\"two words\" '' \"a\q\" a\ b"
suffix --dump 'a;b' 'pretwo words' '' 'a\q' 'a b'

reject -j lib lib-refresh
reject -j all spike
reject lib FELIX_STORE=
# These inputs must reach Make literally, including the shell metacharacters.
# shellcheck disable=SC2016
for flags in '"--refresh"' '--sto"re"=other' '--store other' '--fresh' \
    '$$FLAGS' '`command`' '; echo hello' '--dump a;echo hello' '"unterminated' "trailing\\"; do
    reject lib "FELIX_VERIFY_FLAGS=$flags"
done
printf '%s\n' 'Verification launcher policy and arguments passed.'
