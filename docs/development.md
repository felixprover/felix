# Developing Felix

Start with the [README](../readme.md#development) for the repository map and
routine commands. Read [proof checking and cache reuse](implementation.md) before
changing proof authority, preparation, or persistent reuse. The [CLI guide](cli.md)
describes runtime options and diagnostics; the [benchmark guide](../benchmark/readme.md)
covers profiling and performance measurements.

Development checks use Bash, Perl, and ripgrep, plus GHC through Stack. Python 3
is needed only for the optional ATP comparison, formation summaries, and
benchmark tools. For editor support, install Haskell Language Server through
GHCup; VS Code also needs the
[Haskell extension](https://marketplace.visualstudio.com/items?itemName=haskell.haskell).

## Build configurations

The ordinary configuration builds Felix at O2, selected through Cabal settings.

| Command | Build mode |
| --- | --- |
| `make build`, `make test`, `make spike`, `make lib` | O2 in `.stack-work-o2` |
| `make build-fast` | O0 in `.stack-work-fast` |
| `make profile` and other instrumented profiling targets | O2 with profiling in `.stack-work-profile-o2` |

The fast configuration includes `stack.yaml`, sharing its resolver and project
settings. To run the O0 executable, use:

```sh
stack --stack-yaml stack-fast.yaml exec felix -- library/set.tex
```

For other commands and helper scripts, select the same configuration through
`STACK_YAML`, for example:

```sh
STACK_YAML=stack-fast.yaml make test-fast
```

`test-fast` selects tests; it does not change compilation settings.

Each mode has separate local build products, so switching modes reuses previous
builds without mixing optimization levels. The first build of each mode takes
longer. Avoid changing optimization with `--fast` or `--ghc-options=-O…` in an
existing build directory: Stack and GHC may reuse objects compiled at the
previous level. For optimization experiments, see the
[measurement guidance](../benchmark/readme.md).

## Tests

| Command | Scope |
| --- | --- |
| `make test-fast` | Deterministic unit and golden checks |
| `make test-acceptance` | Slower verification and real-prover acceptance checks |
| `make test` | Both suites |

All three also run the dependency/API boundary checks and the private
obvious-inference bridge checks.

Golden tests compare program output with previously accepted output. Review
intentional differences before updating the golden files with `make golden`.

`make check-boundaries` checks kernel dependency restrictions and attempts to
forge checked evidence through the public Haskell API. These checks use Bash,
ripgrep, and GHC. `make check-imports` runs just the dependency checks and their
small negative controls, without compiling Haskell.

`make check-tools` separately checks the verification launcher, ATP comparison
tool, and runtime startup probe. Only the ATP comparison check uses Python.
The launcher check can also run alone with `bash tools/test-library-command.sh`,
without building Felix or touching a database. Benchmark harness tests remain
with their [respective benchmarks](../benchmark/readme.md).

## Library verification

`make spike` checks the representative slice rooted at
`library/topology/urysohn/chain.tex`. Use it during implementation work.
`make lib` checks the full standard library rooted at `library/everything.tex`;
reserve this slower gate for potentially breaking changes and library
integration. A full verification can take several minutes.

`make lib` reuses `.cache/library.sqlite`; `make spike` reuses
`.cache/spike.sqlite`. Create the store's parent directory first:

```sh
mkdir -p .cache
make spike
```

Both targets honor `FELIX_STORE` from the environment or Make command line;
the command line wins. To share that database with a direct CLI call, pass
`--store PATH`; otherwise the CLI uses its XDG cache store.

`make lib-refresh` and `make spike-refresh` explicitly discard the selected
store before verification. Ordinary targets reject an incompatible store
instead of silently resetting it. All four targets check render hints and
print their root, store, and policy.

Choose one verification policy per invocation, including with `make -j`.
`all` includes `lib`, and `all lib` is allowed. Select the store and policy
through `FELIX_STORE` and the target. `FELIX_VERIFY_FLAGS` accepts additional
literal, shell-quoted arguments, such as `--store-report`; it cannot override
store policy and does not evaluate shell commands or expansions.

```sh
make spike FELIX_VERIFY_FLAGS='--store-report --prover-jobs 2'
```

`make lib` uses the CLI's automatic concurrency defaults unless `FELIX_JOBS`
is explicitly set. `make spike` defaults to `FELIX_JOBS=8`. Setting this variable
passes `--jobs` to Felix; component-specific options in `FELIX_VERIFY_FLAGS`
override their respective limits. See [resource limits](cli.md#concurrency-and-resource-limits).
