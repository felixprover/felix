# Running Felix

See the [README](../readme.md#try-felix) for installation and a first verification.
Run commands from the repository root with `stack exec felix -- <FILENAME>`;
the `--` separates Stack's arguments from Felix's. Use
`stack exec felix -- --help` for the complete option list.

## Modes and imports

The ordinary command verifies a source file and its imports. Add `--html` to
export verified HTML under `./html`; see [HTML output](html.md).

`--version` prints the version. `--parseonly` resolves and parses the source
and its imports without opening SQLite or invoking Vampire. It does not verify
proofs and cannot be combined with verification options.

Imported files are searched for in these directories, in descending priority:

1. The current working directory `.`.
2. `./library`, overridden by the environment variable `NAPROCHE_LIB`.
3. `./debug`.

When working outside the repository, set `NAPROCHE_LIB` to the library you want
to use. `FELIX_VAMPIRE` selects the prover executable; the default is `vampire`
on `PATH`.

## Verification stores

Verification uses a disposable SQLite store. By default Felix uses the
platform's XDG cache directory (typically `~/.cache/felix`). Source remains
authoritative; the store accelerates repeated verification.

- `--store PATH` selects an explicit database file. Its parent directory must
  already exist.
- `--fresh` uses a temporary store that is removed after the command. It cannot
  be combined with `--store`.
- `--refresh` discards the selected persistent store before verification.
- `--store-report` reports store lookup decisions and live Vampire starts.

Ordinary runs reject incompatible or damaged stores rather than migrating or
silently rebuilding them. To recover, explicitly discard the selected store
with `--refresh`, use `--fresh`, or select a new `--store` path.

The Make library targets select their own stores; see
[library verification](development.md#library-verification). For how Felix checks
and saves reusable results, see [proof checking and cache reuse](implementation.md).

## Concurrency and resource limits

Felix scales its defaults from the detected logical processor count C. GHC
capabilities and module pipelines use `max 1 (min 16 (floor(2*C/3)))`, while
Vampire invocations use `max 1 (min 4 (floor(2*C/9)))`. The allocation area is
64 MiB per capability. These defaults apply to direct execution, `stack run`,
and `make lib`.

A positive `--jobs J` sets both module and prover limits. `--module-jobs` and
`--prover-jobs` override their respective component independently. Standard
`+RTS -N… -A… -RTS` options override the runtime defaults. Each Vampire
invocation runs a two-worker CASC portfolio. `-t` and `-m` bound each request's
time and memory.

For Make-specific overrides, see the [development guide](development.md#library-verification).
For performance measurements, see [benchmarks](../benchmark/readme.md).

## Diagnostics

Felix reports selected ATP, proof-structure, and parser failures as
`error[FELIX-...]:` diagnostics with a source location and explanation.
Complete TPTP requests are not printed by default.

The diagnostic codes have these stable meanings; their surrounding wording may
change independently.

| Code | Meaning |
| --- | --- |
| `FELIX-ATP-COUNTERMODEL` | the selected premises do not imply the obligation |
| `FELIX-ATP-CONTRADICTORY-INPUT` | a direct obligation has contradictory selected premises |
| `FELIX-ATP-TIMEOUT` | Vampire reported or reached a time limit |
| `FELIX-ATP-RESOURCE-OUT` | Vampire reported resource exhaustion |
| `FELIX-ATP-GAVE-UP` | Vampire gave up |
| `FELIX-ATP-UNKNOWN` | Vampire reported an unknown result |
| `FELIX-ATP-INDETERMINATE` | Vampire reported multiple compatible indeterminate results |
| `FELIX-ATP-PROTOCOL` | Vampire output did not define a valid supported result |
| `FELIX-ATP-PROCESS` | starting, communicating with, or supervising Vampire failed |
| `FELIX-PROOF-EXPECTED-UNIVERSAL` | a fix step was applied to the wrong goal shape or binder type |
| `FELIX-PROOF-EXPECTED-IMPLICATION` | an implication-opening step was applied to another goal shape |
| `FELIX-PROOF-EXPECTED-ASSUMPTIVE-GOAL` | an assume step was applied to a goal that it cannot open |
| `FELIX-PROOF-SET-INDUCTION-AMBIGUOUS` | set induction has multiple eligible binders |
| `FELIX-PROOF-TRANSFINITE-INDUCTION-AMBIGUOUS` | transfinite induction has multiple eligible ordinal guards |
| `FELIX-PROOF-UNKNOWN-REFERENCE` | a cited fact is not visible |
| `FELIX-PARSE-UNCONSUMED-INPUT` | parsing stopped at an unconsumed token |
| `FELIX-PARSE-AMBIGUOUS` | more than one distinct parse remains |

## Inspecting Vampire requests

Use `--dump` to write the exact requests sent to Vampire. ATP diagnostics name
the module and request position when one exists; this corresponds to
`MODULE-REQUEST.p` in the dump directory. A failed run retains only the requests
that were executed before the failure. The destination must be absent or empty;
Felix owns the complete directory for that run.

```sh
dump_dir=$(mktemp -d "${TMPDIR:-/tmp}/felix-dump.XXXXXX")
printf 'Writing dump to %s\n' "$dump_dir"
stack exec felix -- file-that-fails.tex --dump "$dump_dir"
```

You can then run Vampire manually on one of those files:

```sh
"${FELIX_VAMPIRE:-vampire}" --input_syntax tptp --mode casc "$dump_dir/1-1.p"
```

`make dump` verifies the full library using a fresh temporary store and creates
and prints a temporary dump destination unless `DUMP_DIR` is supplied.
