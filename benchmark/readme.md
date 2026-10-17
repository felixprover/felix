# Benchmarks

The maintained tools are:

- [Parser measurements](parser/readme.md): semantic observations, synthetic and
  corpus workloads, and paired ordinary-CLI comparisons (`make bench-parser`).
- `conversion/`: checked conversion, scaling, and complete proof-workflow cases
  (`stack build felix:bench:conversion-focused --no-run-benchmarks`).
- `source-scan/`: Criterion measurements, source manifests, and space/end-to-end
  comparisons (`make bench-source-scan`, `bench-source-scan-space`, and
  `bench-source-scan-e2e`).
- [Concurrency measurements](concurrency/readme.md): ordered trials with restored
  store snapshots, plus process-tree memory diagnostics.
- `run-timed.sh`: shared elapsed-time and resource measurement used by Make.

Python 3 is needed for the parser and concurrency drivers. They use the standard
library, without third-party Python packages. Their focused harness checks are:

```sh
python3 -B -m unittest discover -s benchmark/parser -p 'test_*.py'
python3 -B -m unittest discover -s benchmark/concurrency -p 'test_*.py'
```

Build before measuring and pin the executables and source inputs. Compare paired
runs with the same build/RTS settings and store policy. Preserve failed trials;
do not count a timeout or verification failure as a fast result. Keep generated
measurements, profiles, and logs under ignored `profiling/` or `.cache/`.

Use a separate Stack configuration and work directory for each optimization
experiment; changing `--fast` or `--ghc-options=-O…` in an existing directory can
reuse objects compiled at the previous level. Keep the compiler, inputs, and
runtime settings matched. See [build configurations](../docs/development.md#build-configurations)
for the maintained ordinary, fast, and instrumented modes.

## Work budgets

Conversion measures deterministic work, rather than elapsed time or allocated
bytes. Each evaluator transition consumes one unit, as does each unit reported
by a delegated Core operation. The total includes input checking, structural
comparisons, evaluation, and checking any recovered term. It is not a count of
beta reductions. The benchmark fields `c5-cost` and `c5-limit` are historical
names for this conversion cost and limit. The counters are implemented in
[`Conversion.Pure`](../source/Felix/Checking/Kernel/Conversion/Pure.hs) and
[`Conversion.Checked`](../source/Felix/Checking/Kernel/Conversion/Checked.hs).

The current conversion allowances are:

| Scope | Work units | Definition |
| --- | ---: | --- |
| One conversion operation | 2,000,000 | [`productionConversionOperationLimit`](../source/Felix/Checking/Kernel/Conversion/Policy.hs) |
| One formation proof interpretation | 20,000,000 | [`defaultFormationProofConversionPool`](../source/Felix/Checking/Notion/FormationProof.hs) |
| One automatic proof request | 100,000,000 | [`defaultObviousConversionPool`](../source/Felix/Checking/Obvious/Driver.hs) |

A caller's remaining pool can further restrict an operation. Failed attempts
still consume work; trying another alternative does not refund it. These
counters do not bound time or memory. Measure complete proof requests and
replay as well as individual conversions when changing an allowance. The
`conversion-focused workflow` cases described in
[bounded search](../docs/logic.md#bounded-search) cover these larger operations.

Decoders have separate limits for input bytes, reconstructed nodes, collection
entries and text characters, nesting depth, and individual fields. Their
current values are defined by
[`standardDecoderLimits`](../source/Felix/Codec/Admission.hs). These limits bound
reconstruction of stored data; they do not change mathematical encodings or
proof-search budgets. [Decoder admission tests](../test/Felix/Test/Unit/CodecAdmission.hs)
exercise the limits and distinguish resource exhaustion from malformed input.

The original conversion calibration and decoder corpus measurements are
historical evidence, not measurements of the current implementation. They can
be read at revision `3cf7978884b9a84b6f8daef424774c910c11cb4e`:

```sh
git show 3cf79788:notes/conversion-inventory.md
git show 3cf79788:docs/optimization-evaluation.md
```

## Profiling

The Make targets share `tools/profile.sh` for builds, metadata, timing, and
failure reporting. Instrumented targets use O2 and a separate
`.stack-work-profile-o2` directory. The baseline uses the ordinary build,
including the selected `STACK_YAML` configuration.

| Target | Default input | Store policy | Measurement |
| --- | --- | --- | --- |
| `profilebaseline` | representative slice | explicit store, refreshed | uninstrumented time and RTS statistics |
| `profile` | representative slice | temporary | cost-centre profile |
| `profileall` | whole library | temporary | cost-centre profile |
| `profilejson` | representative slice | temporary | JSON cost-centre profile |
| `profilewarm` | whole library | default XDG store, reused | warm cost-centre profile |
| `profilemem` | representative slice | temporary | heap profile |
| `profileparser` | whole library | none | parse-only cost-centre profile |

Override `LIBRARY_PROFILE` to select an input. For example:

```sh
make profile LIBRARY_PROFILE=library/set.tex
```

For `profilebaseline`, `PROFILE_STORE` selects the database (default
`.cache/store.sqlite`); its parent directory is created if necessary.
`PROFILE_CACHE_FLAGS=--refresh` resets that store, while an empty value permits
reuse. These are the only two supported baseline policies.
`FELIX_VERIFY_FLAGS` accepts the same literal, shell-quoted arguments as
`make lib`; it cannot override store policy. Flags must be applicable to the
selected mode, including `--parseonly` for `profileparser`.
`PROFILE_RTS_FLAGS` and `STACK_BUILD_FLAGS` are whitespace-separated option lists.
`PROFILE_GHC_OPTIONS` is passed as one argument to Stack's `--ghc-options`.

Each run records command arguments, source and executable hashes, compiler and
prover versions, output, timings, RTS statistics, and the measured command's exit
status under `PROFILE_DIR` (default `profiling/`). Baseline runs also record the
transitive source manifest and store state before verification. Failed runs keep
their logs and status and do not produce a chart.

`profilewarm` first verifies with the same executable, input, and verification
options. It records that warm-up separately and measures a second pass only if
the first succeeds. Neither pass refreshes the store. The timed pass invokes
Felix directly, excluding build and Stack startup. This measures instrumented
verification with a warm store and filesystem cache, not uninstrumented latency.

Cost-centre profiles use `icicle` on `PATH` to produce an SVG chart. Heap profiles
use GHC's `hp2ps` and [Ghostscript](https://ghostscript.readthedocs.io/en/latest/Install.html).

## Retired campaigns

Completed binding, cache/admission, equality/search, catalogue, source-location,
source-sealing, structure-normalization, warm-import, manifolds, and conversion
comparison campaigns have been removed together with their dedicated drivers,
fixtures, and tests. Parser phase experiments and the decoder for temporary
concurrency trace markers have also been removed. Reusable measurement tools
remain listed above; campaign reports remain in Git history.

The complete pre-cleanup tree is revision
`2f60a15a08889bd79aec245353a7cda0e388bd0c`. Inspect an old file with, for example:

```sh
git show 2f60a15a:benchmark/conversion-post-merge/readme.md
```

Generated evidence archived on 2026-09-07 is stored separately at
`../felix-benchmark-artifacts/2026-09-07/`. This local archive is not included in
the repository. Its `manifest.json` maps original paths and historical versions
to archive members; `commit-map` and `original-refs.txt` map old revision names.
The archive SHA256 is
`d47f02055300f09f639252d5495d25d1761cb1fd7bb4804335478587fe34e46d`.
Restore it into an ignored directory when replaying those historical results:

```sh
mkdir -p profiling/benchmark-archive/2026-09-07
tar -xzf ../felix-benchmark-artifacts/2026-09-07/artifacts.tar.gz \
  -C profiling/benchmark-archive/2026-09-07
```

Use the historical source, inputs, and semantic observations together; do not
regenerate a reference oracle from a candidate implementation.
