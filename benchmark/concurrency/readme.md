# Full-library concurrency measurements

This driver measures full-library checking with controlled concurrency and
store state. Use `make lib` for full-library qualification. Small fixtures can
diagnose behavior; choose resource settings using representative workloads.

For direct-executable screening that matches `make lib` verification semantics,
pass `--check-render-hints`. The driver forwards and records it explicitly;
omitting it measures verification alone. These direct-executable measurements
exclude the build and wrapper overhead included in `make lib` timings.

Build outside measured intervals and preserve the exact executable. Supply:

- a JSON source manifest containing `binary_sha256`, source revision/build
  settings, and source hashes;
- a manifest identifying the complete input library and its content hashes;
- an environment manifest identifying GHC, Vampire, machine, inherited RTS
  settings, and resource conditions.

The driver checks the executable against the source manifest and records the
hashes of all three manifests in every trial. The caller is responsible for
freezing the source/library and matching their manifests. Raw logs, timing,
RTS statistics, status, and JSON metadata go into a new output directory. Keep
these generated artifacts under ignored `profiling/` or `.cache/`.
The driver also records load averages and inherited `GHCRTS`, `NAPROCHE_LIB`,
and `FELIX_VAMPIRE` values before each trial. These observations supplement the
environment manifest; they do not establish that the machine was otherwise idle.

For example, with a pinned reference executable and its manifests:

```sh
python3 benchmark/concurrency/run.py \
  --binary .cache/concurrency/reference/felix \
  --source-manifest profiling/concurrency/reference/source.json \
  --input-manifest profiling/concurrency/reference/inputs.json \
  --environment-manifest profiling/concurrency/reference/environment.json \
  --store .cache/concurrency/trial.sqlite \
  --output profiling/concurrency/refresh-screen \
  --mode refresh \
  --configuration 4:6:6 --configuration 2:6:6 \
  --configuration 2:6:6 --configuration 4:6:6
```

Configurations are `CAPABILITIES:MODULES:PROVERS`, executed in the exact supplied
order, including duplicates. The default input is the full library. All runs
retain the current 20-second proof limit and two requested Vampire cores. The
explicit `-N` setting is checked against the effective capability count in the
RTS output. The driver reports missing measurements and mismatches as invalid
trials. It continues after a verifier failure and exits unsuccessfully if any
trial failed or lacked required measurements. Do not omit failed attempts when
comparing performance. A valid measurement is not a proof of semantic parity;
compare authorization counts, interfaces, requests, and contracts separately.

For measured GC experiments, pass repeated `--rts-option` arguments such as
`--rts-option=-A32m` or `--rts-option=-qn4`. They are recorded verbatim in each
trial's command and metadata. Keep the existing proof limits and requested
Vampire cores fixed; vary one justified resource setting at a time. The driver
still checks that effective capabilities match the `N` configuration.

## Store modes

`--mode refresh` resets the selected trial store through Felix's normal
`--refresh` path. It keeps the existing warm validation lookup semantics.

`--mode warm --store-snapshot PATH` restores a closed, populated SQLite snapshot
before each trial. Keep the input unchanged from the snapshot population. Any
live ATP execution invalidates the claimed unchanged-warm trial.

`--mode incremental --store-snapshot PATH` performs the same restoration, but
permits live proof work. Create a disposable library copy, populate the snapshot
from that unedited copy, then apply the chosen edit outside timed intervals.
Populate and edit at the same canonical source-mount root: Felix's source
namespace identity includes that root. A store populated in the original
repository cannot serve as the incremental baseline for a relocated copy.
Point `--input` at that copy's `everything.tex` and supply its post-edit input
manifest. Every repetition therefore starts from the same pre-edit store and
post-edit source, rather than accidentally measuring the previous run's cache.
Verify the intended semantic-interface change or preservation separately.

Use SQLite's backup operation to prepare a standalone snapshot; checkpoint and
close it before passing it to the driver. It must differ from the trial store
and have no nonempty WAL. The driver uses read-only SQLite backup to restore it
outside each measured invocation and checks that the snapshot file is unchanged
before every restoration. Do not share trial stores with another running check.
Filesystem caches remain uncontrolled and must be recorded separately.

## Focused driver checks

```sh
python3 benchmark/concurrency/test_run.py
```

The controlled verifier tests failure retention/continuation, store restoration
after a failed incremental trial, and rejection of ATP work in a warm trial.
These tests validate the measurement protocol; they do not run Felix or support
a performance claim.

## Live memory diagnostics

For a memory-growing configuration, run a diagnostic before ordinary timing:

```sh
python3 benchmark/concurrency/diagnose_memory.py \
  --output profiling/perf-followup/memory-control --limit-kib 16777216 -- \
  "$FELIX_BIN" library/everything.tex \
  --store .cache/perf-followup/memory-control.sqlite --refresh \
  --check-render-hints --store-report -t 20 --module-jobs 12 --prover-jobs 4 \
  +RTS -N8 -A64m -s -RTS
```

Select and record the exact built `FELIX_BIN` and manifests before this command.
The command must launch Felix directly; the controller owns that process and
its private session, while the sampler observes Felix and its descendants.
The 16 GiB threshold above is the current follow-up allowance, not a default
prover limit. Sampled diagnostics do not qualify ordinary timing gains.

Samples are flushed to `memory.samples.jsonl` during execution. The sampler
emits one live JSON notification if summed RSS exceeds the requested limit.
The controller sends `SIGINT` to its owned verifier and waits for normal
cleanup and exit; it does not merely kill a make/Stack/time wrapper. Invalid
notifications or a failed monitor also stop and settle the verifier. The final
summary retains the existing `memory.json` format, with additional threshold
fields. Partial live records survive an interrupted diagnostic.

Sampling can miss peaks, count shared pages repeatedly, and detect an excess
only after it occurs. Use headroom and inspect memory pressure separately;
this is not a hard OS memory cap. Cancellation has no artificial deadline that
would abandon owned prover processes. A separate controlled-process test covers
live notification, successful completion, and monitor-failure cleanup:

```sh
python3 -B benchmark/concurrency/test_memory.py
```

## Simultaneous process-tree memory

For a diagnostic resource trial, start `sample_memory.py PID --output PATH.json`
after launching Felix, using its actual process ID. The script samples the
root and descendants with `ps` every 0.25 seconds until the root exits. Run it
with permission to inspect that process tree, and retain its output beside the
trial metadata. It never signals the measured processes.

The result is the maximum observed **simultaneous sum** of RSS, in KiB. Shared
pages can be counted more than once, short peaks between samples can be missed,
and work before the sampler starts is excluded. Report these limits and the
sampling interval. Do not add separately observed per-process maxima or call
this a physical-memory census. Keep the repeated `ps` sampling out of ordinary
timing comparisons; use matched diagnostic baseline/candidate resource runs.
