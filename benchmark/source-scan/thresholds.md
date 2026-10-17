# Source-scanner acceptance thresholds

These thresholds were fixed from the Stage 1 legacy baseline before production
scanner work began. They apply to the final post-deletion Stage 5 helper, not to
intermediate mixed implementations.

## Baseline identity

- Felix revision: `461b1a2ac89dc07f25f889521eb2afde7c85a733`
- helper SHA-256:
  `9d9285aed5dd895a6c8f03da09fb4a44961b00667ba87d63409a59c13b43bf19`
- CLI SHA-256:
  `fc5053c20663c81d07066e3ed69e7bdbf2dc77c4ca715a397aeae2bd4e9ffe26`
- GHC: 9.10.3; `text`: 2.1.3; helper optimization: `-O2`
- root: `library/topology/urysohn/chain.tex`
- corpus: 33 sources, 441,151 bytes, 12,761 lines
- corpus digest:
  `0c1bdfce774e8dc720c209af8657dae3c978ba402ae5dfaba49af50ee73acf77`
- cache epoch: 93

The retained binaries and raw local, Criterion, end-to-end, manifest, and
production-surface evidence are under the ignored replay directory
`profiling/source-scan/461b1a2-baseline/` in this worktree.

The retained local evidence used seven independent one-case-per-process runs.
The Criterion run used a three-second time limit per case. Baseline-versus-itself
end-to-end noise used three interleaved repetitions per label; final acceptance
uses at least five.

## Semantic hard gates

The baseline and final helpers must emit byte-identical manifests and matching
ordered per-source records, counts, and observation digests:

| Case | Leaf count | Observation digest |
| --- | ---: | --- |
| `prefix` | 66 | `3593877e4974439ac10d9b5ee37302d2cb279d9aafe9c8b9902af7fb04207905` |
| `verification-completion` | 84,057 | `d83f210b6f758cafd718d446148447f31cec9c5d9cc43b7acec4f99be029d7ad` |
| `presentation-decoded` | 1,978 | `892245fcd3832f1072129ef39fe643e06f7e27d610f6ca28ac50bf8559d463e2` |

All compatibility-ledger tests, explicit forcing boundaries, source-binding
checks, cache/demand counters, and the production-surface deletion review remain
independent hard gates. Timing cannot compensate for a semantic, authority,
diagnostic, cache, or demand-flow mismatch.

For every paired successful fresh end-to-end run, the baseline and candidate
stores must also contain identical ordered parsed-artefact rows when compared
by raw `parsed_module_key`, `parsed_module_id`, and canonical `payload`. Record
the row count, per-row digests, and aggregate relation digest; do not compare the
SQLite files themselves.

## Local performance gates

Run seven independent `space` processes for each available case on each retained
executable. Compare medians on the same host and corpus. Use
`thread_allocated_bytes`, not the GC-lagged `allocated_bytes`, as the local
allocation measure. Confirm the result with Criterion; a confidence interval
crossing a bound requires another run rather than a favorable point estimate.

| Case | Baseline median wall | Baseline allocation | Final maximum |
| --- | ---: | ---: | --- |
| `prefix` | 98,879 ns | 1,335,552 B | 75% of baseline wall and allocation |
| `verification-completion` | 195,849,364 ns | 1,974,589,224 B | 50% of baseline wall and allocation |
| `presentation-decoded` | 196,432,761 ns | 1,970,009,056 B | 50% of baseline wall and allocation |

The corresponding Criterion estimates were 90.12 microseconds, 193.7
milliseconds, and 192.4 milliseconds. `presentation-spans` is candidate-only
attribution: record it and require it to be cheaper than the final decoded case,
but do not manufacture a legacy ratio for work that had no legacy boundary.

These are acceptance floors, not the 3--5x target. Missing a bound stops cutover
for profiling and design review; do not weaken it after inspecting the candidate.

## End-to-end gates

Run at least five interleaved repetitions of each fresh/warm and HTML/no-HTML
case from the driver-owned isolated states. The same-binary control observed the
following wall ranges: fresh/no-HTML 17.24--18.69 s, fresh/HTML 18.57--18.91 s,
warm/no-HTML 0.54--0.56 s, and warm/HTML 0.60--0.66 s. Vampire dominates fresh
wall and CPU time, so local scanner acceptance does not depend on detecting that
small effect in whole-process wall time.

Apply these predeclared bounds to medians:

- no fresh case may regress by more than 15% in wall or user CPU time;
- no warm case may regress by more than 10% in wall or user CPU time;
- fresh/no-HTML and fresh/HTML must each allocate at least 5% fewer bytes;
- warm/HTML must allocate at least 3% fewer bytes and improve wall time by at
  least 5%;
- warm/no-HTML allocation may regress by at most 2%; and
- the reported fresh `source parsing` phase must improve by at least 5%, while
  the warm phase may regress by at most 10%.

The legacy median whole-process allocations were approximately 15.416 GB for
fresh/no-HTML, 15.690 GB for fresh/HTML, 4.039 GB for warm/no-HTML, and 4.310 GB
for warm/HTML. Its reported `source parsing` phase was about 1.42 seconds fresh
and 0.10 seconds warm. That field begins after source-graph construction and is
retained only under its existing meaning; the final graph-preparation telemetry
and external process measurements own the newly consolidated prefix work.

If an end-to-end distribution overlaps a bound, increase repetitions and report
the paired schedule and raw data. Do not decide by selecting favorable runs.
