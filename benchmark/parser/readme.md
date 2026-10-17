# Parser measurements

Run from the repository root. `package.yaml`, `stack.yaml`, and `stack.yaml.lock` pin the build;
the benchmark uses the linked, unmodified Earley 0.13.0.1. Build an optimized,
unprofiled executable, including the Felix library:

```sh
make bench-parser
mkdir -p profiling/parser/bin
cp "$(stack path --dist-dir)/build/parser-bench/parser-bench" profiling/parser/bin/reference
python3 benchmark/parser/run.py check profiling/parser/bin/reference profiling/parser/reference-check
python3 benchmark/parser/run.py measure profiling/parser/bin/reference profiling/parser/bin/reference profiling/parser/noise --repetitions 7
```

Pin a candidate executable the same way, then run `check` in a separate directory,
`compare REFERENCE-CHECK CANDIDATE-CHECK`, and `measure REFERENCE CANDIDATE OUTPUT`.
Keep the reference executable and inputs fixed during a comparison. The runner
records measurements and semantic observations; it does not impose the retired
optimization campaigns' percentage gates.

`measure --full` includes every synthetic fixture; the default is the bounded
acceptance panel plus corpus, native, and HTML cases. Each repetition alternates
reference/candidate order. Every case runs in a new process, with a 60-second
timeout, fixed single-capability RTS settings, and an uncontrolled OS filesystem
cache. Correctness cases have a 180-second timeout. Failed and timed-out cases
remain in the report. Stop other builds/profiles during performance trials.

The driver retains JSONL samples (including complete stdout, stderr and RTS
statistics), executable SHA256 identities, and median/range summaries. Correctness
records retain raw result counts and compressed complete observations. The semantic
hash excludes raw derivation multiplicity; the distinct successful value set and
selected result are preserved. The payload codec supplements `Show` with a digest
that includes variable locations and lexical markers. It records line/column,
while the enclosing fixture/module supplies the stable source owner. Incidental
file-registry numbers are not compared. Corpus manifests reuse the source-scan
benchmark format, with the reserved prelude included.

## Workloads and demand

`parser-bench cases` lists deterministic direct-lexicon fixtures. Sizes are bounded
at 128 added entries. Categories vary independently; phrase categories have shared
and disjoint prefixes; predicates vary one versus eight arities. Unrelated,
matching, and malformed target chunks remain fixed across sizes. Size zero is
the negative matching control. These are direct API fixtures, not duplicate source
declarations. Corpus runs separately cover canonical validation/materialization.

| Command/mode | Input and reuse | Timed demand |
| --- | --- | --- |
| `measure CASE parse N` | Forced finite Lexicon and tokens; one parser function; fresh application per invocation | Production result selection and deep forcing of each selected block; failures include fields and diagnostic rendering |
| `measure CASE report N` | Same inputs, independently executed in another process | Earley report position, exact expectations, remaining tokens; skips successful semantic payload extraction |
| `measure CASE rebuild N` | Fixed declarative Lexicon; fresh scanning and parser function per iteration | Scanning/registration, grammar invocation, selection and block/error forcing; no file I/O |
| `measure CASE native N` | One native parser, fixed snippets, first invocation unprimed | Scan snippets, native selection, force all selected payloads; render failures |
| `measure CASE markup N` | One markup/native parser, fixed snippets | Native and layout selection, force presentation tree; render failures |
| `materialize SIZE` | Forced canonical-entry input | Canonical validation and lexicon materialization plus finite-data forcing, combined |
| `corpus ROOT` | Reconstructed from files | Production authority-free workspace API: prelude, discovery, scanning, extraction, validation, effective syntax, parsing, selection, occurrence association, and forced module handoff |
| `html CASE` | Maintained `test/html-fixtures/document-presentation.tex`, chosen direct Lexicon for commentary | File I/O, graph and block parsing, native parser construction, presentation projection, navigation, actual HTML and diagnostics; no verification, SQLite, publication, or store work |

`short` isolates repeated invocations of one identical located chunk. Iteration
zero is the first invocation; later rows are subsequent invocations, with no
unreported warmup. `many-small` and `few-large` contrast chunk shapes at comparable
token counts; they do not isolate invocation overhead. There is no assertion that
sharing a `Parser` function shares Earley's mutable setup. Input reads through an
IORef prevent GHC from sharing evaluated parse results across loop iterations.

`lexical-data` forces the declarative fixture inventory, not Earley setup. Its
timer excludes scanning; scanning and registry setup still contribute to process
residency. The parser function is not forced as a supposed setup measurement.
Prepared implementations report a separate `prepare-lexicon` row before shared
`parse`/`report` trials. That row forces all selected indexes and their payloads;
it is excluded from chunk timings and included in process allocation/residency.
Native and markup trials include preparation of their own parser lifetime in the
first timed invocation. `rebuild` prepares again inside every timed invocation.
Parsing, semantic realization, deduplication, and block forcing are a combined
endpoint. The independently measured `report` difference is attribution evidence,
not an additive phase decomposition. No Earley counter fork is required.

Local allocation is **before minus after `getAllocationCounter`** on the calling
Haskell thread. Completed RTS totals include all threads, setup, GC and harness;
use them for process comparisons. `max_bytes_used` is the sampled whole-process
residency high-water, including retained inputs and small row formatting. It is
never subtracted across stages. No correctness serialization or enumeration runs
inside a performance process. No per-chunk GC is inserted. Small cases may have
only the final residency sample; report the sample count and treat inconclusive
space comparisons accordingly.

## Correctness checks

`controls` checks expectation-preserving lookup feasibility against the existing
labelled alternatives, as well as production selection among duplicate successes,
mixed success/failure, competing concrete failures, empty and unconsumed input.
`observe CASE` records full semantic sets, selected outcomes, raw counts, exact
reports and rendered diagnostics, native expression/type preference, ambiguity,
variable-list fallback, and phrase-marker resolution. `partial` scans a balanced
source first, then removes its closing tokens to exercise concrete EOF reporting.

`manifest ROOT` records transitive source digests, import search order, per-module
token/chunk counts, effective lexical counts, prelude blocks, module handoffs and
each chunk's full concrete observations. Source and direct-lexicon tests remain
separate. Existing `Parser`, HTML, syntax-interface and parsing golden tests cover
the wider language (including reserved numeric syntax, both predicate contexts,
noun slots, structure annotations, collisions and native fallbacks).

Run relevant tests after changes and `make spike` during production-source
iterations. Run the normal test suite and final `make lib` after the accepted
grammar changes. Benchmark-only additions do not justify a full library gate.

## CLI comparisons

`cli.py` compares ordinary Felix executables using a JSON specification. Run
`python3 -B benchmark/parser/cli.py measure SPEC.json OUTPUT`, then use
`summary OUTPUT` to replay the report. An eligible inconclusive seven-pair
screen can be extended with `extend OUTPUT`. The driver checks executable and
command identities, retains failures, and stops descendant processes on timeout.
The controlled checks run with
`python3 -B -m unittest discover -s benchmark/parser -p 'test_*.py'`.

This CLI driver uses macOS `/usr/bin/time -l` for peak RSS. The ordinary
`run.py` parser measurements do not require that macOS timing interface.
The specification supplies `executables` (`reference` and `candidate`, each
with an absolute `path` and `sha256`), an `inputs` map of paths to SHA256s, and
named `workloads` with `command`, expected `stdout`, `stderr_pattern`, and
`kind` (`primary`, `growth`, or `warm`). Warm workloads also specify the expected
module `installations`. Use `mode: calibration` with the same executable in
both slots first. Candidate runs require `correctness_checked: true` after
independent semantic checks. `nonregression` uses the bounds below;
`incremental` requires a primary elapsed improvement and at most 1% extra
allocation, while `final` requires at least 10% elapsed and allocation gains.

## Readability extensions

The CLI driver's `nonregression` mode retains the primary cold `everything.tex
--parseonly` workload while requiring an elapsed paired-bootstrap 95% upper bound
of at most 1.10 and median allocation, live heap and RSS ratios of at most 1.10.
Use seven alternating AB/BA pairs after same-binary calibration; only an
inconclusive timing result with passing space gates permits fourteen extra pairs.
Compare each accepted configuration with both its predecessor and the fixed
initial baseline. Keep grammar comparisons on identical pinned source inputs;
report vocabulary/migration comparisons as changes of input. Re-prime warm
verification after every incompatible binary/source switch; the driver's
once-per-binary priming is insufficient for alternating cache schema versions.

For changed-source comparisons, set a workload's `working_directories` to
absolute `reference` and `candidate` workspace roots, each containing its pinned
`library/`. Use the ordinary `library/everything.tex --parseonly` command in both
roles and hash both complete input trees. The driver records and checks each
process's working directory. Merely passing two different root-file paths from
one workspace does not isolate their imported libraries. Leave `NAPROCHE_LIB`
unset so each workspace supplies its own library mount. These are explicitly
different-input trials; grammar comparisons use the same frozen workspace in
both roles.

Readability evidence belongs under ignored `profiling/readability-1/` or in an
external archive. Preserve failed trials alongside successful comparisons.

The completed phase experiments, patches, and their harness tests have been
retired; see [benchmark history](../readme.md). The [Earley lifecycle audit](phase2.md)
remains as implementation documentation.
