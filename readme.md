# Felix

Felix is an experimental [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant)
based on [Tarski–Grothendieck set theory](https://en.wikipedia.org/wiki/Tarski%E2%80%93Grothendieck_set_theory) in [ω-order logic](https://en.wikipedia.org/wiki/Higher-order_logic).
It uses a [controlled language](https://en.wikipedia.org/wiki/Controlled_natural_language)
embedded in a subset of LaTeX, supporting [literate formalization](https://en.wikipedia.org/wiki/Literate_programming).

## Example

```latex
\begin{theorem}[Cantor]\label{cantor}
    There exists no surjection from $A$ to $\pow{A}$.
\end{theorem}
\begin{proof}
    Suppose not.
    Consider a surjection $f$ from $A$ to $\pow{A}$.
    Let $B = \{a \in A \mid a\notin f(a)\}$.
    Then $B\in\pow{A}$.
    Take an element $a'$ of $A$ such that $f(a') = B$ by \auto{surj}.
    Now $a' \in B$ iff $a' \notin f(a') = B$.
    Contradiction.
\end{proof}
```

## Try Felix

Felix supports Linux x86-64 and macOS AArch64. Other Unix-like platforms may
also work. Windows is unsupported, but [WSL 2](https://learn.microsoft.com/en-us/windows/wsl/)
may work.

Install [Stack](https://haskellstack.org/), for example through
[GHCup](https://www.haskell.org/ghcup/). Stack installs the required GHC compiler
when you first build. On Ubuntu, you may also need `sudo apt install zlib1g-dev`.

Felix uses [Vampire](https://vprover.github.io/) to discharge proof tasks.
Felix and its library are tested with [Vampire 5.1.0](https://github.com/vprover/vampire/releases/tag/v5.1.0),
with support for both FOF and TH0 input. Download a release or
[build Vampire from source](https://github.com/vprover/vampire/wiki/Source-Build-for-Users).
Put the executable on your `PATH` as `vampire`, or select it with
`export FELIX_VAMPIRE=/absolute/path/to/vampire`. Check the selected executable
with `--version`.

From the repository root, build Felix and verify a library file:

```sh
stack build
stack exec felix -- library/set.tex
```

Exit codes are `0` for success, `1` for rejected input or verification, and `2`
for operational failures, including prover or protocol failures. Diagnostics go
to stderr.

Felix automatically reuses a disposable verification cache in the platform's
XDG cache directory (typically `~/.cache/felix`).

Add `--html` to export the verified source and its imports to `./html`:

```sh
stack exec felix -- library/set.tex --html
```

Run `stack exec felix -- --help` for all options. See the
[CLI guide](docs/cli.md) for cache controls, resource limits, and troubleshooting,
and [HTML output](docs/html.md) for browsing and customizing the export.

## Development

Development checks use Bash, Perl, and ripgrep in addition to Stack and Vampire.
Some optional tools require Python 3; see the [development guide](docs/development.md).

| Command | Purpose |
| --- | --- |
| `make build` | Build the ordinary O2 executable |
| `make build-fast` | Build an O0 executable for faster compilation |
| `make test-fast` | Run deterministic unit and golden tests, plus boundary checks |
| `make test` | Run the complete test suite, including real-prover acceptance checks |
| `make spike` | Verify a representative standard-library slice |
| `make lib` | Verify the complete standard library |

Use `make test-fast` and `make spike` during implementation work. Reserve
`make lib` for potentially breaking changes and library integration; it can
take several minutes. Create the Make targets' store directory first with
`mkdir -p .cache`.

`test-fast` selects tests, not an optimization level. See
[build configurations](docs/development.md#build-configurations) for running
the O0 build and selecting it for tests.

| Location | Contents |
| --- | --- |
| [`source/Felix/`](source/Felix/) | Parser, elaboration, checking kernel, store, and prover integration |
| [`cli/`](cli/), [`cbits/`](cbits/) | Executable entry point and native runtime/process support |
| [`library/`](library/) | Mathematical standard library |
| [`test/`](test/) | Unit, golden, and acceptance tests and boundary checks |
| [`tools/`](tools/), [`benchmark/`](benchmark/) | Development helpers and performance measurements |

## Documentation

- [Tutorial](docs/tutorial.md): writing Felix mathematics.
- [CLI guide](docs/cli.md): running Felix, imports, cache controls, and diagnostics.
- [Development guide](docs/development.md): build modes, test selection, golden updates, and Make options.
- [Proof checking and cache reuse](docs/implementation.md): how Felix prepares declarations, checks proofs, and saves verified results.
- [HTML output](docs/html.md): rendering verified mathematics and commentary.
- [Benchmarks and profiling](benchmark/readme.md): measurement tools and `make profile` modes.
