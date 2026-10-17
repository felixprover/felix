# Notion MVP design examples

These files present representative source forms and their intended outcomes in
one readable place. See the user-facing guide to
[notions and formation checking](../../docs/notions.md) for the language rules.
These are design examples rather than standalone Felix modules; the executable
counterparts named below check their Core lowering, authority path, cache
identity, or diagnostic as appropriate.

| Example | Executable coverage | Expected outcome |
| --- | --- | --- |
| `adjective-readings.tex` | `test/phase9/notion-finite.tex`, `test/phase9/notion-finite-ambiguous.tex`, and lexicon/unit tests | ordinary and structure phrases select their reading statically; a bare adjective with two visible readings is ambiguous; intrinsic `equal to` is unchanged |
| `formation-contracts.tex` | `test/phase9/notion-direct*.tex`, `test/phase9/notion-structure.tex`, and the compactness library | contract-bearing predicate and provider occurrences require exact domain evidence; a complete structure phrase licenses its own modifier; sibling modifiers do not license one another |
| `notion-views.tex` | `test/phase9/notion-view*.tex`, `test/phase9/notion-noun-view.tex`, `test/phase9/notion-membership-negative.tex`, and `test/phase9/notion-structure*.tex` | clean theorem-site unary views and generated parent/base views close formation requirements, including direct symbolic membership, non-exporting negative membership, and genuine parameter erasure |
| `guard-scopes.tex` | `test/phase9/notion-guard*.tex` and proposition-compilation unit tests | checked guards license only their guarded body; implication and other non-conjunction results export no assertions |
| composite term notions | `test/phase9/notion-product.tex`, `test/phase9/notion-provider*.tex`, `test/phase9/notion-alias*.tex`, and composite evaluator unit tests | exact rich source identity supports bounded multi-premise rules, provider results, and one-way alias transport; every selected witness is replayed through the ordinary kernel |
| typed application results | `test/phase9/notion-endpoint-direct.tex` and `test/phase9/notion-endpoint-field.tex` | both graph-application spellings remain total; exact endpoint rows can lazily establish a requested result notion without making application itself a checked partial operation |
| exact named relations | `test/phase9/notion-relation.tex`, its `*-negative.tex` companions, and semantic/parser/rendering unit tests | positive named relations support direct evidence, symbolic grouped `Let` headers, classifications, parameterized argument reconstruction, and generic atomic normalization; fixed, inexact, negated, and dynamic forms remain outside the relation notion boundary |

The compactness fixture defines public `compact` directly on topological
spaces.  There is intentionally no intermediate adjective such as `cover
compact`.
