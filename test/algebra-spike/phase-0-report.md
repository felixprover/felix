# Algebra Phase-0 report

Phase 0 is complete.  The proposed interfaces have executable models, their
compatibility obligations hold exactly, and maintained implementation may
begin.

## Baseline

The baseline in `baseline.tsv` was taken at revision `c6723770274f`.  The
ordinary gate passed `make test` and `make lib`; all nine selected roots then
verified from the default reusable store.  Each root also passed once from an
isolated cold store and once from the same warmed store.  Every run reported
zero source axioms and zero explicit proof gaps.

The only cold-baseline obligation over four seconds was
`surreal/absolute-value-estimates.tex:107:6` at 14.58 seconds while verifying
`everything.tex`.  It remained within the 20-second task limit and disappeared
on the warm run.  No baseline failure or authority anomaly was observed.

## Fresh spike results

Every spike was rerun directly with

```text
stack exec felix -- --fresh test/algebra-spike/NN-NAME.tex -t 20 --jobs 8
```

at the end of Phase 0.  The elapsed times below cover complete roots, including
imports; they are not per-obligation times.

| Spike | Result | Elapsed | Axioms | Gaps |
| --- | --- | ---: | ---: | ---: |
| 01 ring reducts | verified | 9.59 s | 0 | 0 |
| 02 module reduct | verified | 9.56 s | 0 | 0 |
| 03 submodule equivalence | verified | 12.14 s | 0 | 0 |
| 04 linear-map equivalence | verified | 13.98 s | 0 | 0 |
| 05 induced submodule | verified | 13.74 s | 0 | 0 |
| 06 quotient module | verified | 20.96 s | 0 | 0 |
| 07 ring subobjects and quotients | verified | 26.34 s | 0 | 0 |
| 08 opposite ring and regular modules | verified | 11.71 s | 0 | 0 |
| 09 finite fold | verified | 14.10 s | 0 | 0 |
| 10 finite support | verified | 12.69 s | 0 | 0 |
| 11 products and direct sums | verified | 43.94 s | 0 | 0 |
| 12 closure hull | verified | 7.36 s | 0 | 0 |
| 13 free module | verified | 34.71 s | 0 | 0 |
| 14 phrase contract | verified | 47.92 s | 0 | 0 |
| 15 natural divisibility | verified | 50.05 s | 0 | 0 |
| 16 power compatibility | verified | 19.87 s | 0 | 0 |
| 17 commutator orientation | verified | 9.36 s | 0 | 0 |

No completed obligation was reported as slow during this final sweep.  The
registered fast test suite also passed all 742 tests, including the parser and
compiled-notion regressions for the new algebra vocabulary.

## Prototype ownership

Each shared construction has one test owner and later spikes import that owner:

| Owner | Interface | Consumers |
| --- | --- | --- |
| 01 | additive-group and multiplicative-monoid ring reducts | 07, 11, 16 |
| 02 | module additive group | 03, 04, 05, 06, 11 |
| 03 | canonical submodule body | 05, 06, 14 |
| 04 | canonical linear-map body | 14 |
| 07 | subring, induced-subring, and quotient-ring prototypes | 14 |
| 08 | opposite ring, right-module body, and regular modules | 13, 14 |
| 09 | canonical finite fold | 11 |
| 10 | support and finite-support function spaces | 11 |
| 11 | products, direct sums, inclusions, reindexing, and mediators | 13 |
| 12 | closure systems and hulls | 14 |
| 13 | free-module specialization and lift | 14 |
| 14 | public phrase bodies and `naturalOne` | 15 and the Haskell tests |

Spikes 16 and 17 are compatibility fixtures rather than shared providers.
There is no duplicate prototype owner.  Generic algebra modules do not import
`algebra/group/all.tex`; the only maintained import is the intended one in
`everything.tex`.

## Frozen contract decisions

- Ring and module reducts are literal records with literal field equations.
  Induced and quotient structures reuse the specified group-level objects
  exactly; these obligations were not weakened to isomorphisms.
- `submodule` and `linear map` retain their public labels but will acquire the
  guarded canonical bodies proved equivalent in spikes 03 and 04.
- Quotient scalar multiplication and quotient-ring multiplication are defined
  by quotient descent and do not choose representatives.
- Finite folds quantify over all enumerations and extract their unique value.
  No selected enumeration enters the interface.
- Arbitrary typed precomposition is available on full products.  Direct-sum
  precomposition requires finite fibers; bijective reindexing supplies the
  corresponding isomorphism.  Finite-index direct sums equal products
  literally.
- The free module is literally the direct sum of the constant family of left
  regular modules, and its lift is the specialized direct-sum mediator.
- Natural gcd is total: it is zero at `(0,0)` and off the natural domain.  Its
  universal property and prime-divides-product theorem use only natural
  arithmetic.
- Natural powers have one monoid-level iteration owner.  Existing group powers
  and ring naturals retain their old equations as compatibility views.
- The commutator convention is exactly `x^-1 y^-1 x y`; conjugation is exactly
  `a x a^-1`.  The inverse and conjugation equations in the plan both verify.
- Every new phrase has a unique full form and the recorded semantic focus and
  argument order.  The dangerous bare or malformed forms are rejected by
  durable tests.

## Felix issues exposed by the spikes

Two implementation limitations were isolated and recorded in `notes/lib.md`.
Neither changes the mathematical contract.

1. Direct introduction of an exact parameterized structure can fail during
   structure-layer residualization even after all defining facts have been
   proved.  Spike 05 uses a classical double-negation step around the final
   left-module introduction; the proposed Felix fix is to make specialization
   agree with the registered body or fall back to the ordinary ATP obligation.
2. Decimal tokens currently denote opaque constants rather than mathematical
   naturals.  Phase 0 therefore defines `naturalOne = suc(emptyset)` and uses
   that term in coprimality and primality.  The follow-up note proposes an
   explicit mathematical-numeral surface and reconciliation of the existing
   natural and cardinal constants, including cardinal two.

These workarounds are confined to the relevant interfaces.  They leave no
unresolved algebraic orientation, representation choice, or grammar choice
for the maintained waves.
