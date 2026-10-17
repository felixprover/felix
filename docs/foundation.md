# Felix's set-theoretic foundations

Felix checks ordinary modules over a fixed higher-order
Tarski--Grothendieck set theory. The compiled manifest, not a source-axiom
file, is the authority for the primitive operations and principles below.
The maintained [`library/prelude.tex`](../library/prelude.tex) is packaged with
Felix and loaded implicitly as the tier-zero library. It gives selected
foundation facts and derived constructions ordinary public names while
retaining a confined, audited build path. It is not an ordinary importable
module; `library/everything.tex` roots the remaining textual library closure.

## Primitive operations

| Operation | Checked type | Public source form | Governing checked authority | Backend |
| --- | --- | --- | --- | --- |
| membership | `Set -> Set -> Prop` | `x \in A` | primitive relation | FOF |
| empty set | `Set` | `\emptyset` | `EmptyCharacteristic` | FOF |
| unordered pair | `Set -> Set -> Set` | `\upair{a}{b}` | `PairSetCharacteristic` | FOF |
| ordered pair | `Set -> Set -> Set` | `(a,b)` | `OrderedPairInjective` | FOF |
| first projection | `Set -> Set` | `\fst{p}` | `OrderedPairFirst` | FOF |
| second projection | `Set -> Set` | `\snd{p}` | `OrderedPairSecond` | FOF |
| family union | `Set -> Set` | `\unions{A}` | `FamilyUnionCharacteristic` | FOF |
| powerset | `Set -> Set` | `\pow{A}` | `PowerSetCharacteristic` | FOF |
| separation | `Set -> (Set -> Prop) -> Set` | bounded comprehension or `\sep{A}{P}` | `SeparationCharacteristic` | TH0 for the primitive construction |
| replacement | `Set -> (Set -> Set) -> Set` | `\repl{A}{f}` and functional replacement comprehension | `ReplacementCharacteristic` | TH0 for the primitive construction |
| logical selection at `tau` | `(tau -> Prop) -> tau` | `\Select{P}` or `\Select[\tau]{P}` | type-indexed logical selection witness | TH0 |
| least universe | `Set -> Set` | `\cumul{A}` | containment, transitivity, union, powerset, replacement closure, and `UnivOfMinimal` | mixed: the operation and first four public laws are FOF; replacement closure and minimality are TH0 |
| bounded least fixed point | `Set -> (Set -> Set) -> Set` | `\lfp{D}{F}` and inductive definitions | checked `SetLfp*` kernel rules | TH0 |
| set-level global choice | `Set -> Set` | `\choice{A}` | `GlobalChoiceMember` | FOF |

The ordered-pair representation is deliberately opaque and distinct from the
intrinsic unordered pair. Its complete foundation contract is injectivity and
the two projection equations. The values of the projections away from ordered
pairs are unspecified. In particular, the contract contains no representation
axiom and no extra claims that an ordered pair differs from either coordinate.

## Global choice and logical selection

These are different operations.

- Global choice is part of HOTG. If `x \in A`, then
  `\choice{A} \in A`. Both its type and membership law are first-order, so
  first-order uses route through FOF.
- Logical selection is an extension of the logical calculus. For every
  concrete type `tau`, `\Select{P}` selects at type `tau` when `P` has type
  `tau -> Prop`; `\Select[\tau]{P}` checks the same type explicitly. Its
  witness principle requires TH0 and is recorded once per selected type,
  separately from global choice.

## Concrete higher-order syntax

Felix exposes monomorphic simple types as `\Set`, `\Prop`, and right-associative
arrows. Thus `\Set\to\Set\to\Set` means
`\Set\to(\Set\to\Set)`. These forms are parsed only in type positions and are
not ordinary set expressions.

Typed logical application and abstraction use `\Apply{F}{x}` and
`\fun{x:\tau}{t}`. Typed symbolic quantifiers have forms such as
`\forall P:\Set\to\Prop.\ ...` and `\exists f:\Set\to\Set.\ ...`. Atomic
logical constants are introduced by signatures such as
`$\Phi : (\Set\to\Prop)\to\Prop$.` and transparent definitions such as
`$\Phi : (\Set\to\Prop)\to\Prop = \fun{P:\Set\to\Prop}{...}$.`

This typed fragment denotes the existing checked simple-type-theory core. It
does not encode predicates or logical functions as sets. Ordinary untyped
binders remain set-sorted, `f(x)` remains application of a set-coded function
graph, and genuinely higher-order goals and premises route through TH0.

## Replacement

`Repl` is function-valued. For a set `A` and checked logical function
term `f : Set -> Set`, `\repl{A}{f}` denotes `Repl(A,f)`. Its characteristic
law says that its elements are exactly the values `f(x)` for `x \in A`.
Functional replacement comprehensions continue to construct the same
primitive with a lambda-valued function argument.

Relation-form source replacement is derived rather than primitive. Felix:

1. restricts the source domain to arguments having an inhabited relation
   fibre;
2. uses logical selection to choose a member of each fibre;
3. applies function-valued replacement; and
4. publishes the expected relational characteristic fact only after checking
   that the relation is functional on the relevant domain.

The resulting theorem therefore carries the logical-selection dependency
honestly. Global choice cannot replace it in general: an arbitrary predicate
fibre is not itself already supplied as a set.

## Least universes

`\cumul{A}` is the least transitive, family-union-, powerset-, and
replacement-closed universe containing `A`. `UnivOfMinimal` is part of the
compiled contract; `UnivOf` is not an arbitrary choice of a suitable
universe.

The prelude exposes the first-order laws as `universe_contains`,
`universe_transitive`, `universe_union_closed`, and
`universe_power_closed`. Its typed higher-order interfaces
`universe_replacement_closed` and `universe_minimal` are exact, audited views
of the corresponding compiled foundation principles. It also proves
`universe_nested`:

```tex
n \in \cumul{m} \quad\Longrightarrow\quad \cumul{n} \subseteq \cumul{m}.
```

## Bounded least fixed points

For `D : Set` and `F : Set -> Set`, `\lfp{D}{F}` denotes the checked bounded
least fixed point. The higher-order form of separation is `\sep{A}{P}` for
`P : Set -> Prop`; it is the same primitive used by bounded comprehensions.

The confined prelude exposes four exact, search-ineligible theorem views:

- `lfp_bound`: `\lfp{D}{F}` is a subset of `D`;
- `lfp_least`: if `F(C)` is a subset of `C` and `C` is a subset of `D`, then
  `\lfp{D}{F}` is a subset of `C`;
- `lfp_fixed`: if `F(D)` is a subset of `D` and `F` is monotone below `D`,
  then `\lfp{D}{F} = F(\lfp{D}{F})`; and
- `lfp_induct`: a predicate closed under `F` on the fixed point holds of each
  member of the fixed point.

These facts are replayed from `SetLfpBound`, `SetLfpLeast`, `SetLfpFixed`, and
`SetLfpInduct`. They are not source axioms. Since they quantify over logical
functions or predicates and mention the higher-order intrinsic, proofs cite
them explicitly and route through TH0.

## Datatypes

Datatype declarations are conservative definitions followed by kernel-checked
proofs. Constructors use explicit Kuratowski pairs
`K(a,b) = {{a},{a,b}}`, with fixed-width binary tags and finite tuples of
arguments. The package defines `K` separately from the primitive ordered-pair
operation: the latter's foundation contract does not imply universe closure.
Constructor terms reference the checked definition of `K`, keeping their
representation linear in arity and logarithmic in the constructor count.

The head may bind distinct set parameters, for example `\tree{A}`. Every
clause targets that same application; recursive premises use its parameters
unchanged. Parameters do not become constructor fields. After defining the
constructors, the compiler elaborates nonrecursive domains in the parameter
context. They may mention constructors from the same declaration, but cannot
depend on clause-local premise variables or the carrier being defined.
It forms a finite seed containing the empty set and those domains, and uses
`UnivOf(seed)` as a bound. Ordinary kernel proofs establish closure of this
universe under the chosen representation. The carrier is the bounded least
fixed point of the clauses' separation operator; bounded monotonicity is
proved from the clauses. For a family this construction and its proofs are
pointwise in the parameters. Recursion remains direct membership in the carrier.
A declaration with only recursive constructors may have an empty carrier.

The public introduction, distinctness, injectivity, cases, and set-induction
laws keep their source statements and aliases. Distinctness and injectivity
are unconditional. Induction quantifies over arbitrary sets, without a
universe-membership or boundedness premise. Extra premise variables remain
quantified even when they are absent from the constructor arguments.
The additional `<label>_predicate_induct` law quantifies a logical predicate
`Set → Prop`. Its cases retain every domain guard and add a hypothesis for
each recursive premise, including unstored witnesses. It follows from the
set-induction law applied to separation of the carrier by that predicate.

An optional item heading such as `\item[Implication]` names the case and its
generated facts: `<label>_implication_intro`, for example. Names start with an
ASCII letter and contain letters, digits, underscores, or whitespace. Keys
ignore capitalization and replace whitespace runs with underscores; rendering
retains the written heading. Unnamed clauses retain constructor-symbol suffixes.
Duplicate case keys and colliding generated aliases are rejected.

Eligible introductions also register constructor results for `by notion`.
Provider arguments and the requested carrier must determine every quantified
variable, and guards obey the usual provider-result restrictions. Unstored
witnesses and richer fixed domains can therefore require explicit use of the
introduction theorem. These registrations retain their checked kernel authority
and their exact guards; formation never supplies a new proof assumption.

Each carrier's semantic binding also describes its cases, premise domains and
stored fields, with references to its checked introduction, no-confusion,
cases and induction laws. Each case records injectivity for a nonnullary
constructor and distinctness from the later constructors in declaration order.
Parameter and constructor arities come from ordinary object types. The owner
reconstructs the laws from this description and checks their exact statements,
both when publishing a declaration and when admitting a cached module. The
description adds no proof authority. Keeping it on the source binding lets
declarations with identical representations retain their own case names.

Structural induction resolves this source descriptor from a bounded universal
goal or an active membership. Each named case is an ordinary independent
subproof. Its domain guards are interleaved with the premise binders for
bounded `Fix` steps; a kernel derivation converts those checked cases to the
public induction theorem's quantified premise blocks. The final application
records that exact theorem as a dependency. Active induction hides the original
focus and retains only independent assumptions, with checked projections for
independent conjuncts. Notion and equality indexes are rebuilt from that scope;
local definitions depending on the focus must instead be part of the motive.

The [datatype frontend](../source/Felix/Checking/Datatype.hs) elaborates the
source and stages one atomic declaration. Its
[construction module](../source/Felix/Checking/Datatype/Construction.hs) builds
the representations, independently specified targets, and ordinary kernel
derivations. The declaration owner checks the defining equations and replays
the derivations against its own typing and ordered import environment. The
generated package makes no external prover requests. Support facts are local
to the declaration and excluded from search; implementation equations do not
register automatic definition views. Source uses remain global references,
so a first-order use of the public laws does not expose the higher-order
fixed-point representation. Identical definitions can share object identities
across declarations while retaining their distinct source names and aliases.

This removes the former trusted datatype-compilation authority. Cache epoch
169 invalidates its old admissions. Prepared declaration identity includes
the actual derivations and their ordered dependencies; subsequent reuse uses
the ordinary declaration-validation cache contract. The conservativity claim
is relative to the current foundation, including `SetLfpBound`, `SetLfpFixed`,
and `SetLfpInduct`. Deriving these rules from the other HOTG principles remains
a separate foundation change; no new kernel rule or prelude axiom is needed
for datatypes.

## Tier-zero public interface

The prelude provides plain public labels for universally needed
material, including:

- `choice_member`, `pair_eq_iff`, `fst_eq`, `snd_eq`, and the `universe_*`
  facts;
- `suc`, `transitiveset`, and `inductive_set`;
- `omega`, `omega_empty`, `omega_successor`, `omega_inductive`, and
  `omega_minimal`; and
- `natural_number`.

Successor and Omega are derived from the set and universe operations; they
are not additional foundation primitives. Ordinary library modules extend
these declarations directly and must not redeclare transparent wrappers for
the same objects or facts.

The module `library/set/choice.tex` derives family choice, the set-coded indexed product,
and the relation-form `axiom_of_choice` theorem from `\choice`.

Structure records use this set theory but remain separate from the concrete
higher-order expression language. Their source syntax and extensional record
semantics are documented in [Structures in Felix](structures.md).
