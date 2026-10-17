# Felix standard-library source style

The standard library should read as controlled textbook mathematics while
making every logically or ontologically significant distinction visible.
The reader should be able to tell what an object is and what a theorem claims
without reverse-engineering the elaborator.

This document governs maintained mathematical source. Support modules may be
more technical, but they remain checked parts of the mathematical narrative.

Prefer OED spelling for new definitions ("centre" instead of "center", but "normalize" instead of "normalise", etc.).

## State the ontology once and accurately

Keep the following notions distinct:

- a set, a proper class predicate, and a structure record;
- a set-coded function graph and a logical function;
- set-level global choice and logical selection;
- a relation and a higher-order predicate;
- a raw family satisfying closure laws and a realized structure;
- a presentation or representative and the value it represents; and
- a totalized defining term and the hypotheses under which its mathematical
  laws hold.

Use `\carrier[X]` for the carrier of a one-sorted structure. Do not silently coerce a
record to its carrier. The set of surreal reals is `\reals`; the exact real
field record `\RealField` has that set as its carrier and is not identical to
it.

Logical application remains explicit as `\Apply{F}{x}`. Ordinary `f(x)` is
application of a set-coded graph. Concrete logical types use `\Set`, `\Prop`,
and right-associative `\to`; a set-level assertion `$f:A\to B$` means exactly
that the graph `f` belongs to `\funs{A}{B}`. Do not flatten a genuinely
higher-order object merely to retain first-order export. Prefer variadic
`\Apply` for curried applications and group adjacent lambda binders with the
same type; keep differently typed binders separate.

Set-level global choice and `\Select` may both be used, but their roles must
not be blurred. Global choice selects from a nonempty set. Logical selection
belongs to the logical framework and carries its own typed witness principle.

## Write definitions at their natural domain

A public definition should identify its mathematical object and its domain.
It should say what happens on empty inputs and, when the defining term is
totalized, what is guaranteed outside the conventional domain.

Do not guard every named notion mechanically. When a noun, adjective,
relation, or verb has a natural structure domain, declare it under that
structure header: for example, `compact` is defined for topological spaces.
The same checked header supplies both the logical domain conjunct and the
source-level notion requirement. Keep a raw predicate only when its off-domain
meaning is itself useful.
See [Notions and formation checking](../docs/notions.md) for the source-level
evidence and inference rules.

Prefer bounded first-order prose such as “for every $x\in A$” in ordinary set
mathematics. Use typed symbolic quantification when the statement genuinely
quantifies over logical functions or predicates.

Use definition lists for a genuine conjunction of named conditions. The list
must elaborate to one transparent definition; labels name checked elimination
facts, never injected axioms.

## Treat structures as extensional mathematical records

Native structures are open set-coded records rooted at `record`.
Schemas declare required fields; a richer record may satisfy a parent schema.
An exact record has precisely the selected schema's fields. Felix calls this
notion `exact`; it corresponds to Mizar's strict structures.

Ask whether the mathematical datum has one distinguished carrier. If it does,
inherit `onesorted structure`; otherwise, inherit `record` and name the
relevant base, total space, endpoints, atlas, or other components explicitly.
Do not invent a carrier to package several equally significant sets. Existing
one-sorted mathematics need not change merely because carrierless records are
available. An exact zero-field record is the empty set; fieldless schemas can
still impose laws.

A structure parameter constrains fields and laws but is not silently stored
as a field or included in record equality. Full parameterized predicates put
the structure object first and parameters in declaration order. Their
parameter premises are conjuncts, not implications that make a structure fact
vacuously true for an invalid parameter.

Keep record shape, field specifications, and mathematical laws separate in
the elaborated representation. Every field has a stable identity independent
of its spelling, projection term, and aggregate position. Inherited fields
retain that identity and cannot be overridden.

Operation fields that are mathematical maps must be set-coded function graphs
with exact domains and codomains. One-sorted constants are carrier elements; order fields
are relations; topologies and uniformities are families of sets. A logical
function can become a record value only through a checked bounded graph
construction.

Concrete aggregates are transparent finite record terms. Prefer named fields
when a schema has several fields or is likely to grow; use positional notation
only for short, self-evident aggregates. Aggregate annotations guide
elaboration but are not nominal tags. A named instance consists of a
transparent object definition followed by a separately checked structure
theorem; neither schemas nor instances imply inhabitation.

Use an ordinary aggregate when choosing all the data, and `based on` when
copying a checked record interface with a few explicit replacements. The
replacements are simultaneous. Neither notation transports mathematical laws:
prove the target's requirements under its stated parameters. Use `instance`
for a closed record and `construction` for a parameterized family with an
immediately following proof. When a required header is outside construction's
registration policy, keep an ordinary definition and a separate theorem.

Prove later results through the structure theorem, `labelshape`, and
`labelprojection_field` consequences. State exactness and field equalities,
then use unannotated structure extensionality. Use an explicit reduct to
forget fields or disambiguate a projection; an open parent predicate is not
an exact parent record. The [checked worked example](../docs/structures.md#named-instances-and-construction-families)
illustrates these choices without exposing the set-coded record graph.

## Prefer mathematical public interfaces

Headline definitions and theorems should use familiar phrases such as
“$X$ is compact”, “linear over $R$”, or “has finite cardinality $n$”. A hosted
noun, adjective, relation, or verb already carries its natural notion
requirements; do not add a composite noun merely to repeat that domain.
Internal helpers may expose implementation details, but those details should
not become the public mathematical claim.

Prefer a natural `has` property when possession or availability is the
mathematical construction and an adjectival name would be ambiguous. For
example, “$X$ has a clopen basis” is clearer than an ambiguous dimensional
name. Such a declaration is an ordinary verb notion, not a special property
mechanism. Name its label after the complete phrase, such as
`has_clopen_basis`.

Begin every verb pattern with its finite verb. Felix derives the base surface
for the bounded regular cases and for `has`/`have`; place `\verbbase{...}`
immediately after the labelled environment header for another irregular form.
The annotation may replace only the leading word. Do not put a lexical prefix
before the finite verb or use metadata to change holes or later words.

Use explicit operation indices when several structures are in scope. Stable
notation such as `$x+_R y$` is preferable to fragile inference. Avoid a large
synonym grammar: every accepted proof phrase or notation should have one exact
lowering.

Judge a shorter statement together with its proof and ordinary uses. Keep an
assumption in its established mathematical shape when a new phrasing would
require conversion steps that add no mathematical idea. Prefer fully
transparent abbreviations for alternative wording; do not add an opaque
synonym or remove useful explicit typing merely to shorten a statement.

Use bounded noun phrases when the noun restriction is central, for example
`for every infinite cardinal $\mu\in\kappa$`. Keep additional conditions in
an explicit `such that` residual. Retain the symbolic spelling when it fits
the existing proof introductions more directly.

Proofs should begin with the mathematical idea. Use `Let`, `Suppose`, `Fix`,
`Take`, `Hence`, `Thus`, and “It suffices to show” where they match the proof
rule.
Use a calculation for a genuine chain of compatible binary relations,
and give each link its own focused justification. Equality transport is built
in; ordinary relation combinations require a checked `composition` fact, so
reuse general laws and their notion conditions where possible. Prove any
missing condition before the calculation; its displayed links do not supply
conditions to one another.
When the completed first-to-last relation is already the current goal, do not
add a separate `Follows` step merely to restate it.
Formula biconditionals remain the separate equality-at-`Prop` calculation
syntax. Use `Since` when a premise is needed only while establishing the next
claim: the premise is temporary and the resulting claim persists. When a proof
rule accepts introductions such as
`Hence`, `Then`, and `Thus`, choose the wording that matches its mathematical
role; the HTML renderer preserves that choice.

After establishing `P or Q`, prefer cases `P` and `Q` themselves over cases
`P` and `not P` when Felix can discharge the exact original disjunction from
the active context.

Preserve exact citations when they communicate a deliberate premise policy;
do not replace them with broader search merely to shorten the source. Do not
replace a comprehensible argument by a single ATP sentence merely to reduce
source length, and remove mechanical restatements that add no idea. See the
[Calculations section of the tutorial](../docs/tutorial.md#calculations) for
syntax and semantics.

Organize modules in mathematical dependency order. Long technical inductions
may live in preliminary, support, or appendix-style modules so that the main
development presents definitions and major theorems as a narrative. This is
not a blanket public/private split: every maintained support module remains
checked, visible, and documented.

Give every maintained theory with mathematical content a coherent local
document hierarchy. Begin that hierarchy at `\section` and use `\subsection`
and `\subsubsection` only beneath an enclosing heading of the preceding level.
The pure `everything.tex` aggregate is exempt. These levels are the source of
truth for presentation and must make sense within the theory itself rather
than treating an imported theory as an enclosing LaTeX section.

## Definition review checklist

Before accepting a maintained definition, answer:

1. What is being defined: a set, class predicate, relation, set-coded map,
   logical function, structure schema, record, or property?
2. What is its intended domain, and is a guard genuinely necessary?
3. What does the defining term mean outside that domain?
4. What happens for an empty carrier, empty family, or empty candidate set?
5. Is a presentation or representative being confused with its value?
6. For a parameterized structure, are parameter premises conjuncts of the
   full subject-first predicate?
7. Does the datum have a distinguished carrier, or should its components be
   named separately?
8. Is every field identity independent of spelling and projection machinery?
9. Is every intended operation graph given its exact domain and codomain?
10. Is a concrete record a closed named instance or an ordinary parameterized
    construction family?
11. Are all generated equations transparent checked consequences with
    reported authority?

## Theorem review checklist

Before accepting a maintained theorem, answer:

1. Are all carrier, relation, function, and structure hypotheses present?
2. Is the result stated at the strongest natural level that is actually
   proved?
3. Does an equivalence omit an independent conjunct such as a separation or
   nonemptiness condition?
4. Are empty and totalized cases correct?
5. Does the wording claim more than the formula?
6. Does the theorem depend on a source axiom or explicit proof gap?
7. Does a first-order public interface remain FOF-projectable when its formula
   is first-order?

No maintained theorem may be completed by adding an ordinary source axiom or
a new `Omitted.` marker. The library-quality tests reject either marker
directly and require every library source to be reachable from
`library/everything.tex`.
The same tests enforce unique labels and nonempty formal declarations and
condition lists. Parsing, citation resolution, proof checking, and authority
are established by verifying the full aggregate `everything.tex`.
The mathematical route and module roles are documented in `library/README.md`; every public notation must have an entry with its defining module and ontological kind in
`library/NOTATION.md`.
