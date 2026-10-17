# Standard library status

This document records the current mathematical boundary of the Felix standard
library. It deliberately does not copy the import list, generated fact IDs,
premise lineages, or completed migration history: those are either source data
or version-control history rather than maintained status.

## Verification and trust boundary

[`prelude.tex`](prelude.tex) is the distinguished implicit library root, and
[`everything.tex`](everything.tex) is the textual root for the remaining
library. Every other maintained `.tex` source below `library/` should be in
the transitive import closure of `everything.tex`. Experimental sources may
remain outside this boundary until they are reviewed, moved below `library/`,
and imported by the aggregate.

The production library currently verifies with:

- zero ordinary source axioms; and
- zero explicit proof gaps (`Omitted.`).

Felix itself resolves imports and citations, elaborates definitions and
theorems, checks proofs, and reports the authority of the resulting facts.
The source-level quality tests enforce only complementary repository policies:
the absence of source escape markers, complete aggregate coverage, globally
unique labels, and nonempty formal declarations and condition lists.

The trusted set-theoretic interface is supplied by the checked prelude. The
ordinary library uses that interface directly instead of restating foundation
facts as wrappers. In particular, extensionality, empty set, pairing, union,
powerset, replacement, ordered pairs, successor and omega, universes, and
choice all have explicit prelude providers and reported authority.

## Foundational and ontological choices

The intended foundation is higher-order Tarski--Grothendieck set theory with
set-level global choice. Felix keeps the following distinctions explicit:

- a set is distinct from a logical predicate or function;
- a set-coded function graph is distinct from a logical function;
- `\choice{A}` is set-level global choice, while `\Select{P}` is typed logical
  selection;
- function-valued replacement `\repl{A}{f}` and bounded replacement
  comprehensions produce sets without pretending that logical functions are
  set-coded graphs;
- the class of all surreals is a guarded predicate, not a set, whereas bounded
  surreal stages, the surreal integers, and the surreal reals are sets; and
- a structure is an extensional set-coded record, not its carrier.

Concrete structure annotations resolve fields but do not add nominal tags to
the resulting records. Structure predicates are open under additional fields;
an exact structure has precisely the declared fields. Structure parameters
may be sets or structures, inherited fields coalesce by operation identity,
and no structure or soft type is assumed inhabited. Definitions of raw
adjectives are not mechanically guarded outside their intended domains;
domain-specific phrases and theorem hypotheses supply guards where they matter.

The record calculus publishes exact-record extensionality by field and the
identity of a schema reduct on an already exact record. These are checked
generated facts, not axioms; per-field staging keeps wide structure schemas
within the ordinary ATP feedback budget.

The surreal reciprocal is totalized at zero. The real numbers are not an
independent axiomatized carrier: `\reals` is a defined set of surreal values,
and its operations are restrictions of the canonical surreal operations.

## Mathematical coverage

The algebra hierarchy includes endpoint-explicit magma and monoid
homomorphisms, embeddings, surjections, and isomorphisms, together with
identity, composition, converse, and Hom-set calculus. Every group
homomorphism exposes its underlying monoid homomorphism without imposing a
group dependency on the monoid layer. Natural powers have one monoid-level
iteration owner; the established group notation and equations remain exact
compatibility views. The two-sided units of a monoid are closed under products
and powers, are preserved by monoid homomorphisms, and form an exact group.
Finite folds in commutative monoids are recovered canonically from the
singleton of all enumeration results, without selecting an enumeration. They
satisfy the empty, singleton, and fresh-adjunction equations, bijective
reindexing, disjoint-union and homomorphism laws, neutral-term deletion, and a
finite Fubini theorem. Shifting a finite-ordinal family by successor and
padding its initial value with the neutral element preserves the fold. Finite
products and finite sums are definitional views of this common owner.

Arbitrary dependent families of monoids have exact coordinatewise products.
The API includes homomorphic projections, the unique universal mediator,
contravariant reindexing by arbitrary functions, and monoid isomorphisms under
bijective reindexing. Empty and singleton products are covered explicitly;
the binary wrapper is literally the indexed product over the von Neumann set
`2={0,1}`.

Indexed group products extend indexed monoid products only by coordinatewise
inversion. They are exact groups, preserve commutativity coordinatewise, and
provide homomorphic projections, unique universal mediators, arbitrary
reindexing homomorphisms, and canonical isomorphisms for bijective reindexing.
Their empty, singleton, and binary cases use the same indexed construction.
The internal product of two subgroup carriers is ambient-bounded and kept
distinct from categorical group products. Either normal factor makes it a
subgroup and normalizes its own inclusion in the induced product group; if
both factors are normal, so is their product in the ambient group.
Subgroup index is the cardinal of the existing left-coset quotient. Every
coset is equinumerous with its subgroup, and a choice of representatives gives
the cardinal product formula without assuming normality. Separately, explicit
finite bijections and induction over the finite coset partition give
witness-form Lagrange divisibility, cyclic-subgroup divisibility, and cyclicity
at prime natural cardinality without using representative choice; no
finite-group record or total element-order term is introduced. Group-action
orbits form a partition, fixed
points have singleton orbits, and equivariant maps carry each orbit onto the
corresponding orbit. The orbit--stabilizer map is a representative-free
quotient descent with exact application and factorization equations; it is a
bijection and yields the finite-cardinality equivalence directly, as well as
the separate cardinal formulation.
The permutation group of a set is constructed exactly from its self-bijection
graphs, using graph composition, the identity graph, and graph converse.
Every group action induces a graph-exact permutation representation. Its
kernel consists precisely of the elements fixing every point, yielding the
faithfulness criterion and Cayley's theorem from the left regular action.

### Sets, functions, orders, and recursion

The base library develops ordinary set operations, products, powersets,
partitions, relations, equivalence relations, closures, and set-coded
functions. It includes set-domain bridges from logical operations to set-coded
graphs, both without a predeclared range bound and on heterogeneous binary
domains, while preserving the older bounded compatibility forms. Unary
quotient descent preserves relation range under the exact source-support
guard, and its compatible typed form preserves and reflects surjectivity. It
also includes global-choice consequences, finite sets and sequences, filters,
and ultrafilters. Set filters admit the unique improper powerset filter, while
properness is stated explicitly wherever nontriviality is required. Filters on
a fixed carrier form a closure system, so every hosted subset family generates
a canonical filter; finite intersections give its concrete membership test and
the hosted finite-intersection property characterizes properness. Filter bases
are presentations of those values, and mutually refining presentations
generate the same filter.

The compositional filter calculus includes named refinement, eventuality,
frequency, meshing, pushforward, pullback, `Tendsto`, filters within subsets,
subset traces, and binary products characterized by their projection
pullbacks. Every quasiorder has total `atTop` and `atBottom` filters, proper
exactly under upward and downward directedness. Nets are typed graphs and carry
the pushforward of `atTop`; top-cofinal reindexings compose convergence. On
ordinal indices this implies the established range-based `cofinalMap`, with the
converse proved under monotonicity. The natural sequence-tail filter is exactly
the pushforward of natural `atTop`, and finite index shifts preserve that filter
by equality, not merely refinement.
Linearly ordered sets carry generic open and closed intervals and rays. Their
order topology is generated by the open rays; finite intersections of those
rays form its canonical open basis, while open intervals are open and closed
intervals are closed. For the surreal real field, the generic intervals and
rays agree literally with the established real sets, metric balls are open
order intervals, and the order topology is literally the canonical real
metric topology. A nondecreasing real sequence bounded above converges in
that metric to the supremum of its range; by pointwise negation, the dual
statement holds for nonincreasing sequences bounded below and their infima.
The generic order layer packages carrier-hosted boundedness and conditional
completeness; for linear orders, the lower-bound/infimum half is derived from
the least-upper-bound half. Complete ordered fields, and hence the surreal
real field, instantiate this interface. Every closed interval in the order
topology of such a linear order is compact, by an ultrafilter cut argument;
in particular every closed real interval is compact in the canonical real
metric topology.
Natural subtraction is the unique additive difference on inputs `k <= n`,
with the expected zero and successor laws.
Natural binomial coefficients are defined by checked recursion on finite
Pascal rows. Each row has exact domain `suc(n)`, coefficients are explicitly
zero off that domain, Pascal's identity holds for all natural indices, and the
weighted identity yields divisibility of every interior prime-row
coefficient. No factorial or quotient operation is introduced.

Ordinary and dependent supports are explicit subsets of their index sets.
Finite-support spaces provide zero sections, coordinate extensionality,
restriction, support-preserving extension by zero, and point masses. Typed
precomposition preserves finite support under the stated finite-fiber
hypothesis; bijective reindexing has an exact converse map and the two maps
are mutually inverse. For constant families, the dependent and ordinary
spaces agree literally.

Dependent products have a common set-level operation layer. Coordinatewise
unary and binary maps, projections, universal mediators, and contravariant
reindexing are exact set-coded graphs with coordinate application laws.
Reindexing the full dependent product is ordinary precomposition and therefore
requires no finiteness hypothesis; finite-fiber conditions remain confined to
finite-support spaces.

Every equivalence relation on a set has an explicit set-coded quotient
projection. A set-coded graph constant on equivalence classes descends without
choosing representatives, with exact typing, application, factorization, and
uniqueness laws. The binary interface permits two different quotient domains
and has the corresponding exact typing, application, and uniqueness laws.
Logical-operation corollaries graphify their inputs first; consequently they
retain the graphifier's current TH0 Replacement authority, while the public
descent contract remains a relation-first statement about ordinary sets.

These graphifiers are mathematically instances of Replacement on a set
domain. Since their values are supplied by logical operations, their current
checked construction uses the TH0 Replacement interface; the resulting graphs
are ordinary sets and require no common codomain bound.

Well-founded induction is available together with two recursion layers.  The
older set-coded recursor retains an explicit codomain and its Zorn/global-choice
implementation for established clients.  The codomain-free recursor instead
uses compatible local solutions and relational Replacement: for every
set-sized well-founded relation and total logical set-valued step it constructs
the unique graph on the carrier, without Zorn, a range bound, or a set-level
choice of a solution.  A separately guarded relation-form interface accepts a
uniquely functional predicate on valid predecessor histories.  Its generic
checked presentation uses higher-order predicates and typed logical selection;
each concrete definable instance represents the ordinary first-order ZF
recursion schema and requires no mathematical Choice principle.

The codomain-free ordinal specialization has function, domain, equation,
uniqueness, derived-range, and literal restriction-compatibility laws.  A
scalar class-style view graphifies back to exactly the same ordinal segments.
The growing-package acceptance example constructs exact records with carrier
`alpha+1`, a current value, and an incoming graph on `alpha+1`; its stages need
no common range bound and its segment graphs are compatible by restriction.
Generated well-orders support Hausdorff's maximal-chain principle, Zorn's
lemma, the well-ordering theorem, order types, and Hartogs' theorem.

Finite sets are defined by bijection with a von Neumann natural number. The
library proves equivalently that a set is finite exactly when it injects into
some natural number. Finite sequences, append, decomposition, induction,
interleaving at exact even and odd positions, and folds are available without
introducing a second set-level notion of finiteness.  The opt-in
`structure/finite.tex` module adds the structural adjective reading and defines
it directly by finiteness of the carrier.

### Abstract reduction systems

The generic relation library includes converse-oriented Noetherianity,
carrier-indexed reflexive-transitive closure with first- and last-step
decompositions, the set-coded joinability relation, pointwise and global
confluence, weak normalization, and normal-form existence and uniqueness.
Newman's lemma is proved first for a binary relation by accessibility
induction; its sharp pointwise form requires local confluence only in the
chosen source's descendant cone.

An abstract reduction system stores only a carrier and its one-step binary
relation. A total transparent constructor packages raw `(X,R)` data and is an
exact system precisely when `R` is binary on `X`; the built-in reduct agrees
with this constructor. The structure layer hosts termination, confluence,
convergence, irreducibility, and normal forms as literal views of the generic
theory, including Newman's lemma and its unique-normal-form consequence.

### Ordered and lattice structures

The order library includes relation traces, induced ordered subsets, explicit
least-upper-bound and greatest-lower-bound predicates, and guarded supremum and
infimum operations.  Order-preserving maps, embeddings, isomorphisms, and
adjunctions have endpoint-explicit graph interfaces.  The lattice hierarchy
contains meet and join semilattices, lattices, bounded lattices, distributive
lattices, their reducts, and their homomorphisms and isomorphisms.  Finite
lattices have canonical extrema, while finite joins and meets are available
for finite subsets of any bounded lattice.

Families of sets closed under binary unions and intersections produce exact
set-family lattices; downsets of a quasiorder form bounded distributive
lattices, with a separate finiteness theorem for finite carriers.  In a finite
bounded lattice every nonbottom element lies above a join-irreducible, and
every element is the finite join of the join-irreducibles below it.

For a finite bounded lattice, the Birkhoff map and finite-join map form an
order adjunction and an order retract.  Their composite on downsets is an
explicit closure operator whose fixed points are exactly the image.  In the
distributive case the two maps are inverse bounded-lattice isomorphisms, and
surjectivity of the Birkhoff map, identity of the closure, and distributivity
are equivalent.  An inhabited finite distributive lattice has a canonical
finite bounded distributive expansion with the same lattice reduct, yielding
the conventional representation by a finite lattice of sets.  The Birkhoff
bijection also identifies the carrier cardinality with the number of downsets
and bounds it by the cardinality of the powerset of the join-irreducibles.

All of these order and lattice results are ordinary proved declarations with
zero source axioms and zero explicit proof gaps.  Generic closure-system
complete-lattice machinery and infinite representation theorems are
deliberately deferred; the present closure theory is the concrete finite
Birkhoff closure needed by the representation theorem.

Boolean algebras have exact powerset, subalgebra, field-of-sets, homomorphism,
embedding, and isomorphism interfaces. Proper lattice filters extend to
Boolean ultrafilters by Zorn's lemma, and ultrafilters separate failed order
relations. The single set-coded Stone map preserves and reflects the Boolean
order, is a Boolean embedding, and induces a Boolean isomorphism onto its image
field. The construction is valid for the one-element algebra: its Boolean
ultrafilter set and Stone-space carrier are empty, while the represented field
and its Boolean algebra remain one-element structures.

### Algebra

Indexed products of left modules are exact coordinatewise structures with
literal product-group additive reducts. Their coordinate projections and
mediators satisfy linear factorization and uniqueness. Full products may be
reindexed along every typed map into the pulled-back family, with bijective
maps inducing module isomorphisms. Empty, singleton, and binary product
constructors are included.

Indexed direct sums of left modules are the exact finite-support submodules of
these products, with literal direct-sum-group additive reducts. Their summand
inclusions and finite-support assembly maps are linear and satisfy the
coproduct universal property. Precomposition preserves a direct sum under the
exact finite-fiber hypothesis, while bijective reindexing gives a module
isomorphism. A finite indexed direct sum is literally its product module; the
empty and singleton cases are included.

Quotient modules reuse the exact quotient of the canonical additive group.
Scalar multiplication is obtained by representative-free descent of each
fixed-scalar endomorphism; the quotient carrier, additive structure, and
projection are literally the existing group constructions. The projection is
a linear surjection and its module kernel is exactly the given submodule.
For every linear map, the existing additive first-isomorphism graph is a
module isomorphism from the exact kernel quotient onto the exact induced image;
its quotient-class equation and factorization through the unchanged quotient
projection are explicit.
For submodules `N,P` of `M`, the restriction to `N` of the canonical quotient
projection from `N+P` has kernel `N inter P` and is surjective. Its unchanged
additive first-isomorphism graph gives the exact module isomorphism
`N/(N inter P) ~= (N+P)/P`, with the class equation and factorization stated.
For nested submodules `N subseteq P`, the projection modulo `P` descends
representative-freely through `M/N`; its kernel is the image of `P` under the
quotient projection. The unchanged additive first-isomorphism graph therefore
gives `(M/N)/(P/N) ~= M/P`, together with its double-class application equation
and both projection factorizations.
The quotient projection also induces the full submodule correspondence:
ordinary image and preimage are mutually inverse, inclusion-preserving
set-coded bijections between submodules of `M` containing `N` and submodules of
`M/N`. Restriction to a corresponding induced submodule is a module surjection
with exact kernel `N`; its first-isomorphism graph identifies the associated
induced quotient and image structures.

The group core includes ambient-dependent trivial subgroup carriers, the
canonical one-element exact group, translations, inversion, and conjugation
graphs. Subgroups are primarily carrier subsets of an explicit ambient group.
Every subgroup carrier has a canonical exact induced group with restricted
operation graphs. A separate `GroupSubstructure` relation compares group
reducts, so richer records such as topological groups remain eligible. The API
includes the nonempty difference criterion, binary and bounded indexed
intersections (with the empty case), inhabited directed unions in a fixed
ambient group, subgroup transfer and transitivity, direct-versus-iterated
induced structure equality, and the raw inclusion graph.
For a group homomorphism, a subgroup containing the kernel is exactly the
preimage of its image; for a surjective homomorphism, every target subgroup is
exactly the image of its preimage. These two equalities form the reusable
algebraic core of the quotient correspondence theorems.

The subgroup generated by a carrier subset is the bounded intersection of all
ambient subgroup carriers containing it. Its principal API consists of the
direct membership characterization and the least-subgroup universal property.
It is monotone, commutes exactly with images
under arbitrary group homomorphisms, and supports the usual determination
principle: homomorphisms agreeing on a generating set are equal.

Characteristic subgroups are subgroup carriers fixed by every automorphism of
their explicit ambient group. They are normal; the centre and the trivial and
full carriers are characteristic. Bounded indexed intersections remain
characteristic, including the empty-index case, and a general higher-order
principle turns a unique automorphism-invariant subgroup description into a
characteristicity theorem.

For an ambient carrier subset, `GroupNormalizer(G,A)` is its stabilizer under
conjugation. It is a subgroup carrier, every subgroup lies in its normalizer,
and a subgroup is normal exactly when its normalizer is the full carrier.
Normal closure is the bounded intersection of all normal subgroup carriers
containing the input and is exposed through its direct membership
characterization and least-normal-subgroup universal property. Equivalently,
it is the subgroup generated by the bounded union of all ambient conjugates of
the input.

Natural powers in an explicit ambient group are checked natural iterations of
right multiplication from the neutral element. The API supplies zero and
successor equations, carrier typing, addition of exponents, subgroup closure,
and preservation by homomorphisms. A cyclic subgroup is definitionally the
subgroup generated by a singleton and has the corresponding membership and
least-subgroup characterizations.
The bounded natural-power and inverse-natural-power carriers lie in it and,
together or using natural powers alone, generate exactly the cyclic subgroup;
no concrete integer domain is imported.

Group homomorphisms are exactly typed set-coded graphs with explicit source
and target structures. Neutral and inverse preservation are derived from
multiplication preservation. The endpoint calculus includes identity,
composition, source restriction, compatible codomain enlargement, and
corestriction to an induced subgroup containing the image. Generic images and
preimages produce subgroup carriers, while source-indexed kernels are bounded
by the displayed source carrier. Under a homomorphism hypothesis they equal
the preimage of the target neutral element, have the familiar first-order
membership law, and characterize injectivity. Group isomorphisms
are bijective homomorphism graphs; their converses and composites are
isomorphisms, embeddings are isomorphic to their induced images, and subgroup
transport is stated through a fixed chosen map with exact image/preimage
equations.

Left and right cosets are carrier subsets obtained from the algebraic
translation graphs. The left-coset relation is an equivalence relation whose
classes are literally the left cosets; normality identifies left and right
cosets and supplies multiplication and inverse congruence. The exact quotient
group is built by representative-free unary and binary descent, and its
canonical projection is a surjective homomorphism with kernel exactly the
given normal subgroup. A group homomorphism descends through every normal
subgroup contained in its kernel. This universal lift has the same range as
the original map, kernel equal to the image of the original kernel, and exact
injectivity and surjectivity criteria. At the full kernel it is literally the
existing first-isomorphism graph; after corestriction to the actual image it
is the unique factorization through the quotient projection and a group
isomorphism.
If `H` is a subgroup and `N` is normal, restriction of the appropriate
quotient projection gives the exact second isomorphism
`H/(H inter N) ~= HN/N`; the library also identifies this target with the
induced subgroup on the image of `H` in `G/N`. If `N subseteq K` are normal,
the universal lift of the projection modulo `K` gives the exact third isomorphism
`(G/N)/(K/N) ~= G/K`, with explicit class and factorization equations. For a
fixed quotient projection, image and preimage are mutually inverse,
inclusion-preserving bijections on subgroup carriers above the kernel, and
normality is preserved and reflected. A chosen group isomorphism similarly
induces inverse bijections between normal-subgroup carriers.

For the convention `[x,y]=x^{-1}y^{-1}xy`, inversion swaps the two arguments,
conjugation acts on both arguments, every group homomorphism preserves
commutators, and the two standard product identities are available. For
arbitrary displayed subsets, `RelativeCommutatorSubgroup(G,A,B)` is the
subgroup generated by commutators of their ambient carrier traces. It has an
explicit generator API and least-subgroup property, is symmetric, monotone,
functorial under homomorphisms, and covariant under conjugation. Normalizer
criteria for subgroup inputs give normality in the subgroup generated by
`A union B`; normal inputs give a normal subgroup contained in their
intersection. Its triviality is equivalent both to the trace-level and the
conventional carrier-typed centralizer conditions. The subgroup generated by
all element commutators is
characteristic, hence normal. A quotient `G/N` is commutative exactly when the
commutator subgroup is contained in `N`. The abelianization is the exact
commutative quotient by this subgroup. Every homomorphism to a commutative
group has a unique representative-free factor through the canonical
projection, with explicit class and factorization equations.

For a homomorphism `a:H -> AutomorphismGroup(N)`, the external semidirect
product is the exact group on ordinary pairs `(n,h)` with multiplication
`(n*a(h)(m),h*k)` and the corresponding explicit inverse. The canonical left
and right inclusions and projection are group homomorphisms. The left image is
exactly the projection kernel and is normal, the right inclusion is a section,
and conjugating the left copy of `N` by the right copy of `H` gives the stated
action. No normality is asserted for the right image. For the trivial action,
the canonical comparison with the binary product is an explicit group
isomorphism from ordinary pairs to functions on `2`; its inverse reads off the
two coordinates, so the two carrier representations are not identified
literally. If `N` is a normal subgroup carrier, `H` is a subgroup carrier,
`N inter H` is trivial, and `NH` is the full ambient carrier, conjugation
defines the exact action `H -> AutomorphismGroup(N)` on the induced groups.
The literal multiplication graph `(n,h) |-> n*h` is then a group isomorphism
from the corresponding external semidirect product to the ambient group.

Directed quasiorders are carrier-bearing structures with inhabited carrier and
pairwise common upper bounds; nonzero ordinals have a canonical exact
instance. A directed index substructure is a literal order reduct whose smaller
carrier is itself directed; group systems restrict to it by ordinary graph
restriction with exact component and bond equations. A group direct system
extends the index structure by set-coded component and bond families with
guarded identity and composition laws. Injective-bond systems are a separate
refinement. Cocones, mediators, compatible cocone isomorphisms, and
direct-limit cocones remain raw predicates on explicit endpoint groups and
set-coded maps, so no fictitious carrier is attached to morphism data and no
common universe of component groups is assumed.

The canonical group direct limit is the representative-free quotient of the
tagged component sum by eventual agreement at a common upper index. Its
multiplication and inverse descend from right-unique relations, while its
neutral is the unique class shared by all stage neutrals; no representative or
upper-bound selector is exposed. The exact group, canonical maps, mediating
map, semantic universal property, and unique compatible isomorphism between
arbitrary direct-limit cocones are proved. Canonical images are subgroup
carriers, cover the whole limit, form an inhabited directed family under
inclusion, and are nested along every bond. For injective-bond systems the
canonical maps are embeddings, and a separate consequence theorem proves that
a limit of centreless component groups is centreless.

A coherent direct-system isomorphism is a set-coded family of chosen
component isomorphisms between systems with the same carrier and order, with a
commuting square for every bond. Identity, pointwise converse, composition,
and extensionality are available. Given an explicit target component family,
conjugating each bond constructs an exact transported system; the target
family remains necessary because raw graph maps do not remember endpoint
structures. Pullback of cocones then proves the semantic result: coherent
system isomorphisms induce a unique compatible group isomorphism between any
two direct-limit cocones. For the concrete quotients this comparison is a
named mediating graph, with exact compatibility on every canonical leg.

The automorphism-tower data layer uses exact local packages whose ordinal
carrier is the genuine domain of the maps into one stage. History validity is
kept outside those records. A set-sized segment is exact stage-and-bond data;
when nonempty, its structural laws are carried by one ordinal-indexed group
direct-system reduct, while the length-zero segment remains available without
pretending that an empty index is directed. Earlier nonzero segments are
ordinary exact restrictions. Canonical limit equations use the concrete
representative-free limit, and their semantic relaxation uses the direct-limit
cocone property; every canonical segment is proved coherent.

The local automorphism-tower constructor is length-independent and total as a
logical set-valued operation. Under the bounded history invariant its zero
branch installs the input group, its successor branch installs the exact
automorphism group and composes all older legs with the inner map, and its
nonzero limit branch installs the concrete group direct limit with the
canonical maps. Each branch yields an exact valid stage package, and adjoining
that package gives a valid history on the successor ordinal. The transfinite
recursor constructs the unique package history on every ordinal. Projecting
its stage and incoming-map fields gives an exact tower segment whose smaller
ordinal instances are literal restrictions. The library proves stable stage
and bond accessors, correctly typed homomorphism, identity, and composition
laws, and the literal base, successor, and representative-free direct-limit
equations. Thus every constructed segment is canonical and therefore
coherent. Canonical segments of a fixed length over a fixed base group are
unique as exact records: bounded transfinite agreement first identifies every
stage and incoming bond, then identifies the full stage and bond graphs. This
remains a bounded set-sized construction rather than an implicit class
function.

For a centreless base group, centrelessness of stages and injectivity of bonds
are propagated as one bounded invariant. At successors this uses the inner
embedding; at limits the earlier restriction is an embedding direct system,
so its canonical maps are embeddings and its concrete direct limit is
centreless. Consequently every stage of a canonical segment is centreless and
every displayed bond is a group embedding. The proof uses the ordinary
bounded transfinite-induction theorem and introduces no universe bound.

For any semantic tower diagram, `SegmentImage(T,alpha,gamma)` is the image
carrier of the displayed bond inside the fixed ambient stage at `gamma`.
These carriers are subgroups, factor through intermediate stages, and are
nested with the index. If `alpha+1 <= gamma`, the image from `alpha` is normal
in the exact induced group on the image from `alpha+1`; this uses the general
normal-image theorem and does not assume injectivity. If the stage at `alpha`
is centreless and the successor bond into `gamma` is an embedding, that same
earlier image has trivial centralizer in the induced successor-image group.
Canonical centreless segments supply these two local hypotheses at every
displayed later stage. At a canonical limit, the segment-image family agrees
literally with the direct-limit canonical image family, is inhabited and
directed, and its union is the full limit-stage carrier.

`TowerSegmentIso(E,T,U)` is the bounded comparison predicate for exact
ordinal segment data with group stages and homomorphic bonds. It keeps both
endpoint segments explicit, requires a stage isomorphism at every index and a
commuting square for every bond, and treats `E` as a raw set-coded family
rather than as a carrier-bearing structure. Pointwise identity, composition,
converse, and extensionality are proved, together with a bridge to the
same-index direct-system isomorphism predicate whenever the two segment-system
reducts satisfy the direct-system laws.

A chosen isomorphism between the base groups recursively determines a
coherent comparison between any two coherent tower segments of the same
length. Successor components are the canonical automorphism transports and
limit components are the uniquely compatible direct-limit comparisons. The
resulting family is a tower-segment isomorphism, is uniquely characterized by
these recursive equations, and compares every coherent segment with the
canonical segment without identifying isomorphic records. Termination is a
bounded property of a displayed segment: both adjacent stages must occur and
the successor bond must be an isomorphism. For the canonical segment of length
`alpha+2`, this is equivalent to completeness of the stage at `alpha`; no
total tower-height operation is postulated.

Left monoid actions are exactly typed graphs on `carrier[M] times X`, with
the acting monoid and acted-on set retained as explicit parameters. Their
orbits are subsets of `X` and are deliberately empty off `X`. Group actions
specialize this interface; the stabilizer of an element of `X` is a subgroup
carrier of the acting group and is deliberately empty off `X`.

Element conjugation `x |-> axa^-1` is a group automorphism and its
heterogeneously graphified two-argument form is a left action in the same
order as group multiplication. Subset conjugation acts on the carrier trace
of an arbitrary set. Normal subgroups are subgroup carriers fixed by every
such conjugation; the library also provides the equivalent closure interface,
normal kernels and preimages, chosen-isomorphism transport, and the general
normal-image theorem into the induced image group. Centralizers likewise
ignore supplied elements outside the ambient carrier. They are antitone
subgroup carriers, commute with passage to a generated subgroup, have the
expected induced-subgroup formula, and transport along homomorphisms and
chosen isomorphisms. They transform covariantly under conjugation, so the
centralizer of a normal subgroup is normal. The centre is a normal subgroup
carrier and is transported exactly by a chosen isomorphism.
`CentrelessGroup(G)` retains both the group guard and the equality of the
centre with the ambient trivial subgroup carrier.

For every group `G`, `AutomorphismSet(G)` is the set of its bijective
endomorphism graphs. `AutomorphismGroup(G)` is the canonical exact group on
that set, with multiplication `f circ g`, neutral graph `id(carrier[G])`, and
inverse graph `converse(f)`. A chosen isomorphism `e : G ~= H` induces the
explicit graph map `f |-> e circ f circ converse(e)` between automorphism
groups. This transport is a group isomorphism and has proved identity,
composition, pointwise, and inner-map naturality laws.

The canonical inner map sends `a` to the conjugation graph `x |-> axa^-1`.
It is a group homomorphism whose kernel is exactly `Centre(G)`, so it is
injective exactly when the centre is the ambient trivial subgroup carrier.
Its image `InnerAutomorphismCarrier(G)` is a normal subgroup carrier of the
automorphism group and has a canonical exact induced group. For a centreless
group its centralizer in the full automorphism group is exactly the trivial
subgroup carrier; the centrelessness of the automorphism group follows by
antitonicity. Finally, `CompleteGroup(G)` means both centrelessness and that
every automorphism is inner; equivalently, the canonical inner map is a group
isomorphism onto `AutomorphismGroup(G)`.

The topology-independent Urysohn support layer defines a total sentinel entry
rank for finite sequences of sets. It proves the exact one-refinement rank
alternatives, including the case where the sentinel represents failure to
enter the last sequence member.

The normality layer defines the raw disjoint-closed-set separation property
without silently adding `T_1`. It proves the topologically guarded
closed-inside-open shrinking equivalence, the corrected open-upper-set
insertion lemma, and the typed `T_4`-to-`T_3` implication. Relational Choice
then supplies one bounded set-coded normal shrinker for deterministic later
chain refinement.

The finite open-chain layer fixes one normal shrinker, simultaneously inserts
one open set into every gap, and proves that exact even/odd interleaving
preserves openness, successive closure nesting, and both endpoints. The
resulting bounded refiner is an exact endomap of the chain-state set, whose
natural iteration starts with one step and doubles the step count at every
level. This layer is independent of surreal and real arithmetic.

The open rank-cell layer gives every positive finite open chain a set-coded
finite open cover of the carrier. It treats both endpoint cells explicitly and
proves that entry rank is constant or takes two adjacent values on each cell,
still without importing surreal arithmetic.

The real-valued step layer scales the chain at level `n` by the existing
dyadic epsilon and proves that its step count times that mesh is exactly one.
Each level is an exact set-coded map into the real unit range, and the levels
form an exact natural family. Successive values are proved to be either
unchanged or increased by one new mesh unit, yielding monotonicity and the
one-mesh upper increment. On every member of the finite open rank-cell cover,
the level map oscillates by at most its mesh. The proofs use the checked
doubling recurrence and dyadic halving directly, without adding exponentiation
or series infrastructure.

Subspace topologies use the trace `A \inter carrier(X)` as their exact
carrier. Their API includes open and closed characterizations, continuous
inclusion, continuous domain restriction, and codomain corestriction without
changing the underlying graph. Continuity has an exact pointwise open-local
criterion and a metric-target local-ball specialization. Positive metric
balls are open, sufficiently separated balls are disjoint, and the canonical
real metric has distance one between zero and one. The real topology and its
unit-interval subspace are named exact structures. Real completeness also
exposes transparent canonical `realSupremum` and `realInfimum` terms with
typing, bound, and extremality laws; the latter is constructed by pointwise
negation from the former.

The open-chain limit layer takes the direct bounded set of all finite-level
values at each carrier point and applies that canonical supremum, producing an
exact set-coded map. A checked telescoping envelope gives the one-sided bound
`s_n(x) <= f(x) <= s_n(x) + epsilon_n`. Combined with the finite open
rank-cell cover, this proves continuity into the real metric topology with the
sharp two-mesh local estimate. The same graph is then corestricted to the
named real unit-interval topology and is one on the first open endpoint and
zero outside the last.

Urysohn's lemma is proved for raw normal topological spaces, without adding a
`T_1` or inhabited-carrier premise. Disjoint closed sets admit an exact
set-coded continuous map to the real unit interval with the conventional zero
and one endpoint values; a real-valued companion retains explicit unit bounds.
The same layer proves the closed-inside-open bump-function form and
characterizes raw normality by continuous unit-interval separation. The
reverse implication uses open half-radius balls about zero and one in the
interval subspace and does not depend on an order topology.

The Tietze layer extends continuous real-valued maps from closed subspaces of
raw normal spaces, again without a `T_1` or inhabited-carrier premise.  Its
fixed-shrinker construction is deterministic and preserves any prescribed
nonnegative absolute bound, including an explicit zero-map branch at bound
zero.  Closed real intervals support both real-valued extensions with
interval-bounded range and genuinely interval-valued extensions, including
the unit interval.  The arbitrary real-valued theorem squashes into `(-1,1)`,
extends into `[-1,1]`, uses the supplied shrinker to push endpoint values
strictly into the open interval while fixing the original closed subspace,
and then unsquashes.  Strict interior range supplies the nonzero denominator
required by the totalized reciprocal; the public normal-space theorems choose
the shrinker existentially.

### Ordinals and cardinals

The ordinal layer uses von Neumann ordinals and proves that finite ordinals are
exactly the natural numbers. Cardinals are initial ordinals, and `\card{X}` is
the least Hartogs-bounded ordinal equinumerous with `X`. Injection comparison
agrees with inclusion between canonical cardinals; strict comparison agrees
with ordinal membership.

Cardinal sum, product, and exponentiation are defined by cardinalizing tagged
sums, products, and function spaces. On natural numbers, cardinal sum and
product agree with natural addition and multiplication. The reconciliation
layer identifies finite cardinality, at-most-countability, countable
infinitude, and the canonical cardinal equations they express.

Cofinality is totalized but its ordinal laws carry explicit ordinal
hypotheses. Normal maps, normal cofinal maps, cardinal-valued normal sequences,
index domination, and infinite-cardinal-valuedness remain separate interfaces.
The ambient-explicit stationary-set layer proves Fodor's lemma, reflection
lifting, self-nonreflection splitting, and Solovay's theorem: every stationary
subset of an uncountable regular cardinal has an exact partition into as many
pairwise-disjoint stationary cells as the cardinal itself. The library also
proves the stationary and all-below-GCH forms of Silver's theorem.

The combinatorics layer provides exact fixed-cardinality subset families,
hereditary pair homogeneity, and a two-colour pair-arrow predicate whose source
and target order types are explicitly ordinal.  These interfaces do not
depend on graph theory.  A separate colour-graph bridge identifies cliques and
independent sets with the corresponding homogeneous sets.  The
Erdős--Dushnik--Miller development proves, on every infinite carrier, the
dichotomy between a full-cardinality independent set and a countably infinite
clique, as well as its complementary graph form.  It then proves the literal
relation `kappa -> (kappa, omega)^2`: the two homogeneous alternatives have
order types `kappa` and `omega`, respectively.  The graph proof separates the
large-neighbourhood construction from the regular and singular small-degree
arguments; the latter uses cofinal regular blocks and diagonal thinning.  The
development uses the existing checked choice interface and introduces no new
source axiom.  Chain--antichain specializations remain a downstream option,
not part of this theorem's contract.

### Surreals, integers, and reals

A surreal is represented by a sign function on an ordinal birthday. Bounded
stage constructions and higher-order class recursion yield cuts, negation,
addition, multiplication, reciprocal, square root, and their order and ring
laws without collecting the proper class of all surreals into a set.

The surreal integers are the differences of embedded naturals. Their exact
presentation, equality and order criteria, canonical signed forms,
discreteness, induction, and ordered integral-domain structure are proved.

The real carrier is a defined subset of the successor-omega surreal stage.
It is closed under the canonical field operations, satisfies the Archimedean
property and least-upper-bound property, and is packaged as an exact complete
Archimedean ordered field. The inherited absolute value and metric give an
exact metric-space structure on the same carrier.

### Algebra and topology

The extensional structure hierarchy includes magmas, semigroups, monoids,
quasigroups, loops, groups, rings, division rings, fields, ordered structures,
modules, vector spaces, and meet semilattices. It proves representative generic
laws such as cancellation, inverse uniqueness, zero annihilation, submodule
closure, and linear-map preservation. The surreal integers and reals are
concrete exact instances of the relevant abstractions.

Every left module has a canonical exact additive commutative-group reduct with
literal field equations. Scalar multiplication preserves zero, negation,
subtraction, natural scalar multiples, and finite sums through that reduct.
The canonical zero module over any ring is an exact one-element structure, and
a unital module over a ring with zero equal to one has singleton carrier.
Right modules are exact views of left modules over opposite rings. Their
right-displayed scalar multiplication retains the underlying ring-first graph
and transports both distributive laws, scalar associativity, and the unit law.
The left regular module has additive reduct exactly `AdditiveGroup(R)` and
scalar action given by left ring multiplication. The right regular module is
literally the left regular module over `OppositeRing(R)`; its displayed action
is right multiplication, while its additive reduct is again exactly
`AdditiveGroup(R)`.
The ring binomial expansion is a finite sum in `AdditiveGroup(R)`. Its
summand uses the Pascal-defined natural coefficient, natural subtraction in
the first exponent, and the existing ring natural elements and powers. In a
commutative ring it equals the corresponding power of a sum.
Left and right ideals are defined as submodules of the corresponding regular
modules; two-sided ideals require both conditions, and the unqualified ideal
predicate means two-sided ideal over any ring. In a commutative ring it is
equivalent to either one-sided condition. Zero and unit ideals, binary and
indexed intersections, the
unit/properness criterion, exact induced additive groups, and two-sided ring
homomorphism kernels are available. Ring kernels and images are source-indexed
by the homomorphism graph and source ring; their guarded laws retain the full
ring endpoints. Left, right, and two-sided ideal carriers
form bounded closure systems; their hulls give generated ideals with
extensivity, monotonicity, leastness, and singleton principal-ideal laws. The
unqualified generated ideal is the two-sided hull; in a commutative ring it
also equals the left- and right-generated hulls. The named principal ideal is
this hull on a singleton. Its zero, one, and unit-invariance laws hold in every
ring; in a commutative ring it is the carrier of multiples of its generator,
membership is divisibility, and principal-ideal membership is preserved by
every natural power. The annihilator of an
arbitrary module subset is a left ideal, and is two-sided when the subset is a
submodule.
Throughout the library, a subring of `R` contains the ambient unit `1_R`.
For a subring `A` and a two-sided ideal `I`, `subringIdealSum(R,A,I)` is the
literal carrier `{a+i | a in A, i in I}`. It is the least subring containing
both inputs. The ideal `I` remains two-sided in its induced ring, while
`A inter I` is two-sided in the induced ring on `A`; these are the fixed raw
endpoints for the second ring isomorphism theorem.
Congruence modulo a two-sided ideal is literally the additive coset relation.
It has the equivalent `-x+y in I` and `x-y in I` characterizations, is
compatible with all ring operations, and is detected exactly by equality
under the canonical quotient projection.
For a two-sided ideal `I` of `R`, `QuotientRing(R,I)` is an exact ring whose
additive reduct is literally `QuotientGroup(AdditiveGroup(R),I)`.
Multiplication is the representative-free binary descent through the same
coset relation, and the unit is the canonical image of `1_R`. The reused
group quotient projection is a ring surjection with kernel `I`; the quotient
is a singleton exactly when `1_R` lies in `I`, and commutativity descends.
Every ring homomorphism has a unique representative-free lift through each
two-sided ideal contained in its kernel. The lift is literally the universal
group quotient lift on the additive reduct. Its range equals that of the
original map, its kernel is the image of the original kernel, and exact
injectivity and surjectivity criteria are available.
For a prime natural `p`, the binomial theorem proves the Freshman's dream
modulo every ideal containing `p_R`. Whenever `p_R` lies in `J` and `d^p`
lies in `J` for every `d` in `I`, the map `x |-> q_J(x^p)` descends
representative-freely to a ring homomorphism `R/I -> R/J`. Its kernel,
congruence-reflection, surjectivity, bijectivity, and ring-isomorphism
criteria are explicit. The specialization from `(a)` to `(a^p)` is available
under the divisibility hypothesis `a^p | p_R`, with the injectivity criterion
reduced to `x^p in (a^p) => x in (a)`.
For every ring homomorphism, the existing additive `firstIsomorphismMap` is a
ring isomorphism from the exact quotient by its ring kernel to the exact
induced subring on its image. Its graph is literally the generic ring quotient
lift at the kernel; the quotient-class application equation and factorization
through the canonical quotient projection are literal.
For a subring `A` and two-sided ideal `I`, restricting the quotient projection
of the induced ring on `A+I` to `A` has kernel `A inter I` and full image.
Its unchanged additive first-isomorphism graph gives the exact ring
isomorphism `A/(A inter I) ~= (A+I)/I`, with explicit class and factorization
equations. Restricting the ambient `R/I` projection to `A+I` gives a second
canonical ring isomorphism from that target to the exact induced subring on
the image of `A` in `R/I`.
For two-sided ideals `I subseteq J`, the projection to `R/J` descends
canonically through `R/I`. Its kernel is the image of `J`, and the resulting
first-isomorphism graph gives the exact ring isomorphism
`(R/I)/(J/I) ~= R/J`, together with its nested-class application and both
projection factorizations. Image and preimage under the quotient projection
are mutually inverse and inclusion-preserving on two-sided ideals, yielding an
explicit bijection between ideals of `R` containing `I` and ideals of `R/I`.
Submodules use the canonical additive-group reduct for their additive closure.
They are closed under intersections, indexed intersections, and inhabited
directed unions. Every submodule carrier has a canonical exact induced module
whose additive reduct and restricted scalar graph are literal, and the full
induced module recovers an exact ambient module.
Linear maps are defined through homomorphisms of the canonical additive
reducts together with scalar preservation. They preserve finite sums, compose,
restrict and corestrict along submodules, enlarge along literal module
substructures, and admit converse linear maps when bijective. Module
embeddings, surjections, isomorphisms, and guarded hom sets use the same
endpoint-explicit graph discipline.
The source-indexed kernel and image carriers of a linear map are obtained from
the existing additive-group kernel and graph image on the source module. Their
guarded laws retain the scalar ring and full module endpoints. Their induced
modules are exact; the kernel inclusion is an embedding and corestriction to
the induced image is a surjection. Zero-kernel and full-image criteria
characterize injectivity and surjectivity, and both carriers have explicit
composition laws.
Submodule carriers form a bounded closure system, whose hull defines module
span. The API includes empty, singleton, full-carrier, monotonicity, and union
laws. Binary submodule sum is the resulting associative, commutative,
idempotent join with zero submodule as identity. Linear maps carry a span onto
the span of its image, and maps agreeing on generators agree on their span.
The free module on an index set is definitionally the module direct sum of the
constant left-regular family. Its carrier is the ordinary finite-support
function space, its basis vectors are point masses with explicit coordinate
and support equations, and every vector has the inherited finite point-mass
decomposition. The empty free module is the canonical zero module, a singleton
free module is canonically isomorphic to the left regular module, and
bijective reindexing uses the existing direct-sum isomorphism. The specialized
direct-sum mediator gives the unique linear extension of every indexed family,
with explicit basis and finite-sum application equations.
The linear-combination map is this free extension under a dedicated public
name. A typed indexed family spans, is linearly independent, or forms a basis
when that map is respectively a module surjection, injective, or a module
isomorphism; each predicate includes its full structural and typing guards.
Over the permitted trivial ring, every module and free module has singleton
carrier, so every well-typed family over every index set forms a basis; this
degeneration is recorded as an explicit theorem rather than excluded by the
definition.
The basis predicate is equivalent to spanning together with linear
independence. The range of the linear-combination map is exactly the
closure-theoretic span of the family, yielding the usual full-span criterion,
coordinate existence and uniqueness, and determination of linear maps by
basis values. Bijective reindexing preserves all three predicates via the
canonical free-module reindexing isomorphism. Dimension, rank, and IBN remain
deliberately deferred.

The group layer also provides ambient-typed commutation, a canonical exact
one-element group distinct from each ambient trivial subgroup carrier, and
set-coded translation, inversion, and conjugation maps. These maps have named
typing, application, converse, and bijection laws; conjugation uses
`x |-> axa^{-1}` and composes in the same order as group multiplication.

The topology hierarchy covers preclosure and topological spaces, arbitrary
generated topologies, set-coded initial and final topologies, prebases and
bases, the refinement order of topologies,
continuous maps and homeomorphisms, pseudometric, metric, and uniform spaces,
induced topologies, compactness, convergence and completeness, separation axioms,
raw normality and normal shrinkers, and topological groups. Topology families
form a closure system, so the generic constructor is the least topology
containing any hosted family of subsets; finite intersections give its
canonical basis presentation. Initial and final topologies satisfy their
indexed universal properties, with explicit empty-index computations and a
direct single-map presentation on both sides.
Quotient topologies are single-map final topologies, and quotient maps are
surjections whose target opens are exactly the subsets with open inverse
image; continuity out of a quotient is detected after composition with its
quotient map. Equivalence relations use the existing quotient carrier,
canonical projection, and representative-free descent graph; a continuous
class-constant map descends uniquely to a continuous map on the quotient.
The binary product is the initial topology of the two coordinate projections
on the literal Cartesian-product carrier. Its projections are continuous and
open,
maps into it are continuous exactly when both coordinates are continuous, and
continuous maps admit a canonical set-coded pairing. Its coordinate slabs
generate exactly the same opens as its open rectangles, which form an open
basis. Open maps use the same endpoint-explicit discipline as continuous
maps; they are closed under identity and composition, and every homeomorphism
is open. Products of continuous maps are continuous. Coordinate swap and
canonical reassociation are homeomorphisms, without identifying product
records whose literal carriers have different parenthesizations. Binary
products commute exactly with subspace topologies, including for arbitrary
sets whose traces on the ambient carriers may be empty. The neighbourhood
filter at a pair is exactly the product of the two coordinate neighbourhood
filters. Indexed products use the existing dependent-product carrier and are
characterized by continuity of every coordinate; the existing dependent
mediator supplies the canonical continuous map into a product. Their
coordinate slabs form an open prebasis, and their finite intersections form
the canonical open basis of finitely constrained boxes. The empty indexed
product is literally the singleton empty function with its indiscrete, hence
also discrete, topology. Indexed coproducts use tagged indexed sums and are
characterized by continuity on every summand; their canonical injections are
continuous, open, and injective. A subset of a coproduct is open exactly when
its inverse image in every summand is open. The indexed-sum mediator assembles
any continuous family of maps into the canonical continuous map out of the
coproduct. Binary coproducts provide named left and right injections as the
two-element specialization of this construction. Their open sets and maps
out are characterized by the corresponding two summand restrictions. The
empty indexed coproduct is the empty discrete space, while a singleton
indexed coproduct is canonically homeomorphic to its unique summand.
Subspaces retain their direct open-family presentation and are proved equal
to the corresponding single-map initial topology. Their universal property,
corestriction criterion, exact transitivity law, and full-carrier reduction to
the explicit topology-only reduct are available without equating richer
structures with their reducts. Every open basis restricts canonically to an
open basis of a subspace by taking traces.
Compactness is equivalent to the closed finite-intersection property, to
convergence of every ultrafilter, and to existence of a cluster point for
every proper filter. Filter clustering is equivalently meshing with the
point's neighbourhood filter, or properness of their common refinement.
Continuous maps preserve filter cluster points under pushforward; consequently
continuous surjective images of compact spaces are compact, and the range of
every continuous map from a compact space is compact in its codomain.
Limits of proper filters belong to every closed eventual set. Consequently,
every closed subspace of a compact space is compact.
Closed real intervals are compact, and a subset of the real line is compact
exactly when it is closed and real bounded.  The boundedness direction uses
finite traces of unit balls; finite unions of real-bounded sets are available
as a separate reusable theorem. Every compact space is pseudocompact. Every
nonempty compact real set has a least and a greatest element, obtained from
its infimum and supremum; consequently every continuous real-valued map on a
nonempty compact space attains both extrema. A continuous map from a compact
subset of a pseudometric space into another pseudometric space is uniformly
continuous on that subset, by the finite-cover half-radius argument.
Connected subsets are interpreted through their subspace topologies.
Continuous surjective images preserve connectedness, and therefore so does
the range of every continuous map from a connected space. Order-convex
subsets of the real line are connected; in particular, all standard open and
closed intervals and rays are connected, including their empty and degenerate
cases. Conversely, every connected real subset is order-convex. Continuous
real-valued maps on connected spaces therefore have the intermediate-value
property, with the usual closed-interval theorem as a specialization.
Neighbourhoods at carrier points form proper filters generated by their
canonical open-neighbourhood bases, and the pure point filter refines them.
Ambient neighbourhood-within filters use carrier traces and characterize
closure by properness, equivalently by meshing with the associated principal
filter. Subspace neighbourhood filters are pullbacks along the canonical
inclusion and push forward to the ambient within filter. A topology is
recoverable pointwise from its neighbourhood filters. Pointwise continuity is
tendency between neighbourhood filters and characterizes global continuity.
Continuity within a set uses the ambient within filter; continuity on the set
is equivalent to continuity of the exact restricted graph from the
corresponding subspace. Exact-domain wrappers give the same pointwise and
global notions directly for partial graphs on the carrier trace, without
choosing ambient extensions. Function limits are uniformly filter-relative,
with ordinary, within-set, punctured, exact-domain, and order-at-top
specializations; continuity is the self-limit case and continuous
postcomposition preserves limits. Arbitrary filter bases
have choice-free open local refinements, and local bases transport under
homeomorphisms. Filter convergence is equivalently `Tendsto` of the identity
graph to the neighbourhood filter. Topological sequence convergence is the
natural-index specialization of generic directed-net convergence. Both are
given by `Tendsto` from the appropriate final-segment filter and admit the
eventual-neighbourhood criterion; sequence convergence is invariant under
finite shifts and equality of sequence graphs. Subsequences are represented
by composition with strictly increasing natural-index selectors, with exact
sequence typing and application laws. Every sequence in a compact subspace of
a metric topology has a convergent subsequence; its increasing selector is
constructed from a cluster point of the sequence-tail filter.
Every real sequence with bounded range has a real convergent subsequence
(Bolzano--Weierstrass), obtained by placing the range in a compact symmetric
interval and invoking the generic compact-metric theorem.
Filter convergence in binary and indexed products is coordinatewise. Binary
products and finite indexed products of compact spaces are compact; the
finite indexed proof uses finite choice rather than global choice.
Hausdorffness is equivalently failure of distinct-point neighbourhood filters
to mesh, or impropriety of their common refinement. Consequently every proper
filter in a Hausdorff space has at most one limit, and every compact subset of
a Hausdorff space is closed. The `T_1` property is also
equivalent to every singleton being its own closure, and to the corresponding
pointwise singleton-closure implication.
For every uniform space, separatedness is equivalent to Hausdorffness of its
induced topology, without an inhabitation hypothesis. At each point, the
ordinary neighbourhood filter of that topology is generated by the uniform
balls of its entourages. Uniform continuity is tendency of the product map
between uniformity filters, equivalently inverse-image preservation of
entourages; uniformly continuous maps include identities and are closed under
composition. A Cauchy filter is a proper filter whose self-product refines the
uniformity, equivalently one that contains a set with entourage-small square
for every entourage.
Pseudometric spaces carry the common nonnegative, diagonal-zero, symmetric,
and triangular distance laws; metric spaces add identity of indiscernibles.
Every pseudometric induces a uniformity and hence a topology, and the latter
is exactly the directly ball-generated topology. The induced topology of a
metric space is Hausdorff. Cauchy filters for a pseudometric uniformity are
equivalently the proper filters containing sets of arbitrarily small positive
diameter. Metric convergence and completeness are connected to this
uniformity, including empty-carrier edge cases.

Clopen subsets of every topological space form a canonical Boolean algebra.
More generally, a field of sets is a clopen open basis for its generated
topology; if it separates points, that topology is Hausdorff, and if the
generated space is compact, it has no clopen subsets outside the field. The
Stone topology on the Boolean ultrafilters is compact and Hausdorff with a
clopen basis, every clopen is a Stone-map value, and the original Boolean
algebra is isomorphic through the same Stone graph to the full clopen Boolean
algebra.

The generated-topology, discrete-space, countability-axiom, clopen-basis,
complete-regularity, local-compactness,
countable-compactness, real-boundedness, and pseudocompactness layers support a
complete Isbell--Mrówka construction.  For every almost-disjoint family on
`naturals`, its Ψ-space has a clopen basis and is Hausdorff,
Tychonoff, locally compact, separable, and first-countable; it is pseudocompact
exactly when the family is maximal. Every infinite almost-disjoint family has
a Ψ-space that is not countably compact. An infinite maximal almost-disjoint
family on `naturals`, and hence the classical counterexample, is
constructed from an explicit disjoint seed and Zorn's lemma rather than
postulated.

## Deliberate deferrals

The following are genuine downstream developments rather than gaps in active
theorems:

- Euclidean division, divisibility, and gcd theory for the surreal integers; and
- a Cayley--Dickson development realized as concrete instances of the native
  algebra hierarchy.

These topics should be added by definitions and checked proofs, not by local
axioms or placeholder theorems. Public symbol meanings and ontological
kinds are recorded in [`NOTATION.md`](NOTATION.md).
