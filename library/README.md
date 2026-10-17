# Reading and extending the Felix library

The Felix library develops formal mathematics from its set-theoretic
foundation. Files follow their mathematical dependencies, with supporting
lemmas in separate modules where useful. Support modules are checked parts
of the library and can be cited like any other module.

## Entry points

- [`prelude.tex`](prelude.tex) is the fixed foundation packaged with Felix.
  It presents higher-order Tarski–Grothendieck set theory and derives the
  natural numbers.
- [`everything.tex`](everything.tex) is the root for the rest of the library.
  Verifying it also loads the prelude automatically.
- [`status.md`](status.md) records what has actually been constructed and
  proved, the foundations used, and work still to be done.
- [`STYLE.md`](STYLE.md) gives the semantic and source-writing rules for new
  material.
- [`NOTATION.md`](NOTATION.md) lists the public notation and the kind of
  object denoted by each symbol.
- [Structures](../docs/structures.md) explains structure declarations,
  aggregates, parameters, instances, exactness, and reducts.
- [Notions](../docs/notions.md) explains how to declare and use notions,
  adjectives, and notion theorems.

The library contains no ordinary source axioms or explicit proof gaps
(`Omitted.`).

## The mathematical route

The main development can be read in the following order.

1. **Sets, relations, and functions.** [`set.tex`](set.tex),
   [`relation.tex`](relation.tex), and [`function.tex`](function.tex) provide
   ordinary set-coded mathematics. The `set/` directory develops products,
   powersets, finite sets and sequences, exact finite interleaving, choice,
   filters, almost-disjoint families and their Zorn-maximal
   extensions, and constructions of set-coded graphs from logical operations.
   The latter include operations without a prescribed codomain and binary
   operations with different input domains.

   [`set/function-power.tex`](set/function-power.tex) specializes the dependent
   product graphs to ordinary function spaces, with coordinate evaluation,
   contravariant reindexing, composition, diagonal maps, and bijective inverse laws.
   [Coordinate restriction and insertion](set/function-coordinate.tex) identify
   the function space on the remaining indices with an evaluation fibre; fixed-value
   insertion is not an inverse to deletion on the whole larger function space.
   [Splitting function powers](set/function-split.tex) identifies disjoint
   coordinate blocks with a Cartesian product. The
   [finite split and join maps](set/finite-function-split.tex) reindex the
   second block by natural translation, include empty blocks, and
   [commute with Cartesian reassociation](set/finite-function-coherence.tex).
   [`set/partial-map.tex`](set/partial-map.tex) gives natural-domain
   composition and restriction laws for ordinary graphs, without requiring
   the whole intermediate range to lie in the next domain.
   Ordinary and dependent supports have restriction, finite-fibre
   reindexing, point-mass, and extension-by-zero laws. Bijective
   precomposition induces explicit mutually inverse bijections of dependent
   finite-support spaces. Arbitrary precomposition need not preserve finite
   support.

   [`relation/quotient-lift.tex`](relation/quotient-lift.tex) provides the
   quotient projection and representative-free unary and heterogeneous binary
   descent of compatible set-coded graphs, with logical-operation corollaries.
   Unary descent preserves the range of any relation supported on the source;
   typed compatible descent is surjective exactly when the original map is.
   The relation layer also develops carrier-aware transitive closures,
   Noetherianity, joinability, confluence, irreducibility, normal forms, and
   Newman's lemma. [`reduction.tex`](reduction.tex) packages this generic
   theory as abstract reduction systems; the relation-level theorems can also
   be used directly.
2. **Orders and recursion.** The `order/`, `relation/`, and `recursion/`
   directories develop well-founded and transfinite reasoning, maximal
   chains, Zorn's lemma, well-ordering, order types, and Hartogs' theorem.
   [`ordinal.tex`](ordinal.tex) develops von Neumann ordinals. Well-founded
   and ordinal recursion construct unique set-coded graphs without a
   prescribed range bound. Related modules give relation and scalar forms,
   compatibility between initial segments, and growing-record examples.
   These constructions use Felix's higher-order foundation; bounded
   recursion is also available. Natural subtraction is the unique additive
   difference on ordered natural inputs. Natural binomial coefficients are
   obtained by recursion on finite Pascal rows, with a zero value outside each
   row; Pascal's identity, its weighted form, and prime divisibility of the
   interior coefficients are proved without factorials.

3. **Surreal numbers.** The early `surreal/` modules construct sign sequences,
   birthdays, cuts, negation, addition, and multiplication. The long
   arithmetic modules keep each nested recursion or induction argument in one
   file, with subsections to guide the reader.
4. **Integers and reals inside the surreals.** The embedding and integer
   chapters identify canonical ordinal and signed-natural values. The real
   chapters define `\reals` as a set of surreal values, prove its field and
   completeness laws, and package the resulting exact ordered field and
   metric space.
5. **Cardinals.** [`cardinal.tex`](cardinal.tex) compares cardinalities by
   injections. The `cardinal/` chapters construct initial-ordinal
   representatives, identify comparison with ordinal inclusion, and develop
   sum, product, exponentiation, finite cardinality, and countability.
   [`cardinal/normal-map.tex`](cardinal/normal-map.tex) gives the reusable
   normal-map hierarchy; the separate normal-sequence chapter constructs the
   stronger index-dominating sequence used for Silver's theorem.

   The combinatorics modules develop fixed-cardinality subset families,
   pair homogeneity, and ordinal pair-arrow relations independently of graph
   theory. [`combinatorics/pair-colouring-graph.tex`](combinatorics/pair-colouring-graph.tex)
   constructs the simple graph of one colour from a pair colouring.
   The Erdős--Dushnik--Miller chapters first prove the
   arbitrary-carrier graph theorem by its large-neighbourhood and
   regular/singular small-degree branches, then use that bridge to derive the
   complementary graph form and the partition relation
   `kappa -> (kappa, omega)^2`, with order types rather than only
   cardinalities in the partition theorem.

   The adjacent [`stationary/all.tex`](stationary/all.tex) aggregate develops
   clubs and stationary sets with explicit ambient ordinals, including club
   limit points, restriction at limit points, local-to-global stationarity,
   canonical least club successors, and the least stationary value and fibre
   supplied by Fodor's lemma. It also develops indexed stationary
   subpartitions, bijective reindexing, exact completion to partitions, and
   canonical lower and upper endpoints for locally avoiding club sequences.
   Its Solovay chapter proves that every stationary subset of an uncountable
   regular cardinal splits into exactly that many pairwise-disjoint
   stationary sets.

   [`silver/theorem.tex`](silver/theorem.tex) proves Silver's theorem in its
   stationary form, with the usual form as a corollary.

6. **Abstract structures.** The `algebra/` modules define magmas, groups,
   rings, ordered fields, modules, and vector spaces. Magma and monoid
   homomorphisms, embeddings, surjections, and isomorphisms use ordinary
   set-coded graphs with both endpoint structures explicit.
   Pointwise multiplication of carrier subsets defines the exact powerset
   magma, which is associative when the original magma is a semigroup.
   For a monoid, the singleton unit gives an exact powerset monoid; its
   monoid powers are the pointwise subset powers.
   Left and right monoid divisibility are kept explicit in the
   noncommutative setting, with their common commutative specialization
   derived from the left and right forms.
   Positive semigroup powers start at exponent one and satisfy the
   commuting-product law. Natural powers are defined for monoids and agree
   with positive powers away from zero. Groups and rings use the same
   construction. In a ring, pointwise products also admit their additive
   spans. These form an exact semigroup
   on carrier subsets, whose positive powers are additive subgroup carriers
   from exponent two onward and are descending under the explicit
   square-contraction hypothesis.
   The invertible elements of any monoid left- and right-divide every carrier
   element and form an exact group whose inverse operation is the graph of the
   unique two-sided inverse.
   Ring divisibility uses the same left and right monoid definitions; the
   unqualified phrase is reserved for commutative rings, and natural-number
   divisibility transports through the canonical natural elements on both
   sides. The binomial theorem evaluates the Pascal-defined finite expansion
   in any commutative ring, using the exact additive reduct and finite sums.

   Finite folds in commutative monoids are defined without choosing an
   enumeration. Their laws cover the elementary equations, bijective
   reindexing, disjoint unions, homomorphism preservation, deletion of
   neutral terms, successor shifts with a neutral initial value, and finite
   Fubini; finite products and sums use this same construction.
   Dependent products share set-coded graphs for coordinatewise
   operations, projections, universal mediators, and contravariant
   reindexing. Algebraic product records use these same graphs.
   Indexed monoid products provide their homomorphic projections, unique
   universal mediators, and reindexing calculus. Their binary form is the
   literal indexed product over the canonical two-coordinate family.
   Indexed group products add coordinatewise inversion to the product monoid
   and expose the corresponding projection, mediator, and reindexing laws.
   Indexed module products and direct sums reuse those exact group structures.
   Products have linear projections and universal mediators under arbitrary
   precomposition. Direct sums have linear point-mass inclusions and universal
   finite-support assembly maps. Reindexing requires finite fibres, and
   finite direct sums equal their products.

   The free module on `I` is the direct sum of the constant family
   of left regular modules. Its carrier is the usual finitely supported
   function space, its canonical basis vectors are point masses, and every
   typed family of target vectors extends uniquely to a linear map by the
   direct-sum construction. Empty, singleton, and bijectively reindexed index
   sets have explicit canonical laws.
   An indexed family spans, is linearly independent, or forms a basis exactly
   when its linear-combination map is respectively surjective, injective, or
   an isomorphism. These phrases require the appropriate ring, module, and
   family typing. Over the trivial ring every well-typed family,
   over every index set, forms a basis because both relevant module carriers
   are singletons. The range of the linear-combination map is
   exactly the closure-theoretic span; bases have unique free-module
   coordinates and determine linear maps by their values. All three notions
   are invariant under bijective reindexing through the canonical free-module
   reindexing isomorphism.

   Quotient modules use the additive quotient group and the same canonical
   projection. Scalar multiplication is defined on classes without choosing
   representatives; the projection is a linear surjection with the specified
   submodule as its exact kernel.
   The module first isomorphism theorem uses the additive
   `firstIsomorphismMap` to identify the kernel quotient with the induced
   image module, proving that it also preserves scalar multiplication.
   The second theorem restricts the canonical `(N+P)/P` projection to `N`,
   proves its kernel is `N inter P` and that it is surjective, and again uses
   the existing first-isomorphism graph. Its class equation and projection
   factorization are explicit.
   For nested submodules `N subseteq P`, the third theorem descends the
   projection modulo `P` through the quotient by `N`. Its kernel is the image
   of `P` in `M/N`, so the same first-isomorphism graph gives the canonical
   exact module isomorphism `(M/N)/(P/N) ~= M/P`, with representative-free
   class and factorization equations.
   Image and preimage under the quotient projection are inverse,
   inclusion-preserving bijections between submodules of `M` containing `N`
   and submodules of `M/N`. Restricting the projection to a corresponding
   submodule is a module surjection with kernel `N`, and its unchanged
   first-isomorphism graph identifies the exact induced quotient with the
   exact induced image.

   Left modules expose a canonical exact additive-group reduct, so their
   zero, negation, subtraction, natural-scalar, and finite-sum laws reuse the
   generic group and monoid interfaces.  The canonical zero module is an
   exact one-element structure on the fixed carrier `\{\emptyset\}`.
   Right modules are guarded left modules over opposite rings; their public
   scalar notation reverses the displayed arguments of the same action.
   The left regular module uses the ring's exact additive group and acts by
   ring multiplication. The right regular module is the same
   construction over the opposite ring; both additive reducts are exactly
   `AdditiveGroup(R)`.

   Left and right ideals are submodules of these regular modules, and
   two-sided ideals require both actions. The unqualified ideal notion means a
   two-sided ideal over any ring; in a commutative ring it is equivalent to
   either one-sided form. The chapters cover zero and unit ideals,
   intersections, the properness criterion, generated and principal ideals,
   exact induced additive groups, and two-sided kernels of ring
   homomorphisms. Generated ideals are bounded closure hulls for the
   chosen sidedness, with the unqualified hull being two-sided. Principal
   ideals have zero, one, and unit-invariance laws in every ring; over a
   commutative ring they are exactly the multiples of their generator, with
   the corresponding divisibility and natural-power containment laws.
   Throughout the library, a subring of `R` contains the ambient unit `1_R`.
   Scalars annihilating a module subset form a left ideal;
   they form a two-sided ideal when that subset is a submodule.
   For a subring `A` and a two-sided ideal `I`, `A+I` is defined by ambient
   ring addition. It is the least subring containing both, `I` is two-sided
   in the induced ring on `A+I`, and `A\inter I` is two-sided in the induced
   ring on `A`.

   Congruence modulo an ideal is the additive coset relation, with
   the equivalent `-x+y in I` and `x-y in I` views and the expected operation
   compatibility. Quotient rings use the additive quotient group and the
   same canonical projection. Multiplication is defined on classes without
   selected representatives, the quotient unit is the class of `1`, and the
   projection is a ring surjection with kernel exactly the given two-sided
   ideal. The quotient is trivial exactly when the ideal contains `1`.
   Every ring homomorphism descends uniquely through any two-sided ideal
   contained in its kernel. The resulting graph is the universal quotient
   lift of the additive reduct, with the same range, kernel, injectivity,
   and surjectivity laws.

   The binomial theorem also gives the Freshman's dream modulo every ideal
   containing the natural ring element determined by a prime. If taking
   prime powers carries a source ideal `I` into a target ideal `J`, the graph
   `x |-> q_J(x^p)` descends to a canonical ring homomorphism `R/I -> R/J`.
   Its injectivity is equivalent to reflection of ideal congruence, and its
   surjectivity says exactly that every target residue class contains a
   `p`th power. For principal ideals `(a)` and `(a^p)`, the single condition
   that `a^p` divides the natural ring element `p_R` supplies the construction
   and the corresponding specialized criteria.

   The ring first isomorphism theorem uses the additive
   `firstIsomorphismMap` unchanged. It is the ring quotient lift at
   the kernel, corestricted to the actual image ring. Its quotient-class
   equation and factorization through the canonical projection are explicit.
   The second theorem restricts the canonical projection on the induced ring
   `A+I` to the induced ring on `A`, proving the exact isomorphism
   `A/(A\inter I) ~= (A+I)/I`. A second canonical first-isomorphism graph
   identifies the target with the exact induced subring on the image of `A`
   in `R/I`.
   For two-sided ideals `I subseteq J`, the third theorem descends the
   projection to `R/J` through `R/I` and identifies `(R/I)/(J/I)` with `R/J`,
   with both class application and factorization equations stated explicitly.
   Image and preimage under the quotient projection also give mutually inverse,
   inclusion-preserving bijections between ideals of `R` containing `I` and
   ideals of `R/I`.

   Submodules are carrier subsets closed under the additive-group operations
   and scalar multiplication. Their induced modules use the induced additive
   group and restricted scalar graph; a separate substructure predicate
   expresses the same requirements for richer records.
   Contained submodules transfer to an induced ambient module, and elements of
   a binary submodule sum have the usual exact `n+p` characterization.
   Linear maps are additive-group homomorphisms with scalar compatibility;
   their endpoint-change, inverse, and hom-set laws use the corresponding
   group constructions.
   The group-homomorphism theorems identify a subgroup with the
   preimage of its image exactly when it contains the kernel. For surjective
   maps, the image of a target subgroup's preimage is that subgroup.
   Kernels and images are source-indexed additive-group carriers; the
   linear-map predicate specifies the scalar ring and full module endpoints.
   Both carriers have canonical induced modules. Inclusion is an embedding,
   and corestriction to the image is a surjection.
   Module spans are bounded closure hulls among submodule carriers. Submodule
   sums are their binary joins, and linear maps carry spans onto spans and are
   determined by their values on a spanning set.

   [`algebra/group/maps.tex`](algebra/group/maps.tex) defines
   translation, inversion, and conjugation graphs independently of their
   topological applications. [`algebra/group/subgroup.tex`](algebra/group/subgroup.tex)
   keeps subgroup carriers distinct from their canonical exact induced groups,
   and compares richer subgroup structures through group reducts. Generated
   subgroups are bounded intersections in a fixed ambient group and expose
   both membership and least-subgroup characterizations; they commute with
   images under arbitrary homomorphisms and determine homomorphisms by their
   values on generators. Characteristic subgroups, normalizers, and normal
   closure are also defined as carriers. Normal closure is identified with
   the subgroup generated by the bounded union of all conjugates. Natural
   powers are defined by iteration, and cyclic subgroups are generated
   by singletons, without importing integers or surreals. The
   homomorphism and isomorphism modules keep raw graphs separate from their
   explicit endpoints and provide identity, composition, restriction,
   corestriction, image, source-indexed kernel, converse, and chosen-map
   subgroup transport laws. Monoid and group actions also use graphs, with
   orbits bounded by the acted-on set. Group-action stabilizers are subgroups.
   Conjugation supplies the canonical group action, normal subgroup and
   induced-image theorems, trace-totalized centralizers, centres, centreless
   groups, and chosen-map transport of centres. Centralizers are antitone,
   commute with generated subgroups, have an exact induced-subgroup formula,
   and transport along homomorphisms and chosen isomorphisms. Internal products of subgroup
   carriers are developed separately from categorical group products: one
   normal factor makes the product a subgroup, while two normal factors make
   it normal. The exact automorphism group uses graph composition and
   converse, and transports along a chosen group isomorphism by graph
   conjugation. Its canonical inner map has kernel the centre and is an
   embedding exactly for centreless groups; the inner carrier is normal and
   has trivial centralizer in the automorphism group when the original group
   is centreless. Thus automorphism groups of centreless groups are
   centreless, and completeness is characterized by the inner map being an
   isomorphism.

   The coset and quotient chapters then construct quotient groups by
   descent without choosing representatives. Every homomorphism whose kernel
   contains the normal subgroup has a universal quotient lift, with range,
   kernel, injectivity, and surjectivity laws. The first isomorphism theorem is
   its specialization to the kernel and the exact induced group on the actual
   image carrier. The same canonical
   first-isomorphism graph gives the second isomorphism theorem in both its
   quotient and induced-image forms. Representative-free descent gives the
   third isomorphism theorem as the lift of the larger quotient projection,
   and image and preimage under a quotient
   projection give the inclusion-preserving subgroup correspondence, with
   normality preserved and reflected. Chosen group isomorphisms likewise give
   inverse bijections between normal-subgroup carriers. Element commutators
   use the fixed convention `[x,y]=x^{-1}y^{-1}xy`, with explicit product
   identities. Relative commutators `[A,B]_G` are subgroup carriers generated
   from the carrier traces of arbitrary displayed subsets. They are symmetric,
   functorial, covariant under conjugation, and trivial exactly when the
   corresponding traces centralize one another. For subgroup inputs they are
   controlled by normalizers and normal in the subgroup generated by
   `A union B`. The subgroup generated by all element commutators is
   characteristic and is the least normal subgroup with commutative quotient.
   The resulting exact commutative quotient is the abelianization,
   with its representative-free universal factorization into every
   commutative target. External semidirect products use ordinary pair
   carriers and an explicit homomorphism into the automorphism group. Their
   canonical left and right inclusions and projection give the normal
   kernel, splitting, and conjugation action. For the trivial action, a
   canonical isomorphism to the dependent binary group product converts pairs
   into two-coordinate functions. Internally,
   complementary subgroup carriers `N` and `H`, with `N` normal, recover the
   ambient group through the conjugation action and the multiplication
   isomorphism `(n,h) |-> n*h`. Subgroup index is the canonical cardinal of
   the existing left-coset quotient; left cosets are equinumerous with the
   subgroup, giving the cardinal product formula without a normality
   hypothesis. Finite partition counting gives a separate proof of Lagrange's
   theorem, its cyclic-subgroup instance, and the theorem that a group of
   prime natural cardinality is cyclic. Group-action orbits partition
   their acted-on set, equivariant maps carry orbits onto orbits, and the
   representative-free quotient descent from stabilizer cosets gives the
   exact orbit--stabilizer bijection, from which both the finite-cardinality
   equivalence and the separate cardinal equation follow. The permutation
   group of a set is the exact group of its self-bijection graphs under
   composition, with identity graph and graph converse. Every group action
   induces an exact homomorphism into this group; its kernel is the pointwise
   action kernel, and the left regular action gives Cayley's embedding theorem.
   These elementary structural chapters are also available through the
   lightweight `algebra/group/foundations.tex` aggregate.

   Directed group systems use inhabited quasiordered index structures and
   set-coded families of groups and bonding maps. Direct limits are
   characterized by their universal property and constructed from tagged
   elements modulo eventual agreement. The component images form a directed
   family of subgroups covering the limit. The chapters cover restriction of
   index structures and transport along compatible component isomorphisms.
   Limits with injective bonding maps preserve centrelessness.

   Automorphism towers start from a base group, take automorphism groups at
   successor stages, and direct limits at nonzero limit stages. Transfinite
   recursion constructs a canonical segment of every ordinal length, together
   with its bonding homomorphisms. Smaller segments are restrictions of larger
   ones. Canonical segments over the same group and ordinal length are equal.
   For a centreless base, every stage remains centreless and every bonding
   map is an embedding. Fixed-ambient segment images are
   subgroup carriers nested inside any later displayed stage. A successor
   image is normal in the exact induced group on the following image. For a
   canonical centreless segment, an adjacent earlier image also has trivial
   centralizer inside that induced successor-image group at every later
   displayed stage. At a canonical limit the set-coded image family is
   inhabited, directed, and covers the whole stage carrier. Coherent
   isomorphisms between segments are set-coded families that commute with
   the bonding maps. They support identity, composition, converse,
   extensionality, and passage to direct-system isomorphisms. Recursive
   transport from a chosen base isomorphism is canonical at successors and
   semantic limits, commutes with every bond, and is unique under those
   recursive equations. It also
   compares any coherent segment with the canonical segment. Termination is
   expressed only at a displayed successor bond, equivalently by completeness
   of the displayed stage; no set or ordinal of all tower stages is postulated.
   [`algebra/group/all.tex`](algebra/group/all.tex) imports these group chapters.

   The `order/` directory develops quasiorders and orders through
   order morphisms, embeddings, adjunctions, semilattices, lattices, bounded
   and distributive lattices, and lattice morphisms and isomorphisms.  Its
   finite layer supplies canonical extrema, finite suprema and infima, and
   finite join-irreducible decomposition.  Set-family lattices and downset
   lattices provide the concrete representation target.  The finite Birkhoff
   modules prove the order adjunction and retract, identify the associated
   closure and fixed points, characterize distributivity by surjectivity, and
   establish the bounded finite distributive representation theorem.  A
   separate companion constructs the canonical bounded expansion of an
   inhabited finite distributive lattice and transfers the representation to
   its original lattice reduct; another records the resulting cardinality
   equality and powerset bound.  The Boolean-algebra chapter develops
   powerset algebras, subalgebras, homomorphisms, proper lattice filters, and
   Boolean ultrafilters, then proves Stone's representation theorem as an
   isomorphism onto a field of sets via the Stone map.

7. **Topology.** The `topology/` directory proceeds from preclosure,
   topological, metric, and uniform structures through induced topologies,
   discrete spaces, countability axioms, compactness, completeness, separation,
   normality, and topological groups.  The Isbell--Mrówka chapter constructs
   Ψ-spaces from almost-disjoint families and proves their structural,
   countable-compactness, and pseudocompactness theorems.
   The compactness chapter follows open covers, closed finite-intersection
   families, and ultrafilter convergence in that order.  Fields of sets
   generate clopen bases used to prove compactness. The Stone-space chapter
   proves that every Boolean algebra is isomorphic, through its original
   Stone map, to the Boolean algebra of clopen subsets of a compact Hausdorff
   space. The construction includes the one-element algebra and its empty
   Stone space.

   At every carrier point the ordinary neighbourhood family is a proper
   filter.  Filter convergence is the primary interface; local bases are its
   open bases, and topological sequence convergence applies it to the generic
   sequence-tail filter.  The topology induced by a uniformity is Hausdorff
   exactly when the uniformity is separated, including for the empty carrier.
   Uniform convergence is defined through this topology. Filter, sequence,
   and Cauchy predicates include their uniform-space and typing requirements;
   the usual entourage formulas are proved as equivalent characterizations.
   Lifting an entourage pointwise over a specified domain generates the
   uniform space of maps, so uniform convergence and uniform Cauchyness of
   map sequences are ordinary sequence notions in that space. The construction
   also covers empty domains and empty target carriers. Proper filter bases
   have direct entourage criteria for convergence and Cauchyness. These give
   the usual basis characterization of complete uniform spaces. The
   neutral-element neighbourhoods of a topological group generate its
   canonical left and right uniform spaces. Both recover the stored topology,
   and they agree for commutative groups.

   Topological rings use this additive uniformity for completeness. In the
   nonarchimedean setting, boundedness theorems construct the exact ring of
   power-bounded elements, while positive additively generated powers lead
   to f-adic and Tate rings.  On the power-bounded ring, the principal
   quotient Frobenius has its expected representative equation and is
   automatically injective for a pseudouniformizer; consequently it is an
   isomorphism exactly when it is surjective.  A perfectoid Tate ring at an
   explicit prime is additively complete and uniform and admits a
   pseudouniformizer for which this Frobenius is an isomorphism.  The
   prime is a parameter; the pseudouniformizer need only exist.
   Perfectoid spaces are not yet developed.

You can also start with a theorem of interest and follow its module's imports.

## Main and support modules

A main module introduces a mathematical subject or construction. A support
module develops an argument needed by later chapters. Examples include
constructing set-coded graphs from logical functions, finite-intersection
families, relative complements of families, generated well-orders, and finite
sequences and folds.

The finite-filter module proves closure under inhabited finite intersections
before filter extension introduces order theory and Zorn's lemma.
Filter bases generate filters by upward closure and are compared by
refinement. Sequence filters use natural tails as an antitone basis and are
unchanged by deleting finitely many initial terms. These constructions are
independent of topology.

The topology chapters characterize local bases through the neighbourhood
filter, give choice-free open refinements and homeomorphism transport, and
derive finite-shift invariance of convergence from the set-level tail-filter
equality.

Uniform convergence is developed independently of metrics and real arithmetic.
Separate modules give the metric comparisons and the countable-base converse
from sequential completeness to completeness, including its use of Choice.
`uniform-convergence.tex` and `uniform-completeness.tex` import the respective
general and metric results. Topological-group uniformities use the general
filter and uniform-space theory, together with translation and inversion
homeomorphisms.

Constructing a set-coded graph from a logical operation uses Replacement,
through Felix's higher-order (TH0) foundation interface.

Every `.tex` source below `library/` is either the implicit prelude or imported,
directly or indirectly, by `everything.tex`. Files under `experimental/` are
outside this guarantee until reviewed and added to the library's imports.

The Urysohn support modules first develop entry ranks for nested finite
sequences, then refine finite chains of open sets with successively nested
closures. The normality module proves the closed-inside-open shrinking
criterion and the `T_4` hierarchy law, keeping normality distinct from `T_1`.
Choice is used to obtain one set-coded normal shrinker.
Each refinement doubles the chain's step count. Entry ranks give finite open
covers on which the later real-valued step maps vary by at most one dyadic
mesh unit. At each refinement, a point's value either stays unchanged or
increases by one new mesh unit. The chain and cover constructions are
independent of real arithmetic.

The general topology modules also provide subspaces formed by intersecting
with the carrier, continuous inclusion and restriction/corestriction laws,
and a pointwise local criterion for continuity.

[Topological powers](topology/power.tex) use constant-family indexed products
with exact function-space carriers. Their coordinatewise continuity criterion
makes arbitrary reindexing and diagonals continuous, and bijective reindexing
a homeomorphism. [Coordinate subspaces](topology/power-coordinate.tex) identify
fixed-coordinate fibres by insertion, with deletion as the inverse. These maps
also work for arbitrary index sets and include the singleton-coordinate case.
[Real coordinate spaces](topology/real-coordinate-space.tex) specialize this
topology without choosing a norm; the empty power agrees with the existing
zero-coordinate model. [Disjoint-block splitting](topology/power-split.tex)
is a homeomorphism for arbitrary index sets. Its
[finite specialization](topology/finite-power-split.tex) identifies the power
indexed by `m+n` with the product of the powers indexed by `m` and `n`, using
explicit mutually inverse maps, including zero-dimensional product units.
[Power properties](topology/power-properties.tex) specialize Hausdorff products
and finite compact products; the empty power is compact and connected.
[Local compactness on open neighbourhoods](topology/local-compactness-local.tex)
can be checked on one open neighbourhood of each point, without separation
hypotheses. Compactness of a subset agrees in a subspace and its ambient space.
[Compact neighbourhoods in Hausdorff spaces](topology/compact-neighbourhood.tex)
can be shrunk inside any prescribed open neighbourhood. The proof separates
a point from a compact subset by a finite subcover. Consequently, locally
compact Hausdorff spaces are regular, and their open subspaces are locally
compact.
[Local compactness of finite powers](topology/power-local-compactness.tex)
uses compact neighbourhoods, binary products, and finite-set induction.
The [real specialization](topology/real-coordinate-properties.tex) is Hausdorff
for every index set and locally compact for every finite index set.
[Second countability of finite powers](topology/power-countability.tex) follows
from countable [rectangle bases](topology/countability-product.tex),
[homeomorphism invariance](topology/countability-continuity.tex), and the same
finite-set induction. Second countability also passes to
[subspaces](topology/countability-subspace.tex) and open continuous surjective
images; every finite topological space is second-countable. The
[real line's countable basis](topology/real-countability.tex) consists of open
intervals with finite-birthday surreal endpoints. Consequently every finite
real coordinate space is second-countable, including dimension zero.
[Straight real paths](topology/real-path.tex) and
[paths in order-convex real subsets](topology/real-interval-path.tex) prove
path connectedness and local path connectedness of the real line.
Both properties pass to finite powers through
[products of paths](topology/path-product.tex),
[path-connected powers](topology/power-path.tex), and
[locally path-connected powers](topology/power-local-path.tex).
Thus every finite real coordinate space has both properties, including
dimension zero. These coordinate topologies and homeomorphisms use no norms
or derivatives; pointwise algebra and norms remain to be developed.

[Topological manifolds](topology/manifold.tex) separate local Euclidean
structure from Hausdorffness and second countability, without storing an atlas.
Euclidean spaces and empty spaces provide the first examples;
[open subspaces](topology/manifold-open.tex),
[homeomorphic transport](topology/manifold-transport.tex), and
[products](topology/manifold-product.tex) preserve the manifold predicates.
[Basic properties](topology/manifold-properties.tex) include local compactness
and local path connectedness for every locally Euclidean space, and regularity
and first countability for topological manifolds. Product dimensions use the
explicit finite-coordinate join homeomorphism.
[Connected components](topology/connected-component.tex) are bounded unions
of connected subsets through a point. They are connected, contain every
connected subset through that point, and agree when based at another member.
They are open in locally connected spaces, so
[components of manifolds](topology/manifold-component.tex) inherit the same
dimension through their subspace topologies. The off-carrier component is
empty; no nonemptiness convention is imposed on the manifold theorem.
Local Euclidean structure can be checked on open neighbourhoods using
the [open-subspace interface](topology/manifold-open.tex).
The canonical [coproduct injections](topology/indexed-coproduct-open.tex)
are open embeddings, identifying each summand with its open image.

[Continuous partial maps](topology/partial-continuity.tex) have open domains,
natural-domain composition, and source locality, without an injectivity or
open-image requirement. [Local map calculi](topology/local-map-calculus.tex)
package admissibility between a set of models; the
[continuous calculus](topology/continuous-calculus.tex) is a set-bounded
instance with one- and two-model interfaces.
[Topological embeddings](topology/embedding.tex)
identify spaces with subspaces of their targets; their restriction,
composition, and open-map criteria retain explicit ambient endpoints.
[Open partial homeomorphisms](topology/partial-homeomorphism.tex) identify
open subspaces by ordinary graphs. Converse, open restriction, natural-domain
composition, and the empty-domain laws use the same graph calculus.

[Coordinate pseudogroups](topology/coordinate-pseudogroup.tex) specify allowable
changes on one model, with source locality for globally bijective candidates.
The [full pseudogroup](topology/full-pseudogroup.tex) contains every open partial
homeomorphism on its model.
The [pseudogroup associated to a local calculus](topology/calculus-pseudogroup.tex)
consists of maps admissible in both directions. Its locality proof transports
source neighbourhoods through the candidate homeomorphism to check the inverse.
Inclusion of calculi induces inclusion of these pseudogroups; the continuous
calculus gives the full pseudogroup itself.
Calculus compatibility also applies to restrictive pseudogroups: it descends
to subpseudogroups and makes their inverse changes admissible as well.
[Fixed-model intersections](topology/pseudogroup-intersection.tex) give greatest
lower bounds for set-sized families, with the full pseudogroup as the empty
intersection.

[Coordinate atlases](topology/coordinate-atlas.tex) use local transition
factorization through a covering family to construct maximal atlases.
Cross-compatible presentations generate the same maximal atlas; the empty
presentation on an empty space generates the singleton containing the empty chart.
[Homeomorphic transport](topology/coordinate-transport.tex) composes charts
with the inverse homeomorphism, leaving every transition graph unchanged.
It preserves maximal atlases and commutes with maximalization; the underlying
set operation has identity, composition, and inverse laws.

[Open restriction of atlases](topology/coordinate-atlas-restriction.tex) sends
each chart to its restricted graph. Restriction commutes with maximalization;
for a maximal atlas it retains precisely the charts whose domains lie in the
open subset. Thus the restricted maximal atlas is independent of its presentation.
[Coordinates on open subspaces](topology/coordinate-restriction.tex) package
this restricted maximal atlas as an exact relative structure. The chart
membership criterion uses only ambient atlas membership and domain containment.
Any presenting atlas gives the same restriction: generating coordinates from
its restricted charts recovers the same relative record.
Nested restriction agrees with direct restriction, full restriction recovers
an exact relative datum, and the empty restriction has just the empty chart.
Equipping preserves the restricted presentation and has exactly the subspace
as its topological reduct. The subspace inclusion is coordinate-admissible
whenever the pseudogroup is compatible with the chosen calculus.

[Transported relative coordinates](topology/coordinate-homeomorphism.tex)
package the transported maximal atlas and can be computed from any presenting
atlas. Transport composes and commutes with open restriction; inverse transport
recovers an exact relative datum. The homeomorphism and its inverse are
coordinate-admissible for every compatible calculus, since their expressions
in transported charts are identities. A bare bijection first supplies its
target topology through the existing initial topology of its inverse.

[Pseudogroup weakening](topology/coordinate-weakening.tex) enlarges a relative
atlas by maximalizing under a larger pseudogroup on the same model. Any
original presentation computes the result. Successive weakening agrees with
one-step weakening, while identity weakening recovers an exact relative datum.
Weakening commutes with equipping/extraction, open restriction, and homeomorphic
transport. Admissible maps survive weakening when both larger endpoint
pseudogroups are compatible with the chosen calculus.

[Relative and equipped coordinate structures](topology/coordinate-structure.tex)
share one atlas field. Constructions generate a relative structure,
equip a topological space, and extract its coordinate datum. These operations
satisfy exact round-trip laws; cross-compatible presentations give equal records.
[Atlas presentations and point charts](topology/coordinate-atlas-presentation.tex)
describe generation, membership, and coverage without unfolding maximal atlases.
The same `ChartsAt` operation applies to relative and equipped records.

[Coordinate expressions](topology/coordinate-expression.tex) retain exact
domains under source restriction and reconstruct the original restricted map.
Continuity follows from continuity in coordinates without requiring an open
image for the map itself.
[Coordinate-admissible maps](topology/coordinate-map.tex) have open exact domains
and an admissible expression near each source point. Their continuity, open
restriction, source locality, identity, and natural-domain composition laws
follow from this definition, with the endpoint pseudogroups and calculus
specified. At a domain point, any source chart and any target chart through
its image admit an admissible expression after shrinking the source
neighbourhood. Admissibility can be checked using any presenting atlases,
under the same open-domain and endpoint-compatibility hypotheses. Calculus
inclusion preserves map admissibility and endpoint compatibility without
changing the equipped records or their pseudogroups. The relative/equipped
criterion uses the same local expressions on explicitly named ambient
spaces; equipping also preserves presentations without identifying richer
spaces with their reducts.
For the continuous calculus, coordinate admissibility is exactly continuity,
provided the endpoint pseudogroup models belong to the chosen model family;
the map image need not be open.
[Concrete coordinate-map examples](topology/coordinate-map-examples.tex) prove
that the real zero map is admissible between the identity and reflection
presentations, although its exact singleton image is not open. The empty map
is admissible between the same equipped endpoints. Both use the closed
continuous calculus and the full real pseudogroup.

[Spaces from raw charts](topology/coordinate-presentation.tex) connect the
induced topology to these constructions. The theorems describe open sets,
charts, topology, and relative coordinates, and show that the original atlas
presents the generated space. Rebuilding an exact equipped space from a full
pseudogroup presentation recovers that record.
Two raw presentations on the same set and model, using the full pseudogroup,
produce equal equipped spaces exactly when their induced topologies agree.
In particular, cross-compatible raw presentations produce equal records.
[Coordinate examples](topology/coordinate-examples.tex) check this path on two
overlapping real rays versus one real-line chart, the zero-coordinate function
space, and the empty source.

The [positive real pseudogroup](topology/positive-real-pseudogroup.tex) consists
of locally increasing open partial homeomorphisms. Its inverse, restriction,
composition, and locality laws do not require global monotonicity between
disconnected components.
[Reflection](topology/positive-coordinate-examples.tex) is an allowed change
in the full real pseudogroup and is excluded from the positive one. The identity
and reflection singleton presentations are both positive atlases, but generate
different positive coordinate structures. Transport by reflection exchanges
these structures and is admissible in both directions in every compatible
calculus. Weakening either positive structure to the full pseudogroup gives
the same relative structure and the same equipped record.

[Raw coordinate charts](topology/coordinate-chart.tex) do not presume a
source topology. Their transition graphs have exact overlap domains and
ranges; restriction requires an open coordinate image.
[Coordinate topologies](topology/coordinate-topology.tex) are the common
open-image topologies of raw charts. Compatible presentations make their
charts into open partial homeomorphisms, and a chart cover recovers an existing
space's topological reduct. The development includes empty and two-chart covers.
A metric-target specialization uses open balls;
the canonical real metric then supplies named real-line and unit-interval
topologies, each distinct from its carrier.

The open-chain limit module takes the real supremum of the finite-level
values at each point and proves a one-sided dyadic approximation bound.
The rank-cell oscillation theorem gives continuity into the real line; the
same graph is then corestricted to the unit interval. This construction uses
a supplied normal shrinker. The Urysohn theorem module obtains the shrinker
from normality and proves Urysohn's lemma without assuming `T_1` or an
inhabited carrier. It also provides the real-valued companion, the
closed-inside-open bump-function form, and the converse characterization of
normality by continuous separation into the unit interval.

The Tietze chapter continues this construction for continuous real-valued
maps on closed subspaces. For a supplied normal shrinker, successive
quarter-corrections have a deterministic pointwise limit. The normal-space
theorems obtain such a shrinker by Choice. The bounded theorem preserves any
given nonnegative absolute bound, including zero. Closed-interval data have
extensions into the same interval, including the real unit interval.
For unbounded real-valued data, the construction maps into `(-1,1)`, extends
into `[-1,1]`, and moves endpoint values into the interior while fixing the
original closed subspace. Applying the inverse of the initial transformation
then gives the extension. None of these theorems assumes `T_1` or an
inhabited carrier.

## Ontological conventions

Keep these distinctions in mind when reading or writing Felix:

- sets are distinct from logical functions and predicates;
- a set-coded function graph is distinct from a logical function;
- the proper class of all surreals is expressed by a predicate, whereas each
  surreal stage, the surreal integers, and the surreal reals are sets;
- a structure is an extensional set-coded record and is distinct from its
  carrier;
- adjectives such as “compact” require the appropriate structure: for example,
  a topological space. Some raw predicates are also available;
- ordinary set finiteness and structural finiteness are separate adjective
  readings: `finite set` means set finiteness. Import `structure/finite.tex`
  to use `finite group` and similar phrases for finiteness of the carrier; and
- set-level global choice is distinct from typed logical selection.

Concrete structures use aggregate terms. The annotation in
`\structure[SCHEMA]{...}` identifies the fields; it is not stored in the
resulting set. Structure predicates are open: a record with extra fields may
still satisfy a parent schema. “Exact” means that the record has precisely
the schema's fields. Carriers are not assumed inhabited unless this follows
from the structure's fields or laws.

## Adding a chapter

Place a theorem after its prerequisites and before the results that use it.
Add a support file when an argument is needed independently; keep a single
induction together even if it makes the file longer. Ensure that
`everything.tex` imports new modules, directly or indirectly. Keep unfinished
experiments outside `library/`.

Add new public symbols to `NOTATION.md`. Before committing, verify the changed
root and `everything.tex`, run the library quality tests, and confirm that the
summary reports no source axioms or explicit proof gaps.
