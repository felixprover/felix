# Notions and formation checking

Felix uses ordinary predicates as *notions*. A notion may express that a term
is a set, a group, a topological space, compact, or a member of a particular set.
Formation checking uses such predicates to reject expressions whose mathematical
domain has not been established. This is similar to soft types in Mizar and Naproche.
In contrast to Mizar, notions are not assumed to be inhabited.

For example, compactness is declared on its natural domain:

```latex
\begin{definition}\label{is_compact}
    Let $X$ be a topological space.
    $X$ is compact iff for every open cover $C$ of $X$ there exists
        a finite set $D$ such that $D\subseteq C$ and
        $D$ covers $\carrier[X]$.
\end{definition}
```

The header makes being a topological space part of the definition of
compactness. An object outside this domain is not compact. Felix also requires
evidence that `X` is a topological space whenever you write `$X$ is compact`.

In a predicate definition joined by `and`, an earlier clause can establish
the domain needed by a later clause. For example, if `\notionTermValue{X}`
requires `X` to be a notion base, this definition is well formed:

```latex
$X$ is staged iff
    $X$ is a notion base and
    $\notionTermValue{X}=\notionTermValue{X}$.
```

Both clauses remain part of the definition. This left-to-right checking
applies to the outer conjunction: a fact inside `or`, `not`, or another logical
form cannot establish the domain for a clause outside it.

## Set-valued definitions remain total

Headers on named set-valued definitions restrict where you may use the
notation. The defining equation still holds unconditionally. For example:

```latex
\begin{definition}\label{group_hom_set}
    Let $G$ be a group.
    Let $H$ be a group.
    $\groupHomSet{G}{H}=
        \{f\in\funs{\carrier[G]}{\carrier[H]}
            \mid \groupHom{f}{G}{H}\}$.
\end{definition}
```

Writing `\groupHomSet{G}{H}` requires evidence that `G` and `H` are groups.
The term still has a value for every pair of sets. A failed formation check
means that its use in the source lacks the required evidence.

## What counts as direct evidence

A checked atomic assertion supplies notion evidence while it is in scope. This
includes explicit negative atoms such as `$c\notin B$`. Felix
also uses the individual facts in a conjunction. For example,

```latex
Suppose $G$ is a group and $H$ is a group.
```

allows `\groupHomSet{G}{H}` wherever these assumptions are in scope. A condition
in an `if` clause or a bound such as `$x\in X$` similarly supplies evidence
within its body.

A negated compound, disjunction, equivalence, quantified statement, or completed
implication does not by itself supply its component facts. For example,
knowing that `G` or `H` is a group does not establish that either one is a group.
Such a supplied formula can satisfy an identical whole requirement. Identity
preserves symbols, types and binding structure; it disregards bound-variable
names and the weakening needed to refer to the same surrounding binders.

A supplied set universal can also establish an instance, provided its
guards are available. For example, these separately quantified hypotheses
can share evidence:

```latex
Suppose for every $i\in I$ we have $X(i)$ is a topological space.
Suppose for every $j\in I$ we have $X(j)$ is locally Euclidean of dimension $n$.
```

The first hypothesis is instantiated at the second hypothesis's bound `j`,
using its exact membership `j\in I`. The new hypothesis cannot supply its own
domain. Captured parameters such as `X` and `I` remain fixed. Dependent set
binders, successive guards, and conjunctive results are supported. Arguments
can be determined jointly by several premises. Every guard remains a proof
obligation; a universal never supplies an unconditional membership fact.

Instances use the same bounded notion search as classifications. The finite
term support is frozen before search. Partial requests whose written shape
has no possible ground completion in that support are rejected; this check
supplies neither assignments nor evidence and never enlarges the support. Their
proofs retain the complete universal and every guard, then replay universal,
implication, and conjunction elimination. Proved local universals also work
with `by notion`. No universal body becomes an unconditional atomic fact, and
ordinary unregistered theorems remain outside formation search. Marked
classifications can also require a complete universal. Felix can prove such a
requirement under a fresh arbitrary set and its stated guards. It does not
prove a universal by sampling finitely many instances.

Whole-premise matching preserves the ordered set binders and the exact guards
at each binder depth. Adjacent guards may be regrouped or reordered, and a
stronger supplied result conjunction may supply a requested projection.
Replay introduces the requested binders and guards, reconstructs the supplied
premise's exact guards, and projects its result through the kernel. Additional
guards, different bounds or captured terms must be justified exactly. Separate
universals can establish a compound requirement by proving its components
under the same fresh binder and assumptions. Named provider arguments remain
part of matching. Compiler-owned local aliases may normalize those arguments:
the source proof retains each defining equality. An abbreviation argument erased
by expansion supplies no matching parameter. Ordinary equalities do not rewrite
captured universal parameters during matching. Existing transport of an atomic
conclusion remains available as a separate proof step.

Source-call contracts for definitions accept atomic and whole requirements,
including separate `Suppose` headers. Each application instantiates its ordered requirements
under one shared budget and replays their proofs. Supplied-universal matching
also applies to eligible whole goals written with `by notion`. A proved sibling
requirement does not become an assumption for another sibling. Definition result
annotations use the same atomic and whole goal rules.
Construction hypotheses instead condition the proved results of a total
construction; they impose no source-call contract on its set term.

Notions include nouns, adjectives, membership, named verbs, and named
relations. Thus `$X$ has a clopen basis` supplies one fact, and `$X$, $Y$ have a
clopen basis` supplies that fact for each subject. Likewise,

```latex
Let $A,B\subseteq C$.
```

supplies `$A\subseteq C$` and `$B\subseteq C$`. Write separate named relations
when you need notion evidence from a chain; dynamic relations such as
`$x\mathrel{R}y$` do not supply it. Local equalities have a separate use,
described below.

A named prefix predicate also supplies a single notion fact. For example,

```latex
Suppose $\booleanSubalgebra{A}{B}$.
```

can support a classification about `\booleanSubalgebraStructure{B}{A}`.
Establishing the individual conditions in the predicate's definition does not
automatically establish the named predicate for notion checking.

A named predicate supplies every leaf of its definition's outer conjunction.
Atomic leaves retain their usual matching rules. Other leaves, including
existentials and universals, supply their exact whole proposition. For example,
a filter basis supplies the existential meaning of `inhabited`, which can
satisfy the premise of `choice_in`. Supported universal, implication, equivalence, and
conjunction eliminations also apply to derived whole propositions during the
same search. A derived equality remains an exact whole fact; it does not extend
equality transport merely because it was discovered.

## Transparent abbreviations

An abbreviation contributes its expanded body to notion checking. For example,
the abbreviation

```latex
$f$ is a function from $X$ to $Y$ iff $f\in\funs{X}{Y}$.
```

makes the prose and symbolic spellings interchangeable for notion checking
and `by notion`. Both also support inference about function application,
described below.

Conjunctions contribute their individual leaves. Explicit negative atoms retain
their signed argument views. Other expanded formulas use the logical operations
below, including finite witness search for positive existentials. An abbreviation
provides no additional equality transport for a non-literal formula.
Term abbreviations likewise retain the construction of
their expansion: an identity abbreviation returns the argument's own source
occurrence. Named definitions retain their separate notion and provider
identities.

Every argument is checked as written, including an argument the body erases.
The body and its internal formation obligations are checked at declaration;
substitution at a use does not impose those obligations again. Nested bodies
are already expanded in the stored payload. Contextual abbreviations retain
the exact identities of their required fields, so inherited presentations agree
while unrelated overloaded fields cannot substitute for one another.

Expansion has a separate 131,072 work-unit allowance. Nested calls in a
declaration share that declaration's remaining allowance. Each written use
owns its substitution and completed-occurrence sealing; declaration preparation
also bounds the final Core check, identity hashing and payload encoding.
Repeated arguments under binders share their weakened occurrences. Failure
names the written call and the body path where the allowance was exhausted.
Fresh and cached payload admission are bounded and counted once at admission.

## Adjective readings and complete phrases

Ordinary objects and structures have separate adjective readings where the
mathematics requires them. For example, `finite set` selects the ordinary
reading of `finite`, whereas `finite group` selects the structure reading,
which means that the group's carrier is finite. The phrase selects the reading.

A phrase such as `$X$ is finite` is accepted when exactly one reading
is visible. If both ordinary and structure readings are visible, it is
ambiguous. Write a complete phrase, such as `$G$ is a finite group` or
`$\carrier[G]$ is a finite set`.

The carrier reading requires a `onesorted structure`. For a structure without
a carrier, define adjectives using the relevant components explicitly.

Within a complete phrase, the noun or structure can supply the domain needed
by its modifiers. For example:

```latex
Let $G$ be a finite group.
```

Here `group` supplies the domain needed by `finite`. Modifiers are otherwise
checked independently: one modifier cannot establish the domain of another.

In a bounded phrase such as `for every finite set $X\in F$`, the noun and the
positive bound are available when checking the modifiers. A negative bound
such as `$X\notin F$` does not supply membership evidence. The endpoint `F`
must already make sense before `X` is introduced.

A grouped phrase applies to each named object. For example,

```latex
Let $X,Y$ be finite sets such that $X\subseteq Y$.
```

checks `finite set` separately for `X` and `Y`, then checks `$X\subseteq Y$`
using both completed phrases. Later headers and the body may use all three
assumptions.

Modifiers agree with the grammatical number of their phrase: write
`a set that is finite`, `sets that are finite`, `a space that has a clopen
basis`, and `spaces that have a clopen basis`.

## Reusable notion theorems

Use a `classification` to make a theorem available to notion checking. For
example:

```latex
\begin{classification}\label{field_is_ring}
    Let $K$ be a field.
    Then $K$ is a ring.
\end{classification}
```

The classification needs an ordinary proof. Once checked, it lets Felix use a
field wherever a ring is required. Classifications can also combine several
notion premises and can be chained.

A classification may also conclude an exact whole formula, such as an equality,
disjunction or universal. Several atomic premises can jointly determine its
parameters. Parameters occurring inside a whole conclusion's set operands,
including written arguments erased by expansion, are also admitted as finite
inputs. Occurrence does not make an opaque operand invertible. Complete set
operands of the requested conclusion can constrain
the remaining inputs. Every premise must still be proved, including exact
whole premises. Positive compound premises can also determine parameters through
their successful instances. If written argument views do not determine an
assignment, bounded finite discovery supplies an alternative; it grants no
evidence by itself. The resulting whole proof can feed ordinary consumers and supported
eliminations without an intermediate source assertion.

Felix can also derive notion implications from supported clauses in predicate
definitions. For example, a definition beginning

```latex
$\fAdicPresentation{R}{U}{T}$ iff
    $R$ is a commutative topological ring and ...
```

lets the named predicate establish that `R` is a commutative topological ring.
These implications work forwards from the named predicate to its component
facts. They can pass through other named predicates, but do not recover a
predicate merely from its defining conditions.

A classification can also describe the result of a named set-valued
definition. For example:

```latex
\begin{classification}\label{automorphism_group_is_group}
    Let $G$ be a group.
    Then $\automorphismGroup{G}$ is a group.
\end{classification}
```

This lets Felix use `\automorphismGroup{G}` where a group is required, once it
has established that `G` is a group. Such classifications may have several
premises, or none when the result holds unconditionally.

Result classifications retain every ordinary guard. Different written views
of the same checked value can satisfy the same exact proposition, but this
does not expose the arguments of an opaque value or bypass a call's contract.

Notion inference uses a restricted collection of checked rules. It does not
search arbitrary theorems or invoke the automatic prover. Its successful
inferences are checked by the kernel, but a formation check does not add an
unstated fact to the proof. State facts needed later in the proof explicitly.

## Result annotations on definitions

A set-valued definition can include a result annotation:

```latex
\begin{definition}\label{finite_copy}
    Let $X$ be a finite set.
    $\copy{X}=X$, which is a finite set.
\end{definition}
```

Felix checks that the right-hand side has the stated notion using the
definition's assumptions and notion rules. It then records a result
classification for the new notation. Here it establishes that `\copy{X}` is
finite whenever `X` is finite.

The result phrase may combine notions or include a verb modifier, as in
`which is a set that has a clopen basis`. An abbreviation in the phrase may
expand to a whole condition, including a quantified condition. Felix checks
the instantiated condition on the right-hand side and transports the checked
result to the defined notation. One annotated result cannot serve as an
assumption for another. `which is a set` alone is rejected because every
set-valued term already denotes a set.

Result annotations require a definition with parameters and at least one
checked header. The surface result phrase uses ordinary notion syntax;
write a compound logical condition through an abbreviation. Structure nouns
and an additional `such that` clause are unsupported in the result phrase.
For an unconditional result, a structure result, or a result needing a separate
argument, state and prove a `classification` instead.

## Explicit proofs by notion

Use `by notion` to prove notion statements from the available facts and rules:

```latex
\begin{proposition}\label{field_is_ring_example}
    Let $K$ be a field.
    Then $K$ is a ring.
\end{proposition}
\begin{proof}
    Follows by notion.
\end{proof}
```

This uses proof-local notion facts, local equalities and aliases, and the
registered notion rules. It does not invoke the automatic prover.

`Follows by notion.` also accepts whole propositions. An identical supplied
formula or a registered rule can establish any whole goal; matching preserves
the complete checked formula. The following additional operations depend on the
formula's logical structure, after transparent abbreviations have expanded.
Named predicates retain their atomic identity.

| Formula | Establishing a goal | Using checked evidence |
| --- | --- | --- |
| Literal, including an explicit negative atom | Match a fact or rule, with complete-argument equality transport | Supply that literal |
| Truth | Succeed without a premise | No additional facts |
| `P and Q` | Prove both components | Project either component |
| `P or Q` | Prove either component | Use the complete disjunction; no case analysis |
| `P implies Q` | Prove `Q` in a child scope assuming `P` | Prove the guard `P`, then obtain `Q` |
| `P iff Q` | Prove both guarded directions in separate child scopes | Prove either side to obtain the other |
| `for every set x, P(x)` | Prove the body under a fresh arbitrary set | Instantiate at an admitted term and discharge every guard |
| `there exists a set x, Q(x)`, with positive body `Q` | Find an admitted witness and prove its body | Use the complete existential; no witness extraction |
| Set equality | Reflexivity or a path of supplied equations | Supply the exact equation; only eligible supplied equations form transport edges |
| Other non-literals | Exact evidence or an applicable registered rule | Supported projections and guarded eliminations only |

Here a *positive query* is a literal, truth, set equality, a conjunction or
disjunction of positive queries, or an existential over sets with a positive
body. An explicit negative atom counts as a literal; a compound negation does
not. Positive compound rule premises use the same grammar and can discover
concrete parameter assignments. An existential with an implication or universal
in its body still requires exact evidence or an ordinary producer rule. This
restriction is syntactic: a rule used to prove a positive atom may itself have
conditional or universal premises, whose proofs create child scopes.

For example, `x in A` can establish that `A` is inhabited by proving its expanded
existential with witness `x`. This can discharge the inhabitedness requirement
of a choice operation. A supplied `P iff Q` together with `P` can establish `Q`;
the equivalence alone supplies neither side. A missing finite witness is a
failed notion search, not a proof that a set is empty. Disjunction introduction
does not provide general case analysis.

Introduced assumptions and fresh binders belong to child scopes. Their local
facts, equality edges, and discovered answers cannot escape into a parent or
sibling. A discharged whole proposition can be reused with its proof, including
through its supported eliminations.

You can also state the intended consequence explicitly:

```latex
Hence $F(x)$ is finite by notion.
```

If notion reasoning cannot establish the result, prove it as an ordinary
intermediate claim or add a reusable `classification` theorem.

## Explicit negative evidence

Positive and negative atoms have distinct identities. Checked classifications
may use either polarity in their premises and conclusion. For example, a
classification registering `not_in_subseteq` lets `$A\subseteq B$` together with
`$c\notin B$` establish `$c\notin A$`, including for a source-call contract.
Proper filters expose their explicit condition `$\emptyset\notin F$`, and
guarded universal clauses may likewise produce negative instances.

Failure to prove a positive atom supplies no negative evidence. The engine
does not reverse implications, apply contraposition, cancel double negations,
or derive unrelated facts from a contradictory pair. Compound negations remain
whole propositions unless an explicitly registered clause applies. Negative
equalities do not add edges to equality transport.

## Equality transport

A local equality can transfer a known notion from one term to another. For
example:

```latex
\begin{proposition}\label{equal_finite_sets}
    Let $X$ be a finite set.
    Let $Y$ be a set.
    Suppose $Y=X$.
    Then $Y$ is a finite set.
\end{proposition}
\begin{proof}
    Follows by notion.
\end{proof}
```

Either orientation of the equality works, and Felix can follow chains of local
equalities. Formation checking uses equalities in the current assumptions;
`by notion` uses those available in the proof.

Transport applies to every complete set argument of a literal. For example,
`x in A`, `x=y`, and `A=B` establish `y in B`. Likewise, either argument of a
prefix predicate such as `\booleanSubalgebra{A}{B}` can be replaced along a
supplied equality. Predicate identity and polarity stay fixed, and every
replacement is replayed as a kernel equality step.

The boundary is the complete argument: `a=b` does not turn `P(f(a))` into
`P(f(b))`. A rule `Q(x) implies P(f(x))` may nevertheless be instantiated at
`b` once `Q(b)` is established from `Q(a)` and `a=b`; this is a new concrete rule
instance. Equality classes share lookup, while witness assignments retain the
actual chosen terms. An equation derived during search can discharge an exact
equality requirement, but it does not extend the supplied equality relation.
Non-literal formulas are not transported along that relation. Logical equality
also grants no structure designation, provider identity, or omitted-receiver
eligibility.

## Total graph application and typed results

The two source forms `f(x)` and `\apply{f}{x}` denote the same total
set-theoretic graph application. Merely writing either form does not require
Felix to prove that `f` is a function or that `x` belongs to its domain. This
matches the underlying set term, which has a value for every pair of sets.

Notion checking can still establish a notion about the result. If `f` is a
function from `A` to `B` and `x` belongs to `A`, it can establish `$f(x)\in B$`
when a surrounding expression requires it, or in a proof by notion.

Declared set-valued notation and structure operations may have their own
formation requirements, as in the Hom-set example above.

## Calculation conditions and written operands

A calculation's selected composition law may require several conditions. Felix
instantiates them with the parameters determined by the two input predicates
and submits their conjunction as one notion query. All conditions share the
usual search budget and frozen initial inputs. A condition cannot obtain
parameters from search, use a displayed link as a new assumption, or cause
Felix to choose a different law. A missing condition should be established
before the calculation, or exposed by a checked classification. An exhausted
notion account remains an error and does not invoke ATP.

Written operand views matter independently of Core equality. For example,
matching a relation parameter to `\leq[X]` retains the field-projection view
needed to use the transitivity classification for a quasiordered set. If the
same parameter has several written views, all eligible views are retained;
an earlier opaque spelling does not hide a later projection. Felix does not
infer provider structure by inspecting arbitrary opaque Core subterms.
Only parameters used by a condition or result contribute additional inputs
there. These views survive later folds and publication of the completed claim,
subject to the ordinary rules for binders, guards, and universal sources.

Internally, `SourceInputs` describes the complete operands of an opaque
formula. An empty list deliberately contributes no operands, and omitted Core
subterms remain omitted. `SourceWithInputs` adds written views to the inputs of
its underlying source evidence; it does not replace them or grant facts.
Adding no views to an explicitly empty description leaves it empty. Nested
annotations preserve source order and record the binders under which each
operand is available. This distinction applies equally to atomic and whole
formula queries and is preserved by abstraction, imports, and cache encoding.

## Bounded inference and ground premises

Exact local evidence is indexed when its scope is extended. Scoped universal
producers and equality classes are shared by later queries in that scope;
leaving the scope restores the parent index. Candidate indexes retain the
consumer's evidence policy, so proof-local facts cannot supply a definition's
result check.

The catalogue shares clause dependencies at atomic and whole heads. Support
selection follows only the shapes needed by a query, before its term domain is
frozen. A separate necessary-source check retains all guards of each clause and
alternatives between clauses; a producer's existence alone is not a starting
point. This check can avoid futile discovery, but supplies no proof and removes
no support templates. Adding an unused producer does not rebuild every consumer's
closure. Same-shape producers can still require substantial work.

Once a rule's parameters are determined, its premise requests are prepared
once. Ground instances retain ordinary premise checking and failure provenance
even when the necessary-source check rules out discovery. Repeated premises
share lookup while retaining their separate proof
positions. Rows used to determine parameters remain pinned in that activation;
a proof of an already instantiated premise cannot replace a source row needed
to discover those parameters. Ground requests inspect candidates with the same
equality classes at all complete argument positions. Every successful
conversion or equality transport still requires checked evidence.

Candidate filtering preserves shared parameters across complete operands. A
request for `P(Full(A), B)` can constrain the parameter of a conclusion
`P(Full(E), E)` before any row supplies a binding. Fixed captures and existing
bindings retain their source spelling. Only a singleton supplied equality class
can fill an unknown parameter inside another operand; a non-singleton class
constrains the complete operand only. These temporary denotations can exclude
an incompatible candidate, but supply neither clause inputs nor evidence.

Exact direct evidence is tried first, retaining source/view order and the
existing direct-cost tie-break. Initial views follow their dependency order.
Search keeps the first founded witness for each complete evidence key and
returns the first accepted root answer. Evidence delivery precedes producer
expansion; alternatives remain in deterministic queues for outstanding demands
or completed failure. Search does not rerank composite proofs or seek a globally
shortest proof. Equality-chain limits apply independently of this policy.

Repeated uses of a founded premise share its proof. Only the selected proof and
its used sources survive the query. Derivation node and depth limits apply to
the emitted kernel proof, including the logical bindings that preserve sharing;
an estimate obtained by duplicating shared subproofs does not reject a query.

Propagation with one witness per ground premise is linear apart from indexed
lookup costs. Parameter discovery, finite assignments, and recursive scoped
goals can require more work, as can Core processing and proof replay. These
costs remain part of the measured total; the complete algorithm has no general
linear bound. They share the bounded evaluator: exceeding its allowance is
reported as exhaustion, separately from a completed unsuccessful search.

All requirements of one written application share a budget, frozen domain,
request tables, and proof arena. Identical instantiated requirements reuse
their search result. Proving one leaf supplies checked truth, not a new
assumption. Multi-part definition-result annotations use the same mechanism
with only their eligible definition headers.

The finite domain has one template layer over its initial inputs. Write `B` for
those inputs and `T` for the selected templates. The domain `U` consists of `B`
and the well-scoped instances of templates in `T` whose free slots use `B`.
Templates written only beneath a query's existential binder also belong to `T`.
Inputs come
from eligible source facts, all requested operands, aliases, and fixed clause
captures. Only written provider and pair views expose subterms; an opaque
operand contributes one complete value. Whole formulas retain their independent
set operands even when no inverse matcher applies. Selected clause templates
may instantiate their free slots with these initial inputs, but newly generated
terms do not become further seeds. Clause parameters range over the resulting
domain, and each instantiated relational operand must belong to it.

For example, deriving a notion about `f(a)` does not by itself make `g(f(a))`
available for a later inference. The latter term must already be a written
input or be covered by a selected template over the initial inputs. Authorized
definition consequences are exposed when preparing those inputs; an ordinary
classification proved during search does not repeat that preparation. This
boundary prevents recursive rules from generating an unbounded tower of terms.
For example, with `B = {a}` and a selected pair template `(x,x)`, `U` contains
`a` and `(a,a)`, but not `((a,a),(a,a))` unless that term or template was already
admitted. Equality classes do not add another template layer. A vacuous
existential still needs an admitted witness; with an empty domain it fails.

Each child scope inherits its parent's initial inputs and templates, adding its
fresh variable and explicit new inputs. Parent answers do not become new inputs.
Recursive scoped obligations can create further children and exhaust the shared
allowance. Independent finite-oracle regressions establish agreement for their
tested programs, not a general completeness proof. In particular, fixed-scope
finiteness does not establish termination of recursive scoped proof search.
The group inspection allowance is 524,288; declaration and scope preparation
each have a separate 262,144 allowance.

Formation diagnostics are opt-in. `FELIX_FORMATION_STATS=1` collects owner
work, exclusive phase times, limit high-water marks and a requirement-group
histogram. `FELIX_FORMATION_COST=` additionally emits detailed completions and
work events; a nonempty value filters those details by source location. Both
settings are read once per verification. Ordinary runs perform no formation
timer calls.

Write diagnostic runs to a log and inspect them with
`python3 tools/formation-cost-summary.py LOG` (or `--json`). Detailed group
records describe portions of the final physical account; the reporting tool
does not add them again. Accepted work and rejected budget debits are separate,
and ordinary failures retain their completion account. Use runs with tracing
disabled for end-to-end performance comparisons.

`AttemptedProducer` counts candidates returned by atomic, ground-whole, and
open-whole producer streams, including later matching or eligibility failures.
Catalogue exclusions and resumed joins add no attempt. `ProducerCompilation`
counts scoped projections and introduction clauses before publication; a
refused publication debit retains that compilation count and its completed
work. Publication charges one source entry plus one unit per producer,
separately from compiler work. These corrections retain work-unit version 1;
cache epoch 168 invalidates admissions made with the incomplete publication
debit.

Detailed leaf records identify the atomic requirement by source site, consumer
and logical formula. Compare that unchanged cohort with
`python3 tools/formation-cost-summary.py --cohort-baseline BEFORE.log AFTER.log`.
The comparison excludes sites whose requirement or occurrence count changed,
and reports both direct-hit fractions and the excluded population. `--groups`
includes individual group and leaf records. Reused leaves retain their written
occurrences; they do not repeat search work.

Independently checked declarations with identical complete rule descriptions
share one executable registration. Explicit references still resolve each
declaration's own checked source. Definition views and classifications keep
their different policies, and local universal sources remain distinct.

## Reading and repairing errors

A formation error identifies the missing notion and explains where inference
failed. Typical repairs are:

- add an enclosing assumption that establishes the missing notion;
- write a complete noun or structure phrase when a bare adjective is ambiguous;
- prove the missing notion as an intermediate claim before using the term; or
- add a `classification` or result annotation for a result that should be
  available automatically.

Formation checking establishes the notions needed to use an expression.
It does not replace an ordinary mathematical proof.
