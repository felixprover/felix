# Felix Tutorial


## Definitions

Definitions are given within a normal `definition` environment.

```tex
\begin{definition}\label{ordinal}
    $\alpha$ is an ordinal iff
    $\alpha$ is \in-transitive and every element of $\alpha$ is \in-transitive.
\end{definition}
```

The vocabulary you define is automatically extracted as a pattern and added to the grammar of Felix. Each pattern can consist of multiple words and also include variables as parameters.

You can define the following:

Kind | Pattern | Example
---- | ---- | ----
Nouns | `<VAR> is a <NOUN PATTERN> iff <STATEMENT>` | `$k$ is a divisor of $n$ iff ...`
Adjectives | `<VAR> is <ADJECTIVE PATTERN> iff <STATEMENT>` | `$n$ is divisible by $k$ iff ...`
Verbs | `<VAR> <VERB PATTERN> iff <STATEMENT>` | `$k$ divides $n$ iff ...`
Operators | `$<MIXFIX PATTERN> = <TERM>$` | `$n + k = ...$`
Relators | `$<VAR> <RELATOR PATTERN> <VAR>$ iff <STATEMENT>` | `$n < k$ iff ...`
Predicates | `$\<PREDICATE COMMAND>{<VAR>}...{<VAR>} iff <STATEMENT>` | `$\Cong{a}{b}{c}{d}$ iff ...`

Source fixity declarations are line-leading pragmas such as `%! infixl 4`.
User declarations may use literal levels 0 through 7; the two higher internal
levels are reserved. Verification keeps compact proof-independent theorem
authority separate from exact proof/declaration validation. Its authorization
summary lists only direct source axioms and syntactic `Omitted` sites, not
facts that merely inherit their safety.

Every checked definition publishes a canonical view of the defined symbol.
Deterministic obvious inference may expose that view at supported root
positions. An ordinary first-order definition is also published as a
first-order fact, so explicitly requested ATP search can use it without
promoting an otherwise first-order task to TH0. Genuine higher-order premises
route an explicit ATP task through TH0.

The finite verb must be the first literal word of a verb pattern. Literal
`a` and `an` are allowed inside that pattern, so a property may be stated
directly and naturally:

```tex
\begin{definition}\label{has_clopen_basis}
    Let $X$ be a topological space.
    $X$ has a clopen basis iff ...
\end{definition}
```

Felix derives the base surface from the leading finite word for the bounded
regular cases, including `has`/`have`. Put an explicit base annotation
immediately after the labelled environment header when the verb is irregular
or lies outside that convention:

```tex
\begin{definition}\label{lies_over}
    \verbbase{lie}
    $X$ lies over $Y$ iff ...
\end{definition}
```

The annotation changes only the leading word; holes and all later tokens must
be identical. Felix checks and removes this metadata before the declaration is
parsed. One subject selects the finite surface, while a textual list of at
least two subjects selects the base surface: write `$X$ has ...`, `$X$, $Y$
have ...`, `$X$ does not have ...`, and `$X$, $Y$ do not have ...`. These
forms name one predicate and participate in notion reasoning like named nouns,
adjectives, and relations.

This syntax declares an ordinary named predicate. It does not turn the words
after `has` into a possessed noun or introduce an implicit witness. Opaque verb
signatures likewise have no source declaration syntax.

## Typed logical expressions

Ordinary Felix variables and declaration parameters denote sets. When a
formalization needs predicates, propositions, or logical functions as values,
it can use the separate concrete type grammar:

```tex
\Set
\Prop
\Set\to\Prop
(\Set\to\Set)\to\Prop
```

Arrows associate to the right. Typed application is written
`\Apply{F}{x}`; the compact form `\Apply{P}{x,y,z}` is left-to-right curried
shorthand for `\Apply{\Apply{\Apply{P}{x}}{y}}{z}`, not tuple application.
The notation `f(x)` continues to mean application of a set-coded function
graph. Lambdas and typed quantifiers are written as follows:

```tex
\fun{x,y,z:\Set}{x}
\forall P:\Set\to\Prop.\ \Apply{P}{x}
\exists f:\Set\to\Set.\ \Apply{f}{x}=x
```

Adjacent same-type lambda binders may be grouped; use separate binders when
their types differ.

An atomic logical constant can be opaque or transparently defined:

```tex
\begin{signature}\label{predicate_functional}
    $\Phi : (\Set\to\Prop)\to\Prop$.
\end{signature}

\begin{definition}\label{identity_functional}
    $\mathcalI : \Set\to\Set = \fun{x:\Set}{x}$.
\end{definition}
```

Logical selection is `\Select{P}` when the selected type can be inferred from
`P : \tau\to\Prop`, or `\Select[\tau]{P}` when it should be checked
explicitly. Set-level global choice remains the distinct expression
`\choice{A}`. Higher-order statements use the same proof methods as
first-order statements. A step that needs general higher-order search must
request `\auto` explicitly; citing a higher-order premise routes that task
through TH0.

Higher-order separation and bounded least fixed points are written
`\sep{A}{P}` and `\lfp{D}{F}` for `P : \Set\to\Prop` and
`F : \Set\to\Set`. The prelude facts `lfp_bound`, `lfp_least`, `lfp_fixed`,
and `lfp_induct` expose their checked rules and must be cited explicitly.

## Natural numerals and opaque integer atoms

A bare nonnegative decimal is a mathematical von Neumann natural. Thus `0`
is `\emptyset`, `1` is `\suc{\emptyset}`, and each further step applies the
validated successor supplied by the final prelude. Bare negative decimals are
not expression syntax.

```tex
$0=\emptyset$
$2=\suc{\suc{\emptyset}}$
```

Use `\opaqueInteger{n}` when an integer-shaped token is intentionally only an
uninterpreted set atom. Its payload may be nonnegative or begin with one minus
sign, but never with a plus sign. The explicit form remains visible when Felix
renders the expression and receives no natural-number equations.

```tex
$\opaqueInteger{17}=\opaqueInteger{17}$
$\opaqueInteger{-3}\neq\opaqueInteger{3}$
```

This is a source compatibility break: a formerly bare decimal used as an
opaque identity must be rewritten with `\opaqueInteger{...}`. Zero is available
while the empty bootstrap compiler constructs the final prelude. Positive
naturals require that validated prelude, so bootstrap-only fixtures must use a
set-theoretic construction or the explicit opaque form. Literal expansion is a
linear successor spine; Felix accepts magnitudes through 1024 and rejects a
larger one before constructing Core.

Set-sized recursion is function-valued. If `R` is well-founded on `A` and
`H` belongs to `Fun(A \times Pow(A \times B), B)`, then
`\wfrec{A}{B}{R}{H}` belongs to `Fun(A,B)` and satisfies

```tex
\apply{\wfrec{A}{B}{R}{H}}{x}
  = H((x,\restrl{\wfrec{A}{B}{R}{H}}{\downward{R}{x}})).
```

For an ordinal `\alpha`, `\ordinalRecursion{\alpha}{B}{H}` specializes this
equation so that the predecessor graph at `\beta` is simply the restriction
to `\beta`. The codomain bound is explicit because these operators construct
ordinary set-coded function graphs rather than logical-framework functions.

## Bounded noun binders

A quantified noun can carry a symbolic bound at its name slot:

```tex
For every infinite cardinal $\mu\in\kappa$ we have ...
For all subsets $A,B\in F$ of $X$ we have ...
There exists a subset $A\in F$ of $X$ such that ...
Take a subset $A\in F$ of $X$ such that ...
```

The bound precedes trailing noun parameters such as `of $X$`. Existing signed
relations are allowed, including `\notin` and `\neq`. Quantified arguments
(`every`, `some`, and `no`) accept one optional name; a bound requires that name.
Their existing scope is unchanged: a predicate distributed over several
subjects gives each subject its own argument witness. To require one witness
shared by all subjects, introduce it with an explicit outer existential.

Predicate negation stays inside subject quantifiers: `every set $x$ is not
an element of $A$` means that each set is outside A. Likewise, `$x$ and $y$
are not elements of $A$` asserts nonmembership for both subjects. Negation
covers the complete noun predicate, including its modifiers and quantified
arguments. Use `It is not the case that ...` to negate a whole statement.

A group shares one endpoint evaluated in the enclosing scope. Thus `$A,B\in F$`
restricts both names to F, while an endpoint containing either A or B is
rejected, even if an outer variable has the same spelling. Use nested noun
quantifiers for dependent bounds. An existential group introduces its witnesses
together; `there exist no` negates that complete existence assertion.

These bounds belong to quantified nouns and `Take`. Headers still use
`Let $A,B$ be subsets of $X$ such that $A\in F$ and $B\in F$.`
Purely symbolic `Let $A,B\in F$.` and sequential symbolic universal bounds
keep their existing meanings. Predicative noun names, structure phrases,
signatures, and definition-result annotations do not acquire bounds.

## Structures

Structures are transparent set-coded records. The general root `record` has
no required fields; `onesorted structure` adds the canonical carrier. Structure
predicates are open, while “exact” asserts that a record has precisely the
selected schema's fields. In particular, an exact zero-field record is the
empty set. Aggregates, parameters, named instances, projections, and reducts
are described in [Structures in Felix](structures.md).

Use `topological space based on M` to copy just the topology fields of a
checked record; append `with \carrier=U and \opens=O` to replace fields
explicitly. This constructs an exact record, but does not prove topology laws.
A parameterized `construction` declaration pairs such a body (or an aggregate)
with a mandatory proof. Its public structure, shape, and projection facts all
retain the stated hypotheses. The [worked coordinate example](../test/structure-spikes/manifolds-0.tex)
shows composition and equality proofs through that public interface.
Use `instance` for a closed record and an ordinary aggregate when no fields
are being copied. The [worked construction and its consequences](structures.md#named-instances-and-construction-families)
also explain explicit reducts, projection disambiguation, and the exactness
facts needed before `Follows by structure extensionality.`

## Abbreviations

Abbreviations are definitions that are always automatically expanded by Felix.

## Proof vernacular

Felix separates two kinds of proof automation. Its internal obvious-inference
procedure handles small deterministic logical steps and constructs a proof
that the kernel replays. General-purpose search is performed by Vampire only
when the source explicitly requests `\auto`. Larger steps should normally cite
their exact mathematical premises.

Within proofs, we distinguish between *global facts*, which are all preceding theorems that have been successfully proved, and *local assumptions*, which are the assumptions of the theorem statement (e.g. `Suppose ...`) or of individual proof steps (`Assume ...`) and *intermediate claims* that are established throughout the proof.

At the start of a proof, the *sufficiency* or *proof goal* corresponds to the conclusion of the theorem statement.
Some proof steps may change this sufficiency.

For a theorem quantified over ordinals, transfinite induction fixes the
current ordinal, adds the expected induction hypothesis for all of its
members, and leaves the claim at the current ordinal as the goal:

```tex
\begin{proposition}\label{ordinal_example}
    For every ordinal $\alpha$ we have $P(\alpha)$.
\end{proposition}
\begin{proof}[Proof by transfinite induction]
    % Here alpha is an ordinal, P(beta) is available for every beta in alpha,
    % and the goal is P(alpha).
\end{proof}
```

The transformation uses set induction internally and the visible theorem that
members of ordinals are ordinals. The standard ordinal library provides this
as `elem_of_ordinal_is_ordinal`; source proof steps see the simplified
transfinite hypothesis rather than the guarded set-induction premise.

### Proof via intermediate claims

The simplest proofs state mathematically useful intermediate claims and give
each non-obvious step a focused justification. An absent justification uses
obvious inference with the active local context and canonical definition
views; it never searches the ordinary global theorem library or invokes
Vampire.

The following proof first establishes the relevant property of restriction,
then applies the general theorem that a subrelation of an injective relation is
injective.

```tex
\begin{proposition}\label{restrl_injective}
    Suppose $R$ is injective.
    Then $\restrl{R}{A}$ is injective.
\end{proposition}
\begin{proof}
    $\restrl{R}{A}\subseteq R$ by \auto{restrl_subseteq}.
    Follows by \auto{subseteq_of_injective_is_injective}.
\end{proof}
```

The proof methods have deliberately different premise policies:

Source form | Meaning
---- | ----
No justification | Deterministic obvious inference; no ordinary global facts
`by \obv{foo,bar}` | Obvious inference with exactly the cited global facts
`by \auto` | Vampire with the complete local context and no ordinary global facts
`by \auto{foo,bar}` | Vampire with exactly the cited global facts
`by assumption` | Exact active-local reuse with structural conjunction projection
`by definition` | Deterministic inference which must use canonical definition evidence
`by notion` | Bounded notion inference for literals and supported compound goals

All methods receive the active local context. Plain `\auto` retains complete
locals, including higher-order local definitions. To use global facts with
Vampire, cite them explicitly with `\auto{foo,bar}`; there is no unrestricted
global selection. Obvious inference never silently falls back to Vampire:
an unsuccessful implicit, cited Obvious, or definition step reports failure.
An explicitly cited `\auto{...}` may use a kernel proof when one is available;
its source instruction already authorizes ATP if that attempt finds no proof.

Obvious inference is a bounded two-tier procedure. It first tries focused
logical introduction, theorem application, equality paths, target-shaped
congruence, and controlled canonical-definition exposure. For an ordinary
obvious request, a deterministic refutation tier can then use signed
propositional decomposition, ground congruence closure over the terms already
present in the request, and forward rules of the form
`forall x1 ... xn. A1 -> ... -> Am -> C`. Rule binders range over sets;
premises must be atomic first-order applications or equalities. Derived rules
and propositions may feed the same branch-local fixed point.

Before freezing its ground universe, the refutation tier recursively prepares
the proposition roots selected by logical structure: quantified bodies,
negations, both sides of binary connectives, implication premises, and
implication conclusions. Rule recognition and later signed decomposition reuse
these same prepared views. Thus a beta redex may hide the next logical
constructor, and a ground term revealed at such a proposition root belongs to
the initial universe. A term occurring only in syntax discarded by that root
exposure does not.

Preparation stops at an exposed atomic or equality root. Its interior syntax,
including beta redexes in atomic arguments or equality operands, remains exact;
obvious inference does not normalize below that boundary. A derived compound
proposition is likewise prepared and checked against the frozen universe once,
then its logical children reuse the resulting catalogue evidence when they are
later selected.

This procedure is intentionally incomplete. It does not invent existential
witnesses, perform higher-order unification, enumerate arbitrary terms, or
rewrite below arbitrary contexts. Its semantic-view ground universe and
explicit work, beta, term, branch, and rule-instance limits keep failure
predictable. Source-ordered equality alternatives are consumed depth first,
and a named root-branch cap is checked after catalogue preparation but before
root equality initialization or proof-context construction.
Every success is reconstructed with checked kernel combinators and replayed;
failure never falls back to Vampire. `by definition` remains focused-only, so
the refutation tier cannot accidentally satisfy its canonical-evidence
requirement.

When Obvious inference fails, its structured diagnostic identifies both the
obligation site and the method. The site distinguishes an implicit theorem
close, an implicit instance obligation, a final `Follows`, a `Contradiction`,
and an inline inference such as `Have` or `Since`. The method independently
distinguishes implicit, cited, and definition-aware Obvious inference. This is
diagnostic context only; it does not change which facts are visible or which
proof search is performed.

The diagnostic always includes a bounded rendering of the checked goal. It
also says whether focused exposure was unavailable, failed, retained that
goal, or produced a changed beta-exposed view. Local facts, cited facts, and
local and imported definition views are shown in separate bounded inventories.
Finally, it reports both the focused and refutation outcomes, or the exact
reason the refutation tier did not start. These inventories describe supplied
inputs, not necessarily conclusions that search compared, and truncation is
explicit. Diagnostic summaries are non-authoritative and are discarded after
a successful run.

Failed focused search also reports up to three “best observed focused
candidates.” These are actual root-goal comparisons made by the focused tier,
ranked by deterministic progress: a completed proof rejected only by
`by definition` ranks above a matched conclusion with an unavailable premise,
which ranks above a rejected comparison. A candidate can be a direct fact, a
conjunction projection, a prepared theorem conclusion, or a qualifying
equality transport. The list is bounded and non-exhaustive; it is not a
mathematical nearest-neighbour search and says nothing about untried facts or
the refutation tier's saturation.

Candidate coverage says whether observation did not start, finished normally,
or stopped early with partial evidence. Definition participation is reported
separately for fact-side and goal-side views. It means that those exact
canonical-definition occurrences participated in the observed comparison; it
does not claim that a definition caused the failure. Requirement rejection in
an introduction component, theorem antecedent, or transport premise remains
auxiliary and is never promoted into the root-candidate ranking.

```tex
\begin{proposition}\label{inters_of_family_of_partial_equivalences_is_partial_equivalence}
    Let $F$ be a family of relations.
    Suppose every element of $F$ is a partial equivalence.
    Then $\inters{F}$ is a partial equivalence.
\end{proposition}
\begin{proof}
    $\inters{F}$ is a relation
        by \obv{inters_of_family_of_relations_is_relation}.
    $\inters{F}$ is symmetric by \auto{symmetric,inters_iff_forall,inters_destr}.
    $\inters{F}$ is transitive by \auto{transitive,inters_iff_forall,inters_destr}.
\end{proof}
```

`by assumption` is narrower than implicit obvious inference or
`\obv{...}`: it reuses active local propositions up to judgemental conversion,
including conjunction projection and construction. `by definition` performs
definition-aware obvious inference and succeeds only when the resulting kernel
proof actually uses canonical definition evidence. Neither form falls back to
Vampire. A bare `by \obv` is not a second spelling for implicit inference; omit
the justification instead. `by notion` likewise does not invoke Vampire: it
retains the exact local facts, checked local equalities, and registered
classifications selected by the notion calculus. See
[Notions and formation checking](notions.md) for its logical fragment, finite witness domain, equality transport, and
evidence scopes.

In an `Assume` or `Suppose` sentence, textual `and` introduces separate
assumptions, while an explicit mathematical `\land` keeps one compound
premise. `that` is optional only immediately after the introduction keyword;
inner `and that` is unsupported. Assumption opening may consume implication
premises out of order and conjunction leaves under a terminal negation, but
disjunctions remain opaque to this rule (Felix's existing classical
disjunction opening still applies) and nested negations remain opaque except
for exact negation openings. Grouped `Let` clauses are sequential, so later
clauses may depend on earlier ones. Symbolic bounded `Fix` binders such as
`Fix $x,y\in A$.` are opened left to right; put a variable first when a bound
depends on it.

`Since` proves a temporary premise and then a durable intermediate claim:

```tex
Since $P$ by \auto{proof_of_p}, we have $Q$ by \obv{p_implies_q}.
```

Both justifications may be omitted. Felix proves `P` in the current context,
uses `P` only while proving `Q`, and continues with `Q`. A newly established
`P` is not available after this step; any copy of `P` that was already an
outer assumption remains available normally.

### Proof finishing steps

If no explicit finishing step is given, the implicit last step is `Follows.`:
deterministic obvious inference from the active locals and canonical
definitions. This applies to both first-order and higher-order statements. Use
`Follows by \auto{<labelname>}` when the step needs Vampire and a selected
global fact.

```tex
\begin{proposition}\label{function_apply_default}
    Suppose $x\notin\dom{f}$.
    Then $f(x) = \emptyset$.
\end{proposition}
\begin{proof}
    $\img{f}{\{x\}} = \emptyset$ by \auto{setext,emptyset,img_singleton_iff,dom_intro}.
    Follows by \auto{apply,unions_emptyset}.
\end{proof}
```

The extensionality finisher can close a set equality from two exact membership
directions or from one exact pointwise membership `iff`. A direction may also
be exposed through the forward canonical definition of an active positive
fact, so two subset premises are sufficient. Write
`Follows by set extensionality.` to request this family explicitly, or
`Follows by extensionality.` to let Felix first try exact-record extensionality
and then set extensionality.

The finisher constructs and kernel-checks the complete derivation. It may
project an outer conjunction, eliminate a propositional equality, and expose a
root-only chain of canonical pointwise definitions. It does not invoke
Vampire, look up ordinary theorems, fold definitions in reverse, or perform
general logical normalization.

```tex
\begin{proposition}\label{subset_extensionality_example}
    Suppose $A\subseteq B$ and $B\subseteq A$.
    Then $A=B$.
\end{proposition}
\begin{proof}
    Follows by set extensionality.
\end{proof}

\begin{proposition}\label{pointwise_extensionality_example}
    Suppose for every $x$ we have $x\in A$ iff $x\in B$.
    Then $A=B$.
\end{proposition}
\begin{proof}
    Follows by set extensionality.
\end{proof}
```

```tex
\begin{proposition}\label{dom_circ_exact}
    Let $f, g$ be functions.
    Suppose $\ran{f} = \dom{g}$.
    $\dom{g\circ f} = \dom{f}$.
\end{proposition}
\begin{proof}
    Every element of $\dom{g\circ f}$ is an element of $\dom{f}$.
    Follows by set extensionality.
\end{proof}
```

### Assumption steps

If the sufficiency is syntactically of the form `$\phi$ implies $\psi$` or similar, then we can locally assume `\phi` and are left with `\psi` as the sufficiency. Here is a simple artificial example.

```tex
\begin{proposition}\label{assumption_example}
    If $x\in y$ and $a\in b$, then $x\in y$.
\end{proposition}
\begin{proof}
    Assume $a\in b$. % Sufficiency is now "If $a\in b$, then $x\in y$."
    Assume $x\in y$. % Sufficiency is now "$x\in y$."
    Follows by assumption. % Finishing proof steps, which uses only local assumptions and intermediate claims (no global facts).
\end{proof}
```

We can also make an assumption step against sufficiencies of the form `$\phi$ or $\psi$`, which changes the goal to the negation of `\psi`.


## Proof by contradiction

You can start a proof by negation (or, if the sufficiency is negative, a proof of a negation) with `Suppose not`.
Below is a proof of a negative statement ("It is not the case that there exists...").

```tex
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

`Suppose not` should only be used when necessary. It disables checking for contradictions within axioms and can lead lower quality error messages.
`Contradiction` ends the current proof or explicit subproof, so no further proof step may follow it in the same scope.


## Case splits

You can split into any finite number of cases. Felix must establish that their
disjunction is exhaustive, and each case becomes an active local assumption.
Within each case, there is a local assumption that the case holds.

```tex
\begin{proposition}\label{ordinal_preceq_implies_subseteq}
Let $\alpha,\beta$ be ordinals.
Suppose $\alpha\precedeseq\beta$.
Then $\alpha\subseteq\beta$.
\end{proposition}
\begin{proof}
    \begin{byCase}
        \caseOf{$\alpha = \beta$.}
            Follows by \auto.
        \caseOf{$\alpha\precedes\beta$.}
            Follows by \auto{ordinal_elem_implies_subseteq}.
    \end{byCase}
\end{proof}
```


## Consider

We can obtain a witness of an existential statement as a local constant with `Consider`.
For example, `Consider $p$ such that $p$ is a prime factor of $n$` requires the selected proof method to establish that such a `$p$` exists. Add an explicit `by \auto{...}` when this is not obvious.
After this, `$p$` is available as a local constant with the desired property.


## Suffices

We can change the sufficiency by using a step of the form `It suffices to show that ...`.
The selected proof method must show that the new sufficiency implies the old one within the current context.


## Datatypes and structural induction

A datatype family separates its parameters from the fields stored in its
constructors. For example, formulas over an arbitrary set of atoms are:

```tex
\begin{datatype}\label{pl_formula}
    %! infixr 0
    Define $\plform{A}$ inductively as follows.
    \begin{enumerate}
        \item[Falsity] $\propbot\in\plform{A}$.
        \item[Atom] $\propvar{a}\in\plform{A}$ for $a\in A$.
        \item[Implication]
            $(p\propto q)\in\plform{A}$ for
            $p\in\plform{A}$ and $q\in\plform{A}$.
    \end{enumerate}
\end{datatype}
```

Every recursive premise uses the same family parameters. A fixed domain may
depend on those parameters, but not on another premise variable. Constructors
have exactly the arguments written in the declaration. An additional witness
premise remains a required premise even when no constructor field stores it.

The item names also name the induction cases and the introduction theorems,
such as `pl_formula_atom_intro`. Names ignore capitalization and normalize
whitespace to underscores. Each structural proof must supply every case once;
the order is free. Ordinary `Fix` and `Suppose` steps introduce the case's
variables, domain guards and induction hypotheses:

```tex
\begin{proposition}[Carrier monotonicity]\label{pl_formula_monotone}
    Suppose $A\subseteq B$.
    Then for every $p\in\plform{A}$ we have $p\in\plform{B}$.
\end{proposition}
\begin{proof}[Proof by structural induction on $p$]
    \begin{byCase}
        \caseOf{Falsity.}
            Follows by \obv{pl_formula_falsity_intro}.
        \caseOf{Atom.}
            Fix $a\in A$.
            Then $a\in B$ by \obv{subseteq}.
            Follows by \obv{pl_formula_atom_intro}.
        \caseOf{Implication.}
            Fix $q,r\in\plform{A}$.
            Suppose $q\in\plform{B}$ and $r\in\plform{B}$.
            Follows by \obv{pl_formula_implication_intro}.
    \end{byCase}
\end{proof}
```

This [checked importing example](../test/phase5/propositional-induction.tex)
uses the ordinary subset definition. Each case starts in its own scope with
its full obligation. Every recursive premise supplies an induction hypothesis,
including a witness absent from the constructor's fields.

The same proof header can prove a goal about an active variable `p` when the
context contains `p\in\plform{A}`. Its family parameters and all other active
assumptions must be independent of `p`; this also applies to local definitions.
Independent conjuncts of the membership assumption remain available. Put any
additional condition on `p` inside the motive, for example
`for every $p\in\plform{A}$ we have if $p\in C$ then ...`.
When several source datatypes could supply induction, use a bounded universal
goal naming the intended carrier.

Eligible constructor introductions also support `by notion`. This can check
nested formation directly, but does not introduce new assumptions into a proof.
Introductions with extra witnesses or unsupported premise shapes remain
available through their named theorems.


## Structural recursion

Import `recursion/well-founded-relation.tex` to define operations and predicates
by constructor equations. For example, satisfaction on the formulas above is:

```tex
\begin{recursive-definition}[Satisfaction]\label{pl_satisfaction}
    Define $\plSat{A}{V}{p}$ recursively for $p\in\plform{A}$ as follows.
    \begin{enumerate}
        \item[Falsity] $\plSat{A}{V}{\propbot}$ iff $\bot$.
        \item[Atom] $\plSat{A}{V}{\propvar{a}}$ iff $a\in V$.
        \item[Implication] $\plSat{A}{V}{p\propto q}$ iff
            if $\plSat{A}{V}{p}$ then $\plSat{A}{V}{q}$.
    \end{enumerate}
\end{recursive-definition}
```

Set-valued operations use `=` in their clauses. The
[checked definitions](../test/phase5/propositional-recursion.tex) include
occurring atoms, reconstruction and constant recursion. Their
[importing client](../test/phase5/propositional-recursion-use.tex) proves small
equations by definition and bounds the occurring atoms by structural induction.

The final head argument is the structural variable. All earlier arguments are
fixed Set parameters, and the datatype's family arguments must be among them.
Supply every constructor once, in any order; optional item headings must name
the matching datatype cases. Constructor fields bind distinct local variables.
Their bounds come from the datatype declaration. Extra premise witnesses remain
requirements of the equations, but cannot be used as branch inputs.

Each self-call must preserve the fixed parameters and recurse on an immediate
stored recursive field. Calls may be repeated, discarded, negated or occur in
an implication. Abbreviations cannot conceal a call on a larger expression.
Passing the unfinished operation as a value, changing parameters, and mutual
recursion are unsupported. Calls to previously checked recursive operations
use their ordinary formation contracts.

Ordinary `Let` headers may constrain fixed parameters. They cannot mention the
structural argument, since a condition on a parent need not hold on its children.
As for other definitions, Set headers restrict source formation; predicate
headers also contribute logical conjuncts. Satisfaction needs no condition
`V ⊆ A`: it consults membership in `V` only for atoms in `A`.

Each public equation, named `<definition-label>_<case-key>`, is a checked theorem
with its header and constructor guards. `by definition` applies these equations
when the structural argument has a visible constructor and all guards are
available. It can continue through compound branch results, including negative
predicates. A variable structural argument remains opaque to this evaluation.
The transparent underlying construction defaults to the empty set, or false
for predicates, outside the datatype; source applications still require carrier
membership. Recursive definitions add no axioms or trusted recursion rule.


## Proof by ∈-induction (set induction)

```tex
\begin{lemma}\label{regularity_aux}
    For all $a, A$ such that $a\in A$
    there exists $b\in A$ such that
    $b\notmeets A$.
\end{lemma}
\begin{proof}[Proof by \in-induction on $a$]
    Follows by \auto{disjoint}.
\end{proof}
```

The induction hypothesis is part of the active local context; the cited fact
is the only ordinary global premise supplied to Vampire.


## Calculations

A calculation presents a chain of successive compatible binary relations.
Ordinary term equality is one relation in this syntax, and Felix
also retains a separate source form for biconditionals between formulas. Each
adjacent link is checked independently and has its own justification; a
justification may be omitted when the link is an obvious inference.

For example, the proof of `commuting_squares_composition` contains the
following portion of a calculation:

```tex
\begin{align*}
    e\circ(b\circ p)
        &= (e\circ b)\circ p
            \explanation{by \auto{circ_assoc}}
        \\
        &= (c\circ d)\circ p
            \explanation{by \auto}
        \\
        &= c\circ(d\circ p)
            \explanation{by \auto{circ_assoc}}
\end{align*}
```

The production proof continues with further rewrites. The first cited step
uses the exact global fact `circ_assoc`; the local-only step uses the active
assumptions and does not search the ordinary global theorem pool. The
calculation checker applies the selected premise policy independently to each
link.

Equality is the only built-in composition family. Equality can transport an
ordinary relation on either endpoint, and two equalities compose directly. A
chain of two non-equality relations uses an exact theorem declared in the
`composition` environment. For example, the set library
registers both

```tex
\begin{composition}\label{subseteq_transitive}
    Suppose $A\subseteq B\subseteq C$.
    Then $A\subseteq C$.
\end{composition}
```

and the heterogeneous `\in`-then-`\subseteq` composition. This permits a
calculation such as:

```tex
\begin{align*}
    a
        &\in A
            \explanation{by \auto}
        \\
        &\subseteq B
            \explanation{by \auto}
\end{align*}
```

The declaration is ordinary checked proof evidence, not a compiler relation
matrix. Composition itself is deterministic structural checking and does not
invoke Vampire. The selected theorem occurrence is retained as a proof
dependency, while Vampire requests—if explicitly requested—belong only to the
independent displayed-link discharges.

Links use ordinary assertion elaboration, including formation requirements.
They may contain negation, relation parameters, term-given relations such as
`a\mathrel{R}b`, and contextual abbreviations. An abbreviation may reverse or
ignore endpoints. Equality works at each supported concrete Core type;
biconditionals keep their separate formula syntax. Disequality supports
transport (`a=b\neq c`), but `a\neq b\neq c` has no built-in composition.

A composition's final assumption must be a two-link chain with three distinct
variable endpoints; its conclusion connects the first and last. Earlier
headers may introduce parameters and conditions. For example, the relation
library proves:

```tex
\begin{composition}\label{transitive_relation_composition}
    Suppose $R$ is transitive.
    Suppose $x\mathrel{R}y\mathrel{R}z$.
    Then $x\mathrel{R}z$.
\end{composition}
\begin{proof}
    Follows by \obv{transitive}.
\end{proof}
```

Felix selects a law by matching its expanded, beta-normal input predicates.
Every parameter must occur in those inputs; parameters cannot be applied as
logical functions. A law cannot capture one of its endpoint variables as a
separate relation parameter or receiver. Equality inputs use the built-in
transport rule. Registration rejects overlapping laws, including conflicts
between independent imports, even when no calculation uses them. Conditions
and declaration order do not resolve an overlap.

After selecting the law, Felix proves its instantiated conditions together
using the bounded `notion` mechanism. The available context consists of the
assumptions and facts preceding the calculation, plus its quantified prefix
and guards. Individual displayed links do not become assumptions for other
links or conditions. There is no ATP fallback for missing conditions. Prove a
needed condition before the calculation, or provide an appropriate checked
classification. The generic law above also handles structure orders because
`quasiorder_relation_transitive` establishes transitivity of `\leq[X]` by
notion.

Resolution fixes contextual receivers and operand adjustments for each link.
For a structure `G`, `a\in G` means `a\in\carrier[G]`. Transport through
`G=H` produces `a\in\carrier[H]` using that same carrier projection; it does
not reinterpret `H`. An ordinary membership–subset law consequently does not
match a link whose right endpoint is a structure. Write the carrier explicitly
when the following link concerns a set of elements.

After the calculation, the completed relation from its first expression to its
final one is available as a local claim, retaining its ordinary source notion
views and written operands. Later steps can use it by notion or as equality
evidence. A quantified or guarded result exposes only the views permitted by
its binders and antecedents; its prefix does not escape. If that
completed result is the current goal, the implicit finishing step `Follows.`
can close the theorem. This is the first-to-last claim, not the final endpoint
by itself.

Use a calculation when the mathematical argument genuinely consists of
successive rewrites. Use ordinary proof steps when the argument also contains
unrelated deductions, such as introducing assumptions or establishing an
intermediate fact that is not one link in the rewrite chain.

The existing `Since` form is useful when a premise is needed only while
establishing the next claim: the premise is temporary, and the resulting claim
is what remains available afterward. See the `Since` discussion above for its
scope and proof-method details.
