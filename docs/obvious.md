# Obvious inferences

Obvious inferences are the default proof automation of Felix.
They are a bounded proof search over the current local facts,
explicitly cited global facts and permitted canonical definition views.
A proof step without an explicit justification leads to an obvious inference
without any cited global facts. To cite global facts, use `by \obv{...}`.
The justification `by definition` is a variant of obvious inferences.
Proofs found by obvious inference are replayed in the kernel.

If obvious inferences fail, you can try using the stronger proof automation
powered by the external automated theorem prover with `by \auto` or `by \auto{...}`.
Plain `\auto` supplies only local facts to the automated prover.

The following are typical uses. Each example assumes that the stated facts
are available locally or cited explicitly.

- **Combine facts.** From `$a\in A$` and `$a\in B$`, Felix can prove
  `$a\in A$ and $a\in B$`. It can also extract either fact from a conjunction.

- **Follow implications.** From `$a\in A$` and `if $a\in A$, then $a\in B$`,
  it can infer `$a\in B$`. Several such steps can be chained without writing
  every intermediate claim.

- **Reason by cases.** If `$a\in A$ or $a\in B$` and either alternative implies
  `$a\in C$`, Felix can conclude `$a\in C$` without an explicit `byCase` proof.

- **Use negation and contradictions.** From `$a\in A$ or $a\in B$` and
  `$a\notin A$`, it can infer `$a\in B$`. If both `$a\in A$` and `$a\notin A$`
  are available, `Contradiction.` closes the contradiction proof.

- **Instantiate universal facts.** From `for all $x$ we have $x\in A\lor x\in B$`
  and `$a\notin A$`, it can infer `$a\in B$` by using the universal fact at `a`.
  This also works with conditional rules and conjunctions of rules.

- **Apply cited theorems.** Felix can determine a theorem's parameters from
  the goal and available facts, then prove its premises. For example, with
  `$A\subseteq B$` and `$B\subseteq C$` available, write:

  ```latex
  Then $A\subseteq C$ by \obv{subseteq_transitive}.
  ```

- **Follow equalities through expressions.** From `$a=b$` and `$b=c$`, it can
  prove `$a=c$` or `$c=a$`, as well as `$f(a)=f(c)$`. Equalities can also be used
  in predicates: `$a=b$` and `$a\in A$` give `$b\in A$`. Explicitly cited
  equality theorems can supply links in these arguments.

- **Use definitions.** Felix can use a defining equation to prove the
  current goal. For example, if `\myset` is defined to be `\emptyset`, either
  of these steps proves its defining equation:

  ```latex
  We have $\myset=\emptyset$.
  We have $\myset=\emptyset$ by definition.
  ```

  The second form succeeds only if the proof uses a definition.

- **Use local names.** A local definition remains available in later steps.
  For example, when `$a\in A$` is known:

  ```latex
  Let $b=a$.
  Then $b\in A$.
  ```

- **Find an existing witness.** From `$a\in A$`, Felix can prove
  `there exists $x\in A$ such that $x=x$`, using `a` as the witness. Witness
  search tries values already available in the goal or facts.

- **Use an existential assumption.** From
  `there exists a set $x$ such that $x\in A$ and $x\in B$`, it can prove
  `there exists a set $y$ such that $y\in B$` without an explicit `Take` step.

- **Prove set equality by membership.** If every member of `A` belongs to `B`
  and every member of `B` belongs to `A`, write:

  ```latex
  Then $A=B$ by \obv{setext}.
  ```

  Felix can also prove these two membership conditions as part of the step,
  using the available facts and case reasoning.

Search is bounded, so a valid consequence may still need intermediate claims
or explicit `Fix`, `Take`, or `byCase` steps. Definitions and equalities do not
provide unrestricted rewriting inside arbitrary expressions.

For developers: `Felix.Checking.Obvious` is the public module;
`Felix.Checking.Obvious.Driver` and `Felix.Checking.Obvious.Refutation` are private.
For a preparation request with several residual searches, create one
`ObviousAllowance` and pass the returned balance from `obviousProofReportWithin`
to the next residual. This preserves private attempt quotas as well as work
and allocation limits. `obviousInitialProofReportWithin` makes a bounded first
attempt with one quarter of each consumable, rounded down, and returns the full
balance after actual expenditure. It skips a zero focused-work slice. These
interfaces retain no suspended search state; ordinary callers continue to use
`obviousProofReport` with their full budget.

Recursive definitions publish binding-owned constructor equations. Admission
checks each equation against the named body, datatype, headers, and branch
descriptions; imports repeat that check. Raw recursor implementation equations
are not automatic definition views.

When an ordinary first attempt fails, source preparation can introduce the
goal's binders and assumptions and apply an owned equation. It proves all
headers and constructor domains as one scoped guard, existentially quantifying
unstored witnesses. Notion evidence for that guard stays private to the
application. The declaration owner checks the association again and replays
the equation use. A composed `by definition` proof must actually depend on
that application or an ordinary canonical definition; proving a guard alone
does not qualify. Preparation, guard queries, and residual Obvious searches
share their respective request allowances.

Evaluation proceeds outside-in and carries each equality through the surrounding
expression with checked congruence, including beneath binders. A branch can
therefore compute compound Set values or contain recursive propositions under
negation. Supplied facts use the same evaluator and checked equality transport;
an unused transformed fact supplies no definition authority. A successful
application can be reused within the same lexical scope and premise set, while
proof copying and source substitution still consume preparation work. Missing
guards and variable scrutinees remain residual. An exhausted optional guard
query returns its spent budget and stops further guard attempts in that request;
residual Obvious reasoning can still finish the proof.
