# Felix's logical foundations

## Logical function equality

Checked conversion uses βη equality with opaque globals. For example,
`\fun{x:\Set}{\Apply{f}{x}}` converts to `f`. This does not identify distinct
opaque functions from hypotheses, change structural term encoding, or change
TH0 export. `betaNormalizeChecked` still performs β-only readback.

Ordinary equality search can prove `f=g` from pointwise evidence by opening
fresh logical arguments and reconstructing abstraction congruence followed by
conversion. Predicate equality can additionally consume both implication
proofs through `PropositionalExtensionality`. Intermediate arrow prefixes use
direct evidence and non-recursive supplied-theorem elimination; a premise
needing broader reasoning may require a separately requested ordinary equality.
Logical application `\Apply{f}{x}` is distinct from set-graph application `f(x)`.

Equality transport can also complete function-valued application arguments from
permitted pointwise equations. This restricted route does not start completion
for operators, search guards recursively, open existentials, create ground
families, or initiate nested completion. Ordinary evidence is published before
support search; retained alternatives resume only under live search demand.
Conversion and propositional extensionality do not themselves count as use of
a canonical definition. These routes remain bounded automation, not a
completeness guarantee. Small internal-only examples are in
[`test/phase8/eta-equality.tex`](../test/phase8/eta-equality.tex).

## Bounded search

Boolean ground execution reuses prepared syntax and shares the directional
base between descendant goal selections. Directions try direct evidence and
implication introduction before general whole-direction fallback. Actual
bodies retain focused fallback when their local ground query blocks or misses,
including when a blocked-body fork or selected-fact capture is unaffordable.
Partial expenditure remains charged. Exhausted focused credit must not strand
a pending query or late evidence; observers cannot drive search.

Ordinary demand checks visit each shared producer once per query. Consumer
registration checks the new waiter, and publication and phase completion deliver
FIFO notifications. Exact obligation lookup retains encounter order: changing
this order can let competing searches exhaust shared ground credit before an
existing root proof finishes. Scheduling changes therefore need both local
work measurements and representative source verification.

The [conversion benchmark](../benchmark/conversion/Main.hs) includes `workflow`
cases `function-pointwise`, `argument-pointwise`, `boolean-directional`, and
`function-miss`, plus `function-replay` for fresh checking of a retained proof.
Each accepts a size and repetition count; run measurements with `+RTS -T -RTS`.
Complete-request measurements include proof replay. The failed case checks for
a semantic miss and rejects budget exhaustion as a substitute.

## Calculational composition

A relator in a lexical context Γ is a checked binary predicate
`λu:α. λv:β. body`, normalized by beta conversion. Its parameters, negation,
carrier projections, and other endpoint adjustments are part of that term.
A checked application retains the ordinary source proposition and evidence,
and establishes that its Core converts to the relator applied to the two
original operands. Transparent expansion uses the same source-template
operations as ordinary elaboration.

Let a registered theorem, in its actual binder order, have the form

```text
∀q̄. σ₁ → … → σₖ → (ρ₁ x y ∧ ρ₂ y z) → ρ₃ x z.
```

Three distinct telescope positions designate `x`, `y`, and `z`; all other
binders are parameters. Matching the two normalized input relators determines
those parameters uniquely for a selected law. Parameters are typed leaves in
a first-order pattern: they cannot occur in function position or capture a
relator endpoint or an internal binder. Captured source operands remain
explicit even when expansion erases them. Every parameter must occur in the
normalized inputs. Registration rejects overlapping input patterns using the
same rigid syntax and an occurs-checked unifier.

The composition inference is

```text
Γ ⊢ ρ₁[θ] a b       Γ ⊢ ρ₂[θ] b c       Γ ⊢ σ₁[θ] ∧ … ∧ σₖ[θ]
────────────────────────────────────────────────────────────────
                         Γ ⊢ ρ₃[θ] a c
```

Here θ includes the actual endpoints in their original telescope positions.
For `k=0` there is no condition child. The group is a balanced conjunction;
checked projections recover each condition in theorem-premise order. Its
proof uses the pre-calculation context and any calculation prefix, with one
bounded notion query. Equality transport uses ordinary equality elimination
instead of a registered composition theorem. Prefix assumptions and binders
are discharged only around the completed first-to-last claim.

Soundness follows from the retained kernel derivation: specialize the checked
theorem at θ, eliminate each condition implication, conjoin the two link
proofs, and apply the remaining implication, inserting checked conversions
where needed. During execution every child must succeed before this derivation
is replayed against its exact child goals, imports, and parent goal. Planning
alone grants no authority. Composition preserves the theorem and child proof
dependencies, including inherited external proofs and explicit proof gaps.
Portable source metadata is checked against the theorem and visible provider
identities on fresh and cached admission; it contributes no proof authority.

Calculation work and law admission have independent mandatory allowances of
1,000,000 and 262,144 respectively. A calculation shares its allowance across
lowering, normalization, matching, source-view association, all folds, and
composition construction. Each distinct admitted law shares one allowance
across metadata checks and every overlap comparison. Diamond duplicates are
removed before another admission account is allocated. Exhaustion is an error,
independent of optional preparation of explicitly automated link proofs.
