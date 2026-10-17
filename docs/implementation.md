# Proof checking and cache reuse

Felix separates source elaboration, proof search, evidence checking, and store
publication. Preparing a proof or decoding a cache entry does not establish a
theorem. For the mathematical foundations and inference rules, see
[set theory](foundation.md), [logic](logic.md), [notions](notions.md), and
[structures](structures.md).

## Checked evidence

`Checking.Core` and `Checking.Kernel.Semantics` share term transformations,
inference, and logical rule checks between ordinary execution and execution
that counts work. The execution policy determines how work is counted and
errors are reported. Without matching cached validation, kernel replay checks
the retained derivation against its goal and imports. A matching validation
record allows Felix to reuse the earlier check; search and preparation cannot
establish that success themselves.

`Checking.Elaboration` resolves lexical scope and checks source propositions.
`Checking.Proof` stores a proof tree and a private planning summary describing
request order, direct facts, and explicit proof gaps. Execution and syntax
encoding remain independent of that summary.

`Checking.Declaration` prepares each declaration, validates its evidence, and
commits the results in source order. Preparation records resolved identities
and exact prover requests. The current invocation separately selects cached
validation or live prover work and holds any running request handles. Before
committing, it checks that the plan matches the current builder, theory,
declaration position, preceding declarations, and dependencies.

## Reuse and publication

`Checking.Semantic` describes rules to register. `Checking.Notion.Registration`
compiles these descriptions, and `Checking.Declaration` checks their supporting
evidence and installs the rules. Formation search returns kernel proof recipes
that the caller must check. Its scheduling, finite term support, and shared
work limits are documented in
[bounded inference](notions.md#bounded-inference-and-ground-premises).

`Checking.Module` represents complete, importable modules separately from the
result of fresh checking, which also contains the declaration batches to save.
`Store` validates serialized entries and writes immutable rows and complete
module roots atomically. A module root is saved only after its interfaces agree
with its committed declarations. Successfully checked declarations can be saved
separately when a later declaration fails; this does not make the incomplete
module importable.

Persistent stores speed up verification and can be discarded. Source remains
authoritative, and compatibility depends on both the theory identity and cache
epoch. Runtime representations may change without changing serialized
identities. Changes to the meaning of stored data must cover both fresh checking
and reuse. Retain tests for mathematical identities, serialized ordering,
transaction rollback, and verification with and without cached results.
