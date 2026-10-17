# Earley session lifecycle

This audit records the ownership assumptions behind Felix's parser sessions.
The Phase 2 comparison harness and its bounded-consumer prototype are retired;
their source and experimental results remain in Git history as described in the
[benchmark overview](../readme.md). The upstream [Earley license](Earley-LICENSE)
is retained with the parser documentation.

A session instantiates the grammar once, creates a fresh initial state and parse
environment per input, and drains results through `Ended`. Complete-result
semantic actions execute before their continuation. No mutable state or deferred
ST action may escape the scoped session.

Lifecycle inventory from Earley 0.13.0.1:

| State | Proposed lifetime / reset obligation |
| --- | --- |
| Rule production, grammar topology | Shared for the session |
| `ruleConts` outer reference | Shared; `resetConts` installs a fresh empty inner reference after every position that expands it |
| Nullable cache | Grammar-derived and token-independent; first call writes an empty recursion guard, then memoizes pure null values; may survive inputs |
| Initial continuation and argument references | Fresh per input; argument references reset by the recorded position reset action |
| Chart, position, input, names, result-action list | Fresh per input, position zero; never reused |
| `Many` rules | Allocated while parsing, not installed into shared grammar topology; per-input continuations/results must release them |
| Delayed semantic result references | Result actions must execute before continuation/consumer; do not carry ST actions across inputs |
| Position reset actions | Already run at `Parsed` and `Ended`, as well as before advancing a position; draining to `Ended` precedes consumer stop |


First-use nullable work and dynamic rule construction are part of chart work.
The historical microbenchmarks did not justify session integration under their
original gates. The later whole-library experiment did, and production now uses
module sessions. Bounded ambiguity consumption was not adopted: production
continues to preserve exact ambiguity counts and diagnostics.
