# Development checkpoint

Updated 2026-11-27 (UTC).

## Current repository state

- Main includes PR #22 (source positions, residual-goal checks and branch-local name expiry), PR #37/#38 (bounded element-operation candidates), PR #39 (scoped local lemmas), PR #40 (Mathlib subgroup closure) and PR #45 (conservative repeated-row identity reconciliation).
- PR #45 was squash-merged as `9cc0c7ea122df39cc3b4026c8f52b6f64592a3e4`. Its exact head `175c35bbe23bc5804e0fc656281b6e4f6f2e3c60` passed full Tests run `46081647742`; the main push Tests run `46083385839` is still being checked, and Pages deployment `46083385823` succeeded.
- PR #42's benchmark implementation passed full Tests run `46082417456` on exact head `5ecaa856efde5fef2eba34b4b02e7ede1e68129a`. This branch is now synchronized with #45's main commit and the checkpoint records results from the corrected public cold-compiler baseline; rerun the full workflow on the synchronized head before merging.
- PR #46 adds a linear-map additivity case. Its two generated Lean candidates compiled under pinned Mathlib 4.19. The integration then exposed an overly strict test lookup for the extracted declaration name; the current branch revises that lookup and is being revalidated. Do not count the corpus case as fully verified until its dependency-closure checks pass.
- Contributor PR #44 (Urdu language pack) remains open from a fork with workflow `action_required`; it is not treated as validated.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branch closure checks the residual goal; local declarations expire at scope exit; only parent-visible dependencies return. Conjunction, equivalence, existential construction, intuitionistic negation introduction and explicit ex-falso are constructive operations. Classical reductio is not silently introduced.

Bounded element requests preserve the set restriction and local identity. A displayed type is required; a known local carrier can reject a mismatch; universal introduction creates membership as a subgoal; an existential witness carries both membership and its property. Universal introduction and existential extraction remain separate structural readings until the goal, typed context or user choice constrains them. The parser does not infer arbitrary set carriers or local definitions from the same phrase.

A local lemma uses an explicit claim and proof block. Its child scope inherits parent identities, closes only against the stated claim, and returns parent-visible dependencies. Child-local declarations expire. An incomplete lemma remains an open dependency and cannot produce a complete Lean export.

The reviewed Mathlib seed corpus covers a continuous image of a compact set and subgroup multiplication closure. The corresponding generated Lean terms compile against pinned Mathlib 4.19, and dependency extraction checks data, propositions and relevant typeclass instances. These are small acceptance examples, not broad mathematical-language coverage.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking and author-intent fidelity are distinct states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison, not general definitional equality. Current source identities are reconciled conservatively across edits; repeated identical rows may remain intentionally unmatched when correspondence is ambiguous.

The new benchmark measures synthetic editor cases only. It must report the observed medians and P95 values, including cases with little reuse or slower cached evaluation; no user-facing latency claim has been established yet.

## Incremental benchmark observations

Run `46082417456` used Ubuntu 24.04.5 and Node 22.23.5, with 24 warmups and 160 timed samples per case. Every cached result was compared structurally with a cold public `compileNaturalDraft` result. Times are milliseconds; reuse is mean reused rows. These synthetic figures are not browser keystroke latency and do not generalize to user documents.

| Case | Median | P95 | Reuse |
|---|---:|---:|---:|
| Cold full evaluation (16 proof rows, 62 locals) | 1.442 | 2.249 | 0 |
| Exact replay (16 proof rows, 62 locals) | 1.112 | 1.785 | 16 |
| Final-premise character edit (15-row prefix) | 1.081 | 1.561 | 15 |
| Local proof-dependency edit (7-row prefix) | 1.069 | 1.393 | 7 |
| Eight-level nested cases, cold (41 lines) | 6.283 | 8.981 | 0 |
| Eight-level nested cases, exact replay | 1.160 | 1.405 | 25 |
| Nested case conclusion edit | 6.951 | 7.958 | 16 |
| Interleaved sequence, cold (two case blocks) | 2.012 | 2.801 | 0 |
| Interleaved replay plus terminal edit | 2.524 | 3.228 | 4 |
| Conjunction child goals, cold | 0.097 | 0.211 | 0 |
| Second conjunction goal edit | 0.268 | 0.340 | 1 |
| Element candidates, cold (50 locals) | 0.976 | 1.389 | 0 |
| Element candidates, exact replay | 0.450 | 0.758 | 1 |
| Element candidate property edit | 1.013 | 1.337 | 0 |
| New existential premise | 0.988 | 1.296 | 0 |
| Local lemma, cold (51 locals) | 1.412 | 1.831 | 0 |
| Local lemma, exact replay | 0.313 | 0.338 | 3 |
| Local lemma one-premise edit | 1.667 | 2.150 | 1 |
| Local lemma source-line shift | 1.686 | 2.182 | 0 |

Exact replay is faster in these fixtures. Reuse does not guarantee a speedup: nested conclusion edits, interleaved terminal edits and local-lemma edits can be slower than their cold baselines despite some reused rows. The benchmark is synthetic and does not establish general editor latency.

## Next dependency-ready work

1. Confirm the main push Tests run `46083385839` for PR #45 and close issue #4 once its two-sided conflict and repeated-row acceptance tests are verified on main.
2. Complete full Tests and pinned Mathlib validation for synchronized PR #42, then merge only the exact green head.
3. Finish PR #46's linear-map declaration and dependency-closure validation, sync it to the new main tree, and rerun both workflows.
4. Prototype issue #1's small InfoTree adapter: tactic source ranges, goals before/after, local context and referenced declarations, with explicit opaque-tactic range mapping and a pinned Lean regression.

The original eight-stage implementation order remains authoritative. Current work advances tree scopes, bounded structural ambiguity, declaration dependencies, local editing, incremental evaluation and real-math acceptance cases; it does not complete any full stage.
