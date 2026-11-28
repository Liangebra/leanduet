# Development checkpoint

Updated 2026-11-28 (UTC).

## Current repository state

- Main is `f1cd98152c1b92d3cf3911204ccc291689d3aafe` and includes PR #22, #37/#38, #39, #40, #42, #45 and #46. PR #22's branch-scope, source-position and residual-goal fixes are already in the baseline.
- Main's latest Full Tests run `46087674165`, Mathlib integration `46087674089`, and Pages deployment `46087674048` succeeded.
- PR #47 adds the pinned Lean 4.19 InfoTree trace adapter, a local `/api/trace` endpoint, and an on-demand browser view. Its synchronized head is `bc8de53416e69a22a9994fe45eb10eef08762be7`; exact-head Mathlib integration passed (`46095692867`). The Full Tests run (`46095692897`) is checking the browser path. The schema coalesces only exact duplicate observations and retains raw multiplicity; it does not infer author-intent alignment.
- PR #48 adds an explicit `classical reductio hnot` operation, distinct from intuitionistic negation introduction and ex-falso. Its current head `9c7e4cab49505c4d88fa2fec9eea5505f96b33a9` has passed Node, Python, benchmark and core Lean steps; generated-term integration and browser CI are still running.
- PR #48 adds an explicit classical reductio operation. Its current head `9c7e4cab49505c4d88fa2fec9eea5505f96b33a9` passed Full Tests (`46094812885`) on the previous base; it still needs synchronization with #47 before merge.
- PR #49 adds Lean-compatible function composition syntax and a continuous-composition Mathlib case. Exact-head Mathlib integration passed (`46096101548`); Full Tests (`46096101544`), including browser checks, are running.
- PR #44 (Urdu language pack) remains open from a fork with workflow `action_required`; it is not treated as validated.
- The real-math fixture has three small checked seeds: compact image in topology, subgroup multiplication closure, and linear-map additivity. These are acceptance anchors, not broad mathematical-language coverage.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branch closure checks the residual goal; local declarations expire at scope exit; only parent-visible dependencies return. Conjunction, equivalence, existential construction, intuitionistic negation introduction and explicit ex-falso are constructive operations. Classical reductio is not silently introduced.

Bounded element requests preserve the set restriction and local identity. A displayed type is required; a known local carrier can reject a mismatch; universal introduction creates membership as a subgoal; an existential witness carries both membership and its property. Universal introduction and existential extraction remain separate structural readings until the goal, typed context or user choice constrains them. The parser does not infer arbitrary set carriers or local definitions from the same phrase.

A local lemma uses an explicit claim and proof block. Its child scope inherits parent identities, closes only against the stated claim, and returns parent-visible dependencies. Child-local declarations expire. An incomplete lemma remains an open dependency and cannot produce a complete Lean export.

The reviewed Mathlib seed corpus covers a continuous image of a compact set, subgroup multiplication closure, and linear-map additivity. The corresponding Lean terms compile against pinned Mathlib 4.19, with dependency checks on relevant object, proposition and typeclass context. These are small acceptance examples, not broad mathematical-language coverage.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking and author-intent fidelity are distinct states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison, not general definitional equality. Current source identities are reconciled conservatively across edits; repeated identical rows may remain intentionally unmatched when correspondence is ambiguous. Lean InfoTree traces are observations from elaboration: tactic ranges and goals are not author-intent alignments, and references are syntactic occurrences from recorded terms or assigned goals, not a complete logical dependency graph.

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

1. Finish Full Tests and browser validation for synchronized PR #47; after its checkpoint is current and the exact head is green, merge and verify main Full Tests, Mathlib, and Pages.
2. Synchronize PR #48 with the updated main, rerun the full workflow on the resulting tree, then merge only if the branch-composed browser and Lean checks pass.
3. Synchronize PR #49 with the resulting main, rerun Full Tests and pinned Mathlib, then merge only after checking its formula and topology corpus behavior on the exact head.
4. Extend local source-region correspondence from Lean tactic observations and scoped identities, preserving conflicts when prose alignment is not supported.
5. Add the reviewed same-type-premise proof-refactoring counterexample requested by issue #9.
6. Continue the bounded bridge from the Scoped model to the serialized semantic IR in issue #10; do not claim correspondence with arbitrary browser ASTs or Lean expressions.
