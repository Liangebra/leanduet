# Development checkpoint

Updated 2026-11-27 (UTC).

## Current repository state

- Main includes PR #22 (physical source addresses, residual-goal checks and expired branch-local names), PR #37/#38 (structural bounded-element readings and set restrictions), PR #39 (scoped local-lemma proofs), and PR #40 (a Mathlib subgroup-closure corpus case).
- PR #39 was squash-merged as `5c6205e7df9f0a55f422a6d74be22f71e9a499a9`. Its exact head `3d899d39ec508d93d20cfc9f2d97af853d5421c6` passed two full Tests runs (`46077887989`, `46077892803`) and pinned Mathlib integration (`46077892834`). The browser smoke selected the elaborated `letFun` node, checked and applied a local-lemma patch, then rechecked the theorem. The corresponding main push Tests, Mathlib integration, and Pages deployment (`46078929296`, `46078929261`, `46078929322`) passed.
- PR #40 was squash-merged as `bace4536f9005e0f98edc1282cd6876caeb1f155`. Its exact head `034c9ca2fc9a3f740dd2b2695c469071de981ec7` passed full Tests run `46079119023` and pinned Mathlib runs `46079118710` and `46079119058`. Lean 4.19 accepted both the compact-image and subgroup-multiplication candidates; the dependency view retained their data and instance assumptions. The main-branch Tests run `46080575167`, pinned Mathlib run `46080575219`, and Pages deployment `46080575174` all passed.
- PR #42 has been synchronized onto the #40 main tree. Its exact head `f9e6436845b7efd8632236f2b6011a39ce6c1c1a` passed the full Tests workflow (`46080842726`), including the benchmark, Node/Python suites, Lean models, semantic integrations, and browser smoke/static-browser checks. It compares 19 synthetic incremental-session cases against the public cold `compileNaturalDraft` path with structural equality on every sample; the measurements below are fixture-specific.
- Contributor PR #44 (Urdu language pack) remains open from a fork. Its workflow run `46069875209` is `action_required`; the branch is not treated as validated or merge-ready.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branch closure checks the residual goal; local declarations expire at scope exit; only parent-visible dependencies return. Conjunction, equivalence, existential construction, intuitionistic negation introduction and explicit ex-falso are constructive operations. Classical reductio is not silently introduced.

Bounded element requests preserve the set restriction and local identity. A displayed type is required; a known local carrier can reject a mismatch; universal introduction creates membership as a subgoal; an existential witness carries both membership and its property. Universal introduction and existential extraction remain separate structural readings until the goal, typed context or user choice constrains them. The parser does not infer arbitrary set carriers or local definitions from the same phrase.

A local lemma uses an explicit claim and proof block. Its child scope inherits parent identities, closes only against the stated claim, and returns parent-visible dependencies. Child-local declarations expire. An incomplete lemma remains an open dependency and cannot produce a complete Lean export.

The reviewed Mathlib seed corpus covers a continuous image of a compact set and subgroup multiplication closure. The corresponding generated Lean terms compile against pinned Mathlib 4.19, and dependency extraction checks data, propositions and relevant typeclass instances. These are small acceptance examples, not broad mathematical-language coverage.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking and author-intent fidelity are distinct states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison, not general definitional equality. Current source identities are reconciled conservatively across edits; repeated identical rows may remain intentionally unmatched when correspondence is ambiguous.

The new benchmark measures synthetic editor cases only. It must report the observed medians and P95 values, including cases with little reuse or slower cached evaluation; no user-facing latency claim has been established yet.

## Incremental benchmark observations

Run `46080842726` used Ubuntu 24.04.5 and Node 22.23.5, with 24 warmups and 160 timed samples per case. Each cached result was structurally compared with a cold public compiler result. Times are milliseconds; “reuse” is mean reused rows. These synthetic figures are not browser keystroke latency and do not generalize to user documents.

| Case | Median | P95 | Reuse |
|---|---:|---:|---:|
| Cold full evaluation (16 proof rows, 62 locals) | 1.496 | 2.662 | 0 |
| Exact replay (same draft) | 1.160 | 1.927 | 16 |
| Final-premise character edit (15-row prefix) | 1.118 | 1.925 | 15 |
| Local proof-dependency edit (7-row prefix) | 1.118 | 1.548 | 7 |
| Eight-level nested cases, cold (41 lines) | 6.522 | 7.750 | 0 |
| Eight-level nested cases, exact replay | 1.293 | 1.768 | 25 |
| Nested case conclusion edit | 7.397 | 8.093 | 16 |
| Interleaved sequence, cold (two case blocks) | 2.235 | 2.700 | 0 |
| Interleaved replay plus terminal edit | 2.746 | 3.354 | 4 |
| Conjunction child goals, cold | 0.149 | 0.283 | 0 |
| Second conjunction goal edit | 0.214 | 0.392 | 1 |
| Element candidates, cold (50 locals) | 1.003 | 1.484 | 0 |
| Element candidates, exact replay | 0.482 | 0.833 | 1 |
| Element candidate property edit | 1.072 | 1.293 | 0 |
| New existential premise | 1.059 | 1.540 | 0 |
| Local lemma, cold (51 locals) | 1.513 | 1.948 | 0 |
| Local lemma, exact replay | 0.332 | 0.360 | 3 |
| Local lemma one-premise edit | 1.774 | 2.412 | 1 |
| Local lemma source-line shift | 1.778 | 2.355 | 0 |

Exact replay is faster in these fixtures. Reuse does not guarantee a speedup: the nested conclusion edit and interleaved terminal edit exceed their cold baselines, and dependency edits can leave little reuse. Follow-up optimization should target these invalidation patterns and report the same paired comparison rather than infer speed from reuse counts.
## Next dependency-ready work

1. Confirm main-branch Tests, pinned Mathlib and Pages results after PR #40.
2. Finish the synchronized PR #42 full CI run; inspect its benchmark output and record actual medians/P95 and structural-equivalence results.
3. Continue issue #4 on stable proof-node identities and explicit conflict handling for insertions, deletions, repeated steps and simultaneous edits.
4. Add a reviewed analysis or linear-algebra case with natural prose, expected semantic structure, a Mathlib-compiled Lean term and a local-edit regression.

The original eight-stage implementation order remains authoritative. This work advances tree scopes, bounded structural ambiguity, declaration dependencies, local editing, incremental evaluation and representative corpus coverage; it does not complete any full stage.
