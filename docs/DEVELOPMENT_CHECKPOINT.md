# Development checkpoint

Updated 2026-11-27 (UTC).

## Current repository state

- Main includes PR #22 (physical source addresses, residual-goal checks and expired branch-local names), PR #37/#38 (structural bounded-element readings and set restrictions), PR #39 (scoped local-lemma proofs), and PR #40 (a Mathlib subgroup-closure corpus case).
- PR #39 was squash-merged as `5c6205e7df9f0a55f422a6d74be22f71e9a499a9`. Its exact head `3d899d39ec508d93d20cfc9f2d97af853d5421c6` passed two full Tests runs (`46077887989`, `46077892803`) and pinned Mathlib integration (`46077892834`). The browser smoke selected the elaborated `letFun` node, checked and applied a local-lemma patch, then rechecked the theorem. The corresponding main push Tests, Mathlib integration, and Pages deployment (`46078929296`, `46078929261`, `46078929322`) passed.
- PR #40 was squash-merged as `bace4536f9005e0f98edc1282cd6876caeb1f155`. Its exact head `034c9ca2fc9a3f740dd2b2695c469071de981ec7` passed full Tests run `46079119023` and pinned Mathlib runs `46079118710` and `46079119058`. Lean 4.19 accepted both the compact-image and subgroup-multiplication candidates; the dependency view retained their data and instance assumptions. Main-branch checks for the #40 merge are still to be confirmed.
- PR #42 has been synchronized onto the #40 main tree. It corrects the incremental benchmark's cold baseline to use `compileNaturalDraft`, asserts structural equality against full recomputation for each case, and adds the benchmark to CI. Its fresh checks and measurements are pending.
- Contributor PR #44 (Urdu language pack) remains open from a fork. Its workflow run `46069875209` is `action_required`; the branch is not treated as validated or merge-ready.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branch closure checks the residual goal; local declarations expire at scope exit; only parent-visible dependencies return. Conjunction, equivalence, existential construction, intuitionistic negation introduction and explicit ex-falso are constructive operations. Classical reductio is not silently introduced.

Bounded element requests preserve the set restriction and local identity. A displayed type is required; a known local carrier can reject a mismatch; universal introduction creates membership as a subgoal; an existential witness carries both membership and its property. Universal introduction and existential extraction remain separate structural readings until the goal, typed context or user choice constrains them. The parser does not infer arbitrary set carriers or local definitions from the same phrase.

A local lemma uses an explicit claim and proof block. Its child scope inherits parent identities, closes only against the stated claim, and returns parent-visible dependencies. Child-local declarations expire. An incomplete lemma remains an open dependency and cannot produce a complete Lean export.

The reviewed Mathlib seed corpus covers a continuous image of a compact set and subgroup multiplication closure. The corresponding generated Lean terms compile against pinned Mathlib 4.19, and dependency extraction checks data, propositions and relevant typeclass instances. These are small acceptance examples, not broad mathematical-language coverage.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking and author-intent fidelity are distinct states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison, not general definitional equality. Current source identities are reconciled conservatively across edits; repeated identical rows may remain intentionally unmatched when correspondence is ambiguous.

The new benchmark measures synthetic editor cases only. It must report the observed medians and P95 values, including cases with little reuse or slower cached evaluation; no user-facing latency claim has been established yet.

## Next dependency-ready work

1. Confirm main-branch Tests, pinned Mathlib and Pages results after PR #40.
2. Finish the synchronized PR #42 full CI run; inspect its benchmark output and record actual medians/P95 and structural-equivalence results.
3. Continue issue #4 on stable proof-node identities and explicit conflict handling for insertions, deletions, repeated steps and simultaneous edits.
4. Add a reviewed analysis or linear-algebra case with natural prose, expected semantic structure, a Mathlib-compiled Lean term and a local-edit regression.

The original eight-stage implementation order remains authoritative. This work advances tree scopes, bounded structural ambiguity, declaration dependencies, local editing, incremental evaluation and representative corpus coverage; it does not complete any full stage.
