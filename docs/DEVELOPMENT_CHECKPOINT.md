# Development checkpoint

Updated 2026-11-27 (UTC).

## Current repository state

- Main includes PR #22 (source positions, residual-goal closure checks, and branch-local name expiry), PR #43 (constructive ex-falso from an explicit `False` premise), PR #37 (structural operation candidates), PR #38 (set-restricted element operations), and PR #39 (scoped local lemma subproofs).
- PR #39 was squash-merged as `5c6205e7df9f0a55f422a6d74be22f71e9a499a9`. Its exact head `3d899d39ec508d93d20cfc9f2d97af853d5421c6` passed both full Tests runs (`46077887989`, `46077892803`) and pinned Mathlib integration (`46077892834`). The browser path selected the actual elaborated `letFun` node, built a local-lemma draft, checked/applied its Lean patch, and rechecked the theorem.
- The main push, Mathlib integration, and Pages deployment for the #39 merge were started as runs `46078929296`, `46078929261`, and `46078929322`; verify their final result before treating main as fully green.
- PR #40 adds the subgroup multiplication-closure acceptance case alongside the compact-image topology case. Its earlier stacked head is being synchronized onto current main; the synchronized head still needs full Tests and pinned Mathlib validation.
- PR #42 corrects the incremental benchmark baseline to use the public full compiler path and compares every cached result structurally with a cold result. It still needs synchronization and a fresh run on the final stack.
- PR #44 is an independent Urdu language-pack contribution. Its fork workflow is `action_required`; its tests are not verified.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branches close only against their stated residual goals; child-local declarations expire; only parent-visible dependencies can return. Conjunction, equivalence, existential construction, intuitionistic negation introduction, and ex-falso remain constructive operations. Classical reductio is not silently introduced.

Bounded element requests preserve the set restriction and its local identity. A displayed element type is required; a known local carrier can reject a mismatch; a universal introduction creates membership as an explicit premise; an existential witness carries both membership and its property. The browser keeps universal-introduction and existential-extraction readings separate until the goal, typed context, or user choice constrains them. The parser does not infer arbitrary set carriers.

A local lemma uses an explicit claim and proof block. The child inherits parent identities, must structurally close against the stated claim, and returns only parent dependencies. Child-local declarations expire. An incomplete claim remains visible as an open dependency but cannot produce a complete Lean export. The browser-to-backend path and Mathlib local-lemma candidate compile on the validated PR #39 head.

The representative corpus now includes a compact-image theorem in topology and a subgroup multiplication-closure theorem in abstract algebra. The latter's synchronized Mathlib run must confirm both compilation and dependency extraction before it is counted as validated.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking, and author-intent fidelity are separate states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison, not general definitional equality. Local scope IDs and incremental cache behavior still require improvement for source-line shifts.

## Next dependency-ready work

1. Finish checking the main #39 push Tests, Mathlib integration, and Pages deployment runs.
2. Validate and merge synchronized PR #40, including its pinned subgroup Lean case and dependency view.
3. Synchronize PR #42; record cold, replay, edit and nested-scope medians/P95 and report cases where incremental work is slower.
4. Continue issue #4 with stable proof-node IDs and edit migration for insertions, deletions, repeated steps, and ambiguous two-sided edits.
5. Add a reviewed analysis or linear-algebra case with natural prose, expected semantic structure, Lean compilation, and a local-edit regression.

The original eight-stage implementation order remains authoritative. The current work advances tree scopes, structural operation ambiguity, declaration dependency checks, local bidirectional editing, incremental evaluation, and real-math acceptance cases; it does not complete any full stage.
