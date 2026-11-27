# Development checkpoint

Updated 2026-11-27 (UTC).

## Current repository state

- Main includes PR #22 (source locations, residual-goal closure checks, and branch-local name expiry), PR #43 (constructive ex-falso from an explicit `False` premise), PR #37 (structural candidates for bounded universal introduction and existential witness extraction), and PR #38 (set-restricted element operations).
- PR #38 merged as `2e511b6a0ab7da22cad1f3f6f3cd7eb3e9fceabe`. Its exact head passed the Tests, browser smoke/static-browser path, and pinned Mathlib integration before merge. The Pages deployment for the merge passed; the main push test run is being checked separately.
- PR #39 adds explicit local-lemma proof blocks on the tree-scope machinery. It is being synchronized to the post-#38 main tree; its exact synchronized head still needs the complete test and Mathlib runs.
- PR #40 adds a reviewed compact-image/subgroup Mathlib acceptance case. PR #42 adds cold-versus-incremental structural comparison and a benchmark. Both were created against the earlier stack and must be synchronized and revalidated after #39.
- PR #44 is an independent Urdu language-pack contribution. Its fork workflow is marked `action_required`, so its tests are not treated as verified.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branches close only against their stated residual goals; child-local declarations expire; only parent-visible dependencies return. Conjunction, equivalence, existential construction, negation introduction, and ex-falso are represented as constructive goal operations. Classical reductio is not silently introduced.

Bounded element requests preserve the set restriction and its local identity. A displayed type is required; a known local carrier can reject a mismatch; existential evidence contains both membership and the requested property. A universal introduction creates the membership implication as an explicit subgoal. These rules remain conservative surface semantics and do not infer arbitrary set carriers.

PR #39 extends the same scope mechanism to local lemma subproofs. The claimed proposition enters the parent context only after its proof closes; child-local names expire; incomplete proofs remain open dependencies and do not produce an executable term. The scope model is not a full Lean elaborator.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking, and author-intent fidelity are separate states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison rather than general definitional equality.

## Next dependency-ready work

1. Complete synchronized PR #39 validation, including nested/sibling scopes, incomplete local lemmas, browser interaction, and pinned Mathlib compilation.
2. Synchronize PR #40, review its compact-image and subgroup cases, then run the pinned Mathlib integration.
3. Synchronize PR #42 and compare cached edits with full recompilation case by case. Report losses as well as gains; source-line shifts currently invalidate more work than ideal.
4. Add a reviewed analysis or linear-algebra example with natural prose, expected semantic structure, Mathlib-backed Lean code, and a local-edit regression.

The original eight-stage order remains authoritative. This work primarily advances tree scopes and proof operations, structural ambiguity, incremental evaluation, and representative acceptance; it does not complete any full stage.
