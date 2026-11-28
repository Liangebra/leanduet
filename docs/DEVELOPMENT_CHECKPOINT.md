# Development checkpoint

Updated 2026-11-28 (UTC).

## Repository and review state

- `main` is `907404d26c5187f96922a54dd264446f284bce1f`. PR #22 is merged at
  `0eaf7dd608579e442c5f1c3b835a83c558f75348`; its source-line mapping,
  residual-goal checks, and branch-local lifetime fixes are in the baseline.
- PR #61 and #63 are merged. PR #62 was closed as a duplicate of #63. The
  latest verified main checks after #63 were Full Tests `46120595641`, pinned
  Mathlib `46120595602`, and Pages deployment `46120595644`.
- PR #64 (`1643e61`) adds explicit Nat induction. Full Tests
  `46124889627` is running its browser smoke step; pinned Mathlib
  `46124889639` passed. The prior full-test run `46122850837` failed in the
  browser path and does not validate this head.
- PR #65 (`c363032`) adds Nat existential formulas to the scoped semantics
  fragment. Pinned Mathlib `46125273505` passed. Full Tests `46125273495` is
  still running through integration checks; do not treat it as passed yet.

## Mathematical and engineering state

Proof contexts form a tree. Child goals inherit parent object identities;
siblings remain isolated; closure checks the child result against its target;
child-local declarations expire; only parent-visible dependencies return.
Current bounded operations include universal and implication introduction,
intuitionistic negation introduction, explicit ex falso, disjunction
elimination, conjunction and equivalence introduction, explicit existential
witness construction, local lemmas, and named classical reductio. Classical
reasoning is never inserted by ordinary candidate generation. Nat induction
is restricted to an explicitly typed universal Nat goal and remains under
PR #64 review.

The parser retains supported operation readings as candidates. In particular,
arbitrary-variable introduction and existential-witness extraction remain
distinct until a typed goal, premise, or user choice constrains them. Bounded
element requests preserve the set restriction and require an explicit carrier
annotation; the browser does not infer arbitrary set types, subtype coercions,
or local definitions from prose.

Issue #10's small formal core in `lean/Scoped.lean` uses Nat expressions and
first-order propositions with substitution, denotation, and erasure laws. The
browser projection is deliberately partial. PR #65 adds explicit Nat
existentials and mixed-binder substitution checks; it does not serialize
arbitrary browser ASTs or Lean `Expr`, nor does it align proof routes.

Reviewed Mathlib fixtures cover compact images, subgroup closure, linear-map
additivity, continuous composition, same-typed local premises, and a dependent
`Fin (n + 1)` witness. They are acceptance examples, not broad coverage or
claims of natural-language fidelity.

## Current worktree: intuitionistic contradiction elimination

The independent `feat/intuitionistic-negation-elimination` worktree adds a
deterministic context rule for applying a visible `hnot : ¬ P` (or `P → False`)
to a matching `hp : P`. It produces `hnot hp : False`, or uses that term under
`False.elim` for another target. It does not derive `P` from `¬ ¬ P` and does
not use `Classical`. All 291 Node tests and 21 Python unit tests pass; Python
syntax and `git diff --check` pass. Exact Lean integration is running locally
with the available Lean 4.36 toolchain; repository-pinned Lean 4.19 and browser
CI remain required.

## Verification boundary

Parsing, candidate generation, structural compatibility, open proof
obligations, Lean elaboration, kernel checking, and author-intent fidelity are
separate states. A renderable candidate is not a checked proof or a fidelity
claim. Surface AST comparison is conservative and is not Lean definitional
equality. Lean InfoTree ranges and term references are observations from
elaboration, not author-intent alignments or a complete logical dependency
graph.

## Next dependency-ready work

1. Resolve PR #64's exact browser test, then merge only after exact-head Full
   Tests and Mathlib pass; verify main and Pages afterward.
2. Rebase or retest PR #65 on the resulting main, then merge only after its
   exact-head Full Tests and pinned Mathlib pass.
3. Finish and submit the current intuitionistic contradiction-elimination
   rule with Lean-backed integration and focused candidate tests.
4. Extend Issue #9 with a reviewed real analysis or subspace proof and an
   explicit expected dependency set.
5. Continue local region alignment and branch-level incremental reuse; compare
   each edited scoped result with a cold recomputation.

The original eight-stage order in `IMPLEMENTATION_ORDER.md` remains
authoritative: representation, identity, partial graph, candidate forest,
mathematical inference, incremental evaluation, bidirectional projection, and
acceptance. Later work does not replace that dependency order.
