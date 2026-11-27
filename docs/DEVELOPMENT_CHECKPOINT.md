# LeanDuet development checkpoint

Updated 2026-11-27. This checkpoint follows the dependency order in
`IMPLEMENTATION_ORDER.md`; the eight-stage sequence is unchanged.

## Current mathematical focus

The active line of work is stage 2/3: tree-scoped proof contexts, local object
identity, and the propagation of open proof obligations through case branches.
The browser draft is a semantic editor for a bounded grammar. A translated or
complete draft is still only a Lean candidate; it is not a compilation result
or a claim that the author's mathematical intent has been captured.

## Completed and in flight

- PR #21 established bounded binary disjunction elimination with nested branch
  scopes and branch-local identities.
- PR #22 is merged as `0eaf7dd` (head `73af927`). It preserves physical source
  lines through branch bodies, checks terminal annotations against residual
  goals, closes branch-local names at the scope boundary, and checks the final
  proposition against the remaining goal. Both CI runs for that head passed.
- PR #23 (`research/partial-case-continuations`, feature commit `0a685a9`,
  browser follow-up `08713e0`) keeps parent continuation rows in the semantic
  graph while a branch is open. The common result is provisional, dependent
  rows remain marked open, branch names do not escape, no Lean term is exported,
  and the final goal check still runs. Local verification: 185 Node tests, 17
  Python unit tests, and Python syntax compilation passed. Latest CI exercises
  Lean integration and the editor's partial-branch interaction.
- PR #24 (`68a3d0c`) adds repeatable cold, warm, single-character, local
  dependency-edit, and nested-case timing with structural comparison against a
  fresh evaluation. One local run used Node 24.22.3 on Linux x64 / AMD EPYC
  9V74 (24 warmups, 160 samples): cold 0.179/0.774 ms median/P95; warm exact
  replay 0.198/0.650 ms; one-character final-premise edit 0.178/0.508 ms;
  local dependency edit 0.198/0.483 ms; 41-line, eight-level case draft
  2.639/4.279 ms. This single synthetic run does not establish a speedup or a
  real-world latency guarantee.
- PR #25 (`f37c313`) adds intuitionistic negation introduction for `¬ P` and
  `Not P`, leaving `False` as the residual goal, and tests explicit
  `False.elim` separately. No classical axiom is inserted. The generated Lean
  cases are in CI; local verification reached 187 Node tests and 17 Python unit
  tests, while this environment has no Lean executable.

## Actual boundaries

- Case analysis accepts only an explicit binary `Or` split with both arms in
  order, bounded to eight nested splits and 64 nonblank lines.
- A branch-local binder must currently use a name fresh in its parent context;
  sibling branches may reuse a display name while retaining different IDs.
- Case blocks are fully reevaluated after edits. Branch-level prefix reuse is
  not implemented or claimed.
- Formula matching is a conservative structural check modulo bound-variable
  renaming. It is not Lean definitional equality or elaboration.
- An open branch may still expose useful continuation structure, but it cannot
  yield an executable proof candidate until all dependencies close.
- Negation introduction only handles the intuitionistic `P → False` direction;
  proving `P` from `¬ P → False` requires an explicit classical principle.

## Next dependency-ready work

1. Finish CI for PRs #23–#25, merge only after the current heads pass, then
   verify main-branch tests and the Pages deployment.
2. Build reusable subgoal operations for local lemmas, conjunction/iff goals,
   and branch return, keeping `False.elim` explicit and classical reasoning
   opt-in.
3. Extend structural candidates from proposition types to mathematical
   operations, preserving ambiguity and distinguishing unsupported rules,
   missing information, incompatibility, and exhausted search budgets.
4. Align the existing Lean fixtures with human-reviewed prose across analysis,
   algebra, sets, and topology. Existing IR tests already cover dependent `Fin`
   witnesses, local lets, distinct same-type premises, universe-polymorphic
   limits, and a Mathlib compact-image example.
5. Return to stage 6/7 for local semantic patching and branch-level cache
   invalidation, comparing every incremental result with full recomputation.

## Research and roadmap relation

The scope work is grounded in the repository's Ranta/GF, Hazelnut, and
dependent-context notes; it does not replace the existing eight-stage order.
The candidate-structure work belongs after scope and object identity because
scope supplies the constraints needed to prune interpretations. Corpus and
latency evaluation remain acceptance tasks throughout later implementation.
