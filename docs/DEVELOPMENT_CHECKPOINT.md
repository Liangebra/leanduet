# Development checkpoint

Updated 2026-11-28 (UTC).

## Repository state

- `main` is `907404d26c5187f96922a54dd264446f284bce1f`. PR #21 and PR #22 are
  merged; #22's source-line mapping, residual-goal matching, and local-object
  lifetime fixes are in this baseline.
- PR #61 (typed-context substitution checks) is merged at
  `dc3faf8576e97e532d84d3783f5bbc632c079d46`. PR #63 (real-analysis proof
  refactoring counterexample) is merged at the current `main` head. PR #62 was
  closed as a duplicate of #63.
- PR #64 adds explicit bounded induction on `∀ n : Nat, P n`. Exact-head Tests
  run `46122850837` failed in the browser smoke path: the selected target still
  reached the planner as a non-universal goal. The test now selects the exact
  elaborated target type; its new exact-head Tests run `46124889627` and pinned
  Mathlib run `46124889639` are in progress. The previous Mathlib run
  `46122850830` passed, but does not validate the new head.
- PR #65 adds an initial explicit-Nat existential fragment for Issue #10. Its
  first exact-head Full Tests run `46123531543` failed before browser execution
  because `tests/browser_smoke.py` contained a malformed assertion string; the
  pinned Mathlib run `46123531595` passed. The corrected browser file retains
  the existential projection regression and removes an unrelated Nat-induction
  case that is not supported by PR #65's base branch. CI must rerun on the
  corrected head before merge.
- The latest verified main checks after PR #63 were Full Tests
  `46120595641`, pinned Mathlib `46120595602`, and Pages deployment
  `46120595644`; all passed.

## Current semantic capabilities and limits

Proof scopes are trees. Child goals inherit parent identities; branch-local
objects are isolated from siblings and expire on closure; branch results must
match the residual goal before returning to the parent. Universal and
implication introduction, intuitionistic negation introduction, explicit
ex-falso, disjunction elimination, conjunction and equivalence introduction,
explicit existential witnesses, local lemmas, and named classical reductio
have separate scope-aware operations. Natural-number induction is limited to
an explicit universal Nat goal and remains under PR #64 review. No classical
principle is inserted implicitly.

Natural-language parsing keeps supported interpretations as candidates when
the context does not decide between them. Candidate readiness, an open proof
obligation, Lean elaboration, kernel checking, and author-intent fidelity are
separate states. A structural candidate is not a verified proof or a fidelity
claim. Name resolution is lexical and identity-based; ambiguous repeated
source occurrences are left unmatched rather than assigned an invented
identity.

The Mathlib fixtures cover set membership, compact images, subgroup closure,
linear-map additivity, continuous composition, derivatives, and proof-shape
counterexamples involving local lets, dependent `Fin` witnesses, and distinct
same-typed premises. These are reviewed acceptance examples, not broad
natural-language coverage. The synthetic incremental benchmark compares
cached results with cold evaluation; its measurements do not establish general
browser latency or a general speedup.

## Issue #10: scoped semantic fragment

`lean/Scoped.lean` defines a typed syntax of Nat expressions and propositions,
with capture-avoiding substitution, a shallow denotation into `Nat` and `Prop`,
and erasure into the generic `Scoped.Term`. The browser exposes a versioned
partial projection for closed formulas and explicitly typed Nat contexts.
Before the current work, the typed formula fragment supported only universal
quantification. The in-progress extension adds explicit Nat existentials,
checks substitution under mixed binders and context replacement, and compiles
the denotation and erasure laws. The existential denotation equality uses
propositional extensionality; it does not identify proof terms. Local checks
passed with Lean 4.36.0, 296 Node tests, 21 Python unit tests, and
`tests/ir_integration.py`; CI with the repository's pinned Lean 4.19.0 remains
required.

This is not a serialization of arbitrary browser syntax or Lean `Expr`. It
excludes dependent domains, general predicates, arbitrary constants, partial
terms, the full Lean type system, and a proof-route alignment. Syntax equality,
Lean definitional equality, and proof-term irrelevance remain distinct.

## Next work

1. Finish and merge PR #64 only after its exact-head browser smoke and full
   Tests workflow pass; verify main checks and the Pages deployment afterward.
2. Submit the explicit Nat-existential extension for Issue #10 as its own PR,
   preserve the exact Lean 4.19 CI result, and update this checkpoint with the
   merged commit.
3. Continue Issue #9 with reviewed analysis or subspace examples whose expected
   dependency closure and Lean compilation are checked separately from prose
   correspondence.
4. Extend structure-level operation candidates only where a typed context or
   goal constraint can propagate across alternatives without collapsing
   distinct object or proof identities.
5. Improve local bidirectional alignment and branch-level incremental reuse;
   require edited results to match a cold recomputation and preserve unrelated
   author wording.

The original eight-stage dependency order remains in
`docs/IMPLEMENTATION_ORDER.md`: representation and identity, scopes, candidate
constraints, declaration dependencies, proof fidelity, bidirectional edits,
incremental evaluation, then broad mathematical acceptance. Later-stage work
does not replace that order.
