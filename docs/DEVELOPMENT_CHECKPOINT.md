# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Repository and PR state

The latest observed `main` is `c99c14c`, which includes merged PR #36. PR #22
is merged as `0eaf7dd`; it preserves physical source addresses in nested
branches, checks terminal branch annotations against the residual goal, and
expires branch-local names after closure. The original eight-stage order in
`IMPLEMENTATION_ORDER.md` remains authoritative.

PR #37 (`research/element-operation-candidates`, head `fe4556f`) keeps
universal-variable introduction and existential witness extraction as distinct
structural candidates for “take an element satisfying …”. Its Mathlib
integration run `46026642155` passed. Tests run `46026642256` is in progress;
the earlier browser failure came from clicking a target inside collapsed
`details`. The current head locates the typed hypothesis by its formula and
term, opens the ancestor chain, and still needs a complete browser run before
merge.

PR #38 (`research/bounded-element-operations`, head `0c2008a`) adds bounded
universal introduction and restricted existential extraction. Its Mathlib
integration run `46026943713` passed. Tests run `46026943572` is in progress;
the earlier head failed on the same collapsed-node click, so this head selects
the intended binder/hypothesis nodes and opens their ancestors. It remains
stacked on #37 and must be retargeted to `main` after #37 is integrated, then
revalidated.

The local `research/local-lemma-scopes` work adds an explicit named local
subproof block to the latest #38 head. It is not yet committed or published as
a PR. Keep it stacked on #38 until that dependency is merged and checked.

## Mathematical contract and current work

A local lemma has the explicit bounded syntax `local lemma h : $P$`, followed
by an indented `proof` block (Chinese: `局部引理 h : $P$`). It forks a child
goal that inherits the parent's object identities. Closing it checks the
child's target against the stated proposition, discharges child-local
identities, and returns only parent dependencies and the new proposition.
An unfinished proof remains in the graph, and subsequent rows may be analyzed
as depending on the open lemma, but no complete Lean candidate is exported.
A structurally closed child that depends on an upstream open object remains an
unverified candidate with that dependency marked open. This extends stage 2's
scope/closure mechanism and gives stage 3+ a reusable local claim operation; it
is not free-language lemma invention or proof verification.

The element-operation candidate pair advances stage 3 while preserving the
same phrase and candidate identity. The set-restricted forms retain membership
as an explicit premise/evidence and require a stated element type. The carrier
check is limited to visible simple identifiers; coercion and compound-carrier
inference remain unsupported. These additions do not replace or reorder the
eight-stage plan.

## Local verification

- JavaScript unit suite: 257/257 passed, including 10 local-lemma scope,
  lifecycle, identity, and incremental-versus-cold tests.
- Python unit suite: 19/19 passed, including local-lemma backend-shape and
  rejection checks.
- `py_compile`, `node --check` on touched modules, and `git diff --check`
  passed.
- The repeatable draft benchmark passed its incremental-versus-cold equality
  assertions (Node v24.22.3, Linux x64, 24 warmups / 160 samples). For the
  local-lemma fixture with 51 typed locals: cold evaluation was 1.653 ms
  median / 2.329 ms P95; exact replay was 0.333 / 0.588 ms; a one-premise
  edit was 1.836 / 2.629 ms; a leading-line shift was 1.897 / 2.425 ms.
  Structural lemma edits still recompute the bounded block; these are local
  synthetic measurements, not browser response guarantees.
- Generated local-lemma Lean has not yet been compiled in this workspace.
  The browser smoke also has not run locally because Chromium is unavailable;
  the new browser workflow test must pass on the PR head before merge.
- The Mathlib integration now has a real compact-image local-lemma fixture:
  it exercises both browser candidate generation and backend scope return,
  then asks the pinned Mathlib toolchain to compile the generated theorem.
  This remote integration result is pending.
- The earlier #37 synthetic candidate-evaluation benchmark predates the
  bounded-quantifier extension. It is not a browser-latency measurement and
  is not updated by the local-lemma change.

## Next dependency-ready work

1. Let the latest #37 Tests run reach browser smoke and finish; repair concrete
   failures, then merge only with both required workflows green.
2. Retarget #38 to `main` after #37 merges, rerun CI on the updated head, and
   merge only after generated Lean and browser paths pass.
3. Finish reviewing the local-lemma child/parent dependency boundary, add the
   current tests and docs to the PR branch, and require full browser plus Lean
   CI before merge.
4. Continue stage 2 by auditing explicit `False` elimination and the boundary
   between intuitionistic negation introduction and classical reductio; do not
   add a classical principle implicitly.
5. Continue stage 8 with one reviewed analysis or linear-algebra proof fixture
   containing authored prose, an expected semantic graph, Lean code, and local
   edit checks. Keep Lean compilation distinct from informal fidelity.

## Boundaries

`complete` means only that the bounded browser structure can render a Lean
candidate. It does not assert elaboration, kernel verification, author-intent
fidelity, or mathematical correctness. Surface formula matching is
scope-aware but is not Lean definitional equality. Missing context, unsupported
rules, inconsistent constraints, unresolved candidates, and exhausted search
remain distinct. The browser graph, backend inference, and Lean validation are
separate layers. Local-lemma blocks are currently recomputed as a whole after
structural edits.
