# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Verified repository state

- `main` is at `98405e14ff5790d7f20ddb66acd10857ab4761c2`, including merged
  PR #22 (scoped source positions, residual-goal checks, and local-name expiry)
  and PR #43 (constructive ex-falso from an explicit `False` premise).
- PR #22 is closed and merged at `0eaf7dd608579e442c5f1c3b835a83c558f75348`.
- The open research stack is #37 → #38 → #39 → #40 → #42. Their downstream
  branches still target older stack heads and must be synchronized and tested
  after each dependency lands.
- PR #37 is based on current `main`, head
  `02adf00f65241bc360cfcfa6e2888fde2845542a`. The Tests run
  `46063313266` and Mathlib integration run `46063313286` are in progress.
  An earlier run exposed a malformed Python integration fixture introduced
  during stack synchronization. The truncated ex-falso line and orphaned
  duplicate suffix are repaired on the current head; the new runs are the
  validation for that repair.
- PR #38 previously failed browser smoke on an outdated base; #39 has no CI
  run on its latest head. #40's older Mathlib run passed but its full workflow
  failed in the browser path. #42's benchmark step ran, but its full workflow
  inherited the same browser failure. None of those old results validates the
  current dependency stack.

## Mathematical work and limits

The scoped proof model now carries parent binding identities into child goals,
isolates sibling declarations, checks a branch's terminal annotation against
its residual goal, expires branch-local declarations at closure, and returns
only dependencies already present in the parent. Conjunction, equivalence,
explicit existential goals, negation introduction, and ex-falso use
constructive operations; no classical axiom is silently introduced.

PR #37 adds a bounded structural candidate family for “take an element
satisfying …”: a matching universal goal may justify arbitrary introduction,
and a visible typed existential premise may justify witness extraction.
Remaining-goal constraints can remove incompatible readings. If the supported
evidence does not select one reading, the request stays open and creates no
local binding until a user chooses. This is a small candidate family, not a
general shared parse forest. Local definitions, subtype coercions, general
implicit quantifiers, Lean definitional equality, and unique author-intent
recovery remain outside its scope.

## Verification boundary

JavaScript and Python suites passed on an earlier PR #37 revision, as did
syntax checks. They do not validate the current fixture repair. Lean and
Playwright Chromium are unavailable in the local work environment, so generated
Lean and browser interaction require green repository workflows. Synthetic
latency measurements are documented in the PR and are not browser performance
guarantees. The current GitHub Pages deployment has not been independently
verified.

A structurally complete draft is only an exportable candidate. It is not, by
that fact alone, elaborated by Lean, kernel-verified, or confirmed faithful to
the author's mathematical intent.

## Next dependency-ready tasks

1. Check both workflows on PR #37 head `02adf00`; inspect the Python/Lean
   integration and browser-selection path. Merge only after both are green.
2. Rebase/synchronize PR #38 on the merged #37 and resolve the outstanding
   identity issue conservatively: bounded-set references must resolve to one
   visible object identity, not merely a matching displayed name.
3. Review PR #39's local-lemma closure contract and its identity behavior under
   shadowing, siblings, incomplete subproofs, and edits; run full workflows.
4. Validate #40's compact-image and subgroup cases against pinned Mathlib and
   the extracted dependency graph.
5. Rerun #42's benchmark and cold-vs-incremental equality checks on the final
   stack. Report per-case medians and P95 honestly, including edits where
   incremental work is slower.
6. Add the next reviewed analysis or linear-algebra case with prose,
   semantic graph, Lean compilation, and a local-edit regression.

This checkpoint follows the original eight-stage dependency order:
surface semantics → identity → partial graph → candidate forest →
mathematical inference → incremental evaluation → bidirectional projection →
representative acceptance. Later stages remain partial; no stage is claimed
complete.
