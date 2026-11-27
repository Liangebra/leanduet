# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Active work

Main is at merge commit `06e6c1d`, which includes PRs [#22](https://github.com/Liangebra/leanduet/pull/22), [#29](https://github.com/Liangebra/leanduet/pull/29), and [#32](https://github.com/Liangebra/leanduet/pull/32). PR #32's latest head `00b870b` passed the full Tests workflow, browser smoke, and Mathlib topology integration before merge.

PR [#33](https://github.com/Liangebra/leanduet/pull/33) adds bounded per-scope row-prefix caches and exact replay memoization for scoped proof drafts. Cache keys include lexical binding identities, names, types and kinds, goals, source offsets, choices, closed names, open obligations, and continuation status. Nested cache state is LRU-bounded to 128 scope entries; exact root results are bounded to 32 entries. Reset clears both. Tests compare edited results with cold evaluation and cover changed parent identity, a newly added same-typed candidate (a negative dependency), and mutation isolation for memoized results.

This continues stage 2 and stage 7 of the original eight-stage order; PR #32 also advances stage 3 by exposing separate resolution states. No general natural-language parser, arbitrary inductive elimination, or broad Lean type inference is introduced.

The base already supports intuitionistic negation introduction in a linear draft: assuming `P` under goal `¬ P`/`Not P` leaves `False`, and the fixture requires an explicit contradiction proof such as `hnot hp`. `False.elim` is handled separately. This does not yet provide a reusable nested child-goal scope for arbitrary local subproofs.

## Checked local state

- Cache worktree: Node suite 209/209; Python unit suite 17/17; Python byte-compilation and `git diff --check` passed.
- PR #33 head `6ca0a86`: Mathlib topology integration and full Tests workflow passed against main `06e6c1d`. The local environment has no Lean executable or Chromium; compiler and browser evidence comes from CI.
- `tests/draft-benchmark.mjs` checked incremental/cold structural equality across 160 samples per case after 24 warmups, on Node v24.22.3 / Linux x64. Latest medians/P95 in ms: linear 16-line cold `0.362/1.609`; linear replay `1.377/2.552`; final-line edit `1.235/1.960`; dependency edit `1.216/1.955`; 8-level, 41-line case program cold `6.673/8.618`; exact replay `1.273/1.568`; one branch conclusion edit `7.596/9.163`; two-case interleaving cold `2.296/2.981`; interleaving terminal edit `2.908/3.702`.
- A prior no-scope-cache run of the same nested-case evaluation measured `6.186/8.503` ms. Treat this as one synthetic comparison, not a general performance guarantee. Small linear replay and structural edits show no speedup in these samples.

## Semantic boundaries

Case analysis remains explicit binary `Or` elimination, bounded to eight nested splits and 64 nonblank lines per program; each ordinary segment retains its 16-inference-line bound. `complete` means only that this bounded structure can be rendered. It does not imply Lean elaboration, kernel verification, or semantic fidelity. Formula compatibility remains conservative surface structure, not Lean definitional equality. Scope IDs and line IDs are revision-local. Edited branch bodies may reuse unchanged rows, but the current graph is rebuilt; the benchmark does not show that branch edits run faster.

## Next dependency-ready tasks

1. Recheck PR #33 on its current main base and merge only with every required check green; verify the resulting main workflows.
2. Generalize proof operations around child goals, context extension and closure. Reuse the current negation rule, then add conjunction subgoal splitting and local subproof return without classical axioms.
3. Add structure-level candidates for “take an element satisfying …”, keeping arbitrary-variable introduction, witness extraction, definition, subtype introduction, and an open existence obligation distinct.
4. Expand the real-math corpus with a reviewed analysis or linear-algebra proof, including natural language, expected structure, generated Lean, and independent compilation.
5. Improve branch-level incremental reuse only when cold-result comparisons establish equivalence; current measurements are a baseline, not a speed target.

The existing aligned corpus includes predicate-set operations and a compact-image Mathlib example. LeanReviewBench's statement-only material should be used only to extract error mechanisms, not as proof-body ground truth.
