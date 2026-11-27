# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Active work

Main is based on `4f9f925` (PR #29). PR [#22](https://github.com/Liangebra/leanduet/pull/22) and [#29](https://github.com/Liangebra/leanduet/pull/29) are merged. PR #29's Mathlib workflow and full test workflow passed; its set-image case generates and compiles an `IsCompact.image` candidate with the required continuity and compactness premises.

PR [#32](https://github.com/Liangebra/leanduet/pull/32) adds explicit semantic-resolution states and composes ordinary inference lines with multiple binary-disjunction blocks, including a linear prefix inside a branch. The scope parser carries physical line offsets; each branch receives a lexical child scope; only a common branch result returns to its parent. An unresolved prefix remains represented and prevents structural completion while later blocks remain available. The first browser run failed because its fixture exceeded the Lean extractor's depth limit; the theorem was shortened in commit `0907149`, then its natural-language types were aligned with the shortened Lean context in commit `00b870b`. The Mathlib job passed on `0907149`, but the new head `00b870b` has fresh CI running. On the earlier head, the Tests workflow passed the unit suites, Lean model files, semantic/search/LSP integrations and generated Lean interpretation fixtures; the corrected browser smoke has not yet completed.

The local `research/scoped-draft-cache` worktree adds bounded scope-local row caches and a root-level exact-result cache for scoped programs. Cache keys include lexical binding identities, names, types and kinds, goals, source offsets, choices, closed names, open obligations, and continuation status. Nested cache state is LRU-bounded to 128 scope entries; exact root results are bounded to 32 entries. Reset clears both. Tests compare edited results with cold evaluation and cover changed parent identity, a newly added same-typed candidate (a negative dependency), and mutation isolation for memoized results.

This continues stage 2 and stage 7 of the original eight-stage order; PR #32 also makes progress on stage 3 by exposing distinct resolution states. No general natural-language parser, arbitrary inductive elimination, or broad Lean type inference is introduced.

## Checked local state

- In the cache worktree: Node suite 209/209; Python unit suite 17/17; Python byte-compilation and `git diff --check` passed.
- The Lean executable and Chromium are not installed in this local workspace. The PR #32 GitHub run is the source of Lean and real-browser evidence; its browser step must complete on the corrected fixture before merge. The cache changes are JavaScript-only and still require CI after a PR is opened.
- `tests/draft-benchmark.mjs` checks incremental/cold structural equality across 160 samples per case after 24 warmups, on Node v24.22.3 / Linux x64. In the latest run, medians/P95 in ms were: linear 16-line cold `0.362/1.609`; linear replay `1.377/2.552`; final-line edit `1.235/1.960`; dependency edit `1.216/1.955`; 8-level, 41-line case program cold `6.673/8.618`; exact replay `1.273/1.568`; one branch conclusion edit `7.596/9.163`; two-case interleaving cold `2.296/2.981`; interleaving terminal edit `2.908/3.702`.
- A prior no-scope-cache run of the same nested-case evaluation measured `6.186/8.503` ms; exact replay in the cache run is `1.273/1.568` ms. Treat this as a synthetic local comparison, not a general performance guarantee. Small linear replay and structural edits show no speedup in these samples; the cache work must not be described as making every edit faster.

## Semantic boundaries

Case analysis remains explicit binary `Or` elimination, bounded to eight nested splits and 64 nonblank lines per program; each ordinary segment retains its 16-inference-line bound. `complete` means only that this bounded structure can be rendered. It does not imply Lean elaboration, kernel verification, or semantic fidelity. Formula compatibility remains conservative surface structure, not Lean definitional equality. Scope IDs and line IDs are revision-local. Edited branch bodies may reuse unchanged rows, but the current graph is rebuilt; the benchmark does not show that branch edits run faster.

## Next dependency-ready tasks

1. Finish PR #32's corrected browser smoke and full CI, review the latest diff, merge only if all checks pass, then verify main and Pages deployment.
2. Rebase the local scope-cache work on the merged head, run its CI, and submit it separately with the measured limits above.
3. Generalize proof operations around child goals, context extension and closure; begin with conjunction introduction, then add intuitionistic negation introduction and contradiction elimination without silently adding classical axioms.
4. Add structure-level candidates for “take an element satisfying …”, keeping arbitrary-variable introduction, witness extraction, definition, subtype introduction, and an open existence obligation distinct.
5. Add a reviewed analysis or linear-algebra proof to the small real-math corpus, with source language, expected structure, generated Lean, and independent compilation.

The existing aligned corpus includes predicate-set operations and a compact-image Mathlib example. LeanReviewBench's statement-only material should be used only to extract error mechanisms, not as proof-body ground truth.
