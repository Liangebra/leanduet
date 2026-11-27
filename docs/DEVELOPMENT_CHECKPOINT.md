# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Repository and upstream review

Main's latest observed commit is `e17fe92`. It includes merged PRs [#22](https://github.com/Liangebra/leanduet/pull/22), [#32](https://github.com/Liangebra/leanduet/pull/32), [#33](https://github.com/Liangebra/leanduet/pull/33), and [#34](https://github.com/Liangebra/leanduet/pull/34). PR #22 preserves branch source positions, checks conclusions against residual goals, and prevents branch-local declarations from escaping. PR #32 composes sequential scoped case blocks; PR #33 adds identity-aware scoped caches; PR #34 makes one compact-image Mathlib case a shared JavaScript/Lean corpus fixture.

PR #34's Mathlib integration and complete test/browser workflow passed on head `517b74f` (runs 46001497049 and 46001497038). PR #35 adds scoped conjunction child goals. Its latest head is `8b02858`; the Mathlib workflow passed (run 46005423369) and its complete Tests workflow (run 46005423224) is in progress. A prior run on a superseded head failed in the JavaScript step; the current remote tree was then restored from the local snapshot and every one of its 20 changed files was fetched back and compared with that snapshot. Do not use the superseded run as evidence about the current head.

## Current proof-operation work

PR #35 defines a shared child-goal compiler for conjunction introduction. Parent identities flow into child scopes, sibling declarations remain isolated, and child locals are discharged when a subgoal closes. Structural exportability stays distinct from proof closure; `exact?` remains an open obligation.

The local stacked extension adds constructive equivalence introduction and explicit existential introduction to that same contract. Equivalence opens both implications without classical axioms. Existential construction requires a uniquely visible typed local object, checks explicit domains by conservative formula structure, carries the witness identity and dependencies of its dependent type, and leaves the predicate as a child obligation. It does not infer or search for a witness. Capture, unknown or ambiguous witnesses, and surface-type mismatches are rejected.

Local verification for this extension:

- `node --test tests/*.test.mjs`: 225/225 passed.
- `python -m unittest discover -s tests`: 17/17 passed.
- Python byte-compilation and `git diff --check`: passed.
- `tests/static_browser.py` could not start because the local Playwright Chromium executable is absent; the repository CI must validate the browser path.
- Lean is not installed locally; generated conjunction/equivalence/existential terms are covered by the interpretation integration intended for PR CI.

This advances stage 2 of the original eight-stage order. It also tests stage 7's incremental-versus-cold consistency on an edited equivalence child. It does not establish general name/type resolution, Lean elaboration, kernel correctness, or semantic fidelity.

## Next dependency-ready work

1. Finish PR #35's current full workflow, inspect the head and review threads, then merge only if unit, Lean, and browser checks pass.
2. Open the local goal-operation extension as stacked PR #36; require its generated Lean and browser smoke to pass, then update its base after #35 merges.
3. Add structure-level candidates for arbitrary elements, existential witnesses, local definitions, subtype objects, and unresolved existence. Preserve distinct interpretations and let typed context constrain them.
4. Add a reviewed real analysis or linear-algebra proof fixture with source language, expected structure, Lean compilation, and local-edit regressions.

## Current boundaries

`complete` means only that this bounded structure can be rendered. It does not imply Lean elaboration, kernel verification, author-intent fidelity, or mathematical correctness. Formula compatibility is conservative surface structure, not Lean definitional equality. Goal and case scopes are limited to eight nested levels and 64 nonblank block lines. General local-lemma return, classical reductio, arbitrary inductive elimination, full Lean type resolution, and broad real-mathematics coverage remain open.
