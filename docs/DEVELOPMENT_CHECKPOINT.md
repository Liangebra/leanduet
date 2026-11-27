# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Repository state

Main includes merged PRs [#22](https://github.com/Liangebra/leanduet/pull/22),
[#32](https://github.com/Liangebra/leanduet/pull/32),
[#33](https://github.com/Liangebra/leanduet/pull/33), and
[#34](https://github.com/Liangebra/leanduet/pull/34); latest observed main
commit is `e17fe92`. PR #22 preserves physical source addresses in branch
proofs, checks branch conclusions against residual goals, and keeps closed
branch-local names unavailable to later parent steps. PR #32 composes ordinary
proof lines with sequential scoped case blocks. PR #33 adds identity-aware
scoped caches with negative-dependency invalidation. PR #34 makes the compact
image Mathlib example a shared JavaScript/Lean corpus fixture.

On PR #34 head `517b74f`, Mathlib topology run 46001497049 and full Tests run
46001497038 both passed. The full run covered JavaScript and Python tests,
Lean models, semantic/search/LSP/interpretation integrations, and browser
smoke. Its merge commit is `e17fe92`; no post-merge main workflow run was
returned by the GitHub workflow lookup.

## Current implementation batch

Local commit `305fbee` on `research/goal-constructors` adds bounded
conjunction-goal compilation on the shared operation plan. Two sibling scopes
inherit parent identities but cannot see each other's local declarations;
local objects are discharged at closure. An `exact?` term remains an open
proof obligation. Nested identity reconciliation preserves unchanged child
choices after edits. This batch is being prepared as PR #35; it has not yet
received remote CI or Lean/browser validation.

Local verification on this commit:

- `node --test tests/*.test.mjs`: 221/221 passed.
- `python -m unittest discover -s tests`: 17/17 passed.
- Python byte-compilation and `git diff --check`: passed.
- Lean and Chromium are not installed locally; PR CI is required for generated
  Lean compilation and browser interaction.

The original eight-stage order remains in `IMPLEMENTATION_ORDER.md`. Current
work advances stage 2 and stage 7; the Mathlib fixture is a small stage 8 seed,
not broad domain coverage.

## Next dependency-ready work

1. Open PR #35 from the latest main-based commit, inspect current checks, and
   merge only after full unit, Lean, and browser validation pass.
2. Extend the same child-goal contract with constructive equivalence
   introduction and explicit typed-witness construction. Keep witness choice
   separate from existence proof and reject capture or ambiguous identities.
3. Add structure-level natural-language candidates for arbitrary element,
   existential witness, local definition, subtype object, and unresolved
   existence; preserve alternatives until later context constrains them.
4. Add a reviewed analysis or linear-algebra proof fixture and test generated
   Lean, semantic boundaries, and local-edit behavior independently.

## Current boundaries

`complete` describes bounded structural exportability only. It does not certify
Lean elaboration, kernel checking, author-intent fidelity, or mathematical
correctness. Formula matching is conservative surface structure rather than
Lean definitional equality. Branches and child goals are limited to eight
nested scopes and 64 nonblank block lines. General local-lemma return,
classical reductio, arbitrary inductive elimination, full Lean name/type
resolution, and broad real-mathematics coverage remain open.
