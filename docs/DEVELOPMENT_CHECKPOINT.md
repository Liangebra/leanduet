# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Repository and PR state

The latest observed `main` is `324411b`, which includes PR #35. PR #22 is
merged; its branch-source positions, residual-goal checks, and branch-local
declaration lifetime rules remain in the current base. The original eight-stage
implementation order is unchanged.

PR #36 adds equivalence and explicit existential child goals. Its branch now
contains a two-parent synchronization commit, `3e390ca`, with current `main`;
the merged tree preserves the PR implementation and resolves the textual
overlap with #35. The current Tests workflow is queued as run `46016092798`.
Mathlib integration run `46016092675` passed. Tests run `46016092798` has
passed unit, Lean model, backend and generated-Lean steps; browser smoke is
still running. Merge only after that step and the complete workflow pass.

PR #37 adds bounded structural candidates for element requests. Its latest
head is `96a2488`. At the preceding head, the Mathlib workflow passed, but the
full workflow failed in browser smoke at `tests/browser_smoke.py:259`: the new
fixture used `:= hall`, while this editor accepts theorem bodies in `:= by`
form. The fixture now uses `by / exact hall` and the local Lean-source parser
accepts it. Tests run `46016046831` passed unit, Lean model and backend
integration steps; browser smoke is still running. Mathlib run `46016046804`
passed. PR #37 still needs its base refreshed after #36 is integrated.

PR #38 (`ac24373`) publishes the next layer on top of #37. Its Tests workflow
`46017119145` has passed unit tests and Lean model compilation; backend and
browser integration are still running. It remains stacked until #36 and #37
are merged.

## Mathematical contract and current capabilities

The element request keeps the utterance separate from its operational
readings. A matching universal goal can justify introducing an arbitrary
variable; a visible typed existential premise can justify witness extraction.
The source object's identity is part of the witness choice. If multiple
readings remain, the draft adds no speculative local object. Only supported
later structure may constrain a candidate. Local definitions, subtype
coercions, and open existence obligations are not inferred.

For the bounded subset, `∀ x ∈ A, P x` introduces `x` and leaves
`x ∈ A → P x`; the membership proof stays an explicit assumption. Extracting
from `∃ x ∈ A, P x` produces a witness and evidence of `(x ∈ A) ∧ P x`. The
request must explicitly name the set and annotate the element type. If a
visible set identifier has a simple known carrier (`Set`, `List`, `Finset`, or
`Multiset` applied to one type), an incompatible annotation is rejected. The
browser does not infer coercions or carriers for compound expressions. Lean
elaboration remains necessary.

This advances stages 2–4 of the original plan: the bounded subset reuses the
goal-operation and scope machinery from stage 2, and the distinct
universal/witness readings advance stage 3's structural ambiguity work. It is
not a general shared parse forest, type elaborator, or natural-language parser.

## Verification

- Local full JavaScript suite: 246/246 passed, including eight new bounded
  element tests and the existing scope, identity, and candidate regressions.
- Local Python unit suite: 17/17 passed.
- Python byte-compilation, `node --check` on changed modules, and
  `git diff --check` passed.
- Generated bounded Lean terms were inspected, and integration cases were
  added to compile them in CI. Lean is not installed in this workspace, so
  those new terms have not yet been independently compiled here.
- Playwright is installed, but no local Chromium executable is available.
  The previous remote browser failure and corrected fixture are recorded
  above; the new head's browser run is pending.
- The earlier #37 synthetic benchmark recorded 0.678 ms median / 1.124 ms P95
  for cold evaluation over 50 context entries, and 0.461 / 0.735 ms for exact
  replay (Node v24.22.3; 24 warmups, 160 samples). These figures predate the
  restricted-quantifier extension and are not browser-latency guarantees.

## Next dependency-ready work

1. Inspect run `46016092798` for #36. Merge only after its full Tests workflow
   passes, including Lean integration and browser smoke.
2. Let #37's latest Tests and Mathlib workflows finish; repair any concrete
   failure, then retarget it to `main` after #36 merges and rerun CI there.
3. Let #38's latest CI validate the generated bounded Lean terms and browser
   selection path. Keep the local carrier check explicitly partial.
4. Continue stage 2 with local-lemma return and classical reductio only after
   keeping intuitionistic negation introduction distinct. Continue stage 3
   with shared structural candidates and bounded constraint propagation.
5. Add a reviewed analysis or linear-algebra proof fixture with natural
   language, semantic structure, generated Lean, and local-edit regressions.

## Boundaries

`complete` means only that a bounded structure can render a Lean candidate. It
does not assert elaboration, kernel verification, author-intent fidelity, or
mathematical correctness. Formula matching is conservative scoped surface
structure, not Lean definitional equality. Candidate budget exhaustion,
missing context, unsupported interpretations, and incompatible choices remain
distinct outcomes. Browser conversion, backend inference, and Lean validation
are separate paths. Case and child-goal blocks retain their existing nesting
and line budgets.
