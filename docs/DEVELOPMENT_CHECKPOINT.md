# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Upstream and review state

The latest observed `main` is `324411b`, the squash merge of PR #35. PR #22
and PRs #32–#35 are merged. PR #36 (`ee64768`,
`research/goal-operation-extensions`) is based on this `main`; its Mathlib
workflow passed, but its complete Tests workflow exposed a browser smoke
failure: after adopting a new existential theorem, the test filled `#chainText`
while its enclosing editor was collapsed. This is fixed on PR #36 at head
`4a6628a`; the workflow for that new head must pass before merge. The failed
run passed JavaScript, Python, Lean models, backend integration and generated
Lean integration; only the browser smoke step failed.

The current local branch, `research/element-operation-candidates`, is based on
PR #36's prior head `ee64768` and contains the next stacked change, including
the same browser-test correction as #36. It is not yet on GitHub. Its
dependency is explicit: it uses the constructive equivalence and
existential child-goal operations introduced by #36 in neighboring integration
tests, while the operation-candidate resolver itself also reuses main's scope,
identity and existential-elimination machinery.

## Current mathematical problem

One short utterance such as “take an element `x` satisfying `P(x)`” can state
different mathematical operations. The current change models one shared
request with a bounded family of structurally justified readings: introduce a
variable from a matching universal goal, or extract a witness and evidence
from a visible typed existential premise. The goal and a later explicit
conclusion can constrain the family. If both readings remain possible, the
request remains unresolved and introduces no local object until the user
chooses. Object-source identity, rather than its displayed name, is part of
existential choice identity.

This is a narrow first step in original stage 4 (candidate forest), dependent
on stages 2–3 and the stage 5 proof-operation contract. It is not an unrestricted
shared parse forest or a general natural-language parser. Local definitions,
subtype objects, unresolved existence proofs and arbitrary quantifier inference
remain unimplemented.

## Verification

- JavaScript unit suite: 238/238 passed after the candidate-graph null-selection
  regression was fixed.
- Python unit suite: 17/17 passed.
- Python byte-compilation and `git diff --check`: passed before the latest docs
  and benchmark edits; rerun before commit.
- Opt-in synthetic benchmark: Node v24.22.3, Linux x64, 24 warmups and 160
  samples; candidate evaluation over 50 typed context entries measured 0.678 ms
  median / 1.124 ms P95 cold and 0.461 / 0.735 ms on exact replay. A property
  edit measured 0.622 / 1.148 ms; adding another existential premise measured
  0.696 / 1.162 ms. Every incremental case matched a fresh full evaluation.
  These are synthetic local measurements, not browser latency guarantees.
- Local Playwright is installed but its Chromium executable is absent; Lean is
  also absent locally. The new real Lean compilation and browser interactions
  therefore require CI. PR #36's Mathlib CI passed; its full workflow remained
  in progress at the last status check.

## Next dependency-ready work

1. Finish local review of the candidate family and its acceptance fixtures;
   rerun all tests and the benchmark, then publish the stacked change as PR #37.
2. Wait for #36's latest full workflow, review its final head and merge only
   after Lean and browser checks pass. Retarget #37 to `main` afterward and
   rerun its workflows against the merged base.
3. Audit the shared goal-operation contract for proof-local assumptions,
   conjunction/iff children, and return behavior before adding another
   operation. The intuitionistic negation introduction subset is already
   present; classical reductio and general local-lemma blocks are not.
4. Add one reviewed real analysis or linear-algebra proof fixture with prose,
   semantic structure, Lean compilation, and local-edit regression coverage.

## Boundaries

`complete` still means only that the bounded structure can render a Lean
candidate. It does not establish Lean elaboration, kernel verification,
author-intent fidelity, or mathematical correctness. Formula compatibility is
conservative scoped surface structure, not Lean definitional equality. The
current operation resolver recognizes only a small English/Chinese phrase
fragment and scans at most 64 local entries; more than eight candidates reports
budget exhaustion rather than truncating. Typed object dependencies and proof
dependencies remain distinct. Browser goal conversion, backend inference and
Lean's final validation are separate paths.
