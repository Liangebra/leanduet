# Development checkpoint

Updated 2026-11-27 (UTC).

## Current repository state

- `main` includes merged PR #22 (scoped source positions, residual-goal checks, and branch-local name expiry), PR #43 (constructive ex-falso from an explicit `False` premise), and PR #37 (bounded structural alternatives for universal introduction and existential witness extraction).
- PR #37 merged at `07905c568e91783e95696b3567f5644d829710ca`. The Tests workflow `46063313266` and Mathlib integration workflow `46063313286` passed on the repaired code head before merge.
- PR #38 develops set-restricted element operations. Its original branch targets an older stacked base. The current patch carries its set-identity and ambiguity fixes onto the merged main tree; validation must run on this synchronized head before merge.
- PRs #39, #40, and #42 depend on the earlier stack and have not yet been validated against this synchronized series.

## Mathematical and engineering state

Proof scopes are trees. Parent object identities are inherited by child goals; sibling locals remain isolated; branch conclusions must match residual goals; local declarations expire on closure; only parent-visible dependencies may return. Conjunction, equivalence, existential construction, negation introduction, and ex-falso are represented as constructive goal operations. Classical reductio is not silently added.

Element-operation ambiguity is represented by distinct bounded candidates rather than a forced parse. A matching universal goal supports arbitrary introduction; a typed existential premise supports witness extraction. Later supported goals can constrain candidates. An unresolved request introduces no speculative object.

The set-restricted extension recognizes explicit element requests such as “take an arbitrary element x : Nat in A satisfying P(x)” and their Chinese counterpart. It preserves the set restriction, requires a displayed element type, checks a known local set carrier when available, tracks referenced local set identities in the choice key and dependency graph, and rejects duplicate visible names. For `∃ x ∈ A, P x`, the witness evidence includes both membership and the requested property. These rules are surface-level and conservative; Lean still must elaborate the generated term.

## Verification boundary

A structurally exportable draft is not, by itself, Lean elaboration, kernel verification, or confirmation of author intent. Formula comparison is conservative structural comparison, not general definitional equality. The editor does not infer set carriers from an arbitrary global Lean environment unless that information is present in the local context. The current browser and Mathlib workflows are the validation gate for this PR.

## Next dependency-ready work

1. Run the full Tests/browser workflow and the pinned Mathlib integration on the synchronized PR #38 head. Review any generated bounded-universal and bounded-existential terms at the Lean boundary.
2. Rebase/synchronize PR #39 and check local-lemma scope closure under shadowing, siblings, incomplete proofs, and edits.
3. Validate PR #40's compact-image and subgroup corpus cases against the pinned Mathlib environment and dependency extraction.
4. Rerun PR #42's cold-versus-incremental benchmark on the final stack; report per-case medians and P95, including edits where caching loses.
5. Add one reviewed analysis or linear-algebra example with prose, semantic structure, Lean compilation, and a local-edit regression.

The original eight-stage order remains authoritative: surface semantics → identity → partial graph → candidate forest → mathematical inference → incremental evaluation → bidirectional projection → representative acceptance. The work here primarily advances scope/context handling and structural operation candidates; it does not complete any whole stage.
