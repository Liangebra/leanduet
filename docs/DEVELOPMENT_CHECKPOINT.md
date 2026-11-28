# Development checkpoint

Updated 2026-11-28 (UTC).

## Current repository state

- Main is 0264ee19fe54adcb703e2aa7a820e9f169709406. PR #22's branch-scope, source-position, residual-goal, and local-object lifetime fixes are in the baseline.
- Recent merged work: #47 (resolved Lean InfoTree observations; merge dd0584450a603eb6f40f87b3614bbaa8e3cd4cc0), #50 (explicit classical reductio; 406f55773fc22f305a498ea7415dc1955a729721), #52 (function composition and continuous-composition fixture; 62dc2f65b3deb51992065e9093043480796dacd5), #54 (same-type proof dependency/local-let counterexample; ee3c75af4cdf29102bfcaea74545b65102903d73), #55 (browser formula binder/native IR regression; b1507a090e160239528ff58d201d380bca296c23), and #56 (dependent Fin witness refactoring case; 0264ee19fe54adcb703e2aa7a820e9f169709406).
- PR #44, the Urdu mathematical language pack, was merged independently as 64d35f05c82366a8756547780bc9cb260465551c. Its PR-head Actions did not provide runnable jobs; do not treat that as pre-merge CI validation. Post-merge main Full Tests 46104191470 and Pages deployment 46104191494 passed.
- PR #55 exact-head Full Tests 46105078884 passed on c4ee613c65dc77d569c78b0d241768c60b566fa7. PR #56 exact-head Full Tests 46105080974, pinned Mathlib 4.19 integration 46105080903, and push Full Tests 46105076511 passed. Those validate their respective exact heads.
- On main 0264ee19fe54adcb703e2aa7a820e9f169709406, Full Tests 46106764130, pinned Mathlib integration 46106764092, and Pages deployment 46106764104 all passed.
- The repository scan before opening this checkpoint PR found no other open PRs. Research issues #9 and #10 remain open; their recent tests are useful bounded contributions, not full closure of either issue.

## Mathematical and engineering state

Proof scopes form a tree. Child goals inherit parent object identities; sibling locals remain isolated; branch closure checks the residual goal; local declarations expire at scope exit; only parent-visible dependencies return. Conjunction, equivalence, existential construction, intuitionistic negation introduction, explicit ex-falso, and named classical reductio are separate supported operations. Classical reductio is available only when explicitly requested; ordinary candidate generation does not insert a classical principle. Arbitrary inductive elimination remains unsupported.

Bounded element requests preserve the set restriction and local identity. A displayed type is required; a known local carrier can reject a mismatch; universal introduction creates membership as a subgoal; an existential witness carries both membership and its property. Universal introduction and existential extraction remain separate structural readings until the goal, typed context, or user choice constrains them. The parser does not infer arbitrary set carriers or local definitions from the same phrase.

A local lemma uses an explicit claim and proof block. Its child scope inherits parent identities, closes only against the stated claim, and returns parent-visible dependencies. Child-local declarations expire. An incomplete lemma remains an open dependency and cannot produce a complete Lean export.

The checked Mathlib examples include compact image under a continuous map, subgroup multiplication closure, linear-map additivity, continuous composition, same-type compactness premises with a factored local let, and a dependent existential witness in Fin (n + 1). The last two distinguish h1 and h2 by proof identity even though their types coincide. The Fin example checks that the local let stores x and has a type depending on n. These are small extractor and elaboration acceptance cases, not broad natural-language coverage or a general dependency-minimality result.

Issue #10 already has a separate formal core in lean/Scoped.lean: Nat-indexed expressions and first-order formulas, a shallow Lean denotation into Nat and Prop, a checked theorem that simultaneous capture-avoiding substitution commutes with denotation, and a theorem that erasure into the generic Scoped.Term commutes with substitution. This fragment supports zero, successor, addition, equality, truth, falsity, conjunction, implication, and universal quantification over Nat. It excludes dependent object domains, general predicates, arbitrary constants, partial syntax, and the full Lean type system.

PR #55 adds a distinct browser-to-native-IR regression for nested natural-number quantifiers, addition, equality, alpha-renaming, and same-name shadowing. It checks de Bruijn indices, elaborates the generated theorem in Lean, and uses Lean's native judgment round trip. The browser parser is not yet structurally connected to ScopedSemantics.Formula; these two checks do not establish correspondence for arbitrary browser ASTs or Lean expressions.

## Verification boundary

Parsing, candidate construction, structural compatibility, open proof obligations, Lean elaboration, kernel checking, and author-intent fidelity are distinct states. A structurally exportable draft is not by itself a Lean proof or a semantic-fidelity guarantee. Formula comparison is conservative structural comparison, not general definitional equality. Current source identities are reconciled conservatively across edits; repeated identical rows may remain intentionally unmatched when correspondence is ambiguous. Lean InfoTree traces are observations from elaboration: tactic ranges and goals are not author-intent alignments, and references are syntactic occurrences from recorded terms or assigned goals, not a complete logical dependency graph.

The Full Tests workflow covers unit, Python, Lean, integration, and browser paths. Pinned Mathlib integration and Pages deployment are separate workflows. CI now runs Full Tests on PRs and pushes to main; it does not run the same full workflow again for every feature-branch push. A PR still needs an exact-head run, and post-merge checks still need verification on main.

The benchmark measures synthetic editor cases only. It compares cached results structurally with a cold public compileNaturalDraft result and reports medians and P95 values, including cases with little reuse or slower cached evaluation. It is not browser keystroke latency and does not generalize to user documents.

## Incremental benchmark observations

Run 46082417456 used Ubuntu 24.04.5 and Node 22.23.5, with 24 warmups and 160 timed samples per case. Every cached result was compared structurally with a cold public compileNaturalDraft result. Times are milliseconds; reuse is mean reused rows. These synthetic figures are not browser keystroke latency and do not generalize to user documents.

| Case | Median | P95 | Reuse |
|---|---:|---:|---:|
| Cold full evaluation (16 proof rows, 62 locals) | 1.442 | 2.249 | 0 |
| Exact replay (16 proof rows, 62 locals) | 1.112 | 1.785 | 16 |
| Final-premise character edit (15-row prefix) | 1.081 | 1.561 | 15 |
| Local proof-dependency edit (7-row prefix) | 1.069 | 1.393 | 7 |
| Eight-level nested cases, cold (41 lines) | 6.283 | 8.981 | 0 |
| Eight-level nested cases, exact replay | 1.160 | 1.405 | 25 |
| Nested case conclusion edit | 6.951 | 7.958 | 16 |
| Interleaved sequence, cold (two case blocks) | 2.012 | 2.801 | 0 |
| Interleaved replay plus terminal edit | 2.524 | 3.228 | 4 |
| Conjunction child goals, cold | 0.097 | 0.211 | 0 |
| Second conjunction goal edit | 0.268 | 0.340 | 1 |
| Element candidates, cold (50 locals) | 0.976 | 1.389 | 0 |
| Element candidates, exact replay | 0.450 | 0.758 | 1 |
| Element candidate property edit | 1.013 | 1.337 | 0 |
| New existential premise | 0.988 | 1.296 | 0 |
| Local lemma, cold (51 locals) | 1.412 | 1.831 | 0 |
| Local lemma, exact replay | 0.313 | 0.338 | 3 |
| Local lemma one-premise edit | 1.667 | 2.150 | 1 |
| Local lemma source-line shift | 1.686 | 2.182 | 0 |

Exact replay is faster in these fixtures. Reuse does not guarantee a speedup: nested conclusion edits, interleaved terminal edits, and local-lemma edits can be slower than their cold baselines despite some reused rows. No general editor-latency claim follows.

## Next dependency-ready work

1. Extend the Issue #9 corpus with a reviewed subspace or analysis proof and its explicit expected dependency closure. Keep the issue open until examples cover the requested range; the compact-image and Fin cases address only part of the request.
2. Connect the browser formula AST to the overlapping fragment of ScopedSemantics.Formula with a checked translation or serialization test. Then investigate a typed bridge from that fragment to native Lean Expr, preserving explicit bounds and the distinctions between syntax, definitional equality, and proof irrelevance.
3. Extend local source-region correspondence from Lean tactic observations and scoped identities, preserving conflicts when prose alignment is not supported.
4. Add real editor-path measurements and branch-local edit comparisons against full recomputation before making responsiveness claims.
5. Expand the reviewed mathematics corpus across analysis, linear algebra, topology, and algebra. Separate statement parsing, proof transformation, Lean compilation, semantic fidelity, and author-route preservation in every report.

The original eight-stage dependency order remains in force: semantic representation, scope/context, ambiguity constraints, declaration/concept dependencies, proof fidelity, bidirectional editing, incremental computation, then broad corpus evaluation. Work on the later stages may expose regressions in earlier ones, but does not replace that order.
