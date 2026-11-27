# Research methods mapped to the implementation order

The eight-stage dependency plan in [IMPLEMENTATION_ORDER.md](IMPLEMENTATION_ORDER.md)
remains authoritative. Literature supplies methods, not new parallel
subsystems. This is a design map, not a claim of implementation or proven
properties. No upstream source is copied.

| Stage | Reference | Adopt selectively |
| --- | --- | --- |
| 1 | Ranta, [Type theory and the informal language of mathematics](https://ncatlab.org/nlab/files/InfLang.pdf); GF/Informath; [Hazelnut](https://arxiv.org/abs/1607.04180) | Typed abstract syntax, incomplete expressions, separate concrete realization; check substitution against a small denotational interpretation |
| 2 | [FaithAlign](https://arxiv.org/abs/2610.18498); [LeanArchitect](https://doi.org/10.4230/LIPIcs.ITP.2026.25) | Object identity and region-to-object links; preserve author wording separately |
| 3 | [Pistis](https://arxiv.org/abs/2608.15432); [FaithSieve](https://arxiv.org/abs/2608.26310) | Local obligations and explicit inference provenance; distinguish cited from necessary premises |
| 4 | [AmbiQT / LogicalBeam](https://aclanthology.org/2023.emnlp-main.436/); shared parse forests | Multiple structural plans; bounded joins, scope-aware candidate constraints; no neural decoder required |
| 5 | [Lean Atlas](https://arxiv.org/abs/2604.16347); [Aria](https://arxiv.org/abs/2510.04520); [LeanDojo](https://papers.neurips.cc/paper_files/paper/2023/hash/4441469427094f8873d0fecb0c4e1cee-Abstract-Datasets_and_Benchmarks.html) | Separate statement/definition dependencies from proof dependencies; environment-specific concept and theorem signatures |
| 6 | Incremental attribute evaluation | Explicit positive and negative dependencies, bounded local recomputation, cold-evaluation equivalence |
| 7 | [SAE](https://arxiv.org/abs/2610.25018); [GTED](https://arxiv.org/abs/2507.07399); [Contract Lenses](https://doi.org/10.1017/S0956796823000059) | Role-sensitive structural comparison, conservative edit correspondence, partial update contracts |
| 8 | [LeanReviewBench](https://github.com/MechMath/LeanReviewBench); FaithAlign | Independent statement targets, semantic error categories, paired revision fixtures, held-out evaluations |

## Boundaries

- One shared semantic interface, not independent natural-language and Lean truth stores.
- Parse alternatives are not equivalence classes; equality saturation is optional
  only after typed, scoped rewrites with evidence. Do not use edit distance as
  proof of equality or natural-language faithfulness.
- Browser conversion remains deterministic and bounded; the Lean kernel is an
  independent verifier. A checked theorem does not certify its informal reading.
- Borrow algorithms and design principles, not an entire agent stack or neural
  verifier. Review upstream licensing, exact revisions and Lean toolchains
  before reusing source/data. LeanReviewBench's statement-only snapshots
  erase proof bodies; they cannot serve as full proof round-trip gold data.
- Treat the cited preprints as research leads; verify their definitions and
  source implementations before asserting compatibility or reproducing metrics.
- The typed fragment in `lean/Scoped.lean` is deliberately narrow, over
  `Nat` and `Prop`. Its substitution theorem checks semantic preservation for
  that grammar only; it neither serializes nor interprets arbitrary Lean
  `Expr`, and it is distinct from the browser's incomplete surface AST.

## Next implementation gates

Stage 2 now has shared goal-operation plans for universal and implication
introduction, intuitionistic negation introduction, disjunction elimination,
and conjunction introduction. The conjunction block opens two isolated child
goals; local declarations and open proof obligations remain scope-local, and
the nested identity matcher preserves only uniquely aligned child scopes.
Generated Lean and the browser interaction are checked by repository CI
before merge. This does not cover named local-lemma return, existential goal
construction, equivalence introduction, or classical reductio.

Next, complete those bounded proof operations over the same child-scope
contract. Then extend stage 3 with distinct structure candidates for arbitrary
elements, existential witnesses, definitions, subtype objects, and unresolved
existence. Each gate requires scope/identity regression tests, independent Lean
compilation of emitted fragments, and incremental-versus-cold evaluation tests.
Preserve the existing eight-stage order.
