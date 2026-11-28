# Research methods mapped to the implementation order

The eight-stage dependency plan in [IMPLEMENTATION_ORDER.md](IMPLEMENTATION_ORDER.md)
remains authoritative. Literature supplies methods, not new parallel
subsystems. This is a design map, not a claim of implementation or proven
properties. No upstream source is copied.

| Stage | Reference | Adopt selectively |
| --- | --- | --- |
| 1 | Ranta, [Type theory and the informal language of mathematics](https://ncatlab.org/nlab/files/InfLang.pdf); GF/Informath; [Hazelnut](https://arxiv.org/abs/1607.04180); Naproche | Typed abstract syntax, incomplete expressions, separate concrete realization; check substitution against a small denotational interpretation |
| 2 | de Bruijn representations; Naproche; [FaithAlign](https://arxiv.org/abs/2610.18498); [LeanArchitect](https://doi.org/10.4230/LIPIcs.ITP.2026.25) | Keep binding identity, display names, and source regions distinct; treat implicit variable introduction as scoped context change |
| 3 | [Pistis](https://arxiv.org/abs/2608.15432); [FaithSieve](https://arxiv.org/abs/2608.26310); FaithAlign | Partial proof graphs, open obligations, and explicit provenance; distinguish user-cited reasons from observed proof dependencies |
| 4 | [AmbiQT / LogicalBeam](https://aclanthology.org/2023.emnlp-main.436/); shared parse forests; unification | Multiple structural plans; bounded joins, scope-aware candidate constraints; no neural decoder required |
| 5 | LeanTrace; Lean Compass; [Lean Atlas](https://arxiv.org/abs/2604.16347); [Aria](https://arxiv.org/abs/2510.04520); [LeanDojo](https://papers.neurips.cc/paper_files/paper/2023/hash/4441469427094f8873d0fecb0c4e1cee-Abstract-Datasets_and-Benchmarks.html); LCS-Bench | Separate declaration-type, definition, instance, and proof dependencies; use the active Lean environment for concept and theorem signatures |
| 6 | Incremental attribute evaluation | Explicit positive and negative dependencies, bounded local recomputation, cold-evaluation equivalence |
| 7 | [SAE](https://arxiv.org/abs/2610.25018); FaithAlign; [GTED](https://arxiv.org/abs/2507.07399); TransTED; [Contract Lenses](https://doi.org/10.1017/S0956796823000059); LeanArchitect | Role-sensitive structural comparison, conservative edit correspondence, partial update contracts |
| 8 | [LeanReviewBench](https://github.com/MechMath/LeanReviewBench); FaithAlign; ProofNetVerif | Independent statement targets, semantic error categories, paired revision fixtures, held-out evaluations |

For AmbiQT and LogicalBeam, the relevant lesson is to vary and rank
interpretations at the level of logical plans and schema assignments; ordinary
token diversity can return many strings that encode the same reading. The
LeanDuet prototype therefore represents distinct mathematical operations as
separate typed candidate leaves and lets goal/context constraints filter them.
It does not reproduce LogicalBeam's learned template infilling, SQL-specific
beam search, or AmbiQT corpus, and this first deterministic rule family has no
probabilistic ranking. The paper is published by ACL; its code repository is
MIT-licensed. Neither source code nor benchmark data is copied.

The issue #1 adapter treats Lean's resolved InfoTree as an observation boundary for
the later scope and alignment stages. It coalesces wrappers only when their source range, syntax, and goal/context
observations match, preserving their raw multiplicity. It uses recorded tactic
goals and term assignments, but these are not natural-language semantics: absence of a child
TermInfo does not imply absence of a proof term, and a syntactic reference list
does not prove that each reference is logically necessary. The versioned
contract and deterministic pinned example live in
[INFOTREE_TRACE.md](INFOTREE_TRACE.md).

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

Scope and goal editing use shared operation plans for universal and implication
introduction, intuitionistic negation introduction, disjunction elimination,
conjunction introduction, equivalence introduction, and explicit existential
introduction. Named local lemmas now use the same fork/check/close discipline:
the child inherits parent identities, its local declarations are discharged,
and only dependencies already in the parent context can cross the boundary.
An open child remains available for later structural work but makes its
continuation provisional. Existential construction consumes a selected typed
local object and leaves its predicate as an obligation; equivalence
construction proves both directions without classical axioms. Full Tests
cover the local-lemma browser and backend paths, and the pinned Mathlib 4.19
integration compiles an aligned local-lemma case. The proof workflow also
supports an explicit named classical reductio. General inductive elimination
remains unsupported.

The current operation-candidate family pairs arbitrary-variable introduction
with existential witness extraction for a bounded English/Chinese request
grammar. It retains the source occurrence and candidate identity, admits a
later explicit target constraint only when intervening syntax is supported,
and reports context/search limits separately. Its restricted-set form keeps
`x ∈ A` as a separate premise under universal introduction and as part of the
extracted evidence under existential elimination. It requires an explicit
carrier annotation; a known simple local carrier may reject a mismatch, while
unknown or compound carriers remain for Lean to check. Further extensions to
local definitions, subtype objects, and unresolved existence need structural
evidence that distinguishes those operations. Each gate requires
scope/identity regression tests, independent Lean compilation of emitted
fragments, and incremental-versus-cold evaluation tests. In parallel, retain a
small set of reviewed real mathematics examples rather than waiting for all
semantic modules to be complete. Preserve the existing eight-stage order.
