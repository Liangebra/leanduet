# Semantic conversion implementation order

This is a dependency plan, not a claim that the stages are complete.

1. **Surface semantics:** explicitly distinguish presentation and Lean syntax;
   scoped AST, capture-safe substitution, regression tests. Extend coverage
   only with round-trip tests. The native kernel IR is separate.
2. **Identity:** revision-local IDs for introduction occurrences; local
   references are distinct from labels. Persistent identities across arbitrary
   source edits require conservative reconciliation and ambiguity reporting.
3. **Partial graph:** represent propositions, proof obligations, candidate
   applications and their dependency edges. Never treat an open proof as
   verified. Preserve distinct proof objects even when their types coincide.
4. **Candidate forest:** share propositions and reference edges, retain
   alternatives, support explicit choice, enforce constraints and report
   truncation. Do not claim to recover unique author intent.
5. **Mathematical inference:** quantifiers, witnesses, scoped definitions and
   concept/theorem families. Add supported operations and independent tests.
6. **Incremental evaluation:** dependency invalidation, bounded recomputation,
   measure latency on edits. An invalidation closure alone is not incremental
   computation.
7. **Bidirectional projection:** conservative identity correspondence,
   preserve untouched text and modifiers, update only affected regions.
   Never substitute surface equality for Lean definitional equality.
8. **Acceptance:** representative proofs, adversarial cases, checked
   integration, latency and round-trip benchmarks.

Edges: 1 -> 2 -> 3 -> 4; 1+3+4 -> 5; 3+4+5 -> 6;
2+3+6 -> 7; all -> 8. Inference adds constraints back into the candidate
forest; bidirectional tests expose weaknesses in identity.

## First graph implementation

The natural draft returns a versioned revision-local graph. Context ordinals
and physical source lines identify introductions inside a snapshot; they are
not globally persistent IDs. A formula tree replaces uniquely visible free
names by local IDs, retaining unresolved names. Candidate dependencies are
separate from selected proof dependencies. An invalidation traversal includes
possible candidate dependencies by default. This is a dependency index, not
yet an incremental scheduler. The native kernel judgment is not reconstructed
from this speculative graph.

## Explicit candidate resolution

A draft choice is a line-local selection of a currently available candidate;
no choice is inferred from ordering. The original text remains unchanged.
The browser resets choices on text or target change and invalidates staged
patches and in-flight inference when choices change. Choices are not verified
proofs, persisted cross-revision identities, or an automatic CSP solver.

## Quantifier inference subset

The candidate index supports typed existential introduction, bounded universal
elimination, and bounded existential introduction using actual local witness
and membership/evidence references. Indexed joins and a 4096-probe budget
bound search; overflow is not uniqueness. For untyped binders the domain is
not inferred by the browser: Lean elaboration remains necessary.

## Conservative incremental evaluator

The browser uses a bounded exact-text syntax cache and a semantic prefix
cache. Context, planned local names, source line position, conclusion role and
explicit choices are part of reuse conditions. A reused prefix restores the
scope, generated-name counter and open obligations before recomputing the
remaining suffix. The graph is rebuilt for each evaluation. Regression tests
compare incremental and full results. This is not arbitrary DAG scheduling,
cross-revision identity reconciliation or a measured latency guarantee.

## Conservative wording repair

After source edits, exact unique occurrence fingerprints remain the only
automatic wording correspondence. Detached annotations can be explicitly
reattached to a selected unique current occurrence without overwriting existing
wording. This is manual author confirmation, not persistent identity or a
proof of semantic equivalence. It does not rewrite the Lean source.
