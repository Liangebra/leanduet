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

## Acceptance fixtures

`tests/interpret_integration.py` invokes the JavaScript natural draft compiler
and independently compiles its generated bounded-quantifier proof with Lean.
The browser smoke test selects a proof candidate without changing the raw
text and checks that subsequent edits invalidate the staged patch.
`node tests/draft-benchmark.mjs` is an opt-in synthetic full-vs-incremental
latency comparison; results are environment-dependent and do not establish a
real-world latency guarantee. More realistic mathematical corpora and
cross-version bidirectional testing are still required.

## Cross-revision draft correspondence (conservative subset)

Session-local persistent IDs are separate from line/slot addresses. With
unchanged context, uniquely matching raw occurrences whose bound formula
references agree retain their IDs after insertions/deletions. Duplicate
occurrences, altered text, changed context, or unresolved formula structure
are not automatically equated. A selected candidate migrates only if its
schema, term and mapped premise identities still agree. The browser always
invalidates staged Lean output on edits. This is deliberately not arbitrary
alpha-renaming, persistent workspace serialization, or kernel identity.

## Discourse-reference constraints

Explicit anaphora (previous result, earlier result, a numbered source line,
previous two results) introduces a finite domain of preceding local objects.
The goal and other premises constrain those domains through inference schemas.
All compatible referent tuples are retained within a bounded search, with
explicit overflow. Open referents remain open. This is one local relational
constraint over a shared draft graph, not general discourse understanding or
a global parser for unrestricted prose.
