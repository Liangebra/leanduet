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

## Current scope-sequence capability

The browser evaluator can compose ordinary supported inference lines with
multiple explicit binary-disjunction blocks in one proof: a linear prefix can
introduce local facts, a case result returns to its parent scope, and a later
case block can use that result. The same composition works inside a branch.
Each introduction receives a revision-local scope identity; display names are
resolved against the active lexical scope. Physical source line numbers remain
the addresses used by candidate choices and graph nodes, including across
blank lines.

An unresolved prefix remains visible in the semantic graph and prevents the
combined draft from being complete, even when later case blocks are structurally
usable. This is still a bounded parser for supported inference lines and
explicit binary disjunctions, not general mathematical prose or arbitrary
inductive case analysis. Case bodies are recomputed after edits; only the
existing linear draft cache is reused where its context key permits. Tests
compare the edited sequence with a cold evaluation, and the structured backend
integration compiles a generated interleaved sequence with Lean in CI.

## First graph implementation

The natural draft returns a versioned revision-local graph. Context ordinals
and physical source lines identify introductions inside a snapshot; they are
not globally persistent IDs. A formula tree replaces uniquely visible free
names by local IDs, retaining unresolved names. Candidate dependencies are
separate from selected proof dependencies. An invalidation traversal includes
possible candidate dependencies by default. This is a dependency index, not
yet an incremental scheduler. The native kernel judgment is not reconstructed
from this speculative graph.

## Small interpreted syntax fragment

`lean/Scoped.lean` first proves substitution laws for an untyped scope-indexed
operator tree, then adds a separate, intrinsically typed fragment with
natural-number expressions and first-order propositions. Its Lean denotation
is preserved by capture-avoiding substitution, including under universal
binders; an erasure map into the generic tree also preserves substitution.
This is an initial semantic correspondence, not a conversion from the browser
AST to Lean `Expr`, and it excludes dependent object types, predicates beyond
equality, arbitrary constants, and incomplete terms.

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
`tests/fixtures/mathlib-cases.json` stores the compact-image topology example with
its prose, controlled draft, expected structure, theorem header and context
closure. The JavaScript structural test and pinned Mathlib integration consume
the same fixture; Mathlib CI compiles the generated candidate. This single
case is a corpus seed, not broad analysis or algebra coverage.
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

## Typed local definitions

A definition `令 y : $Nat$ := $f(x)$` introduces a typed local value, not
an equality proposition. The draft graph retains separate type and value trees,
including value dependencies; subsequent candidate matching can use the
explicit declared type. Lean checks the actual value and type. Duplicate,
self and forward local references are rejected; unknown global names are
left to Lean. Untyped inference, arbitrary set-builder notation and general
unfolding are not implemented. The structured chain endpoint accepts bounded
single-expression definitions and traces their elaborated local bindings.

## Goal-directed introductions

Explicitly typed universal and implication introductions consume a matching
constructor of the selected goal. Each extension records the residual goal
and emits intro followed by change at the local declaration, so Lean checks
the annotation. Absent or unsupported goals block translation. This is a
single nested scope, not case splitting, implicit binder inference or
arbitrary goal elaboration.

The goal reader additionally accepts single parenthesized Lean binders and
untyped universal syntax when the author explicitly supplies a domain
annotation. Lean, not the browser, decides the inferred domain. The graph
stores initial goal and scope-introduction dependencies even if a later
proof does not use the binder. Structured chain validation accepts bounded
nested named applications emitted by the quantifier translator. Actual
JavaScript-to-Lean tests cover both kinds of context extension.

## Backward proposition constraints (first finite domain)

The explicit proposition hole `建立 hp : $?$,由 h` derives a finite type
and proof domain from a typed conjunction h. A subsequent explicit inference
using hp and currently typed premises constrains that domain. Intersect
supported matches; preserve the original domain and report contradictory or
unsupported constraints without inventing a type. A singleton compatible
candidate can be emitted; otherwise the user must choose or provide more
information. This is not general type inference: only conjunction projections
and supported local relation schemas are used. The incremental cache disables
prefix reuse after any edit in a draft with backward constraints, since a
later line may change an earlier binding. Lean independently validates the
resulting proof.

The integration fixture compiles both left- and right-projection solutions
selected by distinct downstream constraints using the actual browser compiler.

## Context consistency audit

Type holes retain introduction identity independently of their selected type,
provided the original domain and scope still agree. Candidate migration also
checks normalized candidate types and premise IDs. The browser iterates
migration so earlier recovered choices can expose later domains, invalidating
staged output regardless. Candidate-type references and backward constraint
references participate in a fixed-point invalidation closure, not the acyclic
proof dependency graph. Ordinary proposition annotations reject known
forward/ambiguous local references and propagate type-level open dependencies.
These are conservative scope and cache invariants, not Lean type checking.

## Joint finite proposition constraints

Independently sourced conjunction projection holes in a linear scope form
finite domains. Explicit later inferences contribute support relations over
all cited hole variables, rather than independently pruning their types.
Connected components of supported relations are solved by a bounded join
with partial-support pruning. The graph stores shared compatible assignments,
not just marginal candidate lists. User choices are included as constraints,
and inconsistent combinations are reported. Unsupported relations do not
prune; overflow yields no claimed solutions and retains the original domains.
Scope introductions and definitions are barriers; dependent-source holes,
implicit inference, arbitrary theorem search and full Lean type inference
remain outside this subset. Joint constraint edges participate in fixed-point
invalidation, separately from proof dependencies.

The cross-layer integration fixture compiles both correlated assignments using
Lean and checks that inconsistent selections produce no exported fragment.
Identity migration and cache replay tests exercise downstream choices that
change an earlier inferred proposition.

When all surviving proof candidates have the same scoped proposition type,
the intermediate binding is retained as a typed open proof obligation. Later
steps may depend on it but no complete fragment is exported until the proof
choice is resolved. The workbench displays shared compatible assignments
and supports atomic selection or clearing of a joint assignment.

## Dependent finite candidate domains

A projection hole may cite an earlier projection hole whose type is unknown.
Its candidate domain is the union of the projections supported by each source
type, with an explicit source-to-child support relation. Candidates with the
same Lean term but distinct scoped types receive distinct choice keys. A
subsequent inference can constrain the entire chain; a selected projection
cannot be exported if its source type remains unresolved. The graph retains
symbolic dependencies on unresolved holes. Relation construction is bounded
independently of assignment enumeration and reports overflow without treating
partial tuples as exhaustive. This is conditional finite projection inference,
not a general dependent type elaborator or Sigma-type implementation.

The integration suite compiles the same conditional projection expression
under both possible source types, and checks that an incompatible source
choice cannot export a proof. Regression coverage includes three dependent
domains and incremental replay after changing the terminal constraint.

## Quantified context operations

Goal-directed implicit introductions recover a domain or antecedent only from
a supported explicit goal constructor. Existential elimination from a named
local premise introduces two separate semantic objects: a witness and its
proof of the instantiated predicate. The original premise is retained via a
fresh internal copy. The graph records both introductions and their scope
edges; cache replay restores both bindings. Conditional projection lookahead
stops at this scope boundary. An assumption can also consume a matching
negated goal, leaving `False` as the residual obligation. This is intuitionistic:
classical double-negation elimination is never inserted. A bare local reference
whose type is known is compared in the scoped surface grammar, including the
built-in equivalence between `Not P` and `¬ P`; other structural mismatches
remain unresolved and explicitly state that Lean definitional equality was not
checked. Nontrivial applications still require Lean's independent check. From `False`,
users can apply an explicit rule such as `False.elim`. The structured backend
checks the annotations with Lean. Existential elimination remains a linear scope extension; it is
not arbitrary dependent pattern matching or implicit type inference.

## Branch-local disjunction elimination

The natural draft supports an explicit binary split of a typed local premise
whose type is `P ∨ Q` (or Lean `Or P Q`). Each `inl`/`inr` branch receives a
fresh local identity and a branch-local assumption. The same display name may
be reused in sibling branches because those assumptions are different
objects. Each branch must establish the declared common result before its
scope closes. The closure discharges branch-local proof objects and returns
only dependencies already present in the parent. A fresh parent result
binding is then available to later steps. Branch trees and their dependencies
remain visible in the semantic graph, including when a branch is incomplete.
If either arm is still open, the common result is provisional: parent
statements are still parsed and linked to it, but their dependency remains
open and no Lean term is exported. Closed branch-local names stay unavailable
in that continuation, and its final proposition is still checked against the
remaining parent goal.

The implementation accepts nested case blocks with at most eight split levels
and 64 nonblank source lines, but only for explicit binary disjunctions with
both arms supplied in left-to-right order. Branch indentation is parsed
recursively. It does not implement arbitrary inductive `cases`,
`Or` elimination from an untyped premise, `False` elimination, contradiction
or classical proof by cases. The browser checks a shared scoped target; the
structured backend re-elaborates the generated nested Lean term and traces
only parent-scope results, so branch-local names cannot escape through the
backend response. Browser and backend integration fixtures compile nested
generated proofs with Lean and compare branch dependency behavior. This is a
bounded proof-scope operation in stage 5, grounded in stage 2 identity and
stage 3 dependency edges; it does not replace the eight-stage plan or claim
general natural-language proof understanding.

See [research methods](RESEARCH_METHODS.md) for references mapped to this
unchanged eight-stage plan.

The Lean adapter distinguishes tracing arbitrary typed local objects from
tracing proof-only facts. Witnesses, universal introductions and local
definitions use object tracing; evidence and established propositions retain
the proposition check. This also repairs earlier structured-chain paths that
incorrectly attempted to trace data as propositions.

### Scoped draft address and closure audit

Keep physical source line addresses across whitespace in nested branch bodies
and parent continuations. Candidate selection remains revision-local by
physical line, while identity reconciliation uses scoped object identities.
A branch's explicit final proposition must structurally match its residual
goal after introductions. An implicit parent conclusion is permitted only
when the declared case result structurally matches the enclosing goal. These
checks are conservative within the browser grammar, not a decision procedure
for Lean definitional equality. Unsupported equivalent presentations may
require a more explicit continuation or independent Lean checking.

The continuation also receives the set of expired branch-local declaration
names. Unqualified local references cannot silently become global rule
references after scope closure; fresh introductions may reuse a display
name. This remains conservative and does not certify global name resolution.

### Resolution status is not proof status

Draft rows expose `resolutionStatus` separately from `proofStatus` and the
legacy presentation `status`. The finite resolver distinguishes an unverified
candidate, an open dependency, an unselected proof obligation, missing context,
multiple candidates, exhausted search, a stale user choice, inconsistent
constraints, no match in the bounded supported rules, unsupported wording, and
a target mismatch. “No match” is local to the supported rule set; it does not
show that no mathematical explanation exists. At the result level,
`completionKind: structural-export-ready` means the draft can be rendered;
`leanVerification: not-run` and `semanticFidelity: not-assessed` remain explicit
until independent checking and author-intent review occur. This classification
does not yet generate structural parse alternatives for distinct operations
such as arbitrary-element introduction versus witness extraction.
