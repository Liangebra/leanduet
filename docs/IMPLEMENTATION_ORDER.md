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
inductive case analysis. Case frames now have separate bounded row-prefix
caches whose keys include parent binding identities and types, goal, source
offsets, choices, and open/closed continuation state. A bounded exact-result
cache handles replay of a complete root scoped program. The graph is still
rebuilt after structural edits. Tests compare edited sequences with cold
evaluation, including a newly added same-typed premise that must invalidate
candidate sets. In one local synthetic run, exact replay of an eight-level,
41-line case program measured 1.273 ms median / 1.568 ms P95 versus 6.186 /
8.503 ms before scoped caching; ordinary linear replay and edited structures
did not show a speedup. These measurements are workload-specific, not a
general latency guarantee. The structured backend integration compiles a
generated interleaved sequence with Lean in CI.

## Child-goal operations

The browser describes universal introduction, implication introduction,
intuitionistic negation introduction, disjunction elimination, conjunction
introduction, equivalence introduction, and explicit existential introduction
with one bounded goal-operation record. Each record states the
parent goal, child goal(s), local context additions, logical mode, and closure
form. `cases` uses the same plan as the earlier explicit binary-`Or` parser;
splitting `P ∧ Q` opens sibling goals `P` and `Q`, each in a child scope that
inherits parent identities but receives no sibling declarations. The two child
proofs return only after their own target is structurally matched. Nested
scopes may use parent bindings; local assumptions and declarations are
discharged at closure and cannot escape. Case and conjunction scopes share an
eight-level nesting budget.

The bounded blocks are `split conjunction`, `prove equivalence`, and
`construct witness a`. Their ordered child headings are `first goal` / `second
goal`, `forward direction` / `reverse direction`, and `witness property`, each
indented by two spaces with proof lines indented by four. Existential
introduction requires a uniquely visible local object with a known type; the
prototype checks an explicit existential domain syntactically and leaves the
property proof as a child goal. It does not invent a witness or establish
existence. Equivalence introduction proves both implications constructively.
Blank source lines keep physical addresses. An incomplete child remains
represented alongside the other child graphs. Structural renderability is
distinct from proof closure: a child containing `exact?` can still render, but
its proof status is `open-obligation`; it is not described as verified or
semantically faithful. Lean elaboration and the existing local patch check
remain separate. Named local lemmas are supported in the explicit form
`local lemma h : $P$`, followed by an indented `proof` block. The child goal
inherits parent identities; its local declarations are discharged at closure,
and only dependencies already in the parent context can return with the lemma
proposition. An incomplete child leaves later rows visible but provisional and
prevents executable export. The structured backend emits `have h : P := by`
and Lean independently elaborates it. The grammar does not infer an unstated
lemma statement or certify authorial intent. An explicit named classical
reductio is supported; general inductive elimination remains unsupported.
JavaScript tests compare edited
child blocks with cold results; generated terms and browser interactions are
checked in CI because Lean and Chromium are not installed locally.

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

## Explicit Nat context projection

A separate browser projection accepts a finite, oldest-to-newest context of
records containing stable id, display name, and the supported type `Nat`.
The emitted `Formula n` uses Fin indices: the newest context object is index
zero, shifted outward under each universal binder. Free names resolve only
when exactly one context entry has that name; binder shadowing is handled by
the parser's de Bruijn scope. Lean integration checks the emitted indices and
denotation against an explicit finite environment, including a binder that
shadows a context display name. This bridge does not yet accept proposition
assumptions or dependent context entries, infer persistent identity across
edits, or map the serialized schema to arbitrary Lean `Expr`.

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

The browser uses bounded syntax, semantic row-prefix, per-scope, and exact
root-result caches. Context, object identities and types, planned local names,
source line position, conclusion role and explicit choices are part of reuse
conditions. A reused prefix restores the scope, generated-name counter and
open obligations before recomputing the remaining suffix. The graph is rebuilt
for each structural edit. Regression tests compare incremental and full
results, including negative candidate dependencies. This is not arbitrary DAG
scheduling or general cross-revision identity reconciliation.

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
`tests/fixtures/mathlib-cases.json` stores two small Mathlib cases with their
prose, controlled drafts, expected structures and theorem headers: compactness
of a continuous image (topology), and multiplication closure of a subgroup
(abstract algebra). The JavaScript tests consume the same records, and the
pinned Mathlib integration compiles both generated candidates. The second case
also checks that the proof dependency view retains the subgroup, operands,
membership facts and group structure. These are corpus seeds, not broad
analysis or algebra coverage; only the compact-image case currently exercises
the local-lemma syntax.

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
checked. Nontrivial applications still require Lean's independent check. A
typed local premise of `False` can now yield a distinct `False.elim` candidate
for a different goal, including through the deterministic implicit rule search.
The resolver does not derive arbitrary contradictions or insert classical
principles. Existential elimination remains a linear scope extension; it is not
arbitrary dependent pattern matching or implicit type inference.

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
now has a bounded structural alternative family for element introduction and
witness extraction, described below.

### Structural candidates for element requests

The controlled phrases `take an element x satisfying $P(x)$` and
`取一个元素 x 满足 $P(x)$` share one parsed request record. The operation
resolver may produce two different actions when the current goal is a matching
universal and a visible typed local premise is a matching existential:
introduce the universally quantified variable, or extract a witness and its
predicate evidence. “Arbitrary/任意” excludes witness extraction; an explicit
`from h` source restricts extraction to that local object. No local definition,
subtype coercion, or unproved witness construction is inferred.

These are separate structural leaves over one request, not a Cartesian product
of independently parsed words.

Lean may print a nondependent Pi binder as an arrow, such as `Nat → P`. For an
element request with an explicit type, a matching arrow domain also supports
variable introduction, while ordinary `assume h : P` remains the implication
introduction operation. This is a surface normalization backed by the typed
request and Lean's Pi pretty-printing convention; it does not infer arbitrary
domains or establish general type equality. Each leaf records its operation, typed object
identities, source-premise identity when applicable, and a choice key. A unique
supported reading can proceed through the existing goal-introduction or
existential-elimination machinery. Multiple readings remain unresolved and do
not add a speculative local object. A later explicit conclusion can constrain
these leaves only when the intervening supported syntax gives a determinate
residual goal; unsupported syntax, another operation request, or a backward
type hole disables that lookahead rather than pruning candidates speculatively.

The context scan is bounded at 64 visible entries and the rendered family at
eight candidates. Overflow is `budget-exhausted`, distinct from an empty
supported family. The row keeps the original text, candidate family, rejected
readings and constraint explanation. A chosen reading is still an unverified
Lean candidate; it is not proof of author intent. Tests cover English and
Chinese phrases, sibling operation readings, explicit sources, stale choices,
same-draft object identity, downstream target constraints and incremental
versus cold recomputation. Lean compilation and browser selection run in CI.
This advances the original candidate-forest stage and uses the identity,
partial-graph and goal-operation work; it is not a general shared parse forest,
local-definition resolver, or unrestricted natural-language parser.

The same structural request supports bounded set forms such as
`take an arbitrary element x : $Nat$ in A satisfying $P(x)$`. For a goal
`∀ x ∈ A, P x`, introduction opens `x ∈ A → P x`; the membership proof remains
an ordinary child assumption and must be supplied before proving `P x`.
Extraction from `∃ x ∈ A, P x` gives separate local witness and evidence
objects, with evidence type `(x ∈ A) ∧ P x`. The request must name the set and
include an element type. When that set is a visible identifier with a simple
known carrier (`Set`, `List`, `Finset`, or `Multiset` applied to one type), a
conflicting annotation is rejected before emitting Lean. This is a narrow
surface check; compound set expressions, coercions, aliases, and other
container types are not inferred. The emitted candidate still needs Lean
elaboration, and unresolved carrier information is not treated as a match.


## Lean elaboration trace seam (issue #1)

The local Lean 4.19 adapter resolves deferred InfoTree assignments before
reading tactic nodes. It records actual tactic syntax ranges, goals before and
after, local contexts, child TermInfo references and references visible from
assigned proof terms. Identical source/syntax/context/goal wrappers are
coalesced for display, with raw multiplicity retained per observation. This is useful input for later region alignment and
scope-aware dependency views; it is not a replacement for the shared partial
mathematical graph.

Ranges refer back to the user's original UTF-8 source after the adapter
preamble is removed. Opaque means that no child TermInfo expression was
recorded; assigned proof terms can still provide references. No dependency is
inferred from indentation. See [the schema and limits](INFOTREE_TRACE.md).

## Explicit classical reductio

The structured proof editor accepts `classical reductio hnot` (or
`经典反证 hnot`) followed by a `contradiction` (or `矛盾`) subgoal. For
a target `P`, the planner creates a child obligation `False` under a fresh
local binding `hnot : ¬ P` and renders the closure with
`Classical.byContradiction`. This operation is explicitly classical.
Intuitionistic negation introduction remains a separate operation proving
`False` from an assumption `P`; ex falso remains elimination from an
existing `False` proof. The temporary negation has child-scope identity and
is discharged when the child closes.

## Explicit natural-number induction

The structured proof editor also accepts `induction n` (or `对 n 归纳`) only
when the current goal is an explicitly typed `∀ n : Nat, P n`. It opens a
zero/base child goal and a successor child goal. The successor context contains
a fresh Nat step object and `ih : P n`; both are local to that child, and the
induction recursor discharges them when the parent proof is closed. The
successor target is displayed as `P (n + 1)`, which is definitionally equal to
Lean's `P (Nat.succ n)` target. Other inductive types, non-universal targets,
generalized induction hypotheses, and automatic induction discovery remain
unsupported. Candidate status still does not mean Lean-verified until the
separate checker accepts the generated term.
