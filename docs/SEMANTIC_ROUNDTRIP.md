# Semantic round-trip and specialization

Presentation math and Lean surface grammar are distinct concrete syntaxes.
Their common scoped AST supports candidate matching, not definitional equality.

- Preserve application structure across rendering and re-parsing. Mathematical
  adjacency is still rejected unless the input is explicitly Lean syntax.
- Lower bounded quantifiers to an untyped binder with implication/conjunction.
- Typed universal specialization uses a visible, syntactically type-matching
  local witness and capture-safe de Bruijn substitution. It generates
  candidates, not certificates of elaboration.
- Reserve explicitly planned intermediate names; reject forward references
  rather than accidentally treating them as global theorem names.

The Lean syntax subset does not handle tuples, implicit arguments, dependent
elaboration, coercions or notation extensions. Persistent cross-edit IDs and
candidate-forest propagation remain research problems.

## Partial drafts

A parsed intermediate proposition with unresolved reasoning remains available
as a tentative local binding. Subsequent candidate applications expose direct
and transitive dependence on open obligations. Unresolved prose still blocks
fragment export; explicit formula-only obligations may be exported as
`exact?` searches, never as checked proofs.

## Cross-revision identity

Draft correspondence compares goal formulas and context types by their
scoped AST. A change to a bound variable's display spelling therefore preserves
revision-local identities when the parsed structures are otherwise the same.
Parent context names remain significant. Names attached to goal-operation
binders are normalized to their binding slot in that operation's identity key;
a later source row retains correspondence only when its text is identical
modulo those uniquely matched local spellings and its scoped formula and
references still agree. This is alpha correspondence only: it does not identify logically equivalent formulas,
establish Lean definitional equality, rename source text, or certify that a
proof narrative is faithful. Unsupported or structurally changed targets or
types do not retain correspondence.
