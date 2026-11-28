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

Draft correspondence compares parsed goal formulas by their scoped AST. A
change to a bound variable's display spelling therefore preserves the
surrounding revision-local identities when the parsed structures are otherwise
the same. This is alpha correspondence only: it does not identify logically
equivalent formulas, establish Lean definitional equality, rename source text,
or certify that a proof narrative is faithful. An unsupported or structurally
changed goal is treated as a different target and retires the old identities.
