import Mathlib.Topology.Compactness.Compact

/-!
# Proof-refactoring counterexample: same-type premises and local lets

The mathematical subterm selected for abstraction is
`IsCompact.image h2 hf`.  The two local assumptions `h1` and `h2` have
the same proposition type, but the proof uses only the identity of `h2`.
The expected dependency closure for that subterm contains `h2`, `hf`,
`f`, and the data needed by their types; it must not contain `h1`.

The second theorem states the same proposition and factors that subterm
through a local definition.  Its elaborated expression has a let node.
This shows why proposition equality alone cannot identify a proof subterm
or its dependency: source-level factoring changes the elaborated term shape.
-/


theorem compact_image_refactor_direct
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (f : X → Y)
    (h1 h2 : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := by
  exact IsCompact.image h2 hf


theorem compact_image_refactor_local_let
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (f : X → Y)
    (h1 h2 : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := by
  let imageProof : IsCompact (f '' s) := IsCompact.image h2 hf
  exact imageProof
