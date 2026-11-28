import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Module.Submodule.Basic

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


/-!
# Dependent witness: a finite object with a property depending on it

The carrier Fin (n + 1) depends on n, and the property p x depends on the
chosen object x. The selected witness proof uses h2 by identity even though
h1 has the same type. The local-let version names the finite witness before
building the same existential proposition.
-/

theorem fin_witness_refactor_direct
    {n : Nat} (p : Fin (n + 1) → Prop) (x : Fin (n + 1))
    (h1 h2 : p x) :
    ∃ y : Fin (n + 1), p y := by
  exact ⟨x, h2⟩


theorem fin_witness_refactor_local_let
    {n : Nat} (p : Fin (n + 1) → Prop) (x : Fin (n + 1))
    (h1 h2 : p x) :
    ∃ y : Fin (n + 1), p y := by
  let finWitness : Fin (n + 1) := x
  exact ⟨finWitness, h2⟩


/-!
# Subspace addition and proof identity

The sum of two members of a submodule is again a member. The selected
subterm is `S.add_mem h2 hy`. Its expected dependency closure contains R, M,
S, x, y, h2, hy, and the required algebraic structure instances; it excludes
the same-typed but unused h1. The local-let variant keeps the same conclusion
but changes the elaborated proof shape.
-/

theorem submodule_add_refactor_direct
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : Submodule R M) (x y : M)
    (h1 h2 : x ∈ S) (hy : y ∈ S) :
    x + y ∈ S := by
  exact S.add_mem h2 hy

theorem submodule_add_refactor_local_let
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : Submodule R M) (x y : M)
    (h1 h2 : x ∈ S) (hy : y ∈ S) :
    x + y ∈ S := by
  let sumProof : x + y ∈ S := S.add_mem h2 hy
  exact sumProof
