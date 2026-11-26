theorem compose_imp (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  have hq : Q := hpq hp
  exact hqr hq

theorem swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

theorem nested (P : Prop) (h : P) : P ∧ P := by
  have h' : P := by
    exact h
  exact ⟨h', h⟩

theorem reverse_eq (a b : Nat) (h : a = b) : b = a := by
  exact h.symm
