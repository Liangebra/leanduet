import Lean

namespace LeanDuet.TMN

/-- A proof object is data, not a proposition: different derivations remain distinguishable. -/
inductive Derivation : List Prop → Prop → Type where
  | hyp {Γ : List Prop} {P : Prop} : P ∈ Γ → Derivation Γ P
  | intro {Γ : List Prop} {P Q : Prop} : Derivation (P :: Γ) Q → Derivation Γ (P → Q)
  | apply {Γ : List Prop} {P Q : Prop} : Derivation Γ (P → Q) → Derivation Γ P → Derivation Γ Q
  | pair {Γ : List Prop} {P Q : Prop} : Derivation Γ P → Derivation Γ Q → Derivation Γ (P ∧ Q)
  | left {Γ : List Prop} {P Q : Prop} : Derivation Γ (P ∧ Q) → Derivation Γ P
  | right {Γ : List Prop} {P Q : Prop} : Derivation Γ (P ∧ Q) → Derivation Γ Q
  | inl {Γ : List Prop} {P Q : Prop} : Derivation Γ P → Derivation Γ (P ∨ Q)
  | inr {Γ : List Prop} {P Q : Prop} : Derivation Γ Q → Derivation Γ (P ∨ Q)
  | cases {Γ : List Prop} {P Q R : Prop} : Derivation Γ (P ∨ Q) → Derivation (P :: Γ) R → Derivation (Q :: Γ) R → Derivation Γ R
  | absurd {Γ : List Prop} {P : Prop} : Derivation Γ False → Derivation Γ P

def Holds (Γ : List Prop) : Prop := ∀ P, P ∈ Γ → P

theorem extend {Γ : List Prop} {P : Prop} (h : Holds Γ) (hp : P) : Holds (P :: Γ) := by
  intro Q hQ
  rcases List.mem_cons.mp hQ with he | ht
  · subst Q
    exact hp
  · exact h Q ht

/-- Structural induction proves soundness of the propositional fragment. -/
def compile {Γ : List Prop} {P : Prop} (d : Derivation Γ P) : Holds Γ → P :=
  match d with
  | .hyp hp => fun h => h _ hp
  | .intro body => fun h hp => compile body (extend h hp)
  | .apply f a => fun h => compile f h (compile a h)
  | .pair a b => fun h => ⟨compile a h, compile b h⟩
  | .left a => fun h => (compile a h).1
  | .right a => fun h => (compile a h).2
  | .inl a => fun h => Or.inl (compile a h)
  | .inr b => fun h => Or.inr (compile b h)
  | .cases s l r => fun h => Or.elim (compile s h)
      (fun hp => compile l (extend h hp))
      (fun hq => compile r (extend h hq))
  | .absurd a => fun h => False.elim (compile a h)

/-- A typed one-hole context cannot change the statement at its interface. -/
def Context (Γ : List Prop) (Q P : Prop) := Derivation Γ Q → Derivation Γ P

theorem replacement {Γ : List Prop} {Q P : Prop}
    (k : Context Γ Q P) (d : Derivation Γ Q) (h : Holds Γ) : P :=
  compile (k d) h

/-- Composition of implications, authored as derivation data. -/
def composition (P Q R : Prop) : Derivation [Q → R, P → Q] (P → R) :=
  .intro (.apply (P := Q) (.hyp (by simp)) (.apply (P := P) (.hyp (by simp)) (.hyp (by simp))))

theorem composition_correct (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  apply compile (composition P Q R)
  exact extend (extend (by intro A hA; simp at hA) hpq) hqr

/-- A partial lens on an editable presentation; the complement is explicit. -/
structure PartialLens (S V : Type) where
  get : S → V
  put : S → V → Option S
  getPut : ∀ s, put s (get s) = some s
  putGet : ∀ s v s', put s v = some s' → get s' = v

def pairLens (V C : Type) : PartialLens (V × C) V where
  get := Prod.fst
  put s v := some (v, s.2)
  getPut := by intro s; cases s; rfl
  putGet := by intro s v s' h; cases h; rfl

end LeanDuet.TMN
