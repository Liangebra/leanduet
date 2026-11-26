import Lean

namespace LeanDuet.TMN

/-- Unlike a membership proof in Prop, a slot preserves variable identity. -/
inductive Slot : List Prop → Prop → Type where
  | here {Γ : List Prop} {P : Prop} : Slot (P :: Γ) P
  | there {Γ : List Prop} {P Q : Prop} : Slot Γ P → Slot (Q :: Γ) P

def Slot.index {Γ : List Prop} {P : Prop} (s : Slot Γ P) : Nat :=
  match s with
  | .here => 0
  | .there t => t.index + 1

theorem Slot.mem {Γ : List Prop} {P : Prop} (s : Slot Γ P) : P ∈ Γ := by
  induction s with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

example (P : Prop) : (Slot.here : Slot [P,P] P).index ≠
    (Slot.there Slot.here : Slot [P,P] P).index := by
  change 0 ≠ 1
  decide

/-- A proof object is data, not a proposition: different derivations remain distinguishable. -/
inductive Derivation : List Prop → Prop → Type where
  | hyp {Γ : List Prop} {P : Prop} : Slot Γ P → Derivation Γ P
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
  | .hyp hp => fun h => h _ hp.mem
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
  .intro (.apply (P := Q) (.hyp (.there .here)) (.apply (P := P) (.hyp (.there (.there .here))) (.hyp .here)))

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

/-- A syntactic one-hole context. Δ,Q are the hole interface; Γ,P are the result. -/
inductive Hole (Δ : List Prop) (Q : Prop) : List Prop → Prop → Type where
  | here : Hole Δ Q Δ Q
  | intro {Γ : List Prop} {A B : Prop} :
      Hole Δ Q (A :: Γ) B → Hole Δ Q Γ (A → B)
  | applyFn {Γ : List Prop} {A B : Prop} :
      Hole Δ Q Γ (A → B) → Derivation Γ A → Hole Δ Q Γ B
  | applyArg {Γ : List Prop} {A B : Prop} :
      Derivation Γ (A → B) → Hole Δ Q Γ A → Hole Δ Q Γ B
  | pairLeft {Γ : List Prop} {A B : Prop} :
      Hole Δ Q Γ A → Derivation Γ B → Hole Δ Q Γ (A ∧ B)
  | pairRight {Γ : List Prop} {A B : Prop} :
      Derivation Γ A → Hole Δ Q Γ B → Hole Δ Q Γ (A ∧ B)
  | left {Γ : List Prop} {A B : Prop} :
      Hole Δ Q Γ (A ∧ B) → Hole Δ Q Γ A
  | right {Γ : List Prop} {A B : Prop} :
      Hole Δ Q Γ (A ∧ B) → Hole Δ Q Γ B
  | inl {Γ : List Prop} {A B : Prop} :
      Hole Δ Q Γ A → Hole Δ Q Γ (A ∨ B)
  | inr {Γ : List Prop} {A B : Prop} :
      Hole Δ Q Γ B → Hole Δ Q Γ (A ∨ B)
  | casesScrutinee {Γ : List Prop} {A B C : Prop} :
      Hole Δ Q Γ (A ∨ B) → Derivation (A :: Γ) C → Derivation (B :: Γ) C → Hole Δ Q Γ C
  | casesLeft {Γ : List Prop} {A B C : Prop} :
      Derivation Γ (A ∨ B) → Hole Δ Q (A :: Γ) C → Derivation (B :: Γ) C → Hole Δ Q Γ C
  | casesRight {Γ : List Prop} {A B C : Prop} :
      Derivation Γ (A ∨ B) → Derivation (A :: Γ) C → Hole Δ Q (B :: Γ) C → Hole Δ Q Γ C
  | absurd {Γ : List Prop} {A : Prop} :
      Hole Δ Q Γ False → Hole Δ Q Γ A

def Hole.plug {Δ Γ : List Prop} {Q P : Prop}
    (k : Hole Δ Q Γ P) (d : Derivation Δ Q) : Derivation Γ P :=
  match k with
  | .here => d
  | .intro b => .intro (b.plug d)
  | .applyFn f a => .apply (f.plug d) a
  | .applyArg f a => .apply f (a.plug d)
  | .pairLeft a b => .pair (a.plug d) b
  | .pairRight a b => .pair a (b.plug d)
  | .left a => .left (a.plug d)
  | .right a => .right (a.plug d)
  | .inl a => .inl (a.plug d)
  | .inr b => .inr (b.plug d)
  | .casesScrutinee s l r => .cases (s.plug d) l r
  | .casesLeft s l r => .cases s (l.plug d) r
  | .casesRight s l r => .cases s l (r.plug d)
  | .absurd a => .absurd (a.plug d)

theorem Hole.sound {Δ Γ : List Prop} {Q P : Prop}
    (k : Hole Δ Q Γ P) (d : Derivation Δ Q) (h : Holds Γ) : P :=
  compile (k.plug d) h

def compositionHole (P Q R : Prop) :
    Hole [P, Q → R, P → Q] Q [Q → R, P → Q] (P → R) :=
  .intro (.applyArg (.hyp (.there .here)) .here)

example (P Q R : Prop) :
    (compositionHole P Q R).plug
      (.apply (P := P) (.hyp (.there (.there .here))) (.hyp .here)) =
      composition P Q R := rfl

end LeanDuet.TMN
