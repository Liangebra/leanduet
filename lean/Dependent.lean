import Lean

namespace LeanDuet.Dependent
universe u

/-- A semantic context is a type of environments. Its propositions and
    object types are families over that context. This is a shallow model:
    it does not claim completeness for Lean's full dependent type theory. -/
abbrev Family (Γ : Type u) := Γ → Type u
abbrev Predicate (Γ : Type u) := Γ → Prop
abbrev Section {Γ : Type u} (A : Family Γ) := (γ : Γ) → A γ

/-- Context extension by an object or a hypothesis, respectively. -/
abbrev Extend {Γ : Type u} (A : Family Γ) := Sigma A
abbrev Assume {Γ : Type u} (P : Predicate Γ) := Subtype P

inductive Narrative : (Γ : Type u) → Predicate Γ → Type (u+1) where
  | known {Γ : Type u} {P : Predicate Γ} :
      ((γ : Γ) → P γ) → Narrative Γ P
  | hyp {Γ : Type u} {P : Predicate Γ} :
      Narrative (Assume P) (fun γ => P γ.val)
  | pull {Γ Δ : Type u} {P : Predicate Γ} :
      (f : Δ → Γ) → Narrative Γ P → Narrative Δ (fun δ => P (f δ))
  | impI {Γ : Type u} {P Q : Predicate Γ} :
      Narrative (Assume P) (fun γ => Q γ.val) →
      Narrative Γ (fun γ => P γ → Q γ)
  | impE {Γ : Type u} {P Q : Predicate Γ} :
      Narrative Γ (fun γ => P γ → Q γ) → Narrative Γ P → Narrative Γ Q
  | allI {Γ : Type u} {A : Family Γ} {P : (γ : Γ) → A γ → Prop} :
      Narrative (Extend A) (fun s => P s.1 s.2) →
      Narrative Γ (fun γ => ∀ a : A γ, P γ a)
  | allE {Γ : Type u} {A : Family Γ} {P : (γ : Γ) → A γ → Prop} :
      Narrative Γ (fun γ => ∀ a : A γ, P γ a) →
      (w : Section A) → Narrative Γ (fun γ => P γ (w γ))
  | exI {Γ : Type u} {A : Family Γ} {P : (γ : Γ) → A γ → Prop} :
      (w : Section A) → Narrative Γ (fun γ => P γ (w γ)) →
      Narrative Γ (fun γ => ∃ a : A γ, P γ a)
  | exE {Γ : Type u} {A : Family Γ} {P : (γ : Γ) → A γ → Prop} {Q : Predicate Γ} :
      Narrative Γ (fun γ => ∃ a : A γ, P γ a) →
      Narrative (Subtype (fun s : Extend A => P s.1 s.2)) (fun s => Q s.val.1) →
      Narrative Γ Q
  | transport {Γ : Type u} {A : Family Γ} {B : (γ : Γ) → A γ → Prop}
      {x y : Section A} :
      Narrative Γ (fun γ => x γ = y γ) →
      Narrative Γ (fun γ => B γ (x γ)) → Narrative Γ (fun γ => B γ (y γ))

def compile {Γ : Type u} {P : Predicate Γ} (d : Narrative Γ P) : (γ : Γ) → P γ :=
  match d with
  | .known h => h
  | .hyp => fun γ => γ.property
  | .pull f p => fun δ => compile p (f δ)
  | .impI b => fun γ h => compile b ⟨γ,h⟩
  | .impE f a => fun γ => compile f γ (compile a γ)
  | .allI b => fun γ a => compile b ⟨γ,a⟩
  | .allE f w => fun γ => compile f γ (w γ)
  | .exI w p => fun γ => ⟨w γ, compile p γ⟩
  | .exE s b => fun γ => Exists.elim (compile s γ) (fun a h => compile b ⟨⟨γ,a⟩,h⟩)
  | @Narrative.transport _ _ B _ _ e p => fun γ =>
      Eq.mp (congrArg (B γ) (compile e γ)) (compile p γ)

/-- A witness is a section together with its own dependent proof obligation. -/
structure CertifiedWitness {Γ : Type u} (A : Family Γ) (P : (γ : Γ) → A γ → Prop) where
  witness : Section A
  evidence : Narrative Γ (fun γ => P γ (witness γ))

def CertifiedWitness.close {Γ : Type u} {A : Family Γ} {P : (γ : Γ) → A γ → Prop}
    (w : CertifiedWitness A P) : Narrative Γ (fun γ => ∃ a : A γ, P γ a) :=
  .exI w.witness w.evidence

/-- Changing the witness requires evidence for the new fibre, not merely
    another object of the same carrier type. -/
def CertifiedWitness.replace {Γ : Type u} {A : Family Γ} {P : (γ : Γ) → A γ → Prop}
    (_old : CertifiedWitness A P) (w : Section A)
    (proof : Narrative Γ (fun γ => P γ (w γ))) : CertifiedWitness A P :=
  ⟨w, proof⟩

theorem witnessReplacementSound {Γ : Type u} {A : Family Γ}
    {P : (γ : Γ) → A γ → Prop} (old : CertifiedWitness A P)
    (w : Section A) (p : Narrative Γ (fun γ => P γ (w γ))) (γ : Γ) :
    ∃ a : A γ, P γ a := compile (old.replace w p).close γ

def transportSection {Γ : Type u} {A : Family Γ} {B : (γ : Γ) → A γ → Type u}
    {x y : Section A} (e : (γ : Γ) → x γ = y γ)
    (s : (γ : Γ) → B γ (x γ)) : (γ : Γ) → B γ (y γ) :=
  fun γ => cast (congrArg (B γ) (e γ)) (s γ)

/-- Nondependent carrier equality is insufficient for an arbitrary witness change. -/
theorem witnessCounterexample : (0 : Nat) = 0 ∧ ¬ ((1 : Nat) = 0) := by decide

-- A genuinely dependent statement: for each natural number n, Fin (n+1) is inhabited.
def finWitness : CertifiedWitness (fun n : Nat => Fin (n+1)) (fun _ x => x.val = 0) :=
  ⟨fun n => ⟨0, Nat.zero_lt_succ n⟩, .known (fun _ => rfl)⟩

example (n : Nat) : ∃ x : Fin (n+1), x.val = 0 :=
  compile finWitness.close n

example : Narrative Unit (fun _ => ∀ n : Nat, n = n) :=
  .allI (.known (fun _ => rfl))

example (n : Nat) : ∃ x : Nat, x = n :=
  compile (.exI (A := fun _ : Nat => Nat) (P := fun γ x => x = γ)
    (fun γ => γ) (.known (fun _ => rfl))) n

end LeanDuet.Dependent
