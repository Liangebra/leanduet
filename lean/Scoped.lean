import Lean

namespace LeanDuet.Scoped
/-- Scope-indexed syntax: a bound variable cannot refer outside its context.
    Atoms and operators remain uninterpreted until elaboration. -/
inductive Term : Nat → Type where
  | var {n : Nat} : Fin n → Term n
  | atom {n : Nat} : String → Term n
  | unary {n : Nat} : String → Term n → Term n
  | binary {n : Nat} : String → Term n → Term n → Term n
  | app {n : Nat} : Term n → Term n → Term n
  | bind {n : Nat} : String → Term n → Term (n+1) → Term n

def liftRen {n m : Nat} (r : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (r i).succ)

def rename {n m : Nat} (r : Fin n → Fin m) : Term n → Term m
  | .var i => .var (r i)
  | .atom s => .atom s
  | .unary op a => .unary op (rename r a)
  | .binary op a b => .binary op (rename r a) (rename r b)
  | .app f a => .app (rename r f) (rename r a)
  | .bind op a b => .bind op (rename r a) (rename (liftRen r) b)

theorem liftRen_id (n : Nat) : liftRen (id : Fin n → Fin n) = id := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftRen]
  · simp [liftRen]

theorem liftRen_comp {n m k : Nat} (r : Fin n → Fin m) (s : Fin m → Fin k) :
    liftRen (s ∘ r) = liftRen s ∘ liftRen r := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftRen, Function.comp_def]
  · simp [liftRen, Function.comp_def]

theorem rename_id {n : Nat} (t : Term n) : rename id t = t := by
  induction t with
  | var i => rfl
  | atom s => rfl
  | unary op a ih => simp [rename, ih]
  | binary op a b ia ib => simp [rename, ia, ib]
  | app f a hf ha => simp [rename, hf, ha]
  | bind op a b ia ib => simp [rename, liftRen_id, ia, ib]

theorem rename_comp {n m k : Nat} (t : Term n) (r : Fin n → Fin m) (s : Fin m → Fin k) :
    rename s (rename r t) = rename (s ∘ r) t := by
  induction t generalizing m k with
  | var i => rfl
  | atom x => rfl
  | unary op a ih => simp [rename, ih]
  | binary op a b ia ib => simp [rename, ia, ib]
  | app f a hf ha => simp [rename, hf, ha]
  | bind op a b ia ib =>
    simp only [rename, ia, ib, liftRen_comp]

/-- Capture-avoiding simultaneous substitution, including the lift under a binder. -/
def liftSub {n m : Nat} (s : Fin n → Term m) : Fin (n+1) → Term (m+1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (s i))

def subst {n m : Nat} (s : Fin n → Term m) : Term n → Term m
  | .var i => s i
  | .atom x => .atom x
  | .unary op a => .unary op (subst s a)
  | .binary op a b => .binary op (subst s a) (subst s b)
  | .app f a => .app (subst s f) (subst s a)
  | .bind op a b => .bind op (subst s a) (subst (liftSub s) b)

theorem liftSub_var (n : Nat) : liftSub (@Term.var n) = @Term.var (n+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftSub]
  · simp [liftSub, rename]

theorem subst_var {n : Nat} (t : Term n) : subst Term.var t = t := by
  induction t with
  | var i => rfl
  | atom x => rfl
  | unary op a ih => simp [subst, ih]
  | binary op a b ia ib => simp [subst, ia, ib]
  | app f a hf ha => simp [subst, hf, ha]
  | bind op a b ia ib => simp [subst, liftSub_var, ia, ib]


/-- Substitution after renaming is substitution along the composite map. -/
theorem liftSub_liftRen {n m k : Nat} (r : Fin n → Fin m) (s : Fin m → Term k) :
    liftSub s ∘ liftRen r = liftSub (s ∘ r) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftSub, liftRen, Function.comp_def]
  · simp [liftSub, liftRen, Function.comp_def]

theorem subst_rename {n m k : Nat} (t : Term n) (r : Fin n → Fin m) (s : Fin m → Term k) :
    subst s (rename r t) = subst (s ∘ r) t := by
  induction t generalizing m k with
  | var i => rfl
  | atom x => rfl
  | unary op a ih => simp [rename, subst, ih]
  | binary op a b ia ib => simp [rename, subst, ia, ib]
  | app f a hf ha => simp [rename, subst, hf, ha]
  | bind op a b ia ib =>
    simp only [rename, subst, ia, ib, liftSub_liftRen]

/-- Renaming after substitution acts on every substituted term. -/
theorem liftRen_liftSub {n m k : Nat} (s : Fin n → Term m) (r : Fin m → Fin k) :
    (fun i => rename (liftRen r) (liftSub s i)) =
      liftSub (fun i => rename r (s i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftSub, liftRen, rename]
  · simp only [liftSub, Fin.cases_succ, rename_comp]
    congr 1

theorem rename_subst {n m k : Nat} (t : Term n) (s : Fin n → Term m) (r : Fin m → Fin k) :
    rename r (subst s t) = subst (fun i => rename r (s i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | atom x => rfl
  | unary op a ih => simp [rename, subst, ih]
  | binary op a b ia ib => simp [rename, subst, ia, ib]
  | app f a hf ha => simp [rename, subst, hf, ha]
  | bind op a b ia ib =>
    simp only [rename, subst, ia, ib, liftRen_liftSub]

theorem liftSub_comp {n m k : Nat} (s : Fin n → Term m) (r : Fin m → Term k) :
    (fun i => subst (liftSub r) (liftSub s i)) =
      liftSub (fun i => subst r (s i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftSub, subst]
  · simp only [liftSub, Fin.cases_succ, subst_rename, rename_subst]
    congr 1

/-- Associativity of simultaneous capture-avoiding substitution.
    Together with subst_var and the variable equation, this gives the
    relative Kleisli composition laws on finite contexts. -/
theorem subst_comp {n m k : Nat} (t : Term n) (s : Fin n → Term m) (r : Fin m → Term k) :
    subst r (subst s t) = subst (fun i => subst r (s i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | atom x => rfl
  | unary op a ih => simp [subst, ih]
  | binary op a b ia ib => simp [subst, ia, ib]
  | app f a hf ha => simp [subst, hf, ha]
  | bind op a b ia ib =>
    simp only [subst, ia, ib, liftSub_comp]

abbrev Substitution (n m : Nat) := Fin n → Term m

def composeSub {n m k : Nat} (s : Substitution n m) (r : Substitution m k) : Substitution n k :=
  fun i => subst r (s i)

theorem composeSub_id_left {n m : Nat} (s : Substitution n m) :
    composeSub Term.var s = s := rfl

theorem composeSub_id_right {n m : Nat} (s : Substitution n m) :
    composeSub s Term.var = s := by
  funext i
  exact subst_var (s i)

theorem composeSub_assoc {n m k l : Nat} (s : Substitution n m)
    (r : Substitution m k) (q : Substitution k l) :
    composeSub (composeSub s r) q = composeSub s (composeSub r q) := by
  funext i
  exact subst_comp (s i) r q

/-- A concrete capture-avoidance test: inserting free variable 0 under
    a binder must shift it to 1, not turn it into the binder's variable. -/
example :
    subst (fun _ : Fin 1 => Term.var (0 : Fin 1))
      (Term.bind "∀" (.atom "Nat") (.var (1 : Fin 2))) =
    (Term.bind "∀" (.atom "Nat") (.var (1 : Fin 2)) : Term 1) := by
  rfl

end LeanDuet.Scoped

namespace LeanDuet.Context
universe u

/-- A concrete families-of-types model. Context substitutions are functions
    Δ → Γ, and reindexing acts contravariantly on families. -/
abbrev Ty (Γ : Type u) := Γ → Type u
abbrev Tm {Γ : Type u} (A : Ty Γ) := (γ : Γ) → A γ

def reindex {Γ Δ : Type u} (A : Ty Γ) (σ : Δ → Γ) : Ty Δ :=
  A ∘ σ

def reindexTerm {Γ Δ : Type u} {A : Ty Γ} (t : Tm A) (σ : Δ → Γ) :
    Tm (reindex A σ) := fun δ => t (σ δ)

theorem reindex_id {Γ : Type u} (A : Ty Γ) : reindex A id = A := rfl

theorem reindex_comp {Γ Δ Θ : Type u} (A : Ty Γ) (σ : Δ → Γ) (τ : Θ → Δ) :
    reindex (reindex A σ) τ = reindex A (σ ∘ τ) := rfl

/-- Context comprehension: extending Γ by A is the dependent sum. -/
abbrev Extend {Γ : Type u} (A : Ty Γ) := Sigma A

def pair {Γ Δ : Type u} {A : Ty Γ} (σ : Δ → Γ) (t : Tm (reindex A σ)) :
    Δ → Extend A := fun δ => ⟨σ δ,t δ⟩

theorem pair_projection {Γ Δ : Type u} {A : Ty Γ} (σ : Δ → Γ)
    (t : Tm (reindex A σ)) : (fun δ => (pair σ t δ).1) = σ := rfl

/-- Universal property of the extension in the concrete model:
    every map into the extension is reconstructed from its projections. -/
theorem pair_eta {Γ Δ : Type u} {A : Ty Γ} (f : Δ → Extend A) :
    pair (fun δ => (f δ).1) (fun δ => (f δ).2) = f := by
  funext δ
  change (⟨(f δ).1, (f δ).2⟩ : Extend A) = f δ
  cases f δ
  rfl

end LeanDuet.Context

/-!
An initial typed, interpreted fragment for the scope-indexed syntax in
`Scoped.lean`. This language has only natural-number variables, zero,
successor, addition, equality, conjunction, implication, and universal
quantification over `Nat`. It is not a Lean `Expr` codec or a model of arbitrary
dependent types. Its purpose is to check that capture-avoiding substitution in
a small mathematical language agrees with its Lean interpretation.
-/
namespace LeanDuet.ScopedSemantics

inductive NatExpr : Nat → Type where
  | var {n : Nat} : Fin n → NatExpr n
  | zero {n : Nat} : NatExpr n
  | succ {n : Nat} : NatExpr n → NatExpr n
  | add {n : Nat} : NatExpr n → NatExpr n → NatExpr n
  deriving Repr

def liftRen {n m : Nat} (r : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (r i).succ)

def rename {n m : Nat} (r : Fin n → Fin m) : NatExpr n → NatExpr m
  | .var i => .var (r i)
  | .zero => .zero
  | .succ a => .succ (rename r a)
  | .add a b => .add (rename r a) (rename r b)

def liftSub {n m : Nat} (s : Fin n → NatExpr m) : Fin (n+1) → NatExpr (m+1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (s i))

def subst {n m : Nat} (s : Fin n → NatExpr m) : NatExpr n → NatExpr m
  | .var i => s i
  | .zero => .zero
  | .succ a => .succ (subst s a)
  | .add a b => .add (subst s a) (subst s b)

abbrev Env (n : Nat) := Fin n → Nat

def extend (ρ : Env n) (x : Nat) : Env (n+1) := Fin.cases x ρ

def denoteNat {n : Nat} : NatExpr n → Env n → Nat
  | .var i, ρ => ρ i
  | .zero, _ => 0
  | .succ a, ρ => Nat.succ (denoteNat a ρ)
  | .add a b, ρ => denoteNat a ρ + denoteNat b ρ

theorem denoteNat_rename {n m : Nat} (e : NatExpr n) (r : Fin n → Fin m)
    (ρ : Env m) :
    denoteNat (rename r e) ρ = denoteNat e (fun i => ρ (r i)) := by
  induction e with
  | var i => rfl
  | zero => rfl
  | succ a ih => simp [rename, denoteNat, ih]
  | add a b ia ib => simp [rename, denoteNat, ia, ib]

theorem denoteNat_subst {n m : Nat} (e : NatExpr n) (s : Fin n → NatExpr m)
    (ρ : Env m) :
    denoteNat (subst s e) ρ = denoteNat e (fun i => denoteNat (s i) ρ) := by
  induction e with
  | var i => rfl
  | zero => rfl
  | succ a ih => simp [subst, denoteNat, ih]
  | add a b ia ib => simp [subst, denoteNat, ia, ib]

inductive Formula : Nat → Type where
  | truth {n : Nat} : Formula n
  | falsity {n : Nat} : Formula n
  | equal {n : Nat} : NatExpr n → NatExpr n → Formula n
  | and {n : Nat} : Formula n → Formula n → Formula n
  | imp {n : Nat} : Formula n → Formula n → Formula n
  | all {n : Nat} : Formula (n+1) → Formula n
  | existsNat {n : Nat} : Formula (n+1) → Formula n
  deriving Repr

def substFormula {n m : Nat} (s : Fin n → NatExpr m) : Formula n → Formula m
  | .truth => .truth
  | .falsity => .falsity
  | .equal a b => .equal (subst s a) (subst s b)
  | .and p q => .and (substFormula s p) (substFormula s q)
  | .imp p q => .imp (substFormula s p) (substFormula s q)
  | .all p => .all (substFormula (liftSub s) p)
  | .existsNat p => .existsNat (substFormula (liftSub s) p)

def denote {n : Nat} : Formula n → Env n → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .equal a b, ρ => denoteNat a ρ = denoteNat b ρ
  | .and p q, ρ => denote p ρ ∧ denote q ρ
  | .imp p q, ρ => denote p ρ → denote q ρ
  | .all p, ρ => ∀ x : Nat, denote p (extend ρ x)
  | .existsNat p, ρ => ∃ x : Nat, denote p (extend ρ x)

theorem denote_liftSub_env {n m : Nat} (s : Fin n → NatExpr m)
    (ρ : Env m) (x : Nat) :
    (fun i => denoteNat (liftSub s i) (extend ρ x)) =
      extend (fun i => denoteNat (s i) ρ) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftSub, extend, denoteNat]
  · simp [liftSub, denoteNat_rename, extend]

/-- Substitution commutes with interpretation. Under a quantifier the lifted
    substitution maps the new variable to itself and weakens every old term. -/
theorem denote_subst {n m : Nat} (p : Formula n) (s : Fin n → NatExpr m)
    (ρ : Env m) :
    denote (substFormula s p) ρ = denote p (fun i => denoteNat (s i) ρ) := by
  induction p generalizing m ρ with
  | truth => rfl
  | falsity => rfl
  | equal a b => simp [substFormula, denote, denoteNat_subst]
  | and p q hp hq => simp [substFormula, denote, hp, hq]
  | imp p q hp hq => simp [substFormula, denote, hp, hq]
  | all p ih =>
      simp [substFormula, denote, ih, denote_liftSub_env]
  | existsNat p ih =>
      -- The induction hypothesis transports each witness proposition in both
      -- directions. Since this theorem states equality of Prop values, finish
      -- by propositional extensionality rather than identifying proof terms.
      change (∃ x : Nat, denote (substFormula (liftSub s) p) (extend ρ x)) =
        (∃ x : Nat, denote p (extend (fun i => denoteNat (s i) ρ) x))
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        have envAgreement := ih (liftSub s) (extend ρ x)
        rw [denote_liftSub_env] at envAgreement
        exact Eq.mp envAgreement hx
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        have envAgreement := ih (liftSub s) (extend ρ x)
        rw [denote_liftSub_env] at envAgreement
        exact Eq.mpr envAgreement hx

/-- Forget the typing and interpretation annotations into the existing generic
    scope-indexed syntax. This map is only for the fragment above. -/
def eraseNat {n : Nat} : NatExpr n → LeanDuet.Scoped.Term n
  | .var i => .var i
  | .zero => .atom "Nat.zero"
  | .succ a => .unary "Nat.succ" (eraseNat a)
  | .add a b => .binary "Nat.add" (eraseNat a) (eraseNat b)

def eraseFormula {n : Nat} : Formula n → LeanDuet.Scoped.Term n
  | .truth => .atom "True"
  | .falsity => .atom "False"
  | .equal a b => .binary "Eq" (eraseNat a) (eraseNat b)
  | .and p q => .binary "And" (eraseFormula p) (eraseFormula q)
  | .imp p q => .binary "Imp" (eraseFormula p) (eraseFormula q)
  | .all p => .bind "∀ Nat" (.atom "Nat") (eraseFormula p)
  | .existsNat p => .bind "∃ Nat" (.atom "Nat") (eraseFormula p)

theorem eraseNat_rename {n m : Nat} (e : NatExpr n) (r : Fin n → Fin m) :
    eraseNat (rename r e) = LeanDuet.Scoped.rename r (eraseNat e) := by
  induction e with
  | var i => rfl
  | zero => rfl
  | succ a ih => simp [rename, eraseNat, LeanDuet.Scoped.rename, ih]
  | add a b ia ib => simp [rename, eraseNat, LeanDuet.Scoped.rename, ia, ib]

theorem eraseNat_subst {n m : Nat} (e : NatExpr n) (s : Fin n → NatExpr m) :
    eraseNat (subst s e) =
      LeanDuet.Scoped.subst (fun i => eraseNat (s i)) (eraseNat e) := by
  induction e with
  | var i => rfl
  | zero => rfl
  | succ a ih => simp [subst, eraseNat, LeanDuet.Scoped.subst, ih]
  | add a b ia ib => simp [subst, eraseNat, LeanDuet.Scoped.subst, ia, ib]

theorem eraseNat_liftSub {n m : Nat} (s : Fin n → NatExpr m) :
    (fun i => eraseNat (liftSub s i)) =
      LeanDuet.Scoped.liftSub (fun i => eraseNat (s i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [liftSub, eraseNat_rename, LeanDuet.Scoped.liftSub]

theorem eraseFormula_subst {n m : Nat} (p : Formula n) (s : Fin n → NatExpr m) :
    eraseFormula (substFormula s p) =
      LeanDuet.Scoped.subst (fun i => eraseNat (s i)) (eraseFormula p) := by
  induction p generalizing m with
  | truth => rfl
  | falsity => rfl
  | equal a b => simp [substFormula, eraseFormula, eraseNat_subst, LeanDuet.Scoped.subst]
  | and p q hp hq => simp [substFormula, eraseFormula, LeanDuet.Scoped.subst, hp, hq]
  | imp p q hp hq => simp [substFormula, eraseFormula, LeanDuet.Scoped.subst, hp, hq]
  | all p ih =>
      simp only [substFormula, eraseFormula, LeanDuet.Scoped.subst]
      rw [ih (liftSub s)]
      rw [eraseNat_liftSub s]
  | existsNat p ih =>
      simp only [substFormula, eraseFormula, LeanDuet.Scoped.subst]
      rw [ih (liftSub s)]
      rw [eraseNat_liftSub s]

/-- A substitution into two free variables specializes to a one-variable
    context without capturing the binder in the formula. -/
example (ρ : Env 1) :
    denote
      (substFormula (fun _ : Fin 2 => NatExpr.var 0)
        (Formula.all (n := 2) (Formula.equal (n := 3) (NatExpr.var 1) (NatExpr.var 0)))) ρ =
      denote (Formula.all (n := 2) (Formula.equal (n := 3) (NatExpr.var 1) (NatExpr.var 0)))
        (fun _ : Fin 2 => ρ 0) := by
  exact denote_subst
    (Formula.all (n := 2) (Formula.equal (n := 3) (NatExpr.var 1) (NatExpr.var 0)))
    (fun _ : Fin 2 => NatExpr.var 0) ρ

/-- The existential case exercises the same lifted substitution while keeping
    the witness bound. Replacing the outer object must leave the witness slot
    untouched. -/
example (ρ : Env 0) :
    let p : Formula 1 :=
      Formula.existsNat (n := 1)
        (Formula.equal (n := 2) (NatExpr.var (1 : Fin 2)) (NatExpr.var (0 : Fin 2)))
    denote (substFormula (fun _ : Fin 1 => NatExpr.zero) p) ρ =
      denote p (fun _ : Fin 1 => 0) := by
  exact denote_subst _ _ _

example :
    let p : Formula 1 :=
      Formula.existsNat (n := 1)
        (Formula.equal (n := 2) (NatExpr.var (1 : Fin 2)) (NatExpr.var (0 : Fin 2)))
    (eraseFormula (substFormula (fun _ : Fin 1 => (NatExpr.zero : NatExpr 0)) p) :
      LeanDuet.Scoped.Term 0) =
      LeanDuet.Scoped.subst
        (fun _ : Fin 1 => (LeanDuet.Scoped.Term.atom "Nat.zero" : LeanDuet.Scoped.Term 0))
        (eraseFormula p) := by
  simpa [eraseNat] using
    (eraseFormula_subst
      (Formula.existsNat (n := 1)
        (Formula.equal (n := 2) (NatExpr.var (1 : Fin 2)) (NatExpr.var (0 : Fin 2))))
      (fun _ : Fin 1 => (NatExpr.zero : NatExpr 0)))

end LeanDuet.ScopedSemantics
