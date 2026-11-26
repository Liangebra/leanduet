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
