module

public import RequestProject.Sec2.Fin

/-!
# Syntax of the linear-base lineage (Sections 2.1, 5.1, 5.4)

The three linear-base calculi of the paper

* **Linear Base** (Section 2.1): `t ::= x | t₁ t₂ | λx.t | [t] | let [x] = t₁ in t₂`,
  `A ::= A ⊸ B | □_r A | K`;
* **Linear Core** (Section 5.1): Linear Base plus multiplicative products `⊗`, unit and
  additive sums `⊕`;
* **Linear Push Core** (Section 5.4): Linear Core plus `push⊗`, `push⊕`, `push_unit`;

are presented as a single family of grammars indexed by a *level* `F : LLevel`.
Constructors which only exist in the bigger calculi carry a proof that the level supports them
(e.g. `F.Core = true`), so that e.g. `LTm .base n` contains *exactly* the Linear Base terms with
`n` free variables (the other constructors are uninhabited at that level).

Variables are de Bruijn indices `Fin n`; `LTm F 0` is the type of closed terms.
In `let ⟨x, y⟩ = t₁ in t₂` the variable `y` is index `0` and `x` index `1`.
-/

@[expose] public section

namespace Coeffect

/-- The three calculi of the linear-base lineage. -/
inductive LLevel : Type
  /-- Linear Base -/
  | base
  /-- Linear Core (Linear Base + products, unit, sums) -/
  | core
  /-- Linear Push Core (Linear Core + `push` constructs) -/
  | push
  deriving DecidableEq, Repr

namespace LLevel

/-- Does the level contain products, unit and sums? -/
def Core : LLevel → Bool
  | base => false
  | _ => true

/-- Does the level contain the `push` constructs? -/
def Push : LLevel → Bool
  | push => true
  | _ => false

lemma core_of_push {F : LLevel} (h : F.Push = true) : F.Core = true := by
  cases F <;> simp_all [Push, Core]

/-- Inclusion order between the calculi (`Linear Base ⊆ Linear Core ⊆ Linear Push Core`). -/
def toNat : LLevel → ℕ
  | base => 0
  | core => 1
  | push => 2

instance : LE LLevel := ⟨fun F G => F.toNat ≤ G.toNat⟩

instance : DecidableRel (fun F G : LLevel => F ≤ G) :=
  fun F G => inferInstanceAs (Decidable (F.toNat ≤ G.toNat))

lemma core_mono {F G : LLevel} (hFG : F ≤ G) (h : F.Core = true) : G.Core = true := by
  cases F <;> cases G <;> first | rfl | exact h | exact absurd hFG (by decide)

lemma push_mono {F G : LLevel} (hFG : F ≤ G) (h : F.Push = true) : G.Push = true := by
  cases F <;> cases G <;> first | rfl | exact h | exact absurd hFG (by decide)

end LLevel

universe u

/-- Types of the linear-base lineage, over grades `R`, at level `F`:
`A ::= K | A ⊸ B | □_r A | A ⊗ B | unit | A ⊕ B`. -/
inductive LTy (R : Type u) (F : LLevel) : Type u
  /-- the base type `K` -/
  | base : LTy R F
  /-- linear functions `A ⊸ B` -/
  | lolli : LTy R F → LTy R F → LTy R F
  /-- the graded modality `□_r A` -/
  | box : R → LTy R F → LTy R F
  /-- multiplicative product `A ⊗ B` (Linear Core) -/
  | tensor : F.Core = true → LTy R F → LTy R F → LTy R F
  /-- unit (Linear Core) -/
  | unit : F.Core = true → LTy R F
  /-- additive sum `A ⊕ B` (Linear Core) -/
  | oplus : F.Core = true → LTy R F → LTy R F → LTy R F

/-- Terms of the linear-base lineage at level `F` with `n` free variables. -/
inductive LTm (F : LLevel) : ℕ → Type
  /-- variables (de Bruijn indices) -/
  | var {n : ℕ} : Fin n → LTm F n
  /-- application `t₁ t₂` -/
  | app {n : ℕ} : LTm F n → LTm F n → LTm F n
  /-- abstraction `λx. t` -/
  | lam {n : ℕ} : LTm F (n + 1) → LTm F n
  /-- promotion / boxing `[t]` -/
  | box {n : ℕ} : LTm F n → LTm F n
  /-- unboxing `let [x] = t₁ in t₂` -/
  | letbox {n : ℕ} : LTm F n → LTm F (n + 1) → LTm F n
  /-- pairing `⟨t₁, t₂⟩` -/
  | pair {n : ℕ} : F.Core = true → LTm F n → LTm F n → LTm F n
  /-- `let ⟨x, y⟩ = t₁ in t₂` -/
  | letpair {n : ℕ} : F.Core = true → LTm F n → LTm F (n + 2) → LTm F n
  /-- unit `⟨⟩` -/
  | unit {n : ℕ} : F.Core = true → LTm F n
  /-- `let ⟨⟩ = t₁ in t₂` -/
  | letunit {n : ℕ} : F.Core = true → LTm F n → LTm F n → LTm F n
  /-- `inj₁ t` -/
  | inl {n : ℕ} : F.Core = true → LTm F n → LTm F n
  /-- `inj₂ t` -/
  | inr {n : ℕ} : F.Core = true → LTm F n → LTm F n
  /-- `case t of {inj₁ x → t₁; inj₂ y → t₂}` -/
  | case {n : ℕ} : F.Core = true → LTm F n → LTm F (n + 1) → LTm F (n + 1) → LTm F n
  /-- `push⊗ t` (Linear Push Core) -/
  | pushProd {n : ℕ} : F.Push = true → LTm F n → LTm F n
  /-- `push⊕ t` (Linear Push Core) -/
  | pushSum {n : ℕ} : F.Push = true → LTm F n → LTm F n
  /-- `push_unit t` (Linear Push Core) -/
  | pushUnit {n : ℕ} : F.Push = true → LTm F n → LTm F n

namespace LTm

variable {F : LLevel}

/-- Renaming of free variables. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : LTm F n → LTm F m
  | var i => var (ρ i)
  | app t₁ t₂ => app (rename ρ t₁) (rename ρ t₂)
  | lam t => lam (rename (upRen ρ) t)
  | box t => box (rename ρ t)
  | letbox t₁ t₂ => letbox (rename ρ t₁) (rename (upRen ρ) t₂)
  | pair h t₁ t₂ => pair h (rename ρ t₁) (rename ρ t₂)
  | letpair h t₁ t₂ => letpair h (rename ρ t₁) (rename (upRen (upRen ρ)) t₂)
  | unit h => unit h
  | letunit h t₁ t₂ => letunit h (rename ρ t₁) (rename ρ t₂)
  | inl h t => inl h (rename ρ t)
  | inr h t => inr h (rename ρ t)
  | case h t t₁ t₂ => case h (rename ρ t) (rename (upRen ρ) t₁) (rename (upRen ρ) t₂)
  | pushProd h t => pushProd h (rename ρ t)
  | pushSum h t => pushSum h (rename ρ t)
  | pushUnit h t => pushUnit h (rename ρ t)

/-- Weakening by one fresh variable at index `0`. -/
abbrev shift {n : ℕ} (t : LTm F n) : LTm F (n + 1) := rename Fin.succ t

/-- Lift a substitution under a binder. -/
def upSub {n m : ℕ} (σ : Fin n → LTm F m) : Fin (n + 1) → LTm F (m + 1) :=
  var 0 .: (fun i => shift (σ i))

/-- Simultaneous (capture-avoiding) substitution. -/
def subst {n m : ℕ} (σ : Fin n → LTm F m) : LTm F n → LTm F m
  | var i => σ i
  | app t₁ t₂ => app (subst σ t₁) (subst σ t₂)
  | lam t => lam (subst (upSub σ) t)
  | box t => box (subst σ t)
  | letbox t₁ t₂ => letbox (subst σ t₁) (subst (upSub σ) t₂)
  | pair h t₁ t₂ => pair h (subst σ t₁) (subst σ t₂)
  | letpair h t₁ t₂ => letpair h (subst σ t₁) (subst (upSub (upSub σ)) t₂)
  | unit h => unit h
  | letunit h t₁ t₂ => letunit h (subst σ t₁) (subst σ t₂)
  | inl h t => inl h (subst σ t)
  | inr h t => inr h (subst σ t)
  | case h t t₁ t₂ => case h (subst σ t) (subst (upSub σ) t₁) (subst (upSub σ) t₂)
  | pushProd h t => pushProd h (subst σ t)
  | pushSum h t => pushSum h (subst σ t)
  | pushUnit h t => pushUnit h (subst σ t)

/-- Single substitution `[s/x] t` of the innermost variable. -/
abbrev subst1 {n : ℕ} (t : LTm F (n + 1)) (s : LTm F n) : LTm F n := subst (s .: var) t

/-- Double substitution `[s₁/x][s₂/y] t` for `let ⟨x, y⟩` (`y` is index `0`, `x` index `1`). -/
abbrev subst2 {n : ℕ} (t : LTm F (n + 2)) (s₁ s₂ : LTm F n) : LTm F n :=
  subst (s₂ .: s₁ .: var) t

@[simp] lemma upSub_zero {n m : ℕ} (σ : Fin n → LTm F m) : upSub σ 0 = var 0 := rfl
@[simp] lemma upSub_succ {n m : ℕ} (σ : Fin n → LTm F m) (i : Fin n) :
    upSub σ i.succ = shift (σ i) := rfl
@[simp] lemma upSub_one {n m : ℕ} (σ : Fin (n + 1) → LTm F m) :
    upSub σ 1 = shift (σ 0) := rfl

lemma rename_rename {n m k : ℕ} (t : LTm F n) (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing m k with
  | _ => simp_all [rename, upRen_comp]

lemma rename_id {n : ℕ} (t : LTm F n) : rename id t = t := by
  induction t with
  | _ => simp_all [rename, upRen_id]

lemma rename_id' {n : ℕ} (t : LTm F n) : rename (fun i => i) t = t := rename_id t

lemma upSub_upRen {n m k : ℕ} (σ : Fin m → LTm F k) (ρ : Fin n → Fin m) :
    upSub σ ∘ upRen ρ = upSub (σ ∘ ρ) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma subst_rename {n m k : ℕ} (t : LTm F n) (ρ : Fin n → Fin m) (σ : Fin m → LTm F k) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing m k with
  | _ => simp_all [rename, subst, upSub_upRen]

lemma rename_upSub {n m k : ℕ} (σ : Fin n → LTm F m) (ρ : Fin m → Fin k) :
    (fun i => rename (upRen ρ) (upSub σ i)) = upSub (fun i => rename ρ (σ i)) := by
  funext i; refine Fin.cases ?_ ?_ i
  · simp [rename]
  · intro i; simp [rename_rename, upRen_comp_succ]

lemma rename_subst {n m k : ℕ} (t : LTm F n) (σ : Fin n → LTm F m) (ρ : Fin m → Fin k) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m k with
  | _ => simp_all [rename, subst, rename_upSub]

lemma upSub_subst {n m k : ℕ} (σ : Fin n → LTm F m) (τ : Fin m → LTm F k) :
    (fun i => subst (upSub τ) (upSub σ i)) = upSub (fun i => subst τ (σ i)) := by
  funext i; refine Fin.cases ?_ ?_ i
  · simp [subst]
  · intro i
    simp only [upSub_succ, subst_rename, rename_subst]
    rfl

lemma subst_subst {n m k : ℕ} (t : LTm F n) (σ : Fin n → LTm F m) (τ : Fin m → LTm F k) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing m k with
  | _ => simp_all [subst, upSub_subst]

lemma upSub_var {n : ℕ} : upSub (var : Fin n → LTm F n) = var := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [rename]

lemma subst_var {n : ℕ} (t : LTm F n) : subst var t = t := by
  induction t with
  | _ => simp_all [subst, upSub_var]

lemma upSub_ren {n m : ℕ} (ρ : Fin n → Fin m) :
    upSub (fun i => (var (ρ i) : LTm F m)) = fun i => var (upRen ρ i) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [rename]

lemma rename_eq_subst {n m : ℕ} (t : LTm F n) (ρ : Fin n → Fin m) :
    rename ρ t = subst (fun i => var (ρ i)) t := by
  induction t generalizing m with
  | _ => simp_all [rename, subst, upSub_ren]

/-- Substituting into a shifted term ignores the new variable. -/
lemma subst1_shift {n : ℕ} (t s : LTm F n) : subst1 (shift t) s = t := by
  simp [subst_rename, Function.comp_def, subst_var]

end LTm

end Coeffect

namespace Coeffect.LTm

variable {F : LLevel}

lemma rename_shift {n m : ℕ} (t : LTm F n) (ρ : Fin n → Fin m) :
    (shift t).rename (upRen ρ) = shift (t.rename ρ) := by
  simp only [rename_rename]; rfl

lemma rename_subst1 {n m : ℕ} (t : LTm F (n + 1)) (s : LTm F n) (ρ : Fin n → Fin m) :
    (t.subst1 s).rename ρ = (t.rename (upRen ρ)).subst1 (s.rename ρ) := by
  rw [rename_subst]; show _ = subst _ (rename _ t); rw [subst_rename]
  congr 1; funext i; exact Fin.cases rfl (fun i => rfl) i

lemma rename_subst2 {n m : ℕ} (t : LTm F (n + 2)) (s₁ s₂ : LTm F n) (ρ : Fin n → Fin m) :
    (t.subst2 s₁ s₂).rename ρ = (t.rename (upRen (upRen ρ))).subst2 (s₁.rename ρ) (s₂.rename ρ) := by
  rw [rename_subst]; show _ = subst _ (rename _ t); rw [subst_rename]
  congr 1; funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

end Coeffect.LTm
