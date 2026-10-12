module

public import RequestProject.Sec2.Fin

/-!
# Syntax of the graded-base lineage (Sections 2.2, 3.1, 5.3)

The three (monomorphic) graded-base calculi of the paper

* **Graded Base** (Section 2.2): `t ::= x | t₁ t₂ | λx.t`, `A ::= A →^r B | K`;
* **Graded Modal Base** (Section 3.1): Graded Base plus `[t]`, `let [x] = t₁ in t₂` and `□_r A`;
* **Graded Modal Core** (Section 5.3): Graded Modal Base plus products `×`, unit and sums `+`;

are presented as one family of grammars indexed by a level `F : GLevel`, exactly as for the
linear lineage. (Graded Poly Base, which additionally has type variables, is in `Sec4`.)

Variables are de Bruijn indices `Fin n`; `GTm F 0` is the type of closed terms.
-/

@[expose] public section

namespace Coeffect

/-- The three monomorphic calculi of the graded-base lineage. -/
inductive GLevel : Type
  /-- Graded Base -/
  | base
  /-- Graded Modal Base (Graded Base + graded modality) -/
  | modal
  /-- Graded Modal Core (Graded Modal Base + products, unit, sums) -/
  | core
  deriving DecidableEq, Repr

namespace GLevel

/-- Does the level contain the graded modality? -/
def Modal : GLevel → Bool
  | base => false
  | _ => true

/-- Does the level contain products, unit and sums? -/
def Core : GLevel → Bool
  | core => true
  | _ => false

lemma modal_of_core {F : GLevel} (h : F.Core) : F.Modal = true := by
  cases F <;> simp_all [Modal, Core]

/-- Inclusion order (`Graded Base ⊆ Graded Modal Base ⊆ Graded Modal Core`). -/
def toNat : GLevel → ℕ
  | base => 0
  | modal => 1
  | core => 2

instance : LE GLevel := ⟨fun F G => F.toNat ≤ G.toNat⟩

instance : DecidableRel (fun F G : GLevel => F ≤ G) :=
  fun F G => inferInstanceAs (Decidable (F.toNat ≤ G.toNat))

lemma modal_mono {F G : GLevel} (hFG : F ≤ G) (h : F.Modal = true) : G.Modal = true := by
  cases F <;> cases G <;> first | rfl | exact h | exact absurd hFG (by decide)

lemma core_mono {F G : GLevel} (hFG : F ≤ G) (h : F.Core) : G.Core := by
  cases F <;> cases G <;> first | rfl | exact h | exact absurd hFG (by decide)

end GLevel

universe u

/-- Types of the graded-base lineage: `A ::= K | A →^r B | □_r A | A × B | unit | A + B`. -/
inductive GTy (R : Type u) (F : GLevel) : Type u
  /-- the base type `K` -/
  | base : GTy R F
  /-- graded functions `A →^r B` -/
  | fn : R → GTy R F → GTy R F → GTy R F
  /-- the graded modality `□_r A` (Graded Modal Base) -/
  | box : F.Modal = true → R → GTy R F → GTy R F
  /-- products `A × B` (Graded Modal Core) -/
  | prod : F.Core → GTy R F → GTy R F → GTy R F
  /-- unit (Graded Modal Core) -/
  | unit : F.Core → GTy R F
  /-- sums `A + B` (Graded Modal Core) -/
  | sum : F.Core → GTy R F → GTy R F → GTy R F

/-- Terms of the graded-base lineage at level `F` with `n` free variables. -/
inductive GTm (F : GLevel) : ℕ → Type
  | var {n : ℕ} : Fin n → GTm F n
  | app {n : ℕ} : GTm F n → GTm F n → GTm F n
  | lam {n : ℕ} : GTm F (n + 1) → GTm F n
  /-- `[t]` (Graded Modal Base) -/
  | box {n : ℕ} : F.Modal = true → GTm F n → GTm F n
  /-- `let [x] = t₁ in t₂` (Graded Modal Base) -/
  | letbox {n : ℕ} : F.Modal = true → GTm F n → GTm F (n + 1) → GTm F n
  | pair {n : ℕ} : F.Core → GTm F n → GTm F n → GTm F n
  /-- `let ⟨x, y⟩ = t₁ in t₂` (`y` is index `0`, `x` index `1`) -/
  | letpair {n : ℕ} : F.Core → GTm F n → GTm F (n + 2) → GTm F n
  | unit {n : ℕ} : F.Core → GTm F n
  | letunit {n : ℕ} : F.Core → GTm F n → GTm F n → GTm F n
  | inl {n : ℕ} : F.Core → GTm F n → GTm F n
  | inr {n : ℕ} : F.Core → GTm F n → GTm F n
  | case {n : ℕ} : F.Core → GTm F n → GTm F (n + 1) → GTm F (n + 1) → GTm F n

namespace GTm

variable {F : GLevel}

/-- Renaming of free variables. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : GTm F n → GTm F m
  | var i => var (ρ i)
  | app t₁ t₂ => app (rename ρ t₁) (rename ρ t₂)
  | lam t => lam (rename (upRen ρ) t)
  | box h t => box h (rename ρ t)
  | letbox h t₁ t₂ => letbox h (rename ρ t₁) (rename (upRen ρ) t₂)
  | pair h t₁ t₂ => pair h (rename ρ t₁) (rename ρ t₂)
  | letpair h t₁ t₂ => letpair h (rename ρ t₁) (rename (upRen (upRen ρ)) t₂)
  | unit h => unit h
  | letunit h t₁ t₂ => letunit h (rename ρ t₁) (rename ρ t₂)
  | inl h t => inl h (rename ρ t)
  | inr h t => inr h (rename ρ t)
  | case h t t₁ t₂ => case h (rename ρ t) (rename (upRen ρ) t₁) (rename (upRen ρ) t₂)

/-- Weakening by one fresh variable at index `0`. -/
abbrev shift {n : ℕ} (t : GTm F n) : GTm F (n + 1) := rename Fin.succ t

/-- Lift a substitution under a binder. -/
def upSub {n m : ℕ} (σ : Fin n → GTm F m) : Fin (n + 1) → GTm F (m + 1) :=
  var 0 .: (fun i => shift (σ i))

/-- Simultaneous substitution. -/
def subst {n m : ℕ} (σ : Fin n → GTm F m) : GTm F n → GTm F m
  | var i => σ i
  | app t₁ t₂ => app (subst σ t₁) (subst σ t₂)
  | lam t => lam (subst (upSub σ) t)
  | box h t => box h (subst σ t)
  | letbox h t₁ t₂ => letbox h (subst σ t₁) (subst (upSub σ) t₂)
  | pair h t₁ t₂ => pair h (subst σ t₁) (subst σ t₂)
  | letpair h t₁ t₂ => letpair h (subst σ t₁) (subst (upSub (upSub σ)) t₂)
  | unit h => unit h
  | letunit h t₁ t₂ => letunit h (subst σ t₁) (subst σ t₂)
  | inl h t => inl h (subst σ t)
  | inr h t => inr h (subst σ t)
  | case h t t₁ t₂ => case h (subst σ t) (subst (upSub σ) t₁) (subst (upSub σ) t₂)

/-- Single substitution `[s/x] t`. -/
abbrev subst1 {n : ℕ} (t : GTm F (n + 1)) (s : GTm F n) : GTm F n := subst (s .: var) t

/-- Double substitution `[s₁/x][s₂/y] t` (`y` is index `0`, `x` index `1`). -/
abbrev subst2 {n : ℕ} (t : GTm F (n + 2)) (s₁ s₂ : GTm F n) : GTm F n :=
  subst (s₂ .: s₁ .: var) t

@[simp] lemma upSub_zero {n m : ℕ} (σ : Fin n → GTm F m) : upSub σ 0 = var 0 := rfl
@[simp] lemma upSub_succ {n m : ℕ} (σ : Fin n → GTm F m) (i : Fin n) :
    upSub σ i.succ = shift (σ i) := rfl
@[simp] lemma upSub_one {n m : ℕ} (σ : Fin (n + 1) → GTm F m) :
    upSub σ 1 = shift (σ 0) := rfl

lemma rename_rename {n m k : ℕ} (t : GTm F n) (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing m k with
  | _ => simp_all [rename, upRen_comp]

lemma rename_id {n : ℕ} (t : GTm F n) : rename id t = t := by
  induction t with
  | _ => simp_all [rename, upRen_id]

lemma upSub_upRen {n m k : ℕ} (σ : Fin m → GTm F k) (ρ : Fin n → Fin m) :
    upSub σ ∘ upRen ρ = upSub (σ ∘ ρ) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma subst_rename {n m k : ℕ} (t : GTm F n) (ρ : Fin n → Fin m) (σ : Fin m → GTm F k) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing m k with
  | _ => simp_all [rename, subst, upSub_upRen]

lemma rename_upSub {n m k : ℕ} (σ : Fin n → GTm F m) (ρ : Fin m → Fin k) :
    (fun i => rename (upRen ρ) (upSub σ i)) = upSub (fun i => rename ρ (σ i)) := by
  funext i; refine Fin.cases ?_ ?_ i
  · simp [rename]
  · intro i; simp [rename_rename, upRen_comp_succ]

lemma rename_subst {n m k : ℕ} (t : GTm F n) (σ : Fin n → GTm F m) (ρ : Fin m → Fin k) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m k with
  | _ => simp_all [rename, subst, rename_upSub]

lemma upSub_subst {n m k : ℕ} (σ : Fin n → GTm F m) (τ : Fin m → GTm F k) :
    (fun i => subst (upSub τ) (upSub σ i)) = upSub (fun i => subst τ (σ i)) := by
  funext i; refine Fin.cases ?_ ?_ i
  · simp [subst]
  · intro i
    simp only [upSub_succ, subst_rename, rename_subst]
    rfl

lemma subst_subst {n m k : ℕ} (t : GTm F n) (σ : Fin n → GTm F m) (τ : Fin m → GTm F k) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing m k with
  | _ => simp_all [subst, upSub_subst]

lemma upSub_var {n : ℕ} : upSub (var : Fin n → GTm F n) = var := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [rename]

lemma subst_var {n : ℕ} (t : GTm F n) : subst var t = t := by
  induction t with
  | _ => simp_all [subst, upSub_var]

lemma upSub_ren {n m : ℕ} (ρ : Fin n → Fin m) :
    upSub (fun i => (var (ρ i) : GTm F m)) = fun i => var (upRen ρ i) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [rename]

lemma rename_eq_subst {n m : ℕ} (t : GTm F n) (ρ : Fin n → Fin m) :
    rename ρ t = subst (fun i => var (ρ i)) t := by
  induction t generalizing m with
  | _ => simp_all [rename, subst, upSub_ren]

lemma subst1_shift {n : ℕ} (t s : GTm F n) : subst1 (shift t) s = t := by
  simp [subst_rename, Function.comp_def, subst_var]

end GTm

end Coeffect

namespace Coeffect.GTm

variable {F : GLevel}

lemma rename_shift {n m : ℕ} (t : GTm F n) (ρ : Fin n → Fin m) :
    (shift t).rename (upRen ρ) = shift (t.rename ρ) := by
  simp only [rename_rename]; rfl

lemma rename_subst1 {n m : ℕ} (t : GTm F (n + 1)) (s : GTm F n) (ρ : Fin n → Fin m) :
    (t.subst1 s).rename ρ = (t.rename (upRen ρ)).subst1 (s.rename ρ) := by
  rw [rename_subst]; show _ = subst _ (rename _ t); rw [subst_rename]
  congr 1; funext i; exact Fin.cases rfl (fun i => rfl) i

lemma rename_subst2 {n m : ℕ} (t : GTm F (n + 2)) (s₁ s₂ : GTm F n) (ρ : Fin n → Fin m) :
    (t.subst2 s₁ s₂).rename ρ = (t.rename (upRen (upRen ρ))).subst2 (s₁.rename ρ) (s₂.rename ρ) := by
  rw [rename_subst]; show _ = subst _ (rename _ t); rw [subst_rename]
  congr 1; funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

end Coeffect.GTm
