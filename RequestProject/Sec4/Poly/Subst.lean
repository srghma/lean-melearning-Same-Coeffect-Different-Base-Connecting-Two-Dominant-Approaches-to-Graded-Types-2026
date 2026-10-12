module

public import RequestProject.Sec4.Poly.Syntax

/-!
# Graded Poly Base: renaming and substitution lemmas

The usual algebra of de Bruijn renamings and substitutions for the types `PTy R k` and terms
`PTm R k n` of Graded Poly Base, both for type variables and for term variables.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

namespace PTy

lemma rename_rename {k l j : ℕ} (A : PTy R k) (ρ : Fin k → Fin l) (ρ' : Fin l → Fin j) :
    rename ρ' (rename ρ A) = rename (ρ' ∘ ρ) A := by
  induction A generalizing l j with
  | _ => simp_all [rename, upRen_comp]

lemma up_upRen {k l j : ℕ} (σ : Fin l → PTy R j) (ρ : Fin k → Fin l) :
    up σ ∘ upRen ρ = up (σ ∘ ρ) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [up]

lemma subst_rename {k l j : ℕ} (A : PTy R k) (ρ : Fin k → Fin l) (σ : Fin l → PTy R j) :
    subst σ (rename ρ A) = subst (σ ∘ ρ) A := by
  induction A generalizing l j with
  | _ => simp_all [rename, subst, up_upRen]

lemma rename_up {k l j : ℕ} (σ : Fin k → PTy R l) (ρ : Fin l → Fin j) :
    (fun i => rename (upRen ρ) (up σ i)) = up (fun i => rename ρ (σ i)) := by
  funext i; refine Fin.cases ?_ ?_ i
  · simp [up, rename]
  · intro i; simp [up, rename_rename, upRen_comp_succ]

lemma rename_subst {k l j : ℕ} (A : PTy R k) (σ : Fin k → PTy R l) (ρ : Fin l → Fin j) :
    rename ρ (subst σ A) = subst (fun i => rename ρ (σ i)) A := by
  induction A generalizing l j with
  | _ => simp_all [rename, subst, rename_up]

end PTy

namespace PTm

/-! ## Term-variable renaming -/

lemma rename_rename {k n m j : ℕ} (t : PTm R k n) (ρ : Fin n → Fin m) (ρ' : Fin m → Fin j) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing m j with
  | _ => simp_all [rename, upRen_comp]

lemma rename_id {k n : ℕ} (t : PTm R k n) : rename id t = t := by
  induction t with
  | _ => simp_all [rename, upRen_id]

/-! ## Commuting type operations with term-variable renaming -/

lemma trename_rename {k l n m : ℕ} (t : PTm R k n) (ρ : Fin n → Fin m) (θ : Fin k → Fin l) :
    trename θ (rename ρ t) = rename ρ (trename θ t) := by
  induction t generalizing l m with
  | _ => simp_all [rename, trename]

lemma tsubst_rename {k l n m : ℕ} (t : PTm R k n) (ρ : Fin n → Fin m) (σ : Fin k → PTy R l) :
    tsubst σ (rename ρ t) = rename ρ (tsubst σ t) := by
  induction t generalizing l m with
  | _ => simp_all [rename, tsubst]

lemma trename_trename {k l j n : ℕ} (t : PTm R k n) (θ : Fin k → Fin l) (θ' : Fin l → Fin j) :
    trename θ' (trename θ t) = trename (θ' ∘ θ) t := by
  induction t generalizing l j with
  | _ => simp_all [trename, upRen_comp, PTy.rename_rename]

lemma tsubst_trename {k l j n : ℕ} (t : PTm R k n) (θ : Fin k → Fin l) (σ : Fin l → PTy R j) :
    tsubst σ (trename θ t) = tsubst (σ ∘ θ) t := by
  induction t generalizing l j with
  | _ => simp_all [trename, tsubst, PTy.up_upRen, PTy.subst_rename]

lemma trename_tsubst {k l j n : ℕ} (t : PTm R k n) (σ : Fin k → PTy R l) (θ : Fin l → Fin j) :
    trename θ (tsubst σ t) = tsubst (fun i => (σ i).rename θ) t := by
  induction t generalizing l j with
  | _ => simp_all [trename, tsubst, PTy.rename_up, PTy.rename_subst]

/-! ## Term-variable substitution -/

lemma up_upRen {k n m j : ℕ} (σ : Fin m → PTm R k j) (ρ : Fin n → Fin m) :
    up σ ∘ upRen ρ = up (σ ∘ ρ) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [up]

lemma subst_rename {k n m j : ℕ} (t : PTm R k n) (ρ : Fin n → Fin m) (σ : Fin m → PTm R k j) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing m j with
  | var i => rfl
  | app t₁ t₂ ih₁ ih₂ => simp only [rename, subst, ih₁, ih₂]
  | lam t ih => simp only [rename, subst, ih, up_upRen]
  | tlam t ih => simp only [rename, subst, ih]; rfl
  | tapp t A ih => simp only [rename, subst, ih]

lemma rename_up {k n m j : ℕ} (σ : Fin n → PTm R k m) (ρ : Fin m → Fin j) :
    (fun i => rename (upRen ρ) (up σ i)) = up (fun i => rename ρ (σ i)) := by
  funext i; refine Fin.cases ?_ ?_ i
  · simp [up, rename]
  · intro i; simp [up, rename_rename, upRen_comp_succ]

lemma rename_subst {k n m j : ℕ} (t : PTm R k n) (σ : Fin n → PTm R k m) (ρ : Fin m → Fin j) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m j with
  | var i => rfl
  | app t₁ t₂ ih₁ ih₂ => simp only [rename, subst, ih₁, ih₂]
  | lam t ih => simp only [rename, subst, ih, rename_up]
  | tlam t ih => simp only [rename, subst, ih, trename_rename]
  | tapp t A ih => simp only [rename, subst, ih]

lemma up_var {k n : ℕ} : up (var : Fin n → PTm R k n) = var := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [up, rename]

lemma subst_var {k n : ℕ} (t : PTm R k n) : subst var t = t := by
  induction t with
  | var i => rfl
  | app t₁ t₂ ih₁ ih₂ => simp only [subst, ih₁, ih₂]
  | lam t ih => simp only [subst, up_var, ih]
  | tlam t ih => simp only [subst, trename]; exact congrArg tlam ih
  | tapp t A ih => simp only [subst, ih]

/-- Substituting into a weakened term ignores the new variable. -/
lemma subst1_rename_succ {k n : ℕ} (t s : PTm R k n) : subst1 (rename Fin.succ t) s = t := by
  rw [subst1, subst_rename]; exact subst_var t

/-- Substitution commutes with weakening by a fresh innermost variable. -/
lemma subst_up_rename_succ {k n m : ℕ} (t : PTm R k n) (σ : Fin n → PTm R k m) :
    subst (up σ) (rename Fin.succ t) = rename Fin.succ (subst σ t) := by
  rw [subst_rename, rename_subst]; rfl

/-- Type substitution distributes over term substitution. -/
lemma tsubst_subst {k l n m : ℕ} (t : PTm R k n) (σ : Fin n → PTm R k m) (θ : Fin k → PTy R l) :
    tsubst θ (subst σ t) = subst (fun i => tsubst θ (σ i)) (tsubst θ t) := by
  induction t generalizing l m with
  | var i => rfl
  | app t₁ t₂ ih₁ ih₂ => simp only [subst, tsubst, ih₁, ih₂]
  | lam t ih =>
    simp only [subst, tsubst, ih]
    congr 2; funext i; refine Fin.cases rfl (fun i => ?_) i
    simp [up, tsubst_rename]
  | tlam t ih =>
    simp only [subst, tsubst, ih]
    congr 2; funext i
    rw [tsubst_trename, trename_tsubst]; rfl
  | tapp t A ih => simp only [subst, tsubst, ih]

end PTm

end Coeffect
