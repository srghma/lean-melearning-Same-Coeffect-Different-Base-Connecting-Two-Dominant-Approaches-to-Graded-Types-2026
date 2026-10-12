module

public import RequestProject.Sec4.Translations.LinearToPoly.Structural

/-!
# Substitution lemma for the derivation-based translation LB → GPB

The paper's Lemma "interpretation preserves substitution of derivations": substituting translated
derivations into a translated derivation yields the translation of a derivation of the substituted
term. We prove it for simultaneous substitutions; the usage of the result is described by
`SubstUse` (see `UsageAlgebra`).
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R]

lemma update_only {n : ℕ} (i : Fin n) :
    Function.update (Use.only i : Fin n → Use R) i (Use.grd 1) = Use.single i (Use.grd 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; simp only [Use.single, ↓reduceIte]
  · rw [Function.update_of_ne hj]; simp only [Use.only, Use.single, if_neg hj]

/-- A variable, derelicted. -/
lemma LToP.var_grd1 {k n : ℕ} (Γ : Fin n → LTy R .base) (i : Fin n) :
    LToP (k := k) Γ (Use.single i (Use.grd 1)) (.var i) (Γ i) (.var i) := by
  have h := LToP.der (k := k) i (LToP.var Γ i) (by simp only [Use.only, ↓reduceIte])
  rwa [update_only] at h

/-- The variables of the identity substitution. -/
lemma LToP.var_idUse {k n : ℕ} (Γ : Fin n → LTy R .base) (u : Fin n → Use R) (i : Fin n) :
    LToP (k := k) Γ (idUse u i) (.var i) (Γ i) (.var i) := by
  simp only [idUse]
  split
  · exact LToP.var_grd1 Γ i
  · exact LToP.var Γ i

/-- **Substitution lemma** for translated derivations (simultaneous substitution). -/
theorem LToP.subst {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) :
    ∀ {m : ℕ} (Δ : Fin m → LTy R .base) (σ : Fin n → LTm .base m) (τ : Fin n → PTm R k m)
      (v : Fin n → Fin m → Use R) (w : Fin m → Use R),
      (∀ i, LToP Δ (v i) (σ i) (Γ i) (τ i)) → SubstUse u v w →
      LToP Δ w (t.subst σ) A (p.subst τ) := by
  induction h with
  | var Γ i =>
    intro m Δ σ τ v w hσ hw
    rw [hw.var]; exact hσ i
  | @abs k n Γ u t A B p _ ih =>
    intro m Δ σ τ v w hσ hw
    refine LToP.abs (ih (A .: Δ) (LTm.upSub σ) (PTm.up τ) _ _ ?_ hw.cons_lin)
    intro i
    induction i using Fin.cases with
    | zero => exact LToP.var (A .: Δ) 0
    | succ i => exact (hσ i).weaken1 A
  | app _ _ hadd ih₁ ih₂ =>
    intro m Δ σ τ v w hσ hw
    obtain ⟨w₁, w₂, h₁, h₂, h₁₂⟩ := hw.split hadd
    exact LToP.app (ih₁ Δ σ τ v w₁ hσ h₁) (ih₂ Δ σ τ v w₂ hσ h₂) h₁₂
  | weak i _ hi ih =>
    intro m Δ σ τ v w hσ hw
    obtain ⟨w₀, h₀, hle⟩ := hw.weak hi
    exact (ih Δ σ τ v w₀ hσ h₀).mono hle
  | der i _ hi ih =>
    intro m Δ σ τ v w hσ hw
    exact ih Δ σ τ v w hσ (hw.der hi)
  | approx i _ hi hrs ih =>
    intro m Δ σ τ v w hσ hw
    obtain ⟨w₀, h₀, hle⟩ := hw.approx hi hrs
    exact (ih Δ σ τ v w₀ hσ h₀).mono hle
  | @pr k n Γ u t A p r _ hg ih =>
    intro m Δ σ τ v w hσ hw
    obtain ⟨w', hw', hg', rfl⟩ := hw.smul hg r
    have ep : (PTm.tlam (.lam (.app (.var 0) (p.rename Fin.succ))) : PTm R k n).subst τ =
        .tlam (.lam (.app (.var 0)
          ((p.subst (fun i => (τ i).trename Fin.succ)).rename Fin.succ))) := by
      simp only [PTm.subst, PTm.subst_up_rename_succ]; rfl
    rw [ep]
    exact LToP.pr r (ih Δ σ _ v w' (fun i => (hσ i).trename Fin.succ) hw') hg'
  | @letbox k n Γ u₁ u₂ u t₁ t₂ r A B p₁ p₂ _ _ hadd ih₁ ih₂ =>
    intro m Δ σ τ v w hσ hw
    obtain ⟨w₁, w₂, h₁, h₂, h₁₂⟩ := hw.split hadd
    refine LToP.letbox (ih₁ Δ σ τ v w₁ hσ h₁)
      (ih₂ (A .: Δ) (LTm.upSub σ) (PTm.up τ) _ _ ?_ (h₂.cons_grd r)) h₁₂
    intro i
    induction i using Fin.cases with
    | zero => exact LToP.var_grd1 (A .: Δ) 0
    | succ i => exact (hσ i).weaken1 A

/-- Substitution for a linear variable (`β` for `⊸`). -/
theorem LToP.subst1_lin {k n : ℕ} {Γ : Fin n → LTy R .base} {u₁ u₂ u : Fin n → Use R}
    {b : LTm .base (n + 1)} {a : LTm .base n} {A B : LTy R .base} {pb : PTm R k (n + 1)}
    {pa : PTm R k n} (hb : LToP (A .: Γ) (Use.lin .: u₂) b B pb) (ha : LToP Γ u₁ a A pa)
    (hadd : CtxAdd u₁ u₂ u) : LToP Γ u (b.subst1 a) B (pb.subst1 pa) := by
  refine hb.subst Γ (a .: LTm.var) (pa .: PTm.var) (u₁ .: idUse u₂) u ?_ (SubstUse.beta hadd)
  intro i
  induction i using Fin.cases with
  | zero => exact ha
  | succ i => exact LToP.var_idUse Γ u₂ i

/-- Substitution for a graded variable (`β` for `□`). -/
theorem LToP.subst1_grd {k n : ℕ} {Γ : Fin n → LTy R .base} {ua u₂ u : Fin n → Use R}
    {b : LTm .base (n + 1)} {a : LTm .base n} {r : R} {A B : LTy R .base}
    {pb : PTm R k (n + 1)} {pa : PTm R k n} (hb : LToP (A .: Γ) (Use.grd r .: u₂) b B pb)
    (ha : LToP Γ ua a A pa) (hg : Graded ua) (hadd : CtxAdd (smulCtx r ua) u₂ u) :
    LToP Γ u (b.subst1 a) B (pb.subst1 pa) := by
  refine hb.subst Γ (a .: LTm.var) (pa .: PTm.var) (ua .: idUse u₂) u ?_
    (SubstUse.betaBox hg hadd)
  intro i
  induction i using Fin.cases with
  | zero => exact ha
  | succ i => exact LToP.var_idUse Γ u₂ i

end Coeffect
