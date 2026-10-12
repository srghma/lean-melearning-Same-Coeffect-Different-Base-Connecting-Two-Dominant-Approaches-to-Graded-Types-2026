module

public import RequestProject.Sec4.Translations.LinearToPoly.Subst
public import RequestProject.Sec4.Poly.Equations
public import RequestProject.Sec2.Linear.Semantics

/-!
# Operational correspondence for the translation LB → GPB (Theorem 4.1)

Since the translation is defined on typing derivations, operational correspondence is stated for
derivations: for every derivation `Π` of `Γ ⊢ t : A` and every step `t ⇝ t'` there is a
derivation `Π'` of `Γ ⊢ t' : A` (built from `Π`, exactly as in the paper's proof) such that
`⦇Π⦈ ⇝* ⦇Π'⦈` (`LToP.step`). As a by-product we obtain subject reduction for Linear Base
(`LTyped.subject_reduction_base`).
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R]

omit [PreorderedSemiring R] in
/-- The three Graded Poly Base steps simulating `let [x] = [t₁] in t₂ ⇝ [t₁/x] t₂`. -/
lemma PSteps.betaBox_sim {k n : ℕ} (q : PTm R (k + 1) n) (B : PTy R k) (p₂ : PTm R k (n + 1)) :
    PSteps (.app (.tapp (.tlam (.lam (.app (.var 0) (q.rename Fin.succ)))) B) (.lam p₂))
      (p₂.subst1 (q.tsubst1 B)) := by
  have e1 : (PTm.lam (.app (.var 0) (q.rename Fin.succ)) : PTm R (k + 1) n).tsubst1 B =
      .lam (.app (.var 0) ((q.tsubst1 B).rename Fin.succ)) := by
    simp only [PTm.tsubst1, PTm.tsubst, PTm.tsubst_rename]
  have e2 : (PTm.app (.var 0) ((q.tsubst1 B).rename Fin.succ) : PTm R k (n + 1)).subst1
      (.lam p₂) = .app (.lam p₂) (q.tsubst1 B) := by
    show PTm.app (.lam p₂) (((q.tsubst1 B).rename Fin.succ).subst1 (.lam p₂)) = _
    rw [PTm.subst1_rename_succ]
  refine Relation.ReflTransGen.head (.congAppL _ (.tyBeta _ B)) ?_
  rw [e1]
  refine Relation.ReflTransGen.head (.beta _ _) ?_
  rw [e2]
  exact Relation.ReflTransGen.single (.beta _ _)

/-- **Theorem 4.1 (operational correspondence)** of the Linear Base → Graded Poly Base
translation: if `p = ⦇Π⦈` for a derivation `Π` of `Γ ⊢ t : A` and `t ⇝ t'`, then there is a
derivation `Π'` of `Γ ⊢ t' : A` with `⦇Π⦈ ⇝* ⦇Π'⦈`. -/
theorem LToP.step {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) {t' : LTm .base n}
    (hs : LStep t t') : ∃ p', LToP Γ u t' A p' ∧ PSteps p p' := by
  induction h with
  | var => cases hs
  | abs => cases hs
  | app h₁ h₂ hadd ih₁ _ =>
    cases hs with
    | beta b a =>
      obtain ⟨pb, rfl, hb⟩ := h₁.inv_lam
      exact ⟨_, hb.subst1_lin h₂ hadd.comm, .single (.beta _ _)⟩
    | congAppL _ hs₁ =>
      obtain ⟨p₁', h₁', hst⟩ := ih₁ hs₁
      exact ⟨_, .app h₁' h₂ hadd, hst.appL _⟩
  | weak i _ hi ih =>
    obtain ⟨p', h', hst⟩ := ih hs
    exact ⟨p', .weak i h' hi, hst⟩
  | der i _ hi ih =>
    obtain ⟨p', h', hst⟩ := ih hs
    exact ⟨p', .der i h' hi, hst⟩
  | approx i _ hi hrs ih =>
    obtain ⟨p', h', hst⟩ := ih hs
    exact ⟨p', .approx i h' hi hrs, hst⟩
  | pr => cases hs
  | @letbox k n Γ u₁ u₂ u t₁ t₂ r A B p₁ p₂ h₁ h₂ hadd ih₁ _ =>
    cases hs with
    | betaBox a b =>
      obtain ⟨ua, q, hg, hq, rfl, hle⟩ := h₁.inv_box
      obtain ⟨hadd', hle'⟩ := hadd.down hle
      refine ⟨_, ?_, PSteps.betaBox_sim q B.toP p₂⟩
      exact (h₂.subst1_grd (hq.tsubst _) hg hadd').mono hle'
    | congLetL _ hs₁ =>
      obtain ⟨p₁', h₁', hst⟩ := ih₁ hs₁
      exact ⟨_, .letbox h₁' h₂ hadd, (hst.tapp _).appL _⟩

/-- Operational correspondence for many steps. -/
theorem LToP.steps {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t t' : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) (hs : LSteps t t') :
    ∃ p', LToP Γ u t' A p' ∧ PSteps p p' := by
  induction hs with
  | refl => exact ⟨p, h, .refl⟩
  | tail _ hs ih =>
    obtain ⟨p₁, h₁, hst₁⟩ := ih
    obtain ⟨p₂, h₂, hst₂⟩ := h₁.step hs
    exact ⟨p₂, h₂, hst₁.trans hst₂⟩

/-- Subject reduction for Linear Base (a by-product of the substitution lemma). -/
theorem LTyped.subject_reduction_base {n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R}
    {t t' : LTm .base n} {A : LTy R .base} (h : LTyped Γ u t A) (hs : LStep t t') :
    LTyped Γ u t' A := by
  obtain ⟨p, hp⟩ := h.toP_exists 0
  obtain ⟨p', hp', _⟩ := hp.step hs
  exact hp'.typed_L

end Coeffect
