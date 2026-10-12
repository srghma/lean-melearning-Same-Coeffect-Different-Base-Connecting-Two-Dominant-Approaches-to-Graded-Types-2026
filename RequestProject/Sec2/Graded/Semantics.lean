module

public import RequestProject.Sec2.Graded.Syntax

/-!
# Operational semantics and equational theory of the graded-base lineage

* `GStep b` is call-by-name reduction `t ⇝_G t'` (Figure 3, Section 3.1, Section 5).
  When the flag `b` holds we additionally allow reduction under λ (rule `congAbs`); this is
  the full β-reduction `⇝_{βG}` used as the target of the CPS translation (Theorem 2.6).
* `GAx` collects the axioms of `≡_G` and `GCong Ax` is the closure under equivalence and all
  congruences. `GEq := GCong GAx`.
-/

@[expose] public section

namespace Coeffect

variable {F : GLevel}

open GTm

/-- Reduction `t ⇝_G t'`; `underLam` additionally enables reduction under binders. -/
inductive GStep (underLam : Prop) : {n : ℕ} → GTm F n → GTm F n → Prop
  | beta {n : ℕ} (t₂ : GTm F (n + 1)) (t₁ : GTm F n) : GStep underLam (app (lam t₂) t₁) (t₂.subst1 t₁)
  | congAppL {n : ℕ} {t₁ t₁' : GTm F n} (t₂ : GTm F n) :
      GStep underLam t₁ t₁' → GStep underLam (app t₁ t₂) (app t₁' t₂)
  | congAbs {n : ℕ} {t t' : GTm F (n + 1)} (hb : underLam) :
      GStep underLam t t' → GStep underLam (lam t) (lam t')
  | betaBox {n : ℕ} (h : F.Modal) (t₁ : GTm F n) (t₂ : GTm F (n + 1)) :
      GStep underLam (letbox h (box h t₁) t₂) (t₂.subst1 t₁)
  | congLetL {n : ℕ} (h : F.Modal) {t₁ t₁' : GTm F n} (t₂ : GTm F (n + 1)) :
      GStep underLam t₁ t₁' → GStep underLam (letbox h t₁ t₂) (letbox h t₁' t₂)
  | prodCong {n : ℕ} (h : F.Core) {t₁ t₁' : GTm F n} (t₂ : GTm F (n + 2)) :
      GStep underLam t₁ t₁' → GStep underLam (letpair h t₁ t₂) (letpair h t₁' t₂)
  | prodBeta {n : ℕ} (h : F.Core) (t₁ t₂ : GTm F n) (t₃ : GTm F (n + 2)) :
      GStep underLam (letpair h (pair h t₁ t₂) t₃) (t₃.subst2 t₁ t₂)
  | unitCong {n : ℕ} (h : F.Core) {t₁ t₁' : GTm F n} (t₂ : GTm F n) :
      GStep underLam t₁ t₁' → GStep underLam (letunit h t₁ t₂) (letunit h t₁' t₂)
  | unitBeta {n : ℕ} (h : F.Core) (t₂ : GTm F n) :
      GStep underLam (letunit h (unit h) t₂) t₂
  | congCase {n : ℕ} (h : F.Core) {t t' : GTm F n} (t₁ t₂ : GTm F (n + 1)) :
      GStep underLam t t' → GStep underLam (case h t t₁ t₂) (case h t' t₁ t₂)
  | caseInl {n : ℕ} (h : F.Core) (t : GTm F n) (t₁ t₂ : GTm F (n + 1)) :
      GStep underLam (case h (inl h t) t₁ t₂) (t₁.subst1 t)
  | caseInr {n : ℕ} (h : F.Core) (t : GTm F n) (t₁ t₂ : GTm F (n + 1)) :
      GStep underLam (case h (inr h t) t₁ t₂) (t₂.subst1 t)

/-- Reflexive-transitive closure of `GStep b`. -/
abbrev GSteps (underLam : Prop) {n : ℕ} : GTm F n → GTm F n → Prop :=
  Relation.ReflTransGen (GStep underLam)

/-- The axioms of the equational theory `≡_G`. The flag `etaPS` enables the η-rules for products
and sums (`GAxF True` is the full theory; `GAxF False` is the theory `≡_G^{-η⊗⊕}` of
Theorem 5.1, which lacks them). -/
inductive GAxF (etaPS : Prop) : {n : ℕ} → GTm F n → GTm F n → Prop
  | beta {n : ℕ} (t₂ : GTm F (n + 1)) (t₁ : GTm F n) : GAxF etaPS (app (lam t₂) t₁) (t₂.subst1 t₁)
  | eta {n : ℕ} (t : GTm F n) : GAxF etaPS (lam (app (shift t) (var 0))) t
  | betaBox {n : ℕ} (h : F.Modal) (t₁ : GTm F n) (t₂ : GTm F (n + 1)) :
      GAxF etaPS (letbox h (box h t₁) t₂) (t₂.subst1 t₁)
  | etaBox {n : ℕ} (h : F.Modal) (t : GTm F n) : GAxF etaPS (letbox h t (box h (var 0))) t
  | letCommOne {n : ℕ} (h : F.Modal) (t₀ t₁ : GTm F n) (t₂ : GTm F (n + 1)) :
      GAxF etaPS (app t₀ (letbox h t₁ t₂)) (letbox h t₁ (app (shift t₀) t₂))
  | letCommTwo {n : ℕ} (h : F.Modal) (t₀ t₁ : GTm F n) (t₂ : GTm F (n + 1)) :
      GAxF etaPS (app (letbox h t₁ t₂) t₀) (letbox h t₁ (app t₂ (shift t₀)))
  | letCommBox {n : ℕ} (h : F.Modal) (t₁ : GTm F n) (t₂ : GTm F (n + 1)) :
      GAxF etaPS (letbox h (box h t₁) (box h t₂)) (box h (letbox h (box h t₁) t₂))
  | betaUnit {n : ℕ} (h : F.Core) (t : GTm F n) : GAxF etaPS (letunit h (unit h) t) t
  | etaUnit {n : ℕ} (h : F.Core) (t : GTm F n) : GAxF etaPS (letunit h t (unit h)) (unit h)
  | betaProd {n : ℕ} (h : F.Core) (t₁ t₂ : GTm F n) (t : GTm F (n + 2)) :
      GAxF etaPS (letpair h (pair h t₁ t₂) t) (t.subst2 t₁ t₂)
  | etaProd {n : ℕ} (he : etaPS) (h : F.Core) (t : GTm F n) :
      GAxF etaPS (letpair h t (pair h (var 1) (var 0))) t
  | betaSumOne {n : ℕ} (h : F.Core) (t : GTm F n) (t₁ t₂ : GTm F (n + 1)) :
      GAxF etaPS (case h (inl h t) t₁ t₂) (t₁.subst1 t)
  | betaSumTwo {n : ℕ} (h : F.Core) (t : GTm F n) (t₁ t₂ : GTm F (n + 1)) :
      GAxF etaPS (case h (inr h t) t₁ t₂) (t₂.subst1 t)
  | etaSum {n : ℕ} (he : etaPS) (h : F.Core) (t : GTm F n) :
      GAxF etaPS (case h t (inl h (var 0)) (inr h (var 0))) t

/-- The full set of axioms of `≡_G`. -/
abbrev GAx {n : ℕ} : GTm F n → GTm F n → Prop := GAxF (F := F) True

/-- Closure of a set of axioms under equivalence and all congruences. -/
inductive GCong (Ax : ∀ {n : ℕ}, GTm F n → GTm F n → Prop) : {n : ℕ} → GTm F n → GTm F n → Prop
  | ax {n : ℕ} {t t' : GTm F n} : Ax t t' → GCong Ax t t'
  | refl {n : ℕ} (t : GTm F n) : GCong Ax t t
  | symm {n : ℕ} {t t' : GTm F n} : GCong Ax t t' → GCong Ax t' t
  | trans {n : ℕ} {t t' t'' : GTm F n} : GCong Ax t t' → GCong Ax t' t'' → GCong Ax t t''
  | app {n : ℕ} {t₁ t₁' t₂ t₂' : GTm F n} :
      GCong Ax t₁ t₁' → GCong Ax t₂ t₂' → GCong Ax (app t₁ t₂) (app t₁' t₂')
  | lam {n : ℕ} {t t' : GTm F (n + 1)} : GCong Ax t t' → GCong Ax (lam t) (lam t')
  | box {n : ℕ} (h : F.Modal) {t t' : GTm F n} :
      GCong Ax t t' → GCong Ax (box h t) (box h t')
  | letbox {n : ℕ} (h : F.Modal) {t₁ t₁' : GTm F n} {t₂ t₂' : GTm F (n + 1)} :
      GCong Ax t₁ t₁' → GCong Ax t₂ t₂' → GCong Ax (letbox h t₁ t₂) (letbox h t₁' t₂')
  | pair {n : ℕ} (h : F.Core) {t₁ t₁' t₂ t₂' : GTm F n} :
      GCong Ax t₁ t₁' → GCong Ax t₂ t₂' → GCong Ax (pair h t₁ t₂) (pair h t₁' t₂')
  | letpair {n : ℕ} (h : F.Core) {t₁ t₁' : GTm F n} {t₂ t₂' : GTm F (n + 2)} :
      GCong Ax t₁ t₁' → GCong Ax t₂ t₂' → GCong Ax (letpair h t₁ t₂) (letpair h t₁' t₂')
  | letunit {n : ℕ} (h : F.Core) {t₁ t₁' t₂ t₂' : GTm F n} :
      GCong Ax t₁ t₁' → GCong Ax t₂ t₂' → GCong Ax (letunit h t₁ t₂) (letunit h t₁' t₂')
  | inl {n : ℕ} (h : F.Core) {t t' : GTm F n} :
      GCong Ax t t' → GCong Ax (inl h t) (inl h t')
  | inr {n : ℕ} (h : F.Core) {t t' : GTm F n} :
      GCong Ax t t' → GCong Ax (inr h t) (inr h t')
  | case {n : ℕ} (h : F.Core) {t t' : GTm F n} {t₁ t₁' t₂ t₂' : GTm F (n + 1)} :
      GCong Ax t t' → GCong Ax t₁ t₁' → GCong Ax t₂ t₂' →
      GCong Ax (case h t t₁ t₂) (case h t' t₁' t₂')

/-- The equational theory `t ≡_G t'`. -/
abbrev GEq {n : ℕ} (t t' : GTm F n) : Prop := GCong GAx t t'

/-- Reduction (even under binders) is contained in the equational theory. -/
theorem GStep.toGEq {b : Prop} {n : ℕ} {t t' : GTm F n} (h : GStep b t t') : GEq t t' := by
  induction h with
  | beta => exact .ax (.beta _ _)
  | congAppL _ _ ih => exact .app ih (.refl _)
  | congAbs _ _ ih => exact .lam ih
  | betaBox => exact .ax (.betaBox _ _ _)
  | congLetL h _ _ ih => exact .letbox h ih (.refl _)
  | prodCong h _ _ ih => exact .letpair h ih (.refl _)
  | prodBeta => exact .ax (.betaProd _ _ _ _)
  | unitCong h _ _ ih => exact .letunit h ih (.refl _)
  | unitBeta => exact .ax (.betaUnit _ _)
  | congCase h _ _ _ ih => exact .case h ih (.refl _) (.refl _)
  | caseInl => exact .ax (.betaSumOne _ _ _ _)
  | caseInr => exact .ax (.betaSumTwo _ _ _ _)

theorem GSteps.toGEq {b : Prop} {n : ℕ} {t t' : GTm F n} (h : GSteps b t t') : GEq t t' := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact .trans ih h.toGEq

theorem GCong.mono {Ax Ax' : ∀ {n : ℕ}, GTm F n → GTm F n → Prop}
    (hAx : ∀ {n : ℕ} {t t' : GTm F n}, Ax t t' → Ax' t t') {n : ℕ} {t t' : GTm F n}
    (h : GCong Ax t t') : GCong Ax' t t' := by
  induction h with
  | ax h => exact .ax (hAx h)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ ih => exact .lam ih
  | box h _ ih => exact .box h ih
  | letbox h _ _ ih₁ ih₂ => exact .letbox h ih₁ ih₂
  | pair h _ _ ih₁ ih₂ => exact .pair h ih₁ ih₂
  | letpair h _ _ ih₁ ih₂ => exact .letpair h ih₁ ih₂
  | letunit h _ _ ih₁ ih₂ => exact .letunit h ih₁ ih₂
  | inl h _ ih => exact .inl h ih
  | inr h _ ih => exact .inr h ih
  | case h _ _ _ ih ih₁ ih₂ => exact .case h ih ih₁ ih₂

/-- CBN reduction is included in reduction under binders. -/
theorem GStep.toUnderLam {n : ℕ} {t t' : GTm F n} (h : GStep False t t') : GStep True t t' := by
  induction h with
  | beta => exact .beta _ _
  | congAppL _ _ ih => exact .congAppL _ ih
  | congAbs hb => exact absurd hb (by decide)
  | betaBox => exact .betaBox _ _ _
  | congLetL h _ _ ih => exact .congLetL h _ ih
  | prodCong h _ _ ih => exact .prodCong h _ ih
  | prodBeta => exact .prodBeta _ _ _ _
  | unitCong h _ _ ih => exact .unitCong h _ ih
  | unitBeta => exact .unitBeta _ _
  | congCase h _ _ _ ih => exact .congCase h _ _ ih
  | caseInl => exact .caseInl _ _ _ _
  | caseInr => exact .caseInr _ _ _ _

end Coeffect

namespace Coeffect

variable {F : GLevel}

open GTm in
theorem GAxF.rename {b : Prop} {n m : ℕ} {t t' : GTm F n} (h : GAxF b t t') (ρ : Fin n → Fin m) :
    GAxF b (t.rename ρ) (t'.rename ρ) := by
  cases h with
  | beta t₂ t₁ => rw [rename_subst1]; exact .beta _ _
  | eta t => simp only [GTm.rename, rename_shift]; exact .eta _
  | betaBox h t₁ t₂ => rw [rename_subst1]; exact .betaBox _ _ _
  | etaBox h t => exact .etaBox _ _
  | letCommOne h t₀ t₁ t₂ => simp only [GTm.rename, rename_shift]; exact .letCommOne _ _ _ _
  | letCommTwo h t₀ t₁ t₂ => simp only [GTm.rename, rename_shift]; exact .letCommTwo _ _ _ _
  | letCommBox h t₁ t₂ => exact .letCommBox _ _ _
  | betaUnit h t => exact .betaUnit _ _
  | etaUnit h t => exact .etaUnit _ _
  | betaProd h t₁ t₂ t => rw [rename_subst2]; exact .betaProd _ _ _ _
  | etaProd he h t => exact .etaProd he _ _
  | betaSumOne h t t₁ t₂ => rw [rename_subst1]; exact .betaSumOne _ _ _ _
  | betaSumTwo h t t₁ t₂ => rw [rename_subst1]; exact .betaSumTwo _ _ _ _
  | etaSum he h t => exact .etaSum he _ _

theorem GCong.rename {Ax : ∀ {n : ℕ}, GTm F n → GTm F n → Prop}
    (hAx : ∀ {n m : ℕ} {t t' : GTm F n} (ρ : Fin n → Fin m), Ax t t' → Ax (t.rename ρ) (t'.rename ρ))
    {n m : ℕ} {t t' : GTm F n} (h : GCong Ax t t') (ρ : Fin n → Fin m) :
    GCong Ax (t.rename ρ) (t'.rename ρ) := by
  induction h generalizing m with
  | ax h => exact .ax (hAx ρ h)
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | lam _ ih => exact .lam (ih _)
  | box h _ ih => exact .box h (ih ρ)
  | letbox h _ _ ih₁ ih₂ => exact .letbox h (ih₁ ρ) (ih₂ _)
  | pair h _ _ ih₁ ih₂ => exact .pair h (ih₁ ρ) (ih₂ ρ)
  | letpair h _ _ ih₁ ih₂ => exact .letpair h (ih₁ ρ) (ih₂ _)
  | letunit h _ _ ih₁ ih₂ => exact .letunit h (ih₁ ρ) (ih₂ ρ)
  | inl h _ ih => exact .inl h (ih ρ)
  | inr h _ ih => exact .inr h (ih ρ)
  | case h _ _ _ ih ih₁ ih₂ => exact .case h (ih ρ) (ih₁ _) (ih₂ _)

theorem GEq.rename {n m : ℕ} {t t' : GTm F n} (h : GEq t t') (ρ : Fin n → Fin m) :
    GEq (t.rename ρ) (t'.rename ρ) :=
  GCong.rename (Ax := fun a b => GAxF True a b) (fun ρ h => GAxF.rename h ρ) h ρ

end Coeffect
