module

public import RequestProject.Sec4.Poly.Typing
public import RequestProject.Sec4.Poly.Subst

/-!
# Graded Poly Base: equational theory (Section 4.1)

`t ≡_{G∀} t'` is the closure under equivalence and congruence of the `β`/`η` axioms for term
abstraction (`≡_G`) and for type abstraction (`GradPolyEqbetaTy`, `GradPolyEqetaTy`):

```
(λx. t₂) t₁ ≡ [t₁/x] t₂        λx. t x ≡ t   (x # t)
(Λα. t) @ A ≡ [A/α] t          Λα. t @ α ≡ t (α # t)
```
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- The equational theory `≡_{G∀}` of Graded Poly Base. -/
inductive PEq : {k n : ℕ} → PTm R k n → PTm R k n → Prop
  | beta {k n : ℕ} (t₂ : PTm R k (n + 1)) (t₁ : PTm R k n) : PEq (.app (.lam t₂) t₁) (t₂.subst1 t₁)
  /-- `λx. t x ≡ t` when `x # t` -/
  | eta {k n : ℕ} (t : PTm R k n) : PEq (.lam (.app (t.rename Fin.succ) (.var 0))) t
  | tyBeta {k n : ℕ} (t : PTm R (k + 1) n) (A : PTy R k) : PEq (.tapp (.tlam t) A) (t.tsubst1 A)
  /-- `Λα. t @ α ≡ t` when `α # t` -/
  | tyEta {k n : ℕ} (t : PTm R k n) : PEq (.tlam (.tapp (t.trename Fin.succ) (.tvar 0))) t
  | refl {k n : ℕ} (t : PTm R k n) : PEq t t
  | symm {k n : ℕ} {t t' : PTm R k n} : PEq t t' → PEq t' t
  | trans {k n : ℕ} {t t' t'' : PTm R k n} : PEq t t' → PEq t' t'' → PEq t t''
  | app {k n : ℕ} {t₁ t₁' t₂ t₂' : PTm R k n} :
      PEq t₁ t₁' → PEq t₂ t₂' → PEq (.app t₁ t₂) (.app t₁' t₂')
  | lam {k n : ℕ} {t t' : PTm R k (n + 1)} : PEq t t' → PEq (.lam t) (.lam t')
  | tlam {k n : ℕ} {t t' : PTm R (k + 1) n} : PEq t t' → PEq (.tlam t) (.tlam t')
  | tapp {k n : ℕ} {t t' : PTm R k n} (A : PTy R k) : PEq t t' → PEq (.tapp t A) (.tapp t' A)

/-- Reduction is contained in the equational theory. -/
theorem PStep.toPEq {k n : ℕ} {t t' : PTm R k n} (h : PStep t t') : PEq t t' := by
  induction h with
  | beta t₂ t₁ => exact .beta t₂ t₁
  | congAppL t₂ _ ih => exact .app ih (.refl t₂)
  | tyBeta t A => exact .tyBeta t A
  | congTyApp A _ ih => exact .tapp A ih

theorem PSteps.toPEq {k n : ℕ} {t t' : PTm R k n} (h : PSteps t t') : PEq t t' := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact ih.trans h.toPEq

lemma PSteps.appL {k n : ℕ} {t₁ t₁' : PTm R k n} (t₂ : PTm R k n) (h : PSteps t₁ t₁') :
    PSteps (.app t₁ t₂) (.app t₁' t₂) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (.congAppL t₂ h)

lemma PSteps.tapp {k n : ℕ} {t t' : PTm R k n} (A : PTy R k) (h : PSteps t t') :
    PSteps (.tapp t A) (.tapp t' A) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (.congTyApp A h)

end Coeffect

namespace Coeffect

universe v

variable {R : Type v}

lemma PTm.rename_subst1 {k n m : ℕ} (t₂ : PTm R k (n + 1)) (t₁ : PTm R k n) (ρ : Fin n → Fin m) :
    (t₂.subst1 t₁).rename ρ = (t₂.rename (upRen ρ)).subst1 (t₁.rename ρ) := by
  rw [PTm.subst1, PTm.rename_subst, PTm.subst1, PTm.subst_rename]
  congr 1; funext i; exact Fin.cases rfl (fun i => rfl) i

/-- `≡_{G∀}` is stable under renaming of term variables. -/
theorem PEq.rename {k n : ℕ} {t t' : PTm R k n} (h : PEq t t') {m : ℕ} (ρ : Fin n → Fin m) :
    PEq (t.rename ρ) (t'.rename ρ) := by
  induction h generalizing m with
  | beta t₂ t₁ => rw [PTm.rename_subst1]; exact .beta _ _
  | eta t =>
    have e : (PTm.lam (.app (t.rename Fin.succ) (.var 0)) : PTm R _ _).rename ρ =
        .lam (.app ((t.rename ρ).rename Fin.succ) (.var 0)) := by
      simp only [PTm.rename, PTm.rename_rename]; rfl
    rw [e]; exact .eta _
  | tyBeta t A =>
    show PEq (.tapp (.tlam (t.rename ρ)) A) _
    rw [← PTm.tsubst_rename]; exact .tyBeta _ _
  | tyEta t =>
    show PEq (.tlam (.tapp ((t.trename Fin.succ).rename ρ) (.tvar 0))) _
    rw [← PTm.trename_rename]; exact .tyEta _
  | refl t => exact .refl _
  | symm _ ih => exact (ih ρ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | lam _ ih => exact .lam (ih _)
  | tlam _ ih => exact .tlam (ih ρ)
  | tapp A _ ih => exact .tapp A (ih ρ)

end Coeffect
