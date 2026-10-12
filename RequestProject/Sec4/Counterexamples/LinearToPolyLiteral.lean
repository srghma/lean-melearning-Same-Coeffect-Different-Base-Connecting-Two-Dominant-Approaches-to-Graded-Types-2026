module

public import RequestProject.Sec4.Translations.LinearToPoly.Soundness

/-!
# The paper's literal operational correspondence for LB → GPB is false

Theorem 4.1 of the paper states operational correspondence as
`(Π : Γ ⊢ t : A) ∧ (Π' : Γ ⊢ t' : A) ∧ t ⇝ t' ⟹ ⦇Π⦈ ⇝* ⦇Π'⦈` for *arbitrary* derivations `Π'`.
This fails because different derivations of the same term can have translations differing in
the type annotations of `let`-translations. Counterexample (with the linearity semiring):

```
s₀ = let [x] = [λw. w] in x                    -- C for any type C = X ⊸ X
s  = let [_] = [s₀] in λv. v       : K ⊸ K
t  = (λy. y) s ⇝ s                 : K ⊸ K
```

Take `Π` typing the inner `λw. w` at `K ⊸ K` (so `s₀ : K ⊸ K`) and `Π'` typing it at
`(K ⊸ K) ⊸ (K ⊸ K)`.
Every type annotation of every reduct of `⦇Π⦈` is `⦇K ⊸ K⦈` (`PTm.AnnFixed`, preserved by
reduction), while `⦇Π'⦈` contains the annotation `⦇(K ⊸ K) ⊸ (K ⊸ K)⦈`.

The corrected statement (`LToP.step`) asserts the existence of a suitable `Π'`.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- All type annotations `t @ A` in a term are `K →¹ K`. -/
def PTm.AnnFixed [One R] {k n : ℕ} : PTm R k n → Prop
  | .var _ => True
  | .app a b => a.AnnFixed ∧ b.AnnFixed
  | .lam t => t.AnnFixed
  | .tlam t => t.AnnFixed
  | .tapp t A => t.AnnFixed ∧ A = .fn 1 .base .base

namespace PTm

variable [One R]

lemma AnnFixed.rename {k n m : ℕ} {t : PTm R k n} (h : t.AnnFixed) (ρ : Fin n → Fin m) :
    (t.rename ρ).AnnFixed := by
  induction t generalizing m with
  | var => trivial
  | app a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 ρ⟩
  | lam t ih => exact ih h _
  | tlam t ih => exact ih h ρ
  | tapp t A ih => exact ⟨ih h.1 ρ, h.2⟩

lemma AnnFixed.trename {k l n : ℕ} {t : PTm R k n} (h : t.AnnFixed) (θ : Fin k → Fin l) :
    (t.trename θ).AnnFixed := by
  induction t generalizing l with
  | var => trivial
  | app a b iha ihb => exact ⟨iha h.1 θ, ihb h.2 θ⟩
  | lam t ih => exact ih h θ
  | tlam t ih => exact ih h _
  | tapp t A ih => exact ⟨ih h.1 θ, by rw [h.2]; rfl⟩

lemma AnnFixed.tsubst {k l n : ℕ} {t : PTm R k n} (h : t.AnnFixed) (σ : Fin k → PTy R l) :
    (t.tsubst σ).AnnFixed := by
  induction t generalizing l with
  | var => trivial
  | app a b iha ihb => exact ⟨iha h.1 σ, ihb h.2 σ⟩
  | lam t ih => exact ih h σ
  | tlam t ih => exact ih h _
  | tapp t A ih => exact ⟨ih h.1 σ, by rw [h.2]; rfl⟩

lemma AnnFixed.subst {k n m : ℕ} {t : PTm R k n} (h : t.AnnFixed) {σ : Fin n → PTm R k m}
    (hσ : ∀ i, (σ i).AnnFixed) : (t.subst σ).AnnFixed := by
  induction t generalizing m with
  | var i => exact hσ i
  | app a b iha ihb => exact ⟨iha h.1 hσ, ihb h.2 hσ⟩
  | lam t ih =>
    refine ih h (fun i => ?_)
    induction i using Fin.cases with
    | zero => trivial
    | succ i => exact (hσ i).rename _
  | tlam t ih => exact ih h (fun i => (hσ i).trename _)
  | tapp t A ih => exact ⟨ih h.1 hσ, h.2⟩

lemma AnnFixed.step {k n : ℕ} {t t' : PTm R k n} (hs : PStep t t') (h : t.AnnFixed) :
    t'.AnnFixed := by
  induction hs with
  | beta t₂ t₁ =>
    refine AnnFixed.subst (t := t₂) h.1 (fun i => ?_)
    induction i using Fin.cases with
    | zero => exact h.2
    | succ i => trivial
  | congAppL t₂ _ ih => exact ⟨ih h.1, h.2⟩
  | tyBeta t A => exact AnnFixed.tsubst (t := t) h.1 _
  | congTyApp A _ ih => exact ⟨ih h.1, h.2⟩

lemma AnnFixed.steps {k n : ℕ} {t t' : PTm R k n} (hs : PSteps t t') (h : t.AnnFixed) :
    t'.AnnFixed := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

end PTm

section Example

open LTm

/-- The empty typing context. -/
def ctx0 : Fin 0 → LTy Lin .base := fun i => i.elim0

/-- `K ⊸ K` -/
abbrev tyKK : LTy Lin .base := .lolli .base .base

/-- `λw. w` -/
abbrev idTm {n : ℕ} : LTm .base n := lam (var 0)

/-- `s₀ = let [x] = [λw. w] in x` -/
abbrev s0Tm : LTm .base 0 := letbox (box idTm) (var 0)

/-- `s = let [_] = [s₀] in λv. v` -/
abbrev sTm : LTm .base 0 := letbox (box s0Tm) idTm

/-- `t = (λy. y) s` -/
abbrev tTm : LTm .base 0 := app idTm sTm

lemma lToP_id {k n : ℕ} (Γ : Fin n → LTy Lin .base) (X : LTy Lin .base) :
    LToP (k := k) Γ emptyU idTm (.lolli X X) (.lam (.var 0)) := by
  refine LToP.abs ?_
  have h := LToP.var (k := k) (X .: Γ) 0
  rw [Use.only_zero] at h
  exact h

lemma single_zero_fin1 : (Use.single (0 : Fin 1) (Use.grd 1) : Fin 1 → Use Lin) =
    Use.grd 1 .: emptyU := by
  funext j; refine Fin.cases rfl (fun j => j.elim0) j

lemma update_zero_fin1 : Function.update (emptyU : Fin 1 → Use Lin) 0 (Use.grd 0) =
    Use.grd 0 .: emptyU := by
  funext j; refine Fin.cases (Function.update_self _ _ _) (fun j => j.elim0) j

lemma ctxAdd_fin0 (a b c : Fin 0 → Use Lin) : CtxAdd a b c := fun i => i.elim0

lemma usage_fin0 (a : Fin 0 → Use Lin) : a = emptyU := funext fun i => i.elim0

/-- A derivation of `s₀ : X ⊸ X`. -/
lemma lToP_s0 {k : ℕ} (X : LTy Lin .base) :
    LToP (k := k) ctx0 emptyU s0Tm (.lolli X X)
      (.app (.tapp (.tlam (.lam (.app (.var 0) ((PTm.lam (.var 0)).rename Fin.succ))))
        (LTy.toP (.lolli X X))) (.lam (.var 0))) := by
  have h₁ := LToP.pr (k := k) (1 : Lin) (lToP_id ctx0 X) Graded.emptyU
  have h₂ := LToP.var_grd1 (k := k) ((LTy.lolli X X) .: ctx0) 0
  rw [single_zero_fin1] at h₂
  exact LToP.letbox h₁ h₂ (ctxAdd_fin0 _ _ _)

/-- A derivation of `s : K ⊸ K`, typing the inner identity at `X ⊸ X`. -/
lemma lToP_s {k : ℕ} (X : LTy Lin .base) :
    LToP (k := k) ctx0 emptyU sTm tyKK
      (.app (.tapp (.tlam (.lam (.app (.var 0)
        (PTm.rename Fin.succ (.app (.tapp (.tlam (.lam (.app (.var 0)
          ((PTm.lam (.var 0)).rename Fin.succ)))) (LTy.toP (.lolli X X))) (.lam (.var 0)))))))
        (LTy.toP tyKK)) (.lam (.lam (.var 0)))) := by
  have h₁ := LToP.pr (k := k) (0 : Lin) (lToP_s0 (k := k + 1) X) Graded.emptyU
  have h₂ := LToP.weak (k := k) 0 (lToP_id ((LTy.lolli X X) .: ctx0) .base) rfl
  rw [update_zero_fin1] at h₂
  exact LToP.letbox h₁ h₂ (ctxAdd_fin0 _ _ _)

/-- **Counterexample** to the literal statement of operational correspondence in Theorem 4.1
(quantifying over *all* derivations `Π'` of the reduct). -/
theorem LToP.step_forall_counterexample :
    ¬ (∀ (t t' : LTm .base 0) (A : LTy Lin .base) (p p' : PTm Lin 0 0),
        LToP ctx0 emptyU t A p → LToP ctx0 emptyU t' A p' → LStep t t' → PSteps p p') := by
  intro H
  have hPi : LToP (k := 0) ctx0 emptyU tTm tyKK (.app (.lam (.var 0)) _) :=
    LToP.app (lToP_id ctx0 tyKK) (lToP_s .base) (ctxAdd_fin0 _ _ _)
  have hPi' := lToP_s (k := 0) tyKK
  have hstep : LStep tTm sTm := by
    have := LStep.beta (F := .base) (LTm.var 0) sTm
    exact this
  have hred := H _ _ _ _ _ hPi hPi' hstep
  have hfix := PTm.AnnFixed.steps hred (by
    simp only [PTm.AnnFixed, LTy.toP, PTm.rename, and_self])
  simp [PTm.AnnFixed, LTy.toP, PTm.rename] at hfix

end Example

end Coeffect
