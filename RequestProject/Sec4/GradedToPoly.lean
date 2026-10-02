module

public import RequestProject.Sec4.PolyTyping
public import RequestProject.Sec2.GradedSemantics

/-!
# Graded Base ⊆ Graded Poly Base (the dotted arrow `GB ⇢ GPB`)

Graded Poly Base extends Graded Base, so every Graded Base type, term and typing derivation
is one of Graded Poly Base (with no type variables used), and reduction is preserved.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- Inclusion of Graded Base types into Graded Poly Base (in any type-variable context). -/
def GTy.toP {k : ℕ} : GTy R .base → PTy R k
  | .base => .base
  | .fn r A B => .fn r A.toP B.toP
  | .box h _ _ => absurd h (by decide)
  | .prod h _ _ => absurd h (by decide)
  | .unit h => absurd h (by decide)
  | .sum h _ _ => absurd h (by decide)

/-- Inclusion of Graded Base terms into Graded Poly Base. -/
def GTm.toP {k n : ℕ} : GTm .base n → PTm R k n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.toP t₂.toP
  | .lam t => .lam t.toP
  | .box h _ => absurd h (by decide)
  | .letbox h _ _ => absurd h (by decide)
  | .pair h _ _ => absurd h (by decide)
  | .letpair h _ _ => absurd h (by decide)
  | .unit h => absurd h (by decide)
  | .letunit h _ _ => absurd h (by decide)
  | .inl h _ => absurd h (by decide)
  | .inr h _ => absurd h (by decide)
  | .case h _ _ _ => absurd h (by decide)

lemma GTy.toP_cons {k n : ℕ} (A : GTy R .base) (Γ : Fin n → GTy R .base) :
    (fun i => ((A .: Γ) i).toP (k := k)) = (A.toP .: fun i => (Γ i).toP) :=
  scons_map _ _ _

variable [PreorderedSemiring R]

/-- The inclusion `GB ⊆ GPB` preserves typing. -/
theorem GTyped.toP {k n : ℕ} {Γ : Fin n → GTy R .base} {δ : Fin n → R} {t : GTm .base n}
    {A : GTy R .base} (h : GTyped Γ δ t A) :
    PTyped (fun i => (Γ i).toP (k := k)) δ (t.toP (R := R)) A.toP := by
  induction h with
  | var Γ i => exact PTyped.var _ i
  | abs _ ih => rw [GTy.toP_cons] at ih; exact PTyped.abs ih
  | app _ _ ih₁ ih₂ => exact PTyped.app ih₁ ih₂
  | approx i _ hi ih => exact PTyped.approx i ih hi
  | pr h => exact absurd h (by decide)
  | letbox h => exact absurd h (by decide)
  | pair h => exact absurd h (by decide)
  | letpair h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | letunit h => exact absurd h (by decide)
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)
  | case h => exact absurd h (by decide)

omit [PreorderedSemiring R] in
theorem GTm.toP_rename {k n m : ℕ} (t : GTm .base n) (ρ : Fin n → Fin m) :
    (t.rename ρ).toP (R := R) (k := k) = (t.toP).rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | app _ _ ih₁ ih₂ => simp only [GTm.rename, GTm.toP, PTm.rename, ih₁, ih₂]
  | lam _ ih => simp only [GTm.rename, GTm.toP, PTm.rename, ih]
  | box h => exact absurd h (by decide)
  | letbox h => exact absurd h (by decide)
  | pair h => exact absurd h (by decide)
  | letpair h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | letunit h => exact absurd h (by decide)
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)
  | case h => exact absurd h (by decide)

omit [PreorderedSemiring R] in
theorem GTm.toP_subst {k n m : ℕ} (t : GTm .base n) (σ : Fin n → GTm .base m) :
    (t.subst σ).toP (R := R) (k := k) = (t.toP).subst (fun i => (σ i).toP) := by
  induction t generalizing m with
  | var i => rfl
  | app _ _ ih₁ ih₂ => simp only [GTm.subst, GTm.toP, PTm.subst, ih₁, ih₂]
  | lam _ ih =>
    simp only [GTm.subst, GTm.toP, PTm.subst, ih]
    congr 2; funext i; refine Fin.cases rfl (fun j => ?_) i
    exact GTm.toP_rename _ _
  | box h => exact absurd h (by decide)
  | letbox h => exact absurd h (by decide)
  | pair h => exact absurd h (by decide)
  | letpair h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | letunit h => exact absurd h (by decide)
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)
  | case h => exact absurd h (by decide)

omit [PreorderedSemiring R] in
/-- The inclusion `GB ⊆ GPB` preserves (call-by-name) reduction. -/
theorem GStep.toP {k n : ℕ} {t t' : GTm .base n} (h : GStep false t t') :
    PStep (t.toP (R := R) (k := k)) t'.toP := by
  induction h with
  | beta t₂ t₁ =>
    rw [GTm.toP_subst]
    have : (fun i => ((t₁ .: GTm.var) i).toP (R := R) (k := k)) = (t₁.toP .: PTm.var) := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [this]; exact PStep.beta _ _
  | congAppL _ _ ih => exact PStep.congAppL _ ih
  | congAbs hb => exact absurd hb (by decide)
  | betaBox h => exact absurd h (by decide)
  | congLetL h => exact absurd h (by decide)
  | prodCong h => exact absurd h (by decide)
  | prodBeta h => exact absurd h (by decide)
  | unitCong h => exact absurd h (by decide)
  | unitBeta h => exact absurd h (by decide)
  | congCase h => exact absurd h (by decide)
  | caseInl h => exact absurd h (by decide)
  | caseInr h => exact absurd h (by decide)

end Coeffect
