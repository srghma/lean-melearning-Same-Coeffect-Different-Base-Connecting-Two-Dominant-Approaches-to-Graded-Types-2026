module

public import RequestProject.Sec2.Graded.Examples
public import RequestProject.Sec2.Inclusions.Levels
public import RequestProject.Sec2.Translations.GradedToLinear
public import RequestProject.Sec3.Translations.ObservationalIso
public import RequestProject.Sec4.Translations.LinearToPoly.Soundness
public import RequestProject.Sec4.Translations.LinearToPoly.Direct

/-!
# Are Graded Modal Base and Graded Poly Base equivalent?

The paper relates Linear Base and Graded Modal Base by translations in *both* directions
(`LB → GMB`, Theorem 3.1, and `GMB → LB`, Theorem 3.2), whose round trips are observationally
the identity (Corollary 3.4). We check how Graded Modal Base (GMB) and Graded Poly Base (GPB)
compare in the same sense.

## `GMB → GPB`: yes (by composition)

Composing `⟦-⟧ : GMB → LB` (Theorem 3.2) with the derivation-based `⦇-⦈ : LB → GPB`
(Theorem 4.1) gives a translation of GMB into GPB:

* `GTyped.toGPB` (type preservation): every GMB derivation `Δ ⊢ t : A` has a GPB translation
  `p` of `⟦t⟧`, with `Δ ⊢_{G∀} p : ⦇⟦A⟧⦈` (same grades);
* `GStep.toGPB` (operational correspondence): if `p` translates a derivation for `⟦t⟧` and
  `t ⇝ t'`, then some translation `p'` of a derivation for `⟦t'⟧` satisfies `p ⇝* p'`.

(The equational theories do not compose: `⟦-⟧` maps `≡_G` into the full `≡_L`, but `⦇-⦈` only
preserves `≡_L^{-η□}` without commuting conversions, so no equation preservation is claimed.)

## `GPB → GMB`: no type-erasing translation

The paper gives no translation from GPB back to GMB (nor to LB), so the two calculi are **not**
related like LB ⇄ GMB, and no round-trip statement can be made. What can be said formally:
polymorphism adds typable terms. The GPB term

```
selfApp = λx. (x @ (∀α. α →¹ α)) x  :  (∀α. α →¹ α) →^(1+1) (∀α. α →¹ α)
```

is closed and well typed (`selfApp_typed`), but its type erasure `λx. x x` has no typing
derivation in GMB — nor in GB or GMC — in any context and at any type (`selfApp_erase_untypable`,
from `lam_selfApp_untypable`). Hence *every* translation `GPB → GMB` that is homomorphic on
variables, `λ` and application and erases `Λ` and `@` (this includes "instantiate every type
variable by `K`", or any other type-level translation) fails type preservation.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R]

/-! ## `GMB → GPB` by composition -/

lemma toGGrades_id_grdU {n : ℕ} (δ : Fin n → R) : toGGrades (GradeMap.id R) (grdU δ) = δ := rfl

/-- Type preservation of the composite translation `GMB → LB → GPB`. -/
theorem GTyped.toGPB {n : ℕ} {Γ : Fin n → GTy R GradedModalBase} {δ : Fin n → R}
    {t : GTm GradedModalBase n} {A : GTy R GradedModalBase} (h : GTyped Γ δ t A) :
    ∃ p : PTm R 0 n, LToP (toLCtx Γ) (grdU δ) t.toL A.toL p ∧
      PTyped (fun i => (toLCtx Γ i).toP) δ p A.toL.toP := by
  obtain ⟨p, hp⟩ := (GTyped.toL h).toP_exists 0
  exact ⟨p, hp, hp.typed⟩

/-- Operational correspondence of the composite translation `GMB → LB → GPB`. -/
theorem GStep.toGPB {k n : ℕ} {Γ : Fin n → GTy R GradedModalBase} {δ : Fin n → R}
    {t t' : GTm GradedModalBase n} {A : GTy R GradedModalBase} {p : PTm R k n}
    (h : LToP (toLCtx Γ) (grdU δ) t.toL A.toL p) (hs : GStep False t t') :
    ∃ p', LToP (toLCtx Γ) (grdU δ) t'.toL A.toL p' ∧ PSteps p p' :=
  h.steps (GStep.toL hs)

/-! ## A GPB term whose erasure is not typable in the monomorphic graded calculi -/

/-- The polymorphic identity type `∀α. α →¹ α`. -/
def polyIdTy {k : ℕ} : PTy R k := .all (.fn 1 (.tvar 0) (.tvar 0))

/-- Self-application `λx. (x @ (∀α. α →¹ α)) x` in Graded Poly Base. -/
def selfApp : PTm R 0 0 := .lam (.app (.tapp (.var 0) polyIdTy) (.var 0))

/-- `⊢_{G∀} λx. (x @ (∀α. α →¹ α)) x : (∀α. α →¹ α) →^(1+1) (∀α. α →¹ α)`. -/
theorem selfApp_typed :
    PTyped (Fin.elim0 : Fin 0 → PTy R 0) Fin.elim0 selfApp
      (.fn (1 + 1) polyIdTy polyIdTy) := by
  refine PTyped.abs ?_
  have hx : PTyped (polyIdTy .: (Fin.elim0 : Fin 0 → PTy R 0)) (Pi.single 0 1) (.var 0)
      polyIdTy := PTyped.var _ 0
  have h1 := PTyped.tapp (polyIdTy (R := R)) hx
  refine (PTyped.app (h1.castTy rfl) hx).cast ?_
  funext i
  refine Fin.cases ?_ (fun j => j.elim0) i
  simp

namespace GExample

variable {F : GLevel}

/-- Inversion for abstractions, up to approximation. -/
lemma lam_inv {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F (n + 1)} {T : GTy R F}
    (h : GTyped Γ δ (.lam t) T) :
    ∃ (r : R) (A B : GTy R F) (δ' : Fin n → R), T = .fn r A B ∧ GTyped (A .: Γ) (r .: δ') t B := by
  generalize ht : (GTm.lam t : GTm F n) = s at h
  induction h with
  | abs h => cases ht; exact ⟨_, _, _, _, rfl, h⟩
  | approx _ _ _ ih => exact ih ht
  | _ => cases ht

omit [PreorderedSemiring R] in
lemma GTy.fn_ne_self (r : R) (A B : GTy R F) : GTy.fn r A B ≠ A := by
  intro h
  have := congrArg sizeOf h
  simp at this
  omega

/-- Self-application `x x` of a variable is not typable in GB, GMB or GMC. -/
theorem selfApp_var_untypable {n : ℕ} (Γ : Fin n → GTy R F) (δ : Fin n → R) (i : Fin n)
    (T : GTy R F) : ¬ GTyped Γ δ (.app (.var i) (.var i)) T := by
  intro h
  obtain ⟨r, A, δ₁, δ₂, h₁, h₂, -⟩ := app_inv h
  obtain ⟨e₁, -⟩ := var_inv h₁
  obtain ⟨e₂, -⟩ := var_inv h₂
  exact GTy.fn_ne_self r A T (e₁.trans e₂.symm)

/-- `λx. x x` is not typable in GB, GMB or GMC, in any context and at any type. -/
theorem lam_selfApp_untypable {n : ℕ} (Γ : Fin n → GTy R F) (δ : Fin n → R) (T : GTy R F) :
    ¬ GTyped Γ δ (.lam (.app (.var 0) (.var 0))) T := by
  intro h
  obtain ⟨_, _, _, _, -, h'⟩ := lam_inv h
  exact selfApp_var_untypable _ _ 0 _ h'

end GExample

/-- The type erasure of `selfApp` is `λx. x x`. -/
theorem selfApp_erase : (selfApp (R := R)).erase = .lam (.app (.var 0) (.var 0)) := rfl

/-- **No type-erasing translation `GPB → GMB`.** The closed, well-typed GPB term `selfApp`
erases (embedded into any of GB, GMB, GMC) to a term with no typing derivation in any context
and at any type. -/
theorem selfApp_erase_untypable {F : GLevel} (hF : GLevel.base ≤ F) {n : ℕ}
    (Γ : Fin n → GTy R F) (δ : Fin n → R) (T : GTy R F) :
    ¬ GTyped Γ δ (((selfApp (R := R)).erase.embed hF).rename Fin.elim0) T :=
  GExample.lam_selfApp_untypable Γ δ T

end Coeffect
