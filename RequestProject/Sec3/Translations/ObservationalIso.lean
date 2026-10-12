module

public import RequestProject.Sec3.Translations.LinearToGradedModal
public import RequestProject.Sec2.Translations.GradedToLinear

/-!
# Observational isomorphism between Linear Base and Graded Modal Base (Section 3.2.4)

The translations `⦇-⦈ : LB → GMB` and `⟦-⟧ : GMB → LB` are not mutually inverse, but composing
the operational correspondence theorems shows that round-tripping preserves reduction in both
directions (Corollary 3.4).
-/

@[expose] public section

namespace Coeffect

/-- The calculus *Linear Base*. -/
abbrev LinearBase := LLevel.base
/-- The calculus *Linear Core*. -/
abbrev LinearCore := LLevel.core
/-- The calculus *Linear Push Core*. -/
abbrev LinearPushCore := LLevel.push
/-- The calculus *Graded Base*. -/
abbrev GradedBase := GLevel.base
/-- The calculus *Graded Modal Base*. -/
abbrev GradedModalBase := GLevel.modal
/-- The calculus *Graded Modal Core*. -/
abbrev GradedModalCore := GLevel.core

/-- Multi-step version of `GStep.toL`. -/
theorem GSteps.toL {F : GLevel} {n : ℕ} {t t' : GTm F n} (h : GSteps False t t') :
    LSteps t.toL t'.toL := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.trans h.toL

/-- Multi-step version of `LStep.toG` (for Linear Base and Linear Core). -/
theorem LSteps.toG {F : LLevel} (hF : ¬ F.Push) {n : ℕ} {t t' : LTm F n}
    (h : LSteps t t') : GSteps False t.toG t'.toG := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.toG hF)

/-- **Corollary 3.4 (observational isomorphism), Linear Base side**:
`t ⇝_L t' ⟹ ⟦⦇t⦈⟧ ⇝_L* ⟦⦇t'⦈⟧`. -/
theorem LStep.roundTrip {n : ℕ} {t t' : LTm LinearBase n} (h : LStep t t') :
    LSteps t.toG.toL t'.toG.toL :=
  (h.toG (by decide)).toL

/-- **Corollary 3.4 (observational isomorphism), Graded Modal Base side**:
`t ⇝_G t' ⟹ ⦇⟦t⟧⦈ ⇝_G* ⦇⟦t'⟧⦈`. -/
theorem GStep.roundTrip {n : ℕ} {t t' : GTm GradedModalBase n} (h : GStep False t t') :
    GSteps False t.toL.toG t'.toL.toG :=
  LSteps.toG (F := LLevel.base) (by decide) h.toL

end Coeffect
