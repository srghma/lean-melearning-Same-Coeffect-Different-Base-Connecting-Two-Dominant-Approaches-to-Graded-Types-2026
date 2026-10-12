module

public import RequestProject.Sec3.Translations.LinearToGradedModal

/-!
# Operational correspondence of `LPC → GMC` only holds up to a common reduct (Section 5.6)

The paper states operational correspondence for the translation `⦇-⦈` from Linear Push Core to
Graded Modal Core in the form `t ⇝_L t' ⟹ ⦇t⦈ ⇝_G* ⦇t'⦈`. This fails for the rules
`push⊗ [t] ⇝ push⊗ [t']` which reduce *under a box*: Graded Modal Core does not reduce under
boxes, and the translation `⦇push⊗ [t]⦈ = let [x] = [⦇t⦈] in …` substitutes `⦇t⦈` away
before `⦇t⦈` can be reduced.

Concretely, with `M = (λx.x) ⟨⟨⟩, ⟨⟩⟩` we have `push⊗ [M] ⇝_L push⊗ [⟨⟨⟩, ⟨⟩⟩]`, but the
translation of the left-hand side has exactly four reducts, none of which is the translation of
the right-hand side (`LStep.toG_counterexample`). The corrected statement (a common reduct
exists) is `LStep.toG_join`.
-/

@[expose] public section

namespace Coeffect

open LTm in
/-- `M = (λx.x) ⟨⟨⟩, ⟨⟩⟩` in Linear Push Core. -/
def cexM : LTm .push 0 := app (lam (var 0)) (pair trivial (unit trivial) (unit trivial))

open LTm in
/-- `⟨⟨⟩, ⟨⟩⟩` in Linear Push Core. -/
def cexP : LTm .push 0 := pair trivial (unit trivial) (unit trivial)

/-- The reduction `push⊗ [M] ⇝_L push⊗ [⟨⟨⟩, ⟨⟩⟩]` (by `push⊗`-box-congruence and `β`). -/
lemma cex_step :
    LStep (LTm.pushProd (F := .push) trivial (LTm.box cexM)) (LTm.pushProd trivial (LTm.box cexP)) :=
  LStep.pushProdBoxCong (F := .push) trivial (LStep.beta _ _)

open GTm in
/-- The four reducts of `⦇push⊗ [M]⦈`. -/
def cexReducts (x : GTm .core 0) : Prop :=
  x = (LTm.pushProd (F := .push) trivial (LTm.box cexM)).toG ∨
  x = letpair (F := .core) trivial (app (lam (var 0)) (pair trivial (unit trivial) (unit trivial)))
        (pair trivial (box trivial (var 1)) (box trivial (var 0))) ∨
  x = letpair (F := .core) trivial (pair trivial (unit trivial) (unit trivial))
        (pair trivial (box trivial (var 1)) (box trivial (var 0))) ∨
  x = pair (F := .core) trivial (box trivial (unit trivial)) (box trivial (unit trivial))

lemma cexReducts_closed {x y : GTm .core 0} (hx : cexReducts x) (h : GStep False x y) :
    cexReducts y := by
  rcases hx with rfl | rfl | rfl | rfl
  · cases h with
    | betaBox => exact Or.inr (Or.inl rfl)
    | congLetL _ _ h' => cases h'
  · cases h with
    | prodCong _ _ h' =>
      cases h' with
      | beta => exact Or.inr (Or.inr (Or.inl rfl))
      | congAppL _ h'' => cases h'' with | congAbs hb => cases hb
  · cases h with
    | prodBeta => exact Or.inr (Or.inr (Or.inr rfl))
    | prodCong _ _ h' => cases h'
  · cases h

/-- **Counterexample to the paper's Theorem 5.4 as stated**: there is a Linear Push Core
reduction `t ⇝_L t'` between closed terms with `¬ (⦇t⦈ ⇝_G* ⦇t'⦈)`. -/
theorem LStep.toG_counterexample :
    ∃ t t' : LTm .push 0, LStep t t' ∧ ¬ GSteps False t.toG t'.toG := by
  refine ⟨_, _, cex_step, fun h => ?_⟩
  have key : ∀ x, GSteps False (LTm.pushProd (F := .push) trivial (LTm.box cexM)).toG x → cexReducts x := by
    intro x hx
    induction hx with
    | refl => exact Or.inl rfl
    | tail _ hs ih => exact cexReducts_closed ih hs
  rcases key _ h with e | e | e | e <;> cases e

end Coeffect
