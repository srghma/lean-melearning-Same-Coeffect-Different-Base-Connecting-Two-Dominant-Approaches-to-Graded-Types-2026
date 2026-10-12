module

public import RequestProject.Sec2.Embedding
public import RequestProject.Sec2.GradedToLinear
public import RequestProject.Sec2.LinearToGradedCPS
public import RequestProject.Sec3.LinearToGradedModal
public import RequestProject.Sec3.ObservationalIso
public import RequestProject.Sec4.GradedToPoly
public import RequestProject.Sec4.LinearToPoly
public import RequestProject.Sec5.NaiveGradedToLinear
public import RequestProject.Sec5.PushCoreCounterexample

/-!
# The diagram of calculi and translations

Each arrow of the diagram

```
 Linear-Base lineage                 Graded-Base lineage
 LB ⇢ LC ⇢ LPC                       GB ⇢ GPB,  GB ⇢ GMB ⇢ GMC
 LB ⇄ GB,  LB → GPB,  LB ⇄ GMB,  LC → GMC,  GMC ⇢ LC (❌ unsound),  LPC ⇄ GMC
```

is stated here as one theorem about the named calculi, collecting the results proved in the
chapter files (`Sec2` … `Sec5`). Dotted arrows are inclusions of calculi, solid arrows are
translations. For translations we list type preservation, operational correspondence and (where
the paper has one) equation preservation, in the form in which they hold.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R]

/-! ## Dotted arrows: inclusions -/

/-- `LB ⇢ LC` and `LC ⇢ LPC` (and hence `LB ⇢ LPC`): the smaller calculus embeds into the bigger
one, preserving typing and reduction. -/
theorem arrow_linear_inclusion {F G : LLevel} (hFG : F ≤ G) :
    (∀ {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A : LTy R F},
      LTyped Γ u t A → LTyped (fun i => (Γ i).embed hFG) u (t.embed hFG) (A.embed hFG)) ∧
    (∀ {n : ℕ} {t t' : LTm F n}, LStep t t' → LStep (t.embed hFG) (t'.embed hFG)) :=
  ⟨fun h => h.embed hFG, fun h => h.embed hFG⟩

/-- `GB ⇢ GMB` and `GMB ⇢ GMC`: inclusions preserving typing and reduction. -/
theorem arrow_graded_inclusion {F G : GLevel} (hFG : F ≤ G) :
    (∀ {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F},
      GTyped Γ δ t A → GTyped (fun i => (Γ i).embed hFG) δ (t.embed hFG) (A.embed hFG)) ∧
    (∀ {b : Bool} {n : ℕ} {t t' : GTm F n}, GStep b t t' → GStep b (t.embed hFG) (t'.embed hFG)) :=
  ⟨fun h => h.embed hFG, fun h => h.embed hFG⟩

/-- `GB ⇢ GPB`: Graded Base is the fragment of Graded Poly Base without type variables. -/
theorem arrow_GB_GPB :
    (∀ {n : ℕ} {Γ : Fin n → GTy R GradedBase} {δ : Fin n → R} {t : GTm GradedBase n}
      {A : GTy R GradedBase},
      GTyped Γ δ t A → PTyped (fun i => (Γ i).toP (k := 0)) δ (t.toP (R := R)) A.toP) ∧
    (∀ {n : ℕ} {t t' : GTm GradedBase n}, GStep false t t' →
      PStep (t.toP (R := R) (k := 0)) t'.toP) :=
  ⟨fun h => h.toP, fun h => h.toP⟩

/-! ## Solid arrows: translations -/

/-- `GB → LB` (Theorem 2.5) and `GMB → LB` (Theorem 3.2): `⟦-⟧` preserves typing, reduction and
the equational theory. -/
theorem arrow_GB_GMB_to_LB {F : GLevel} (hF : ¬ F.Core) :
    (∀ {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F},
      GTyped Γ δ t A → LTyped (toLCtx Γ) (grdU δ) t.toL A.toL) ∧
    (∀ {n : ℕ} {t t' : GTm F n}, GStep false t t' → LSteps t.toL t'.toL) ∧
    (∀ {n : ℕ} {t t' : GTm F n}, GEq t t' → LEq t.toL t'.toL) :=
  ⟨fun h => h.toL, fun h => h.toL, fun h => h.toL hF⟩

/-- `LB → GB` (Theorem 2.7), the CPS translation: type preservation, simulation of each step by
full β-reduction up to `≡_G`, and preservation of `≡_L^{β→βη□}`. -/
theorem arrow_LB_GB :
    (∀ {n : ℕ} {Γ : Fin n → LTy R LinearBase} {u : Fin n → Use R} {t : LTm LinearBase n}
      {A : LTy R LinearBase},
      LTyped Γ u t A → GTyped (cpsCtx Γ) (toGGrades (GradeMap.id R) u) t.cps A.cps) ∧
    (∀ {n : ℕ} {t t' : LTm LinearBase n}, LStep t t' →
      ∃ t'', GSteps true t.cps t'' ∧ GEq t'.cps t'') ∧
    (∀ {n : ℕ} {t t' : LTm LinearBase n}, LCong (LAxF LAxSel.cps) t t' → GEq t.cps t'.cps) :=
  ⟨fun h => h.cps, fun h => h.cps, fun h => h.cps⟩

/-- `LB → GPB` (Theorem 4.1, type preservation): every Linear Base derivation has a translation
into Graded Poly Base, and translations are well typed. -/
theorem arrow_LB_GPB :
    ∀ {n : ℕ} {Γ : Fin n → LTy R LinearBase} {u : Fin n → Use R} {t : LTm LinearBase n}
      {A : LTy R LinearBase}, LTyped Γ u t A →
      ∃ p : PTm R 0 n, LToP Γ u t A p ∧
        PTyped (fun i => (Γ i).toP) (toGGrades (GradeMap.id R) u) p A.toP := by
  intro n Γ u t A h
  obtain ⟨p, hp⟩ := h.toP_exists 0
  exact ⟨p, hp, hp.typed⟩

/-- `LB → GMB` (Theorem 3.1) and `LC → GMC` (Theorem 5.3): `⦇-⦈` preserves typing (for any grade
map, in particular the identity and the linearity-preserving map of Theorem 3.3), each reduction
step is simulated by one step, and the full equational theory is preserved. -/
theorem arrow_LB_LC_to_GMB_GMC {F : LLevel} (hF : ¬ F.Push) {S : Type u}
    [PreorderedSemiring S] (φ : GradeMap R S) :
    (∀ {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A : LTy R F},
      LTyped Γ u t A → GTyped (toGCtx φ Γ) (toGGrades φ u) t.toG (A.toG φ)) ∧
    (∀ {n : ℕ} {t t' : LTm F n}, LStep t t' → GStep false t.toG t'.toG) ∧
    (∀ {n : ℕ} {t t' : LTm F n}, LEq t t' → GEq t.toG t'.toG) :=
  ⟨fun h => h.toG φ, fun h => h.toG hF, fun h => h.toG hF⟩

/-- `LB ⇄ GMB` round trip (Corollary 3.4, observational isomorphism). -/
theorem arrow_LB_GMB_roundTrip :
    (∀ {n : ℕ} {t t' : LTm LinearBase n}, LStep t t' → LSteps t.toG.toL t'.toG.toL) ∧
    (∀ {n : ℕ} {t t' : GTm GradedModalBase n}, GStep false t t' →
      GSteps false t.toL.toG t'.toL.toG) :=
  ⟨fun h => h.roundTrip, fun h => h.roundTrip⟩

/-- `GMC ⇢ LC` is **unsound**: the naive homomorphic translation maps the well-typed Graded Modal
Core term `λp. let ⟨x, y⟩ = p in ⟨[x], [y]⟩` to an ill-typed Linear Core term. -/
theorem arrow_GMC_LC_unsound (r : R) (A B : GTy R GradedModalCore) :
    ∃ (t : GTm GradedModalCore 0) (T : GTy R GradedModalCore), GTyped (R := R) Fin.elim0 0 t T ∧
      ∀ (Γ : Fin 0 → LTy R LinearCore) (u : Fin 0 → Use R) (T' : LTy R LinearCore),
        ¬ LTyped Γ u t.toLNaive T' :=
  naive_not_typeSound r A B

/-- `GMC → LPC` (Theorem 5.1): `⟦-⟧` preserves typing and reduction, and the equational theory
without the η-rules for products and sums. -/
theorem arrow_GMC_LPC :
    (∀ {n : ℕ} {Γ : Fin n → GTy R GradedModalCore} {δ : Fin n → R} {t : GTm GradedModalCore n}
      {A : GTy R GradedModalCore}, GTyped Γ δ t A → LTyped (toLCtx Γ) (grdU δ) t.toL A.toL) ∧
    (∀ {n : ℕ} {t t' : GTm GradedModalCore n}, GStep false t t' → LSteps t.toL t'.toL) ∧
    (∀ {n : ℕ} {t t' : GTm GradedModalCore n}, GCong (GAxF false) t t' → LEq t.toL t'.toL) :=
  ⟨fun h => h.toL, fun h => h.toL, fun h => h.toL⟩

/-- `LPC → GMC` (Theorem 5.4): `⦇-⦈` preserves typing; operational correspondence holds in the
corrected form "the two sides of a step have a common reduct" (the paper's form
`⦇t⦈ ⇝* ⦇t'⦈` fails, `LStep.toG_counterexample`); the equational theory without the
`push`-η rules is preserved. -/
theorem arrow_LPC_GMC {S : Type u} [PreorderedSemiring S] (φ : GradeMap R S) :
    (∀ {n : ℕ} {Γ : Fin n → LTy R LinearPushCore} {u : Fin n → Use R} {t : LTm LinearPushCore n}
      {A : LTy R LinearPushCore},
      LTyped Γ u t A → GTyped (toGCtx φ Γ) (toGGrades φ u) t.toG (A.toG φ)) ∧
    (∀ {n : ℕ} {t t' : LTm LinearPushCore n}, LStep t t' →
      ∃ s, GSteps false t.toG s ∧ GSteps false t'.toG s) ∧
    (∃ t t' : LTm LinearPushCore 0, LStep t t' ∧ ¬ GSteps false t.toG t'.toG) ∧
    (∀ {n : ℕ} {t t' : LTm LinearPushCore n}, LCong (LAxF LAxSel.noPushEta) t t' →
      GEq t.toG t'.toG) :=
  ⟨fun h => h.toG φ, fun h => h.toG_join, LStep.toG_counterexample, fun h => h.toG⟩

end Coeffect
