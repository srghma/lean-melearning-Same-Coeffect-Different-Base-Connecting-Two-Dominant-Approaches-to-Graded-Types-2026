module

public import RequestProject.Sec2.Graded.Typing

/-!
# Example: the "apply twice" function in Graded Base (Section 2.2)

The paper's example (after Figure 3) types the body of `h = λf. λx. f (f x)`. With de Bruijn
indices, inside the two binders `x` is index `0` and `f` is index `1`, so the body is
`app (var 1) (app (var 1) (var 0))`, and a context on two variables is written
`A .: (A →^r A) .: Fin.elim0` (types) with grade vector `(grade of x) .: (grade of f) .: Fin.elim0`.

The application rule `Δ₁ + r · Δ₂` gives these grades:

* inner `f x`:   `f :_1, x :_r`, as the paper says;
* outer `f (f x)`: `f :_(1 + r·1) = 1 + r`, `x :_(0 + r·r) = r·r`.

The paper's conclusion originally said `f :_(1 + 1)` (and the introduction gave the type
`(A →^r A) →^2 (A →^(r*r) A)`). That grade does **not** follow from the paper's own application
rule unless `r ⊑ 1`, in which case the approximation rule turns `1 + r` into `1 + 1`. The `.tex`
sources (`calculi-ottput.tex`, `introduction-ottput.tex`) have been corrected to `1 + r`, which is
exactly what `twice_body` and `twice_typed` prove. In this file we prove:

* `GExample.twice_body`: the derivation with the grades the rule actually gives,
  `f :_(1 + r), x :_(r · r) ⊢ f (f x) : A`, over any pre-ordered semiring;
* `GExample.twice_typed`: the whole function, `⊢ h : (A →^r A) →^(1 + r) (A →^(r · r) A)`;
* `GExample.twice_body_paper_of_le_one`: the originally printed judgment
  `f :_(1 + 1), x :_(r · r) ⊢ f (f x) : A` holds when `r ⊑ 1`;
* `GExample.twice_body_paper_not_always`: the originally printed judgment fails in general:
  over `ℕ` with its usual order and `r = 2`, it is not derivable.
-/

@[expose] public section

namespace Coeffect

namespace GExample

universe u

variable {R : Type u} [PreorderedSemiring R] {F : GLevel}

/-- The body `f (f x)` of `h = λf. λx. f (f x)` (`x` is index `0`, `f` is index `1`). -/
def twiceBody : GTm F 2 := .app (.var 1) (.app (.var 1) (.var 0))

/-- The closed term `h = λf. λx. f (f x)`. -/
def twice : GTm F 0 := .lam (.lam twiceBody)

/-- The typing context `f : A →^r A, x : A` (index `0` is `x`). -/
def twiceCtx (r : R) (A : GTy R F) : Fin 2 → GTy R F := A .: GTy.fn r A A .: Fin.elim0

/-- The derivation of the paper's example, with the grades produced by the application rule:
`f :_(1 + r) (A →^r A), x :_(r · r) A ⊢ f (f x) : A`. -/
theorem twice_body (r : R) (A : GTy R F) :
    GTyped (twiceCtx r A) ((r * r) .: (1 + r) .: Fin.elim0) twiceBody A := by
  have hf : GTyped (twiceCtx r A) (Pi.single 1 1) (.var 1) (GTy.fn r A A) := GTyped.var _ 1
  have hx : GTyped (twiceCtx r A) (Pi.single 0 1) (.var 0) A := GTyped.var _ 0
  refine (GTyped.app hf (GTyped.app hf hx)).cast ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [Fin.fin_one_eq_zero j]; simp

/-- The whole function: `⊢ λf. λx. f (f x) : (A →^r A) →^(1 + r) (A →^(r · r) A)`. -/
theorem twice_typed (r : R) (A : GTy R F) :
    GTyped (Fin.elim0 : Fin 0 → GTy R F) Fin.elim0 twice
      (GTy.fn (1 + r) (GTy.fn r A A) (GTy.fn (r * r) A A)) := by
  refine GTyped.abs (GTyped.abs ?_)
  exact twice_body r A

/-- The paper's literal conclusion `f :_(1 + 1) (A →^r A), x :_(r · r) A ⊢ f (f x) : A`
holds whenever `r ⊑ 1` (by approximation from `twice_body`). -/
theorem twice_body_paper_of_le_one (r : R) (A : GTy R F) (hr : r ≤ 1) :
    GTyped (twiceCtx r A) ((r * r) .: (1 + 1) .: Fin.elim0) twiceBody A := by
  have h := GTyped.approx 1 (twice_body r A)
    (s := 1 + 1) (PreorderedSemiring.add_mono le_rfl hr)
  refine h.cast ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.fin_one_eq_zero j]; rfl

/-! ## The paper's literal grade is not derivable in general -/

/-- Inversion for variables: the type is the context entry and the grade vector is at least
`Pi.single i 1`. -/
lemma var_inv {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {i : Fin n} {T : GTy R F}
    (h : GTyped Γ δ (.var i) T) : T = Γ i ∧ Pi.single i 1 ≤ δ := by
  generalize ht : (GTm.var i : GTm F n) = t at h
  induction h with
  | var Γ j => cases ht; exact ⟨rfl, le_rfl⟩
  | @approx _ _ δ _ _ k s _ hk ih =>
    obtain ⟨h1, h2⟩ := ih ht
    refine ⟨h1, le_trans h2 fun j => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using hk
    · simp [Function.update_of_ne hj]
  | _ => cases ht

/-- Inversion for applications, up to approximation. -/
lemma app_inv {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t₁ t₂ : GTm F n} {B : GTy R F}
    (h : GTyped Γ δ (.app t₁ t₂) B) :
    ∃ (r : R) (A : GTy R F) (δ₁ δ₂ : Fin n → R), GTyped Γ δ₁ t₁ (.fn r A B) ∧
      GTyped Γ δ₂ t₂ A ∧ δ₁ + r • δ₂ ≤ δ := by
  generalize ht : (GTm.app t₁ t₂ : GTm F n) = t at h
  induction h with
  | app h₁ h₂ => cases ht; exact ⟨_, _, _, _, h₁, h₂, le_rfl⟩
  | @approx _ _ δ _ _ k s _ hk ih =>
    obtain ⟨r, A, δ₁, δ₂, h1, h2, hle⟩ := ih ht
    refine ⟨r, A, δ₁, δ₂, h1, h2, le_trans hle fun j => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using hk
    · simp [Function.update_of_ne hj]
  | _ => cases ht

/-- The natural numbers with their usual order form a pre-ordered semiring. -/
instance natPreorderedSemiring : PreorderedSemiring ℕ where
  add_mono := Nat.add_le_add
  mul_mono := Nat.mul_le_mul

/-- Over `ℕ`, any derivation of `f (f x)` in the context `f : A →^r A, x : A` gives `f` a grade
at least `1 + r`. -/
lemma twice_body_grade_f_nat {F : GLevel} {r : ℕ} {A : GTy ℕ F} {δ : Fin 2 → ℕ}
    (h : GTyped (twiceCtx r A) δ twiceBody A) : 1 + r ≤ δ 1 := by
  obtain ⟨r₁, A₁, δ₁, δ₂, h₁, h₂, hle⟩ := app_inv h
  obtain ⟨e₁, hf₁⟩ := var_inv h₁
  obtain ⟨r₂, A₂, δ₃, δ₄, h₃, _, hle₂⟩ := app_inv h₂
  obtain ⟨_, hf₃⟩ := var_inv h₃
  simp only [twiceCtx, scons_one] at e₁
  injection e₁ with er
  subst er
  have a1 : 1 ≤ δ₁ 1 := by simpa using hf₁ 1
  have a3 : 1 ≤ δ₃ 1 := by simpa using hf₃ 1
  have a2 : δ₃ 1 + r₂ * δ₄ 1 ≤ δ₂ 1 := by simpa using hle₂ 1
  have a0 : δ₁ 1 + r₁ * δ₂ 1 ≤ δ 1 := by simpa using hle 1
  have : r₁ * 1 ≤ r₁ * δ₂ 1 := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The paper's literal conclusion is **not** derivable in general: over `ℕ` (usual order) with
`r = 2`, the judgment `f :_(1 + 1) (A →^2 A), x :_(2 · 2) A ⊢ f (f x) : A` has no derivation,
because every derivation gives `f` a grade of at least `1 + 2 = 3`. -/
theorem twice_body_paper_not_always {F : GLevel} (A : GTy ℕ F) :
    ¬ GTyped (twiceCtx 2 A) ((2 * 2) .: (1 + 1) .: Fin.elim0) twiceBody A := by
  intro h
  have := twice_body_grade_f_nat h
  simp at this

end GExample

end Coeffect
