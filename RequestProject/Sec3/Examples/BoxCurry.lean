module

public import RequestProject.Sec4.Translations.GradedModalVsPoly

/-!
# Is `□_x C →^y D` isomorphic to `C →^(x·y) D` in Graded Modal Base?

We study the two obvious candidate maps between `□_x C →^y D` and `C →^(x·y) D`:

* `modalToGraded = λg. λc. g [c]`;
* `gradedToModal = λf. λb. let [z] = b in f z`.

Results:

* `modalToGraded_typed`: over any pre-ordered semiring and for all grades `x, y`,
  `⊢ modalToGraded : (□_x C →^y D) →^1 (C →^(y·x) D)`.
* `gradedToModal_typed`: if `x·y ⊑ x` and `1 ⊑ y` then
  `⊢ gradedToModal : (C →^(x·y) D) →^1 (□_x C →^y D)`.
* `gradedToModal_typed_nat_iff`: over `ℕ` (usual order) these conditions are also
  **necessary**. More generally (`gradedToModal_typed_nat_necessary`), in *any* context and at
  *any* outer grade `r`, if `gradedToModal` has type `(C →^s D) →^r (□_x C →^y D)` then
  `s ≤ x` and `1 ≤ y`.
* `gradedToModal_untypable_two_three`: in particular over `ℕ`, for `x = 2` and `y = 3`,
  `gradedToModal` has no type `(C →^6 D) →^r (□_2 C →^3 D)` in any context and at any `r`.
-/

@[expose] public section

namespace Coeffect

namespace BoxCurry

universe u

variable {R : Type u} [PreorderedSemiring R]

local notation "M" => GLevel.modal

/-- `λg. λc. g [c]` (inside the binders `c` is index `0`, `g` is index `1`). -/
def modalToGraded : GTm M 0 := .lam (.lam (.app (.var 1) (.box trivial (.var 0))))

/-- `λf. λb. let [z] = b in f z` (under the `let`, `z` is index `0`, `b` index `1`, `f` index `2`). -/
def gradedToModal : GTm M 0 :=
  .lam (.lam (.letbox trivial (.var 0) (.app (.var 2) (.var 0))))

/-- `⊢ λg. λc. g [c] : (□_x C →^y D) →^1 (C →^(y·x) D)`, for all grades `x, y`. -/
theorem modalToGraded_typed (x y : R) (C D : GTy R M) :
    GTyped (Fin.elim0 : Fin 0 → GTy R M) Fin.elim0 modalToGraded
      (.fn 1 (.fn y (.box trivial x C) D) (.fn (y * x) C D)) := by
  refine GTyped.abs (GTyped.abs ?_)
  set Γ : Fin 2 → GTy R M := C .: GTy.fn y (.box trivial x C) D .: Fin.elim0
  have hg : GTyped Γ (Pi.single 1 1) (.var 1) (GTy.fn y (.box trivial x C) D) := GTyped.var Γ 1
  have hc : GTyped Γ (Pi.single 0 1) (.var 0) C := GTyped.var Γ 0
  refine (GTyped.app hg (GTyped.pr (F := M) trivial x hc)).cast ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [Fin.fin_one_eq_zero j]; simp

/-- `⊢ λf. λb. let [z] = b in f z : (C →^(x·y) D) →^1 (□_x C →^y D)`, provided `x·y ⊑ x` and
`1 ⊑ y`. -/
theorem gradedToModal_typed (x y : R) (C D : GTy R M) (hxy : x * y ≤ x) (hy : 1 ≤ y) :
    GTyped (Fin.elim0 : Fin 0 → GTy R M) Fin.elim0 gradedToModal
      (.fn 1 (.fn (x * y) C D) (.fn y (.box trivial x C) D)) := by
  refine GTyped.abs (GTyped.abs ?_)
  set Γ : Fin 2 → GTy R M := GTy.box trivial x C .: GTy.fn (x * y) C D .: Fin.elim0
  have hb : GTyped Γ (Pi.single 0 1) (.var 0) (GTy.box trivial x C) := GTyped.var Γ 0
  have hf : GTyped (C .: Γ) (Pi.single 2 1) (.var 2) (GTy.fn (x * y) C D) := GTyped.var _ 2
  have hz : GTyped (C .: Γ) (Pi.single 0 1) (.var 0) C := GTyped.var _ 0
  have happ := GTyped.app hf hz
  have hbody : GTyped (C .: Γ) (x .: (Pi.single 1 1 : Fin 2 → R)) (.app (.var 2) (.var 0)) D := by
    have := GTyped.approx 0 happ (s := x) (by simpa using hxy)
    refine this.cast ?_
    funext i
    fin_cases i <;> simp [scons] <;> rfl
  have hlet := GTyped.letbox (F := M) trivial hb hbody
  have hlet' := GTyped.approx 0 hlet (s := y) (by simpa using hy)
  refine hlet'.cast ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [Fin.fin_one_eq_zero j]; simp

/-! ## Necessity of the conditions over `ℕ` -/

variable {F : GLevel}

/-- Inversion for `let [x] = t₁ in t₂`, up to approximation. -/
lemma letbox_inv {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {h : F.Modal} {t₁ : GTm F n}
    {t₂ : GTm F (n + 1)} {B : GTy R F} (hty : GTyped Γ δ (.letbox h t₁ t₂) B) :
    ∃ (r : R) (A : GTy R F) (δ₁ δ₂ : Fin n → R), GTyped Γ δ₁ t₁ (.box h r A) ∧
      GTyped (A .: Γ) (r .: δ₂) t₂ B ∧ δ₁ + δ₂ ≤ δ := by
  generalize ht : (GTm.letbox h t₁ t₂ : GTm F n) = t at hty
  induction hty with
  | letbox _ h₁ h₂ => cases ht; exact ⟨_, _, _, _, h₁, h₂, le_rfl⟩
  | @approx _ _ δ _ _ k s _ hk ih =>
    obtain ⟨r, A, δ₁, δ₂, h1, h2, hle⟩ := ih ht
    refine ⟨r, A, δ₁, δ₂, h1, h2, le_trans hle fun j => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using hk
    · simp [Function.update_of_ne hj]
  | _ => cases ht

/-- Over `ℕ`, if `λf. λb. let [z] = b in f z` has type `(C →^s D) →^r (□_x C →^y D)` in any
context, then `s ≤ x` and `1 ≤ y`. -/
theorem gradedToModal_typed_nat_necessary {n : ℕ} (Γ : Fin n → GTy ℕ M) (δ : Fin n → ℕ)
    (r s x y : ℕ) (C D : GTy ℕ M)
    (hty : GTyped Γ δ (gradedToModal.rename Fin.elim0)
      (.fn r (.fn s C D) (.fn y (.box trivial x C) D))) : s ≤ x ∧ 1 ≤ y := by
  have e : (gradedToModal.rename Fin.elim0 : GTm M n) =
      .lam (.lam (.letbox trivial (.var 0) (.app (.var 2) (.var 0)))) := rfl
  rw [e] at hty
  obtain ⟨r₁, A₁, B₁, δ₁, e₁, h₁⟩ := GExample.lam_inv hty
  injection e₁ with er₁ eA₁ eB₁
  subst er₁ eA₁ eB₁
  obtain ⟨r₂, A₂, B₂, δ₂, e₂, h₂⟩ := GExample.lam_inv h₁
  injection e₂ with er₂ eA₂ eB₂
  subst er₂ eA₂ eB₂
  obtain ⟨r₃, A₃, δ₃, δ₄, hb, hbody, hle⟩ := letbox_inv h₂
  obtain ⟨eb, hb1⟩ := GExample.var_inv hb
  have eb' : (GTy.box trivial r₃ A₃ : GTy ℕ M) = (GTy.box trivial x C : GTy ℕ M) := eb
  injection eb' with er₃ eA₃
  subst r₃ A₃
  obtain ⟨s', A₄, δ₅, δ₆, hf, hz, hle₂⟩ := GExample.app_inv hbody
  obtain ⟨ef, -⟩ := GExample.var_inv hf
  obtain ⟨-, hz1⟩ := GExample.var_inv hz
  have ef' : GTy.fn s' A₄ D = GTy.fn s C D := ef
  injection ef' with es' _ _
  subst es'
  have a1 : 1 ≤ δ₃ 0 := by simpa using hb1 0
  have a2 : δ₃ 0 + δ₄ 0 ≤ y := by simpa using hle 0
  have a3 : 1 ≤ δ₆ 0 := by simpa using hz1 0
  have a4 : δ₅ 0 + s' * δ₆ 0 ≤ x := by simpa using hle₂ 0
  have : s' * 1 ≤ s' * δ₆ 0 := Nat.mul_le_mul_left _ a3
  constructor <;> omega

/-- Over `ℕ`: `⊢ λf. λb. let [z] = b in f z : (C →^(x·y) D) →^1 (□_x C →^y D)` holds **iff**
`x·y ≤ x` and `1 ≤ y` (i.e. `y = 1`, or `x = 0` and `y ≥ 1`). -/
theorem gradedToModal_typed_nat_iff (x y : ℕ) (C D : GTy ℕ M) :
    GTyped (Fin.elim0 : Fin 0 → GTy ℕ M) Fin.elim0 gradedToModal
      (.fn 1 (.fn (x * y) C D) (.fn y (.box trivial x C) D)) ↔ x * y ≤ x ∧ 1 ≤ y := by
  constructor
  · intro h
    have h' : GTyped (Fin.elim0 : Fin 0 → GTy ℕ M) Fin.elim0 (gradedToModal.rename Fin.elim0)
        (.fn 1 (.fn (x * y) C D) (.fn y (.box trivial x C) D)) := by
      have e : gradedToModal.rename (Fin.elim0 : Fin 0 → Fin 0) = gradedToModal := by
        have : (Fin.elim0 : Fin 0 → Fin 0) = id := funext fun i => i.elim0
        rw [this, GTm.rename_id]
      rw [e]; exact h
    exact gradedToModal_typed_nat_necessary _ _ _ _ _ _ _ _ h'
  · rintro ⟨h1, h2⟩
    exact gradedToModal_typed x y C D h1 h2

/-- The failing example: over `ℕ`, for `x = 2`, `y = 3`, the term `λf. λb. let [z] = b in f z`
has no type `(C →^6 D) →^r (□_2 C →^3 D)`, in any context and at any outer grade `r`. -/
theorem gradedToModal_untypable_two_three {n : ℕ} (Γ : Fin n → GTy ℕ M) (δ : Fin n → ℕ)
    (r : ℕ) (C D : GTy ℕ M) :
    ¬ GTyped Γ δ (gradedToModal.rename Fin.elim0)
      (.fn r (.fn 6 C D) (.fn 3 (.box trivial 2 C) D)) := by
  intro h
  have := (gradedToModal_typed_nat_necessary Γ δ r 6 2 3 C D h).1
  omega

end BoxCurry

end Coeffect
