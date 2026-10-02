module

public import RequestProject.Sec2.GradedSyntax
public import RequestProject.Sec2.Semiring

/-!
# Typing of the graded-base lineage (Figure 3, Section 3.1, Figure 6)

A Graded Base context `Δ ::= ∅ | Δ, x :_r A` only contains graded assumptions. With de Bruijn
indices a context on `n` variables is a type assignment `Γ : Fin n → GTy R F` together with a
grade vector `δ : Fin n → R`. Context addition `Δ₁ + Δ₂` and scaling `r · Δ` are the pointwise
operations on grade vectors, and a variable that does not occur in the paper's context `Δ`
simply carries grade `0`. Consequently the paper's weakening rule
`Δ ⊢ t : A ⟹ Δ, 0·Δ' ⊢ t : A` is built into the representation, and the variable rule
`x :_1 A ⊢ x : A` becomes `Γ; (Pi.single i 1) ⊢ i : Γ i`.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R] {F : GLevel}

/-- The typing judgment `Δ ⊢_G t : A` of the graded-base calculi. -/
inductive GTyped : {n : ℕ} → (Fin n → GTy R F) → (Fin n → R) → GTm F n → GTy R F → Prop
  /-- `x :_1 A ⊢ x : A` (with all other variables weakened at grade `0`) -/
  | var {n : ℕ} (Γ : Fin n → GTy R F) (i : Fin n) : GTyped Γ (Pi.single i 1) (.var i) (Γ i)
  /-- abstraction: `Δ, x :_r A ⊢ t : B ⟹ Δ ⊢ λx.t : A →^r B` -/
  | abs {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F (n + 1)} {r : R}
      {A B : GTy R F} :
      GTyped (A .: Γ) (r .: δ) t B → GTyped Γ δ (.lam t) (.fn r A B)
  /-- application: `Δ₁ ⊢ t₁ : A →^r B`, `Δ₂ ⊢ t₂ : A ⟹ Δ₁ + r · Δ₂ ⊢ t₁ t₂ : B` -/
  | app {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ t₂ : GTm F n} {r : R}
      {A B : GTy R F} :
      GTyped Γ δ₁ t₁ (.fn r A B) → GTyped Γ δ₂ t₂ A → GTyped Γ (δ₁ + r • δ₂) (.app t₁ t₂) B
  /-- approximation: `Δ, x :_r B ⊢ t : A`, `r ⊑ s ⟹ Δ, x :_s B ⊢ t : A` -/
  | approx {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
      (i : Fin n) {s : R} :
      GTyped Γ δ t A → δ i ≤ s → GTyped Γ (Function.update δ i s) t A
  /-- promotion `Δ ⊢ t : A ⟹ r · Δ ⊢ [t] : □_r A` (Graded Modal Base) -/
  | pr {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
      (h : F.Modal = true) (r : R) :
      GTyped Γ δ t A → GTyped Γ (r • δ) (.box h t) (.box h r A)
  /-- graded modal elimination (Graded Modal Base) -/
  | letbox {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ : GTm F n} {t₂ : GTm F (n + 1)}
      {r : R} {A B : GTy R F} (h : F.Modal = true) :
      GTyped Γ δ₁ t₁ (.box h r A) → GTyped (A .: Γ) (r .: δ₂) t₂ B →
      GTyped Γ (δ₁ + δ₂) (.letbox h t₁ t₂) B
  /-- product introduction -/
  | pair {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ t₂ : GTm F n} {A B : GTy R F}
      (h : F.Core = true) :
      GTyped Γ δ₁ t₁ A → GTyped Γ δ₂ t₂ B → GTyped Γ (δ₁ + δ₂) (.pair h t₁ t₂) (.prod h A B)
  /-- product elimination: the context of the scrutinee is scaled by `r` -/
  | letpair {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ : GTm F n}
      {t₂ : GTm F (n + 2)} {r : R} {A B C : GTy R F} (h : F.Core = true) :
      GTyped Γ δ₁ t₁ (.prod h A B) → GTyped (B .: A .: Γ) (r .: r .: δ₂) t₂ C →
      GTyped Γ (r • δ₁ + δ₂) (.letpair h t₁ t₂) C
  /-- unit introduction -/
  | unit {n : ℕ} {Γ : Fin n → GTy R F} (h : F.Core = true) : GTyped Γ 0 (.unit h) (.unit h)
  /-- unit elimination -/
  | letunit {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ t₂ : GTm F n} {A : GTy R F}
      (h : F.Core = true) (r : R) :
      GTyped Γ δ₁ t₁ (.unit h) → GTyped Γ δ₂ t₂ A → GTyped Γ (r • δ₁ + δ₂) (.letunit h t₁ t₂) A
  /-- left injection -/
  | inl {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A B : GTy R F}
      (h : F.Core = true) : GTyped Γ δ t A → GTyped Γ δ (.inl h t) (.sum h A B)
  /-- right injection -/
  | inr {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A B : GTy R F}
      (h : F.Core = true) : GTyped Γ δ t B → GTyped Γ δ (.inr h t) (.sum h A B)
  /-- sum elimination, with side condition `1 ⊑ r` -/
  | case {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t : GTm F n} {t₁ t₂ : GTm F (n + 1)}
      {r : R} {A B C : GTy R F} (h : F.Core = true) :
      GTyped Γ δ₁ t (.sum h A B) → GTyped (A .: Γ) (r .: δ₂) t₁ C →
      GTyped (B .: Γ) (r .: δ₂) t₂ C → 1 ≤ r → GTyped Γ (r • δ₁ + δ₂) (.case h t t₁ t₂) C

namespace GTyped

variable {n : ℕ} {Γ : Fin n → GTy R F} {δ δ' : Fin n → R} {t : GTm F n} {A : GTy R F}

lemma cast (h : GTyped Γ δ t A) (e : δ = δ') : GTyped Γ δ' t A := e ▸ h

lemma castTy {A' : GTy R F} (h : GTyped Γ δ t A) (e : A = A') : GTyped Γ δ t A' := e ▸ h

end GTyped

/-! ## Renaming -/

section Renaming

variable {n m : ℕ}

lemma pushAlong_zero_add {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (δ₁ δ₂ : Fin n → R)
    {δ' : Fin m → R} (hu : ∀ i, δ' (ρ i) = (δ₁ + δ₂) i) (hoff : ∀ j, (∀ i, ρ i ≠ j) → δ' j = 0) :
    δ' = pushAlong ρ 0 δ₁ + pushAlong ρ 0 δ₂ := by
  funext j
  rcases range_or_off ρ j with ⟨i, rfl⟩ | hj
  · simp [pushAlong_apply hρ, hu]
  · simp [pushAlong_off _ _ j hj, hoff j hj]

lemma pushAlong_zero_smul {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (r : R)
    (δ : Fin n → R) : pushAlong ρ 0 (r • δ) = r • pushAlong ρ 0 δ := by
  funext j
  rcases range_or_off ρ j with ⟨i, rfl⟩ | hj
  · simp [pushAlong_apply hρ]
  · simp [pushAlong_off _ _ j hj]

/-- Typing is preserved by injective renamings (weakening and exchange). -/
theorem GTyped.rename {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
    (h : GTyped Γ δ t A) {m : ℕ} (ρ : Fin n → Fin m) (hρ : Function.Injective ρ)
    (Γ' : Fin m → GTy R F) (hΓ : ∀ i, Γ' (ρ i) = Γ i) (δ' : Fin m → R)
    (hu : ∀ i, δ' (ρ i) = δ i) (hoff : ∀ j, (∀ i, ρ i ≠ j) → δ' j = 0) :
    GTyped Γ' δ' (t.rename ρ) A := by
  have hpa : ∀ (ε : Fin n → R), (∀ i, pushAlong ρ (0 : R) ε (ρ i) = ε i) ∧
      (∀ j, (∀ i, ρ i ≠ j) → pushAlong ρ (0 : R) ε j = 0) :=
    fun ε => ⟨fun i => pushAlong_apply hρ _ _ i, fun j hj => pushAlong_off _ _ j hj⟩
  induction h generalizing m with
  | var Γ i =>
    have : δ' = Pi.single (ρ i) 1 := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; simp only [Pi.single_apply, hρ.eq_iff]
      · rw [hoff j hj, Pi.single_apply, if_neg (fun e => hj i e.symm)]
    rw [this, ← hΓ i]; exact GTyped.var Γ' (ρ i)
  | @abs _ _ _ _ r A _ _ ih =>
    refine GTyped.abs (ih (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ (r .: δ') ?_ ?_ ?_)
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hu]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j => exact hoff j (fun i e => hj i.succ (by simp [e]))
    · intro ε; exact ⟨fun i => pushAlong_apply (upRen_injective hρ) _ _ i,
        fun j hj => pushAlong_off _ _ j hj⟩
  | @app _ _ δ₁ δ₂ _ _ r _ _ _ _ ih₁ ih₂ =>
    have e : δ' = pushAlong ρ 0 δ₁ + r • pushAlong ρ 0 δ₂ := by
      rw [← pushAlong_zero_smul hρ]; exact pushAlong_zero_add hρ _ _ hu hoff
    rw [e]
    exact GTyped.app (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
  | @approx _ _ δ _ _ i s _ hi ih =>
    set δ'' := Function.update δ' (ρ i) (δ i)
    have h1 : ∀ k, δ'' (ρ k) = δ k := by
      intro k
      by_cases hk : k = i
      · subst hk; simp [δ'']
      · simp only [δ'']
        rw [Function.update_of_ne (fun e => hk (hρ e)), hu, Function.update_of_ne hk]
    have h2 : ∀ j, (∀ k, ρ k ≠ j) → δ'' j = 0 := by
      intro j hj; simp only [δ'']; rw [Function.update_of_ne (fun e => hj i e.symm), hoff j hj]
    have h3 : Function.update δ'' (ρ i) s = δ' := by
      simp only [δ'', Function.update_idem]
      have := hu i; rw [Function.update_self] at this
      rw [← this, Function.update_eq_self]
    rw [← h3]
    exact GTyped.approx (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2 hpa) (by simpa [δ''] using hi)
  | @pr _ _ δ _ _ h r _ ih =>
    have e : δ' = r • pushAlong ρ 0 δ := by
      rw [← pushAlong_zero_smul hρ]
      funext j
      rcases range_or_off ρ j with ⟨i, rfl⟩ | hj
      · rw [hu, pushAlong_apply hρ]
      · rw [hoff j hj, pushAlong_off _ _ j hj]
    rw [e]; exact GTyped.pr h r (ih ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
  | @letbox _ _ δ₁ δ₂ _ _ r A _ h _ _ ih₁ ih₂ =>
    rw [pushAlong_zero_add hρ _ _ hu hoff]
    refine GTyped.letbox h (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ (r .: pushAlong ρ 0 δ₂) ?_ ?_ ?_)
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [pushAlong_apply hρ]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j =>
        simp only [scons_succ]
        exact pushAlong_off _ _ j (fun i e => hj i.succ (by simp [e]))
    · intro ε; exact ⟨fun i => pushAlong_apply (upRen_injective hρ) _ _ i,
        fun j hj => pushAlong_off _ _ j hj⟩
  | pair h _ _ ih₁ ih₂ =>
    rw [pushAlong_zero_add hρ _ _ hu hoff]
    exact GTyped.pair h (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
  | @letpair _ _ δ₁ δ₂ _ _ r A B _ h _ _ ih₁ ih₂ =>
    rw [pushAlong_zero_add hρ _ _ hu hoff, pushAlong_zero_smul hρ]
    refine GTyped.letpair h (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ (upRen (upRen ρ)) (upRen_injective (upRen_injective hρ)) (B .: A .: Γ') ?_
        (r .: r .: pushAlong ρ 0 δ₂) ?_ ?_ ?_)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · refine Fin.cases ?_ ?_ i <;> simp [pushAlong_apply hρ]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j =>
        induction j using Fin.cases with
        | zero => exact absurd rfl (hj (Fin.succ 0))
        | succ j =>
          simp only [scons_succ]
          exact pushAlong_off _ _ j (fun i e => hj i.succ.succ (by simp [e]))
    · intro ε; exact ⟨fun i => pushAlong_apply (upRen_injective (upRen_injective hρ)) _ _ i,
        fun j hj => pushAlong_off _ _ j hj⟩
  | unit h =>
    have : δ' = 0 := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; rfl
      · exact hoff j hj
    rw [this]; exact GTyped.unit h
  | letunit h r _ _ ih₁ ih₂ =>
    rw [pushAlong_zero_add hρ _ _ hu hoff, pushAlong_zero_smul hρ]
    exact GTyped.letunit h r (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
  | inl h _ ih => exact GTyped.inl h (ih ρ hρ Γ' hΓ δ' hu hoff hpa)
  | inr h _ ih => exact GTyped.inr h (ih ρ hρ Γ' hΓ δ' hu hoff hpa)
  | @case _ _ δ₁ δ₂ _ _ _ r A B _ h _ _ _ hr ih ih₁ ih₂ =>
    rw [pushAlong_zero_add hρ _ _ hu hoff, pushAlong_zero_smul hρ]
    refine GTyped.case h (ih ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₁ (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ (r .: pushAlong ρ 0 δ₂) ?_ ?_ ?_)
      (ih₂ (upRen ρ) (upRen_injective hρ) (B .: Γ') ?_ (r .: pushAlong ρ 0 δ₂) ?_ ?_ ?_) hr
    all_goals first
      | (intro ε; exact ⟨fun i => pushAlong_apply (upRen_injective hρ) _ _ i,
          fun j hj => pushAlong_off _ _ j hj⟩)
      | (intro j hj
         induction j using Fin.cases with
         | zero => exact absurd rfl (hj 0)
         | succ j =>
           simp only [scons_succ]
           exact pushAlong_off _ _ j (fun i e => hj i.succ (by simp [e])))
      | (intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ, pushAlong_apply hρ])

end Renaming

end Coeffect
