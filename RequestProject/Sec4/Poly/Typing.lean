module

public import RequestProject.Sec4.Poly.Syntax
public import RequestProject.Sec2.Graded.Typing

/-!
# Graded Poly Base: typing and reduction (Section 4.1)

Typing `Δ ⊢_{G∀} t : A` extends Graded Base typing (variables, abstraction, application,
approximation) with the standard rules for type abstraction and application:

```
Δ ⊢ t : B   (α fresh)          Δ ⊢ t : ∀α. B
--------------------           --------------------
Δ ⊢ Λα. t : ∀α. B              Δ ⊢ t @ A : [A/α] B
```

With de Bruijn type variables, "α fresh" is expressed by weakening all context types by the new
type variable. The reduction relation adds `(Λα. t) @ A ⇝ [A/α] t` and congruence for `@`.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- Weakening of a type by a fresh type variable. -/
abbrev PTy.shift {k : ℕ} (A : PTy R k) : PTy R (k + 1) := A.rename Fin.succ

variable [PreorderedSemiring R]

/-- The typing judgment `Δ ⊢_{G∀} t : A` of Graded Poly Base. -/
inductive PTyped : {k n : ℕ} → (Fin n → PTy R k) → (Fin n → R) → PTm R k n → PTy R k → Prop
  /-- `x :_1 A ⊢ x : A` -/
  | var {k n : ℕ} (Γ : Fin n → PTy R k) (i : Fin n) : PTyped Γ (Pi.single i 1) (.var i) (Γ i)
  /-- abstraction -/
  | abs {k n : ℕ} {Γ : Fin n → PTy R k} {δ : Fin n → R} {t : PTm R k (n + 1)} {r : R}
      {A B : PTy R k} :
      PTyped (A .: Γ) (r .: δ) t B → PTyped Γ δ (.lam t) (.fn r A B)
  /-- application -/
  | app {k n : ℕ} {Γ : Fin n → PTy R k} {δ₁ δ₂ : Fin n → R} {t₁ t₂ : PTm R k n} {r : R}
      {A B : PTy R k} :
      PTyped Γ δ₁ t₁ (.fn r A B) → PTyped Γ δ₂ t₂ A → PTyped Γ (δ₁ + r • δ₂) (.app t₁ t₂) B
  /-- approximation -/
  | approx {k n : ℕ} {Γ : Fin n → PTy R k} {δ : Fin n → R} {t : PTm R k n} {A : PTy R k}
      (i : Fin n) {s : R} :
      PTyped Γ δ t A → δ i ≤ s → PTyped Γ (Function.update δ i s) t A
  /-- type abstraction -/
  | tabs {k n : ℕ} {Γ : Fin n → PTy R k} {δ : Fin n → R} {t : PTm R (k + 1) n}
      {B : PTy R (k + 1)} :
      PTyped (fun i => (Γ i).shift) δ t B → PTyped Γ δ (.tlam t) (.all B)
  /-- type application -/
  | tapp {k n : ℕ} {Γ : Fin n → PTy R k} {δ : Fin n → R} {t : PTm R k n} {B : PTy R (k + 1)}
      (A : PTy R k) :
      PTyped Γ δ t (.all B) → PTyped Γ δ (.tapp t A) (B.subst1 A)

namespace PTyped

variable {k n : ℕ} {Γ : Fin n → PTy R k} {δ δ' : Fin n → R} {t : PTm R k n} {A : PTy R k}

lemma cast (h : PTyped Γ δ t A) (e : δ = δ') : PTyped Γ δ' t A := e ▸ h

lemma castTy {A' : PTy R k} (h : PTyped Γ δ t A) (e : A = A') : PTyped Γ δ t A' := e ▸ h

end PTyped

/-- Typing is preserved by injective renamings of term variables (weakening and exchange). -/
theorem PTyped.rename {k n : ℕ} {Γ : Fin n → PTy R k} {δ : Fin n → R} {t : PTm R k n}
    {A : PTy R k} (h : PTyped Γ δ t A) {m : ℕ} (ρ : Fin n → Fin m) (hρ : Function.Injective ρ)
    (Γ' : Fin m → PTy R k) (hΓ : ∀ i, Γ' (ρ i) = Γ i) (δ' : Fin m → R)
    (hu : ∀ i, δ' (ρ i) = δ i) (hoff : ∀ j, (∀ i, ρ i ≠ j) → δ' j = 0) :
    PTyped Γ' δ' (t.rename ρ) A := by
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
    rw [this, ← hΓ i]; exact PTyped.var Γ' (ρ i)
  | @abs _ _ _ _ _ r A _ _ ih =>
    refine PTyped.abs (ih (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ (r .: δ') ?_ ?_ ?_)
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hu]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j => exact hoff j (fun i e => hj i.succ (by simp [e]))
    · intro ε; exact ⟨fun i => pushAlong_apply (upRen_injective hρ) _ _ i,
        fun j hj => pushAlong_off _ _ j hj⟩
  | @app _ _ _ δ₁ δ₂ _ _ r _ _ _ _ ih₁ ih₂ =>
    have e : δ' = pushAlong ρ 0 δ₁ + r • pushAlong ρ 0 δ₂ := by
      rw [← pushAlong_zero_smul hρ]; exact pushAlong_zero_add hρ _ _ hu hoff
    rw [e]
    exact PTyped.app (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
  | @approx _ _ _ δ _ _ i s _ hi ih =>
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
      simp only [δ'', update_idem']
      have := hu i; rw [Function.update_self] at this
      rw [← this, update_eq_self']
    rw [← h3]
    exact PTyped.approx (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2 hpa) (by simpa [δ''] using hi)
  | tabs _ ih =>
    exact PTyped.tabs (ih ρ hρ _ (fun i => by simp only [hΓ]) _ hu hoff hpa)
  | tapp A _ ih => exact PTyped.tapp A (ih ρ hρ Γ' hΓ _ hu hoff hpa)

/-! ## Reduction -/

/-- Call-by-name reduction of Graded Poly Base (`β`, type-`β`, and congruence on the left of
term and type applications). -/
inductive PStep : {k n : ℕ} → PTm R k n → PTm R k n → Prop
  | beta {k n : ℕ} (t₂ : PTm R k (n + 1)) (t₁ : PTm R k n) :
      PStep (.app (.lam t₂) t₁) (t₂.subst1 t₁)
  | congAppL {k n : ℕ} {t₁ t₁' : PTm R k n} (t₂ : PTm R k n) :
      PStep t₁ t₁' → PStep (.app t₁ t₂) (.app t₁' t₂)
  /-- `(Λα. t) @ A ⇝ [A/α] t` -/
  | tyBeta {k n : ℕ} (t : PTm R (k + 1) n) (A : PTy R k) : PStep (.tapp (.tlam t) A) (t.tsubst1 A)
  | congTyApp {k n : ℕ} {t t' : PTm R k n} (A : PTy R k) :
      PStep t t' → PStep (.tapp t A) (.tapp t' A)

/-- Reflexive-transitive closure of `PStep`. -/
abbrev PSteps {k n : ℕ} : PTm R k n → PTm R k n → Prop := Relation.ReflTransGen PStep

end Coeffect
