module

public import RequestProject.Sec4.Translations.LinearToPoly.Soundness

/-!
# Equation preservation for the translation LB → GPB (Theorem 4.1)

As for operational correspondence, the translation is defined on derivations, so equation
preservation is stated as: for every derivation `Π` of `Γ ⊢ t : A` and every equation
`t ≡ t'`, there is a derivation `Π'` of `Γ ⊢ t' : A` with `⦇Π⦈ ≡_{G∀} ⦇Π'⦈`
(`LToP.eq_preserve`).

The equations considered are those of `≡_L` used left to right inside arbitrary contexts
(`LEqDir`), for the sub-theory without the `η`-rule for the graded modality (which the paper
also excludes) and without the commuting conversions (see `FORMALIZATION.md`). The `η`-rule for
`⊸` is included; it needs a strengthening lemma (`LToP.unrename`).
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R]

/-! ## Inversion of renamings on Linear Base terms -/

namespace LTm

lemma rename_eq_var {n m : ℕ} {ρ : Fin n → Fin m} {t : LTm .base n} {j : Fin m}
    (h : t.rename ρ = .var j) : ∃ i, t = .var i ∧ ρ i = j := by
  cases t with
  | var i => exact ⟨i, rfl, by injection h⟩
  | _ => cases h

lemma rename_eq_lam {n m : ℕ} {ρ : Fin n → Fin m} {t : LTm .base n} {b' : LTm .base (m + 1)}
    (h : t.rename ρ = .lam b') : ∃ b, t = .lam b ∧ b' = b.rename (upRen ρ) := by
  cases t with
  | lam b => injection h with _ h; exact ⟨b, rfl, h.symm⟩
  | _ => cases h

lemma rename_eq_app {n m : ℕ} {ρ : Fin n → Fin m} {t : LTm .base n} {a' b' : LTm .base m}
    (h : t.rename ρ = .app a' b') : ∃ a b, t = .app a b ∧ a' = a.rename ρ ∧ b' = b.rename ρ := by
  cases t with
  | app a b => injection h with _ h₁ h₂; exact ⟨a, b, rfl, h₁.symm, h₂.symm⟩
  | _ => cases h

lemma rename_eq_box {n m : ℕ} {ρ : Fin n → Fin m} {t : LTm .base n} {a' : LTm .base m}
    (h : t.rename ρ = .box a') : ∃ a, t = .box a ∧ a' = a.rename ρ := by
  cases t with
  | box a => injection h with _ h; exact ⟨a, rfl, h.symm⟩
  | _ => cases h

lemma rename_eq_letbox {n m : ℕ} {ρ : Fin n → Fin m} {t : LTm .base n} {a' : LTm .base m}
    {b' : LTm .base (m + 1)} (h : t.rename ρ = .letbox a' b') :
    ∃ a b, t = .letbox a b ∧ a' = a.rename ρ ∧ b' = b.rename (upRen ρ) := by
  cases t with
  | letbox a b => injection h with _ h₁ h₂; exact ⟨a, b, rfl, h₁.symm, h₂.symm⟩
  | _ => cases h

end LTm

lemma comp_upRen_scons {α : Type*} {n m : ℕ} (a : α) (f : Fin m → α) (ρ : Fin n → Fin m) :
    (fun i => (a .: f) (upRen ρ i)) = (a .: fun i => f (ρ i)) := by
  funext i; exact Fin.cases rfl (fun _ => rfl) i

lemma update_comp_injective {α : Type*} {n m : ℕ} {ρ : Fin n → Fin m}
    (hρ : Function.Injective ρ) (f : Fin m → α) (i : Fin n) (x : α) :
    (fun j => Function.update f (ρ i) x (ρ j)) = Function.update (fun j => f (ρ j)) i x := by
  funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · rw [Function.update_of_ne (fun e => h (hρ e)), Function.update_of_ne h]

lemma Use.Add.none_result {a b : Use R} (h : Use.Add a b Use.none) :
    a = Use.none ∧ b = Use.none := by
  cases h <;> exact ⟨rfl, rfl⟩

lemma Use.smul_eq_none {r : R} {a : Use R} (h : a.smul r = Use.none) : a = Use.none := by
  cases a with
  | none => rfl
  | lin => cases h
  | grd s => cases h

omit [PreorderedSemiring R] in
lemma only_comp_injective {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (i : Fin n) :
    (fun j => (Use.only (ρ i) : Fin m → Use R) (ρ j)) = Use.only i := by
  funext j; simp only [Use.only, hρ.eq_iff]

/-- **Strengthening**: a translated derivation of a renamed term, in which the variables outside
the image of the renaming are unused, comes from a translated derivation of the original term. -/
theorem LToP.unrename {k m : ℕ} {Δ : Fin m → LTy R .base} {u : Fin m → Use R}
    {t' : LTm .base m} {T : LTy R .base} {p : PTm R k m} (h : LToP Δ u t' T p) :
    ∀ {n : ℕ} (ρ : Fin n → Fin m) (t : LTm .base n), Function.Injective ρ → t' = t.rename ρ →
      (∀ j, (∀ i, ρ i ≠ j) → u j = Use.none) →
      ∃ p₀, p = p₀.rename ρ ∧ LToP (fun i => Δ (ρ i)) (fun i => u (ρ i)) t T p₀ := by
  induction h with
  | var Δ j =>
    intro n ρ t hρ et hoff
    obtain ⟨i, rfl, rfl⟩ := LTm.rename_eq_var et.symm
    refine ⟨.var i, rfl, ?_⟩
    rw [only_comp_injective hρ]
    exact LToP.var _ i
  | @abs k m Δ u b' A B pb _ ih =>
    intro n ρ t hρ et hoff
    obtain ⟨b, rfl, rfl⟩ := LTm.rename_eq_lam et.symm
    obtain ⟨pb₀, rfl, hb⟩ := ih (upRen ρ) b (upRen_injective hρ) rfl (fun j hj => by
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j => exact hoff j (fun i e => hj i.succ (by simp [e])))
    rw [comp_upRen_scons, comp_upRen_scons] at hb
    exact ⟨.lam pb₀, rfl, .abs hb⟩
  | app _ _ hadd ih₁ ih₂ =>
    intro n ρ t hρ et hoff
    obtain ⟨a, b, rfl, rfl, rfl⟩ := LTm.rename_eq_app et.symm
    have h₁ : ∀ j, (∀ i, ρ i ≠ j) → _ := fun j hj => by
      have := hadd j; rw [hoff j hj] at this; exact this.none_result.1
    have h₂ : ∀ j, (∀ i, ρ i ≠ j) → _ := fun j hj => by
      have := hadd j; rw [hoff j hj] at this; exact this.none_result.2
    obtain ⟨p₁, rfl, hp₁⟩ := ih₁ ρ a hρ rfl h₁
    obtain ⟨p₂, rfl, hp₂⟩ := ih₂ ρ b hρ rfl h₂
    exact ⟨.app p₁ p₂, rfl, .app hp₁ hp₂ (fun i => hadd (ρ i))⟩
  | weak i _ hi ih =>
    intro n ρ t hρ et hoff
    rcases range_or_off ρ i with ⟨i₀, rfl⟩ | hoffi
    · obtain ⟨p₀, rfl, hp₀⟩ := ih ρ t hρ et (fun j hj => by
        have := hoff j hj
        rwa [Function.update_of_ne (fun e => hj i₀ e.symm)] at this)
      refine ⟨p₀, rfl, ?_⟩
      rw [update_comp_injective hρ]
      exact .weak i₀ hp₀ hi
    · have := hoff i hoffi; rw [Function.update_self] at this; cases this
  | der i _ hi ih =>
    intro n ρ t hρ et hoff
    rcases range_or_off ρ i with ⟨i₀, rfl⟩ | hoffi
    · obtain ⟨p₀, rfl, hp₀⟩ := ih ρ t hρ et (fun j hj => by
        have := hoff j hj
        rwa [Function.update_of_ne (fun e => hj i₀ e.symm)] at this)
      refine ⟨p₀, rfl, ?_⟩
      rw [update_comp_injective hρ]
      exact .der i₀ hp₀ hi
    · have := hoff i hoffi; rw [Function.update_self] at this; cases this
  | approx i _ hi hrs ih =>
    intro n ρ t hρ et hoff
    rcases range_or_off ρ i with ⟨i₀, rfl⟩ | hoffi
    · obtain ⟨p₀, rfl, hp₀⟩ := ih ρ t hρ et (fun j hj => by
        have := hoff j hj
        rwa [Function.update_of_ne (fun e => hj i₀ e.symm)] at this)
      refine ⟨p₀, rfl, ?_⟩
      rw [update_comp_injective hρ]
      exact .approx i₀ hp₀ hi hrs
    · have := hoff i hoffi; rw [Function.update_self] at this; cases this
  | @pr k m Δ u a' A q r _ hg ih =>
    intro n ρ t hρ et hoff
    obtain ⟨a, rfl, rfl⟩ := LTm.rename_eq_box et.symm
    obtain ⟨q₀, rfl, hq₀⟩ := ih ρ a hρ rfl (fun j hj => Use.smul_eq_none (hoff j hj))
    refine ⟨.tlam (.lam (.app (.var 0) (q₀.rename Fin.succ))), ?_, ?_⟩
    · simp only [PTm.rename, PTm.rename_rename]; rfl
    · exact .pr r hq₀ (fun i => hg (ρ i))
  | @letbox k m Δ u₁ u₂ u t₁ t₂ r A B p₁ p₂ _ _ hadd ih₁ ih₂ =>
    intro n ρ t hρ et hoff
    obtain ⟨a, b, rfl, rfl, rfl⟩ := LTm.rename_eq_letbox et.symm
    have h₁ : ∀ j, (∀ i, ρ i ≠ j) → _ := fun j hj => by
      have := hadd j; rw [hoff j hj] at this; exact this.none_result.1
    have h₂ : ∀ j, (∀ i, ρ i ≠ j) → _ := fun j hj => by
      have := hadd j; rw [hoff j hj] at this; exact this.none_result.2
    obtain ⟨q₁, rfl, hq₁⟩ := ih₁ ρ a hρ rfl h₁
    obtain ⟨q₂, rfl, hq₂⟩ := ih₂ (upRen ρ) b (upRen_injective hρ) rfl (fun j hj => by
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j => exact h₂ j (fun i e => hj i.succ (by simp [e])))
    rw [comp_upRen_scons, comp_upRen_scons] at hq₂
    exact ⟨.app (.tapp q₁ B.toP) (.lam q₂), rfl, .letbox hq₁ hq₂ (fun i => hadd (ρ i))⟩

/-! ## Structural closure and inversions for application and variables -/

/-- The order on usages generated by *all* structural rules (weakening, dereliction,
approximation). -/
inductive Use.SLe : Use R → Use R → Prop
  | refl (a : Use R) : Use.SLe a a
  | noneGrd {s : R} : 0 ≤ s → Use.SLe .none (.grd s)
  | linGrd {s : R} : 1 ≤ s → Use.SLe .lin (.grd s)
  | grd {a b : R} : a ≤ b → Use.SLe (.grd a) (.grd b)

lemma Use.SLe.trans {a b c : Use R} (h₁ : Use.SLe a b) (h₂ : Use.SLe b c) : Use.SLe a c := by
  cases h₁ with
  | refl => exact h₂
  | noneGrd h => cases h₂ with
    | refl => exact .noneGrd h
    | grd h' => exact .noneGrd (le_trans h h')
  | linGrd h => cases h₂ with
    | refl => exact .linGrd h
    | grd h' => exact .linGrd (le_trans h h')
  | grd h => cases h₂ with
    | refl => exact .grd h
    | grd h' => exact .grd (le_trans h h')

lemma Use.Le.toSLe {a b : Use R} (h : Use.Le a b) : Use.SLe a b := by
  cases h with
  | none => exact .refl _
  | lin => exact .refl _
  | grd h => exact .grd h
  | noneGrd h => exact .noneGrd h

lemma Use.SLe.none_right {a : Use R} (h : Use.SLe a .none) : a = .none := by cases h; rfl

lemma Use.SLe.lin_right {a : Use R} (h : Use.SLe a .lin) : a = .lin := by cases h; rfl

/-- One structural step at a single position. -/
lemma LToP.mono1S {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) (i : Fin n) {x : Use R}
    (hx : Use.SLe (u i) x) : LToP Γ (Function.update u i x) t A p := by
  generalize hy : u i = y at hx
  cases hx with
  | refl => rw [← hy, update_eq_self']; exact h
  | grd hab => exact .approx i h hy hab
  | noneGrd hb =>
    have h1 := LToP.weak i h hy
    have h2 := LToP.approx i h1 (Function.update_self _ _ _) hb
    rwa [update_idem'] at h2
  | linGrd hb =>
    have h1 := LToP.der i h hy
    have h2 := LToP.approx i h1 (Function.update_self _ _ _) hb
    rwa [update_idem'] at h2

/-- Admissibility of all structural rules in bulk. -/
theorem LToP.monoS {k n : ℕ} {Γ : Fin n → LTy R .base} {u u' : Fin n → Use R}
    {t : LTm .base n} {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p)
    (hle : ∀ j, Use.SLe (u j) (u' j)) : LToP Γ u' t A p := by
  suffices H : ∀ (k : ℕ) (u' : Fin n → Use R), (∀ j, Use.SLe (u j) (u' j)) →
      (∀ j : Fin n, k ≤ j.val → u' j = u j) → LToP Γ u' t A p from
    H n u' hle (fun j hj => absurd j.isLt (Nat.not_lt.mpr hj))
  intro k
  induction k with
  | zero =>
    intro u' _ hS
    have : u' = u := funext fun j => hS j (Nat.zero_le _)
    rw [this]; exact h
  | succ k ih =>
    intro u' hle' hS
    by_cases hk : k < n
    · let a : Fin n := ⟨k, hk⟩
      have h1 : LToP Γ (Function.update u' a (u a)) t A p := by
        apply ih
        · intro j
          by_cases hja : j = a
          · subst hja; rw [Function.update_self]; exact .refl _
          · rw [Function.update_of_ne hja]; exact hle' j
        · intro j hj
          by_cases hja : j = a
          · subst hja; rw [Function.update_self]
          · rw [Function.update_of_ne hja]
            have : j.val ≠ k := fun e => hja (Fin.ext e)
            exact hS j (by omega)
      have h2 := h1.mono1S a (x := u' a) (by rw [Function.update_self]; exact hle' a)
      rwa [update_idem', update_eq_self'] at h2
    · apply ih u' hle'
      intro j hj
      exact absurd j.isLt (by omega)

/-- Inversion for application, up to structural rules applied afterwards. -/
theorem LToP.inv_app {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R}
    {a b : LTm .base n} {B : LTy R .base} {p : PTm R k n} (h : LToP Γ u (.app a b) B p) :
    ∃ (u₁ u₂ w : Fin n → Use R) (A : LTy R .base) (p₁ p₂ : PTm R k n), p = .app p₁ p₂ ∧
      LToP Γ u₁ a (.lolli A B) p₁ ∧ LToP Γ u₂ b A p₂ ∧ CtxAdd u₁ u₂ w ∧
      ∀ j, Use.SLe (w j) (u j) := by
  suffices H : ∀ (t : LTm .base n), LToP Γ u t B p → t = .app a b →
      ∃ (u₁ u₂ w : Fin n → Use R) (A : LTy R .base) (p₁ p₂ : PTm R k n), p = .app p₁ p₂ ∧
        LToP Γ u₁ a (.lolli A B) p₁ ∧ LToP Γ u₂ b A p₂ ∧ CtxAdd u₁ u₂ w ∧
        ∀ j, Use.SLe (w j) (u j) from H _ h rfl
  clear h
  intro t h
  induction h with
  | app h₁ h₂ hadd =>
    intro e; cases e
    exact ⟨_, _, _, _, _, _, rfl, h₁, h₂, hadd, fun j => .refl _⟩
  | weak i _ hi ih =>
    intro e
    obtain ⟨u₁, u₂, w, A, p₁, p₂, hp, h₁, h₂, hadd, hS⟩ := ih e
    refine ⟨u₁, u₂, w, A, p₁, p₂, hp, h₁, h₂, hadd, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]
      have := hS j; rw [hi] at this; rw [this.none_right]; exact .noneGrd le_rfl
    · rw [Function.update_of_ne hj]; exact hS j
  | der i _ hi ih =>
    intro e
    obtain ⟨u₁, u₂, w, A, p₁, p₂, hp, h₁, h₂, hadd, hS⟩ := ih e
    refine ⟨u₁, u₂, w, A, p₁, p₂, hp, h₁, h₂, hadd, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]
      have := hS j; rw [hi] at this; rw [this.lin_right]; exact .linGrd le_rfl
    · rw [Function.update_of_ne hj]; exact hS j
  | approx i _ hi hrs ih =>
    intro e
    obtain ⟨u₁, u₂, w, A, p₁, p₂, hp, h₁, h₂, hadd, hS⟩ := ih e
    refine ⟨u₁, u₂, w, A, p₁, p₂, hp, h₁, h₂, hadd, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]
      have := hS j; rw [hi] at this; exact this.trans (.grd hrs)
    · rw [Function.update_of_ne hj]; exact hS j
  | var => intro e; cases e
  | abs => intro e; cases e
  | pr => intro e; cases e
  | letbox => intro e; cases e

/-- A usage that is either absent or a non-negative grade. -/
def Use.Nonneg (x : Use R) : Prop := x = .none ∨ ∃ s, x = .grd s ∧ 0 ≤ s

/-- Inversion for variables. -/
theorem LToP.inv_var {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {i : Fin n}
    {T : LTy R .base} {p : PTm R k n} (h : LToP Γ u (.var i) T p) :
    p = .var i ∧ T = Γ i ∧ u i ≠ .none ∧ ∀ j, j ≠ i → (u j).Nonneg := by
  suffices H : ∀ (t : LTm .base n), LToP Γ u t T p → t = .var i →
      p = .var i ∧ T = Γ i ∧ u i ≠ .none ∧ ∀ j, j ≠ i → (u j).Nonneg from H _ h rfl
  clear h
  intro t h
  induction h with
  | var Γ i' =>
    intro e; cases e
    refine ⟨rfl, rfl, by simp [Use.only], fun j hj => Or.inl ?_⟩
    simp only [Use.only, if_neg hj]
  | weak i' _ hi ih =>
    intro e
    obtain ⟨hp, hT, hne, hnn⟩ := ih e
    by_cases hii : i' = i
    · subst hii; exact absurd hi hne
    · refine ⟨hp, hT, ?_, fun j hj => ?_⟩
      · rw [Function.update_of_ne (Ne.symm hii)]; exact hne
      · by_cases hj' : j = i'
        · subst hj'; rw [Function.update_self]; exact Or.inr ⟨0, rfl, le_rfl⟩
        · rw [Function.update_of_ne hj']; exact hnn j hj
  | der i' _ hi ih =>
    intro e
    obtain ⟨hp, hT, hne, hnn⟩ := ih e
    by_cases hii : i' = i
    · subst hii
      refine ⟨hp, hT, ?_, fun j hj => ?_⟩
      · rw [Function.update_self]; exact fun h => by cases h
      · rw [Function.update_of_ne hj]; exact hnn j hj
    · exfalso
      rcases hnn i' hii with h | ⟨s, h, _⟩ <;> rw [hi] at h <;> cases h
  | approx i' _ hi hrs ih =>
    intro e
    obtain ⟨hp, hT, hne, hnn⟩ := ih e
    by_cases hii : i' = i
    · subst hii
      refine ⟨hp, hT, ?_, fun j hj => ?_⟩
      · rw [Function.update_self]; exact fun h => by cases h
      · rw [Function.update_of_ne hj]; exact hnn j hj
    · refine ⟨hp, hT, ?_, fun j hj => ?_⟩
      · rw [Function.update_of_ne (Ne.symm hii)]; exact hne
      · by_cases hj' : j = i'
        · subst hj'; rw [Function.update_self]
          rcases hnn j hj with h | ⟨s', h, hs'⟩ <;> rw [hi] at h <;> cases h
          exact Or.inr ⟨_, rfl, le_trans hs' hrs⟩
        · rw [Function.update_of_ne hj']; exact hnn j hj
  | app => intro e; cases e
  | abs => intro e; cases e
  | pr => intro e; cases e
  | letbox => intro e; cases e

lemma Use.Add.le_of_nonneg {x y z : Use R} (h : Use.Add x y z) (hy : y.Nonneg) : Use.Le x z := by
  cases h with
  | noneLeft =>
    rcases hy with rfl | ⟨s, rfl, hs⟩
    · exact .none
    · exact .noneGrd hs
  | noneRight => exact Use.Le.refl _
  | grd a b =>
    rcases hy with h | ⟨s, h, hs⟩
    · cases h
    · cases h
      exact .grd (by simpa using PreorderedSemiring.add_mono (le_refl a) hs)

lemma Use.Add.lin_result {a b : Use R} (h : Use.Add a b .lin) (hb : b ≠ .none) : a = .none := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl hb | cases h

/-- The `η`-rule for `⊸`: a translated derivation of the body `t x` (with `x # t` used
linearly) of an `η`-redex comes from a translated derivation of `t`. -/
theorem LToP.eta_body {k n : ℕ} {Δ : Fin (n + 1) → LTy R .base} {u : Fin (n + 1) → Use R}
    {t₀ : LTm .base n} {B : LTy R .base} {pb : PTm R k (n + 1)}
    (h : LToP Δ u (.app t₀.shift (.var 0)) B pb) (hu : u 0 = .lin) :
    ∃ pt, pb = .app (pt.rename Fin.succ) (.var 0) ∧
      LToP (fun i => Δ i.succ) (fun i => u i.succ) t₀ (.lolli (Δ 0) B) pt := by
  obtain ⟨u₁, u₂, w, A, p₁, p₂, rfl, h₁, h₂, hadd, hS⟩ := h.inv_app
  obtain ⟨rfl, rfl, hne, hnn⟩ := h₂.inv_var
  have hw0 : w 0 = .lin := by have := hS 0; rw [hu] at this; exact this.lin_right
  have hu₁0 : u₁ 0 = .none := by
    have := hadd 0; rw [hw0] at this; exact this.lin_result hne
  obtain ⟨pt, rfl, hpt⟩ := h₁.unrename Fin.succ t₀ (Fin.succ_injective _) rfl (fun j hj => by
    induction j using Fin.cases with
    | zero => exact hu₁0
    | succ j => exact absurd rfl (hj j))
  refine ⟨pt, rfl, hpt.monoS (fun j => ?_)⟩
  exact ((hadd j.succ).le_of_nonneg (hnn j.succ (Fin.succ_ne_zero j))).toSLe.trans (hS j.succ)


/-! ## Equation preservation -/

/-- One parallel step of `≡_L` on Linear Base terms using the axioms enabled by `S` from left to
right, inside arbitrary contexts. -/
inductive LEqStep (S : LAxSel) : {n : ℕ} → LTm .base n → LTm .base n → Prop
  | ax {n : ℕ} {t t' : LTm .base n} : LAxF S t t' → LEqStep S t t'
  | refl {n : ℕ} (t : LTm .base n) : LEqStep S t t
  | app {n : ℕ} {t₁ t₁' t₂ t₂' : LTm .base n} :
      LEqStep S t₁ t₁' → LEqStep S t₂ t₂' → LEqStep S (.app t₁ t₂) (.app t₁' t₂')
  | lam {n : ℕ} {t t' : LTm .base (n + 1)} : LEqStep S t t' → LEqStep S (.lam t) (.lam t')
  | box {n : ℕ} {t t' : LTm .base n} : LEqStep S t t' → LEqStep S (.box t) (.box t')
  | letbox {n : ℕ} {t₁ t₁' : LTm .base n} {t₂ t₂' : LTm .base (n + 1)} :
      LEqStep S t₁ t₁' → LEqStep S t₂ t₂' → LEqStep S (.letbox t₁ t₂) (.letbox t₁' t₂')

/-- `t ≡_L t'` derivable using the axioms of `S` left to right (any number of times, in any
contexts). -/
abbrev LEqDir (S : LAxSel) {n : ℕ} : LTm .base n → LTm .base n → Prop :=
  Relation.ReflTransGen (LEqStep S)

/-- The theory `≡_L^{-η□}` of the paper, without the commuting conversions. -/
def LAxSel.polyPreserved : LAxSel := { etaBox := False, letComm := False }

/-- Equation preservation for one step. -/
theorem LToP.eqStep {S : LAxSel} (hS₁ : ¬ S.etaBox) (hS₂ : ¬ S.letComm)
    {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) {t' : LTm .base n}
    (he : LEqStep S t t') : ∃ p', LToP Γ u t' A p' ∧ PEq p p' := by
  induction h with
  | var Γ i =>
    cases he with
    | ax hax => cases hax
    | refl => exact ⟨_, .var Γ i, .refl _⟩
  | @abs k n Γ u b A B pb hb ih =>
    cases he with
    | ax hax =>
      cases hax with
      | eta _ t₀ =>
        obtain ⟨pt, rfl, hpt⟩ := hb.eta_body rfl
        exact ⟨pt, hpt, .eta pt⟩
    | refl => exact ⟨_, .abs hb, .refl _⟩
    | lam hb' =>
      obtain ⟨pb', hpb', heq⟩ := ih hb'
      exact ⟨_, .abs hpb', .lam heq⟩
  | app h₁ h₂ hadd ih₁ ih₂ =>
    cases he with
    | ax hax =>
      cases hax with
      | beta b a =>
        obtain ⟨pb, rfl, hb⟩ := h₁.inv_lam
        exact ⟨_, hb.subst1_lin h₂ hadd.comm, .beta _ _⟩
      | letCommOne he => exact (hS₂ he).elim
      | letCommTwo he => exact (hS₂ he).elim
    | refl => exact ⟨_, .app h₁ h₂ hadd, .refl _⟩
    | app he₁ he₂ =>
      obtain ⟨p₁', h₁', e₁⟩ := ih₁ he₁
      obtain ⟨p₂', h₂', e₂⟩ := ih₂ he₂
      exact ⟨_, .app h₁' h₂' hadd, .app e₁ e₂⟩
  | weak i _ hi ih =>
    obtain ⟨p', h', e⟩ := ih he
    exact ⟨p', .weak i h' hi, e⟩
  | der i _ hi ih =>
    obtain ⟨p', h', e⟩ := ih he
    exact ⟨p', .der i h' hi, e⟩
  | approx i _ hi hrs ih =>
    obtain ⟨p', h', e⟩ := ih he
    exact ⟨p', .approx i h' hi hrs, e⟩
  | pr r h hg ih =>
    cases he with
    | ax hax => cases hax
    | refl => exact ⟨_, .pr r h hg, .refl _⟩
    | box he' =>
      obtain ⟨q', hq', e⟩ := ih he'
      exact ⟨_, .pr r hq' hg, .tlam (.lam (.app (.refl _) (e.rename _)))⟩
  | @letbox k n Γ u₁ u₂ u t₁ t₂ r A B p₁ p₂ h₁ h₂ hadd ih₁ ih₂ =>
    cases he with
    | ax hax =>
      cases hax with
      | betaBox a b =>
        obtain ⟨ua, q, hg, hq, rfl, hle⟩ := h₁.inv_box
        obtain ⟨hadd', hle'⟩ := hadd.down hle
        exact ⟨_, (h₂.subst1_grd (hq.tsubst _) hg hadd').mono hle',
          (PSteps.betaBox_sim q B.toP p₂).toPEq⟩
      | etaBox he => exact (hS₁ he).elim
      | letCommBox he => exact (hS₂ he).elim
    | refl => exact ⟨_, .letbox h₁ h₂ hadd, .refl _⟩
    | letbox he₁ he₂ =>
      obtain ⟨p₁', h₁', e₁⟩ := ih₁ he₁
      obtain ⟨p₂', h₂', e₂⟩ := ih₂ he₂
      exact ⟨_, .letbox h₁' h₂' hadd, .app (.tapp _ e₁) (.lam e₂)⟩

/-- **Theorem 4.1 (equation preservation)** of the Linear Base → Graded Poly Base translation,
for the theory `≡_L^{-η□}` without commuting conversions used left to right: if `p = ⦇Π⦈` for a
derivation `Π` of `Γ ⊢ t : A` and `t ≡ t'`, then there is a derivation `Π'` of `Γ ⊢ t' : A`
with `⦇Π⦈ ≡_{G∀} ⦇Π'⦈`. -/
theorem LToP.eq_preserve {S : LAxSel} (hS₁ : ¬ S.etaBox) (hS₂ : ¬ S.letComm)
    {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t t' : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) (he : LEqDir S t t') :
    ∃ p', LToP Γ u t' A p' ∧ PEq p p' := by
  induction he with
  | refl => exact ⟨p, h, .refl _⟩
  | tail _ he ih =>
    obtain ⟨p₁, h₁, e₁⟩ := ih
    obtain ⟨p₂, h₂, e₂⟩ := h₁.eqStep hS₁ hS₂ he
    exact ⟨p₂, h₂, e₁.trans e₂⟩


end Coeffect
