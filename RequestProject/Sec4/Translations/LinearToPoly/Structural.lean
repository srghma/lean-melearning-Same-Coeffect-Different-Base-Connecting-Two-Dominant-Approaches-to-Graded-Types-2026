module

public import RequestProject.Sec4.Translations.LinearToPoly.Basic
public import RequestProject.Sec4.Poly.Subst
public import RequestProject.Sec4.Linear.UsageAlgebra

/-!
# Structural properties of the derivation-based translation LB → GPB

Properties of the relation `LToP Γ u t A p` ("`p` is the translation of a Linear Base derivation
of `Γ ⊢ t : A`") needed for operational correspondence:

* erasure to Linear Base typing (`LToP.typed_L`);
* closure under type substitution / renaming of the (irrelevant) type variables
  (`LToP.tsubst`, `LToP.trename`);
* closure under injective renamings of term variables (`LToP.rename`);
* admissibility of weakening and approximation in bulk (`LToP.mono`);
* inversion for abstractions and boxes (`LToP.inv_lam`, `LToP.inv_box`).
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u} [PreorderedSemiring R]

/-- Erasure: a translated derivation is in particular a Linear Base derivation. -/
theorem LToP.typed_L {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) : LTyped Γ u t A := by
  induction h with
  | var Γ i => exact .var Γ i
  | abs _ ih => exact .abs ih
  | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ hadd
  | weak i _ hi ih => exact .weak i ih hi
  | der i _ hi ih => exact .der i ih hi
  | approx i _ hi hrs ih => exact .approx i ih hi hrs
  | pr r _ hg ih => exact .pr r ih hg
  | letbox _ _ hadd ih₁ ih₂ => exact .letbox ih₁ ih₂ hadd

/-- The type variables of a translation are irrelevant: closure under type substitution. -/
theorem LToP.tsubst {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) {l : ℕ} (σ : Fin k → PTy R l) :
    LToP Γ u t A (p.tsubst σ) := by
  induction h generalizing l with
  | var Γ i => exact .var Γ i
  | abs _ ih => exact .abs (ih σ)
  | app _ _ hadd ih₁ ih₂ => exact .app (ih₁ σ) (ih₂ σ) hadd
  | weak i _ hi ih => exact .weak i (ih σ) hi
  | der i _ hi ih => exact .der i (ih σ) hi
  | approx i _ hi hrs ih => exact .approx i (ih σ) hi hrs
  | pr r _ hg ih =>
    simp only [PTm.tsubst, PTm.tsubst_rename]
    exact .pr r (ih (PTy.up σ)) hg
  | @letbox _ _ _ _ _ _ _ _ _ _ B _ _ _ _ _ ih₁ ih₂ =>
    simp only [PTm.tsubst, LTy.toP_subst]
    exact .letbox (ih₁ σ) (ih₂ σ) ‹_›

/-- Closure under renaming of type variables. -/
theorem LToP.trename {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) {l : ℕ} (θ : Fin k → Fin l) :
    LToP Γ u t A (p.trename θ) := by
  induction h generalizing l with
  | var Γ i => exact .var Γ i
  | abs _ ih => exact .abs (ih θ)
  | app _ _ hadd ih₁ ih₂ => exact .app (ih₁ θ) (ih₂ θ) hadd
  | weak i _ hi ih => exact .weak i (ih θ) hi
  | der i _ hi ih => exact .der i (ih θ) hi
  | approx i _ hi hrs ih => exact .approx i (ih θ) hi hrs
  | pr r _ hg ih =>
    simp only [PTm.trename, PTm.trename_rename]
    exact .pr r (ih (upRen θ)) hg
  | letbox _ _ hadd ih₁ ih₂ =>
    simp only [PTm.trename, LTy.toP_rename]
    exact .letbox (ih₁ θ) (ih₂ θ) hadd

/-- Closure under injective renamings of term variables (weakening and exchange). -/
theorem LToP.rename {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) {m : ℕ} (ρ : Fin n → Fin m)
    (hρ : Function.Injective ρ) (Γ' : Fin m → LTy R .base) (hΓ : ∀ i, Γ' (ρ i) = Γ i)
    (u' : Fin m → Use R) (hu : ∀ i, u' (ρ i) = u i)
    (hoff : ∀ j, (∀ i, ρ i ≠ j) → u' j = Use.none) :
    LToP Γ' u' (t.rename ρ) A (p.rename ρ) := by
  induction h generalizing m with
  | var Γ i =>
    have : u' = Use.only (ρ i) := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; simp only [Use.only, hρ.eq_iff]
      · rw [hoff j hj]; simp only [Use.only]; rw [if_neg (fun e => hj i e.symm)]
    rw [this, ← hΓ i]; exact LToP.var Γ' (ρ i)
  | abs _ ih =>
    refine LToP.abs (ih (upRen ρ) (upRen_injective hρ) _ ?_ _ ?_ ?_)
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hu]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j => exact hoff j (fun i e => hj i.succ (by simp [e]))
  | app _ _ hadd ih₁ ih₂ =>
    exact LToP.app (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₂ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj)) (hadd.pushAlong hρ hu hoff)
  | weak i _ hi ih =>
    obtain ⟨h1, h2, h3⟩ := update_preimage hρ i _ _ hu hoff hi
    rw [← h3]
    exact LToP.weak (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2) (Function.update_self _ _ _)
  | der i _ hi ih =>
    obtain ⟨h1, h2, h3⟩ := update_preimage hρ i _ _ hu hoff hi
    rw [← h3]
    exact LToP.der (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2) (Function.update_self _ _ _)
  | approx i _ hi hrs ih =>
    obtain ⟨h1, h2, h3⟩ := update_preimage hρ i _ _ hu hoff hi
    rw [← h3]
    exact LToP.approx (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2) (Function.update_self _ _ _) hrs
  | @pr _ _ Γ u t A p r _ hg ih =>
    have e : u' = smulCtx r (pushAlong ρ Use.none u) := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; simp only [smulCtx, pushAlong_apply hρ]
      · rw [hoff j hj]; simp only [smulCtx, pushAlong_off _ _ j hj, Use.smul]
    rw [e]
    have ep : (PTm.tlam (.lam (.app (.var 0) (p.rename Fin.succ))) : PTm R _ _).rename ρ =
        .tlam (.lam (.app (.var 0) ((p.rename ρ).rename Fin.succ))) := by
      simp only [PTm.rename, PTm.rename_rename]; rfl
    rw [ep]
    refine LToP.pr r (ih ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj)) ?_
    intro j
    rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
    · rw [pushAlong_apply hρ]; exact hg k
    · rw [pushAlong_off _ _ j hj]; exact fun h => by cases h
  | letbox _ _ hadd ih₁ ih₂ =>
    refine LToP.letbox (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₂ (upRen ρ) (upRen_injective hρ) _ ?_ _ ?_ ?_) (hadd.pushAlong hρ hu hoff)
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [pushAlong_apply hρ]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j =>
        simp only [scons_succ]
        exact pushAlong_off _ _ j (fun i e => hj i.succ (by simp [e]))

/-- Weakening by a fresh innermost variable. -/
lemma LToP.weaken1 {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) (C : LTy R .base) :
    LToP (C .: Γ) (Use.none .: u) t.shift A (p.rename Fin.succ) :=
  h.rename Fin.succ (Fin.succ_injective _) _ (fun _ => rfl) _ (fun _ => rfl)
    (fun j hj => by
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact absurd rfl (hj j))

/-- One step of weakening/approximation at a single position. -/
lemma LToP.mono1 {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) (i : Fin n) {x : Use R}
    (hx : Use.Le (u i) x) : LToP Γ (Function.update u i x) t A p := by
  generalize hy : u i = y at hx
  cases hx with
  | none => rw [← hy, update_eq_self']; exact h
  | lin => rw [← hy, update_eq_self']; exact h
  | grd hab => exact .approx i h hy hab
  | noneGrd hb =>
    have h1 := LToP.weak i h hy
    have h2 := LToP.approx i h1 (Function.update_self _ _ _) hb
    rwa [update_idem'] at h2

/-- Admissibility of weakening and approximation in bulk. -/
theorem LToP.mono {k n : ℕ} {Γ : Fin n → LTy R .base} {u u' : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) (hle : UsageLe u u') :
    LToP Γ u' t A p := by
  suffices H : ∀ (k : ℕ) (u' : Fin n → Use R), UsageLe u u' →
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
          · subst hja; rw [Function.update_self]; exact Use.Le.refl _
          · rw [Function.update_of_ne hja]; exact hle' j
        · intro j hj
          by_cases hja : j = a
          · subst hja; rw [Function.update_self]
          · rw [Function.update_of_ne hja]
            have : j.val ≠ k := fun e => hja (Fin.ext e)
            exact hS j (by omega)
      have h2 := h1.mono1 a (x := u' a) (by rw [Function.update_self]; exact hle' a)
      rwa [update_idem', update_eq_self'] at h2
    · apply ih u' hle'
      intro j hj
      exact absurd j.isLt (by omega)

lemma scons_update {α : Type*} {n : ℕ} (a : α) (f : Fin n → α) (i : Fin n) (x : α) :
    (a .: Function.update f i x) = Function.update (a .: f) i.succ x := by
  funext j
  induction j using Fin.cases with
  | zero => rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]; rfl
  | succ j =>
    by_cases h : j = i
    · subst h; rw [Function.update_self]; simp only [scons_succ, Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Fin.succ_injective _ e))]
      simp only [scons_succ]; rw [Function.update_of_ne h]

/-- Inversion for abstraction: the structural rules can be pushed into the body. -/
theorem LToP.inv_lam {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R}
    {b : LTm .base (n + 1)} {A B : LTy R .base} {p : PTm R k n}
    (h : LToP Γ u (.lam b) (.lolli A B) p) :
    ∃ pb, p = .lam pb ∧ LToP (A .: Γ) (Use.lin .: u) b B pb := by
  suffices H : ∀ (t : LTm .base n) (T : LTy R .base), LToP Γ u t T p → t = .lam b →
      T = .lolli A B → ∃ pb, p = .lam pb ∧ LToP (A .: Γ) (Use.lin .: u) b B pb from
    H _ _ h rfl rfl
  clear h
  intro t T h
  induction h with
  | var => intro e; cases e
  | abs h _ =>
    intro et eT
    cases et; cases eT
    exact ⟨_, rfl, h⟩
  | app => intro e; cases e
  | weak i _ hi ih =>
    intro et eT
    obtain ⟨pb, hp, hb⟩ := ih et eT
    refine ⟨pb, hp, ?_⟩
    rw [scons_update]; exact .weak i.succ hb hi
  | der i _ hi ih =>
    intro et eT
    obtain ⟨pb, hp, hb⟩ := ih et eT
    refine ⟨pb, hp, ?_⟩
    rw [scons_update]; exact .der i.succ hb hi
  | approx i _ hi hrs ih =>
    intro et eT
    obtain ⟨pb, hp, hb⟩ := ih et eT
    refine ⟨pb, hp, ?_⟩
    rw [scons_update]; exact .approx i.succ hb hi hrs
  | pr => intro e; cases e
  | letbox => intro e; cases e

lemma Use.Le.none_right {a : Use R} (h : Use.Le a Use.none) : a = Use.none := by
  cases h; rfl

lemma Use.Le.lin_right {a : Use R} (h : Use.Le a Use.lin) : a = Use.lin := by
  cases h; rfl

/-- Inversion for boxes: a translated derivation of `[a] : □_r A` is a promotion followed by
weakenings and approximations. -/
theorem LToP.inv_box {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R}
    {a : LTm .base n} {r : R} {A : LTy R .base} {p : PTm R k n}
    (h : LToP Γ u (.box a) (.box r A) p) :
    ∃ (ua : Fin n → Use R) (q : PTm R (k + 1) n), Graded ua ∧ LToP Γ ua a A q ∧
      p = .tlam (.lam (.app (.var 0) (q.rename Fin.succ))) ∧ UsageLe (smulCtx r ua) u := by
  suffices H : ∀ (t : LTm .base n) (T : LTy R .base), LToP Γ u t T p → t = .box a →
      T = .box r A → ∃ (ua : Fin n → Use R) (q : PTm R (k + 1) n), Graded ua ∧
        LToP Γ ua a A q ∧ p = .tlam (.lam (.app (.var 0) (q.rename Fin.succ))) ∧
        UsageLe (smulCtx r ua) u from
    H _ _ h rfl rfl
  clear h
  intro t T h
  induction h with
  | var => intro e; cases e
  | abs => intro e; cases e
  | app => intro e; cases e
  | weak i _ hi ih =>
    intro et eT
    obtain ⟨ua, q, hg, hq, hp, hle⟩ := ih et eT
    refine ⟨ua, q, hg, hq, hp, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      have := (hle j); rw [hi] at this
      rw [this.none_right]; exact .noneGrd le_rfl
    · rw [Function.update_of_ne hj]; exact hle j
  | der i _ hi ih =>
    intro et eT
    obtain ⟨ua, q, hg, hq, hp, hle⟩ := ih et eT
    exfalso
    have := hle i; rw [hi] at this
    have h2 := this.lin_right
    simp only [smulCtx] at h2
    cases e : ua i with
    | none => rw [e] at h2; cases h2
    | lin => exact hg i e
    | grd s => rw [e] at h2; cases h2
  | approx i _ hi hrs ih =>
    intro et eT
    obtain ⟨ua, q, hg, hq, hp, hle⟩ := ih et eT
    refine ⟨ua, q, hg, hq, hp, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      have := (hle j); rw [hi] at this
      exact this.trans (.grd hrs)
    · rw [Function.update_of_ne hj]; exact hle j
  | pr r' h hg =>
    intro et eT
    cases et; cases eT
    exact ⟨_, _, hg, h, rfl, UsageLe.refl _⟩
  | letbox => intro e; cases e

end Coeffect
