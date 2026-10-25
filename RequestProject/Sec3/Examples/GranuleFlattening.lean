module

public import RequestProject.Sec3.Examples.BoxCurry
public import RequestProject.Sec2.Graded.Semantics

/-!
# Granule's coeffect flattening as a *graded* `let [x] = …` rule

Granule's checker types a box pattern that sits under an enclosing grade (a graded arrow
`□_x A %y → B`, or an outer box) by *flattening* the two grades: the bound variable receives
the grade `y · x` (outer times inner, `flattenCoeffects`/`flattenable` in Granule's checker).

In terms of the core calculus this is the **graded** elimination rule for boxes

```
Δ₁ ⊢ t₁ : □_r A      Δ₂, x :_(q·r) A ⊢ t₂ : B
───────────────────────────────────────────────  (letbox_q)
        q · Δ₁ + Δ₂ ⊢ let [x] = t₁ in t₂ : B
```

which scales the scrutinee by an arbitrary `q`, exactly like the product and sum eliminations
of Graded Modal Core already do. The paper's Graded Modal Base uses the special case `q = 1`.

This file defines `GTypedQ`, the Graded Modal Base typing judgment with `letbox_q` in place of
the paper's `letbox` (the other rules are unchanged), and proves:

* `GTyped.toQ`: every derivation of the paper's GMB is a `GTypedQ` derivation, so the new
  system types at least the same terms (and, by the next two items, strictly more);
* `gradedToModal_typedQ`: with `letbox_q`, `λf. λb. let [z] = b in f z` has type
  `(C →^(y·x) D) →^1 (□_x C →^y D)` for **all** grades `x, y` — the same term which the paper's
  rule cannot type for `x = 2, y = 3` (`BoxCurry.gradedToModal_untypable_two_three`);
* `flatten_typedQ`: `λy. let [z] = y in let [x] = z in [x] : □_q □_r A →^1 □_(q·r) A`, while
  over `ℕ` the paper's rules give no typing to this term at `q = 2, r = 3`
  (`flatten_untypable_two_three`);
* `GTypedQ.subst`: the graded substitution lemma for `GTypedQ`;
* `GTypedQ.preservation`: subject reduction for every reduction step `GStep` — so the
  flattening rule is **sound** with respect to the operational semantics.
-/

@[expose] public section

namespace Coeffect

namespace GranuleFlat

universe u

variable {R : Type u} [PreorderedSemiring R] {F : GLevel}

/-- Graded Modal Base typing with Granule's flattening (graded) box elimination `letbox_q`. -/
inductive GTypedQ : {n : ℕ} → (Fin n → GTy R F) → (Fin n → R) → GTm F n → GTy R F → Prop
  | var {n : ℕ} (Γ : Fin n → GTy R F) (i : Fin n) : GTypedQ Γ (Pi.single i 1) (.var i) (Γ i)
  | abs {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F (n + 1)} {r : R}
      {A B : GTy R F} :
      GTypedQ (A .: Γ) (r .: δ) t B → GTypedQ Γ δ (.lam t) (.fn r A B)
  | app {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ t₂ : GTm F n} {r : R}
      {A B : GTy R F} :
      GTypedQ Γ δ₁ t₁ (.fn r A B) → GTypedQ Γ δ₂ t₂ A → GTypedQ Γ (δ₁ + r • δ₂) (.app t₁ t₂) B
  | approx {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
      (i : Fin n) {s : R} :
      GTypedQ Γ δ t A → δ i ≤ s → GTypedQ Γ (Function.update δ i s) t A
  | pr {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
      (h : F.Modal) (r : R) :
      GTypedQ Γ δ t A → GTypedQ Γ (r • δ) (.box h t) (.box h r A)
  /-- Granule's flattening box elimination: the scrutinee is used `q` times, and the bound
  variable gets the flattened grade `q · r`. -/
  | letboxq {n : ℕ} {Γ : Fin n → GTy R F} {δ₁ δ₂ : Fin n → R} {t₁ : GTm F n}
      {t₂ : GTm F (n + 1)} {r : R} {A B : GTy R F} (h : F.Modal) (q : R) :
      GTypedQ Γ δ₁ t₁ (.box h r A) → GTypedQ (A .: Γ) ((q * r) .: δ₂) t₂ B →
      GTypedQ Γ (q • δ₁ + δ₂) (.letbox h t₁ t₂) B

namespace GTypedQ

variable {n : ℕ} {Γ : Fin n → GTy R F} {δ δ' : Fin n → R} {t : GTm F n} {A : GTy R F}

lemma cast (h : GTypedQ Γ δ t A) (e : δ = δ') : GTypedQ Γ δ' t A := e ▸ h

/-- The paper's `letbox` is the instance `q = 1` of `letbox_q`. -/
lemma letbox {δ₁ δ₂ : Fin n → R} {t₁ : GTm F n} {t₂ : GTm F (n + 1)} {r : R} {B : GTy R F}
    (h : F.Modal) (h₁ : GTypedQ Γ δ₁ t₁ (.box h r A)) (h₂ : GTypedQ (A .: Γ) (r .: δ₂) t₂ B) :
    GTypedQ Γ (δ₁ + δ₂) (.letbox h t₁ t₂) B :=
  (letboxq h 1 h₁ (by simpa using h₂)).cast (by simp)

end GTypedQ

/-- Every derivation of the paper's Graded Modal Base (no product/sum constructs) is a
derivation with Granule's flattening rule. -/
theorem GTyped.toQ {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
    (hF : ¬ F.Core) (h : GTyped Γ δ t A) : GTypedQ Γ δ t A := by
  induction h with
  | var Γ i => exact .var Γ i
  | abs _ ih => exact .abs ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | approx i _ hi ih => exact .approx i ih hi
  | pr h r _ ih => exact .pr h r ih
  | letbox h _ _ ih₁ ih₂ => exact GTypedQ.letbox h ih₁ ih₂
  | pair h => exact absurd h hF
  | letpair h => exact absurd h hF
  | unit h => exact absurd h hF
  | letunit h => exact absurd h hF
  | inl h => exact absurd h hF
  | inr h => exact absurd h hF
  | case h => exact absurd h hF

local notation "M" => GLevel.modal

/-- With Granule's flattening rule, `λf. λb. let [z] = b in f z` has type
`(C →^(y·x) D) →^1 (□_x C →^y D)` for **all** grades `x` and `y` (no side conditions). -/
theorem gradedToModal_typedQ (x y : R) (C D : GTy R M) :
    GTypedQ (Fin.elim0 : Fin 0 → GTy R M) Fin.elim0 BoxCurry.gradedToModal
      (.fn 1 (.fn (y * x) C D) (.fn y (.box trivial x C) D)) := by
  refine GTypedQ.abs (GTypedQ.abs ?_)
  set Γ : Fin 2 → GTy R M := GTy.box trivial x C .: GTy.fn (y * x) C D .: Fin.elim0
  have hb : GTypedQ Γ (Pi.single 0 1) (.var 0) (GTy.box trivial x C) := GTypedQ.var Γ 0
  have hf : GTypedQ (C .: Γ) (Pi.single 2 1) (.var 2) (GTy.fn (y * x) C D) := GTypedQ.var _ 2
  have hz : GTypedQ (C .: Γ) (Pi.single 0 1) (.var 0) C := GTypedQ.var _ 0
  have hbody : GTypedQ (C .: Γ) ((y * x) .: (Pi.single 1 1 : Fin 2 → R))
      (.app (.var 2) (.var 0)) D := by
    refine (GTypedQ.app hf hz).cast ?_
    funext i
    fin_cases i <;> simp [scons] <;> rfl
  refine (GTypedQ.letboxq (F := M) trivial y hb hbody).cast ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [Fin.fin_one_eq_zero j]; simp

/-- `λy. let [z] = y in let [x] = z in [x]` (flattening of nested boxes). -/
def flatten : GTm M 0 :=
  .lam (.letbox trivial (.var 0) (.letbox trivial (.var 0) (.box trivial (.var 0))))

/-- With Granule's flattening rule, `⊢ flatten : □_q □_r A →^1 □_(q·r) A`. -/
theorem flatten_typedQ (q r : R) (A : GTy R M) :
    GTypedQ (Fin.elim0 : Fin 0 → GTy R M) Fin.elim0 flatten
      (.fn 1 (.box trivial q (.box trivial r A)) (.box trivial (q * r) A)) := by
  refine GTypedQ.abs ?_
  set Γ : Fin 1 → GTy R M := GTy.box (F := M) trivial q (.box trivial r A) .: Fin.elim0
  have hy : GTypedQ Γ (Pi.single 0 1) (.var 0) (GTy.box (F := M) trivial q (.box trivial r A)) :=
    GTypedQ.var Γ 0
  have hz : GTypedQ (GTy.box (F := M) trivial r A .: Γ) (Pi.single 0 1) (.var 0)
      (GTy.box (F := M) trivial r A) := GTypedQ.var _ 0
  have hx : GTypedQ (A .: GTy.box (F := M) trivial r A .: Γ) (Pi.single 0 1) (.var 0) A :=
    GTypedQ.var _ 0
  have hbox := GTypedQ.pr (F := M) trivial (q * r) hx
  have hinner : GTypedQ (GTy.box (F := M) trivial r A .: Γ) (q .: (0 : Fin 1 → R))
      (.letbox trivial (.var 0) (.box trivial (.var 0))) (.box trivial (q * r) A) := by
    refine (GTypedQ.letboxq (F := M) trivial q hz (δ₂ := 0) (hbox.cast ?_)).cast ?_
    · funext i; refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.succ_ne_zero]
    · funext i; refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.succ_ne_zero]
  refine (GTypedQ.letboxq (F := M) trivial 1 hy (by simpa using hinner)).cast ?_
  funext i
  rw [Fin.fin_one_eq_zero i]; simp

/-! ## The paper's rule cannot flatten `□_2 □_3 A` into `□_6 A` (over `ℕ`) -/

/-- Inversion for `[t]` in the paper's system, up to approximation. -/
lemma box_inv_paper {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {h : F.Modal} {t : GTm F n}
    {T : GTy R F} (hty : GTyped Γ δ (.box h t) T) :
    ∃ (r : R) (A : GTy R F) (δ' : Fin n → R), T = .box h r A ∧ GTyped Γ δ' t A ∧ r • δ' ≤ δ := by
  generalize ht : (GTm.box h t : GTm F n) = s at hty
  induction hty with
  | pr _ r h₁ => cases ht; exact ⟨_, _, _, rfl, h₁, le_rfl⟩
  | @approx _ _ δ _ _ k s _ hk ih =>
    obtain ⟨r, A, δ', e, h1, hle⟩ := ih ht
    refine ⟨r, A, δ', e, h1, le_trans hle fun j => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using hk
    · simp [Function.update_of_ne hj]
  | _ => cases ht

/-- Over `ℕ`, the paper's Graded Modal Base gives `flatten` no type `□_2 □_3 A →^s □_6 A`, in any
context and at any grade `s`: the inner `let` binds `x` at grade `3`, but `[x] : □_6 A` needs it
at grade `6`. -/
theorem flatten_untypable_two_three {n : ℕ} (Γ : Fin n → GTy ℕ M) (δ : Fin n → ℕ) (s : ℕ)
    (A : GTy ℕ M) :
    ¬ GTyped Γ δ (flatten.rename Fin.elim0)
      (.fn s (.box trivial 2 (.box trivial 3 A)) (.box trivial 6 A)) := by
  intro hty
  have e : (flatten.rename Fin.elim0 : GTm M n) =
      .lam (.letbox trivial (.var 0) (.letbox trivial (.var 0) (.box trivial (.var 0)))) := rfl
  rw [e] at hty
  obtain ⟨r₁, A₁, B₁, δ₁, e₁, h₁⟩ := GExample.lam_inv hty
  injection e₁ with er₁ eA₁ eB₁
  subst er₁ eA₁ eB₁
  obtain ⟨r₂, A₂, δ₂, δ₃, hy, hbody, -⟩ := BoxCurry.letbox_inv h₁
  obtain ⟨ey, -⟩ := GExample.var_inv hy
  have ey' : (GTy.box (F := M) trivial r₂ A₂ : GTy ℕ M) = GTy.box (F := M) trivial 2 (GTy.box (F := M) trivial 3 A) := ey
  injection ey' with er₂ eA₂
  subst er₂ eA₂
  obtain ⟨r₃, A₃, δ₄, δ₅, hz, hinner, -⟩ := BoxCurry.letbox_inv hbody
  obtain ⟨ez, -⟩ := GExample.var_inv hz
  have ez' : (GTy.box (F := M) trivial r₃ A₃ : GTy ℕ M) = GTy.box (F := M) trivial 3 A := ez
  injection ez' with er₃ eA₃
  subst er₃ eA₃
  obtain ⟨r₄, A₄, δ₆, e₄, hx, hle⟩ := box_inv_paper hinner
  have e₄' : (GTy.box (F := M) trivial 6 A₃ : GTy ℕ M) = GTy.box (F := M) trivial r₄ A₄ := e₄
  injection e₄' with er₄ _
  subst er₄
  obtain ⟨-, hx1⟩ := GExample.var_inv hx
  have a1 : 1 ≤ δ₆ 0 := by simpa using hx1 0
  have a2 : 6 * δ₆ 0 ≤ 3 := by simpa using hle 0
  omega

/-! ## Order lemmas for grade vectors -/

section Order

variable {m : ℕ}

lemma smul_le_smul_vec {a b : R} (hab : a ≤ b) (v : Fin m → R) : a • v ≤ b • v :=
  fun _ => PreorderedSemiring.mul_mono hab le_rfl

lemma smul_vec_le_smul {v w : Fin m → R} (a : R) (hvw : v ≤ w) : a • v ≤ a • w :=
  fun j => PreorderedSemiring.mul_mono le_rfl (hvw j)

lemma add_le_add_vec {v w v' w' : Fin m → R} (h₁ : v ≤ v') (h₂ : w ≤ w') : v + w ≤ v' + w' :=
  fun j => PreorderedSemiring.add_mono (h₁ j) (h₂ j)

lemma sum_le_sum_vec {ι : Type*} (S : Finset ι) {f g : ι → Fin m → R} (hfg : ∀ i, f i ≤ g i) :
    ∑ i ∈ S, f i ≤ ∑ i ∈ S, g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact add_le_add_vec (hfg a) ih

lemma sum_single_smul {n : ℕ} (δ : Fin n → R) : ∑ i, δ i • (Pi.single i 1 : Fin n → R) = δ := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

lemma sum_scons_up {n : ℕ} (r : R) (δ : Fin n → R) (Δ : Fin n → Fin m → R) :
    ∑ j, (r .: δ) j • ((Pi.single 0 1 : Fin (m + 1) → R) .: fun i => (0 : R) .: Δ i) j =
      r .: ∑ i, δ i • Δ i := by
  rw [Fin.sum_univ_succ]
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Fin.succ_ne_zero]

end Order

/-! ## Structural properties of `GTypedQ` -/

namespace GTypedQ

/-- Approximation on all variables at once. -/
theorem mono {n : ℕ} {Γ : Fin n → GTy R F} {δ δ' : Fin n → R} {t : GTm F n} {A : GTy R F}
    (h : GTypedQ Γ δ t A) (hle : δ ≤ δ') : GTypedQ Γ δ' t A := by
  classical
  have key : ∀ S : Finset (Fin n), GTypedQ Γ (fun j => if j ∈ S then δ' j else δ j) t A := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using h
    | insert a S ha ih =>
      have := GTypedQ.approx a ih (s := δ' a) (by simpa [ha] using hle a)
      refine this.cast ?_
      funext j
      by_cases hj : j = a
      · subst hj; simp
      · simp [hj]
  simpa using key Finset.univ

/-- Typing is preserved by injective renamings (weakening and exchange). -/
theorem rename {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
    (h : GTypedQ Γ δ t A) {m : ℕ} (ρ : Fin n → Fin m) (hρ : Function.Injective ρ)
    (Γ' : Fin m → GTy R F) (hΓ : ∀ i, Γ' (ρ i) = Γ i) (δ' : Fin m → R)
    (hu : ∀ i, δ' (ρ i) = δ i) (hoff : ∀ j, (∀ i, ρ i ≠ j) → δ' j = 0) :
    GTypedQ Γ' δ' (t.rename ρ) A := by
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
    rw [this, ← hΓ i]; exact GTypedQ.var Γ' (ρ i)
  | @abs _ _ _ _ r A _ _ ih =>
    refine GTypedQ.abs (ih (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ (r .: δ') ?_ ?_ ?_)
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
    exact GTypedQ.app (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
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
      simp only [δ'', update_idem']
      have := hu i; rw [Function.update_self] at this
      rw [← this, update_eq_self']
    rw [← h3]
    exact GTypedQ.approx (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2 hpa) (by simpa [δ''] using hi)
  | @pr _ _ δ _ _ h r _ ih =>
    have e : δ' = r • pushAlong ρ 0 δ := by
      rw [← pushAlong_zero_smul hρ]
      funext j
      rcases range_or_off ρ j with ⟨i, rfl⟩ | hj
      · rw [hu, pushAlong_apply hρ]
      · rw [hoff j hj, pushAlong_off _ _ j hj]
    rw [e]; exact GTypedQ.pr h r (ih ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
  | @letboxq _ _ δ₁ δ₂ _ _ r A _ h q _ _ ih₁ ih₂ =>
    rw [pushAlong_zero_add hρ _ _ hu hoff, pushAlong_zero_smul hρ]
    refine GTypedQ.letboxq h q (ih₁ ρ hρ Γ' hΓ _ (hpa _).1 (hpa _).2 hpa)
      (ih₂ (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ ((q * r) .: pushAlong ρ 0 δ₂) ?_ ?_ ?_)
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

/-- Weakening by one fresh variable (of grade `0`) at index `0`. -/
lemma shift {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
    (h : GTypedQ Γ δ t A) (B : GTy R F) : GTypedQ (B .: Γ) ((0 : R) .: δ) t.shift A :=
  h.rename Fin.succ (Fin.succ_injective _) _ (fun _ => rfl) _ (fun _ => rfl) (fun j hj => by
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact absurd rfl (hj j))

/-- Lifting a well-typed substitution under a binder. -/
lemma up_typed {n m : ℕ} {Γ : Fin n → GTy R F} {Γ' : Fin m → GTy R F} {σ : Fin n → GTm F m}
    {Δ : Fin n → Fin m → R} (hσ : ∀ i, GTypedQ Γ' (Δ i) (σ i) (Γ i)) (A : GTy R F) :
    ∀ i, GTypedQ (A .: Γ') (((Pi.single 0 1 : Fin (m + 1) → R) .: fun i => (0 : R) .: Δ i) i)
      (GTm.upSub σ i) ((A .: Γ) i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact GTypedQ.var (A .: Γ') 0
  · exact (hσ i).shift A

/-- The graded substitution lemma: substituting, for each variable `i` of grade `δ i`, a term
typed with grades `Δ i` gives grades `∑ i, δ i • Δ i`. -/
theorem subst {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
    (h : GTypedQ Γ δ t A) {m : ℕ} (σ : Fin n → GTm F m) (Γ' : Fin m → GTy R F)
    (Δ : Fin n → Fin m → R) (hσ : ∀ i, GTypedQ Γ' (Δ i) (σ i) (Γ i)) :
    GTypedQ Γ' (∑ i, δ i • Δ i) (t.subst σ) A := by
  induction h generalizing m with
  | var Γ i =>
    have e : ∑ j, (Pi.single i (1 : R) : Fin _ → R) j • Δ j = Δ i := by
      rw [Finset.sum_eq_single i] <;> simp_all
    rw [e]; exact hσ i
  | @abs _ _ δ _ r A _ _ ih =>
    have := ih (GTm.upSub σ) (A .: Γ') _ (up_typed hσ A)
    rw [sum_scons_up] at this
    exact GTypedQ.abs this
  | @app _ _ δ₁ δ₂ _ _ r _ _ _ _ ih₁ ih₂ =>
    refine (GTypedQ.app (ih₁ σ Γ' Δ hσ) (ih₂ σ Γ' Δ hσ)).cast ?_
    simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  | @approx _ _ δ _ _ i s _ hi ih =>
    refine (ih σ Γ' Δ hσ).mono (sum_le_sum_vec _ fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa using smul_le_smul_vec hi (Δ j)
    · simp [Function.update_of_ne hj]
  | @pr _ _ δ _ _ h r _ ih =>
    refine (GTypedQ.pr h r (ih σ Γ' Δ hσ)).cast ?_
    simp [mul_smul, Finset.smul_sum]
  | @letboxq _ _ δ₁ δ₂ _ _ r A _ h q _ _ ih₁ ih₂ =>
    have h₂ := ih₂ (GTm.upSub σ) (A .: Γ') _ (up_typed hσ A)
    rw [sum_scons_up] at h₂
    refine (GTypedQ.letboxq h q (ih₁ σ Γ' Δ hσ) h₂).cast ?_
    simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

/-- Single substitution `[s/x] t`. -/
theorem subst1 {n : ℕ} {Γ : Fin n → GTy R F} {δ δs : Fin n → R} {t : GTm F (n + 1)}
    {s : GTm F n} {A B : GTy R F} {r : R} (ht : GTypedQ (A .: Γ) (r .: δ) t B)
    (hs : GTypedQ Γ δs s A) : GTypedQ Γ (r • δs + δ) (t.subst1 s) B := by
  have := ht.subst (s .: GTm.var) Γ (δs .: fun i => Pi.single i 1)
    (fun i => Fin.cases hs (fun i => GTypedQ.var Γ i) i)
  refine this.cast ?_
  rw [Fin.sum_univ_succ]
  simp [sum_single_smul]

/-! ## Inversion lemmas -/

section Inversion

variable {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R}

private lemma update_ge {δ : Fin n → R} {k : Fin n} {s : R} (hk : δ k ≤ s) :
    δ ≤ Function.update δ k s := fun j => by
  by_cases hj : j = k
  · subst hj; simpa using hk
  · simp [Function.update_of_ne hj]

lemma lam_inv {t : GTm F (n + 1)} {T : GTy R F} (h : GTypedQ Γ δ (.lam t) T) :
    ∃ (r : R) (A B : GTy R F) (δ' : Fin n → R), T = .fn r A B ∧
      GTypedQ (A .: Γ) (r .: δ') t B ∧ δ' ≤ δ := by
  generalize ht : (GTm.lam t : GTm F n) = s at h
  induction h with
  | abs h => cases ht; exact ⟨_, _, _, _, rfl, h, le_rfl⟩
  | approx _ _ hk ih =>
    obtain ⟨r, A, B, δ', e, h1, hle⟩ := ih ht
    exact ⟨r, A, B, δ', e, h1, le_trans hle (update_ge hk)⟩
  | _ => cases ht

lemma app_inv {t₁ t₂ : GTm F n} {B : GTy R F} (h : GTypedQ Γ δ (.app t₁ t₂) B) :
    ∃ (r : R) (A : GTy R F) (δ₁ δ₂ : Fin n → R), GTypedQ Γ δ₁ t₁ (.fn r A B) ∧
      GTypedQ Γ δ₂ t₂ A ∧ δ₁ + r • δ₂ ≤ δ := by
  generalize ht : (GTm.app t₁ t₂ : GTm F n) = s at h
  induction h with
  | app h₁ h₂ => cases ht; exact ⟨_, _, _, _, h₁, h₂, le_rfl⟩
  | approx _ _ hk ih =>
    obtain ⟨r, A, δ₁, δ₂, h1, h2, hle⟩ := ih ht
    exact ⟨r, A, δ₁, δ₂, h1, h2, le_trans hle (update_ge hk)⟩
  | _ => cases ht

lemma box_inv {h : F.Modal} {t : GTm F n} {T : GTy R F} (hty : GTypedQ Γ δ (.box h t) T) :
    ∃ (r : R) (A : GTy R F) (δ' : Fin n → R), T = .box h r A ∧ GTypedQ Γ δ' t A ∧
      r • δ' ≤ δ := by
  generalize ht : (GTm.box h t : GTm F n) = s at hty
  induction hty with
  | pr _ r h₁ => cases ht; exact ⟨_, _, _, rfl, h₁, le_rfl⟩
  | approx _ _ hk ih =>
    obtain ⟨r, A, δ', e, h1, hle⟩ := ih ht
    exact ⟨r, A, δ', e, h1, le_trans hle (update_ge hk)⟩
  | _ => cases ht

lemma letbox_inv {h : F.Modal} {t₁ : GTm F n} {t₂ : GTm F (n + 1)} {B : GTy R F}
    (hty : GTypedQ Γ δ (.letbox h t₁ t₂) B) :
    ∃ (q r : R) (A : GTy R F) (δ₁ δ₂ : Fin n → R), GTypedQ Γ δ₁ t₁ (.box h r A) ∧
      GTypedQ (A .: Γ) ((q * r) .: δ₂) t₂ B ∧ q • δ₁ + δ₂ ≤ δ := by
  generalize ht : (GTm.letbox h t₁ t₂ : GTm F n) = s at hty
  induction hty with
  | letboxq _ q h₁ h₂ => cases ht; exact ⟨q, _, _, _, _, h₁, h₂, le_rfl⟩
  | approx _ _ hk ih =>
    obtain ⟨q, r, A, δ₁, δ₂, h1, h2, hle⟩ := ih ht
    exact ⟨q, r, A, δ₁, δ₂, h1, h2, le_trans hle (update_ge hk)⟩
  | _ => cases ht

lemma no_letpair {hc : F.Core} {t₁ : GTm F n} {t₂ : GTm F (n + 2)} {B : GTy R F}
    (hty : GTypedQ Γ δ (.letpair hc t₁ t₂) B) : False := by
  generalize ht : (GTm.letpair hc t₁ t₂ : GTm F n) = s at hty
  induction hty with
  | approx _ _ _ ih => exact ih ht
  | _ => cases ht

lemma no_letunit {hc : F.Core} {t₁ t₂ : GTm F n} {B : GTy R F}
    (hty : GTypedQ Γ δ (.letunit hc t₁ t₂) B) : False := by
  generalize ht : (GTm.letunit hc t₁ t₂ : GTm F n) = s at hty
  induction hty with
  | approx _ _ _ ih => exact ih ht
  | _ => cases ht

lemma no_case {hc : F.Core} {t : GTm F n} {t₁ t₂ : GTm F (n + 1)} {B : GTy R F}
    (hty : GTypedQ Γ δ (.case hc t t₁ t₂) B) : False := by
  generalize ht : (GTm.case hc t t₁ t₂ : GTm F n) = s at hty
  induction hty with
  | approx _ _ _ ih => exact ih ht
  | _ => cases ht

end Inversion

/-- **Subject reduction** for Graded Modal Base with Granule's flattening rule: every reduction
step (call-by-name, or also under `λ`) preserves the type and the grades. In particular the
β-rule `let [x] = [s] in u ⇝ u[s/x]` is sound for `letbox_q`: the scrutinee `[s]` costs
`q · r · Δ_s`, which is exactly what the `q · r` uses of `x` in `u` consume. -/
theorem preservation {b : Prop} {n : ℕ} {t t' : GTm F n} (hs : GStep b t t') :
    ∀ {Γ : Fin n → GTy R F} {δ : Fin n → R} {A : GTy R F},
      GTypedQ Γ δ t A → GTypedQ Γ δ t' A := by
  induction hs with
  | beta t₂ t₁ =>
    intro Γ δ B h
    obtain ⟨r, A, δ₁, δ₂, h₁, h₂, hle⟩ := app_inv h
    obtain ⟨r', A', B', δ₀, e, hb, hle₀⟩ := lam_inv h₁
    injection e with er eA eB
    subst er eA eB
    refine (hb.subst1 h₂).mono (le_trans ?_ hle)
    rw [add_comm]
    exact add_le_add_vec hle₀ le_rfl
  | congAppL t₂ _ ih =>
    intro Γ δ B h
    obtain ⟨r, A, δ₁, δ₂, h₁, h₂, hle⟩ := app_inv h
    exact (GTypedQ.app (ih h₁) h₂).mono hle
  | congAbs _ _ ih =>
    intro Γ δ T h
    obtain ⟨r, A, B, δ', e, hb, hle⟩ := lam_inv h
    subst e
    exact (GTypedQ.abs (ih hb)).mono hle
  | betaBox h t₁ t₂ =>
    intro Γ δ B hty
    obtain ⟨q, r, A, δ₁, δ₂, h₁, h₂, hle⟩ := letbox_inv hty
    obtain ⟨r', A', δs, e, hs, hle₁⟩ := box_inv h₁
    injection e with er eA
    subst er eA
    refine (h₂.subst1 hs).mono (le_trans (add_le_add_vec ?_ le_rfl) hle)
    rw [mul_smul]
    exact smul_vec_le_smul q hle₁
  | congLetL h t₂ _ ih =>
    intro Γ δ B hty
    obtain ⟨q, r, A, δ₁, δ₂, h₁, h₂, hle⟩ := letbox_inv hty
    exact (GTypedQ.letboxq h q (ih h₁) h₂).mono hle
  | prodCong => intro _ _ _ h; exact (no_letpair h).elim
  | prodBeta => intro _ _ _ h; exact (no_letpair h).elim
  | unitCong => intro _ _ _ h; exact (no_letunit h).elim
  | unitBeta => intro _ _ _ h; exact (no_letunit h).elim
  | congCase => intro _ _ _ h; exact (no_case h).elim
  | caseInl => intro _ _ _ h; exact (no_case h).elim
  | caseInr => intro _ _ _ h; exact (no_case h).elim

/-- Subject reduction for multi-step reduction. -/
theorem preservation_steps {b : Prop} {n : ℕ} {t t' : GTm F n} (hs : GSteps b t t')
    {Γ : Fin n → GTy R F} {δ : Fin n → R} {A : GTy R F} (h : GTypedQ Γ δ t A) :
    GTypedQ Γ δ t' A := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact preservation hstep ih

end GTypedQ

end GranuleFlat

end Coeffect
