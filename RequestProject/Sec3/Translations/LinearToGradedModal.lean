module

public import RequestProject.Sec2.Linear.Typing
public import RequestProject.Sec2.Linear.Semantics
public import RequestProject.Sec2.Graded.Typing
public import RequestProject.Sec2.Graded.Semantics

/-!
# The translation `⦇-⦈` from the linear-base lineage to the graded-base lineage (Section 3.2)

The homomorphic translation of Section 3.2.1 (Linear Base → Graded Modal Base), extended in
Section 5.3 (Linear Core → Graded Modal Core) and Section 5.6 (Linear Push Core → Graded Modal
Core, with the `push` constructs translated to the derivable distributive laws).

```
⦇x⦈ = x   ⦇λx.t⦈ = λx.⦇t⦈   ⦇t₁ t₂⦈ = ⦇t₁⦈ ⦇t₂⦈   ⦇[t]⦈ = [⦇t⦈]
⦇push⊗ t⦈ = let [x] = ⦇t⦈ in let ⟨y, z⟩ = x in ⟨[y], [z]⟩     (similarly push⊕, push_unit)
⦇A ⊸ B⦈ = ⦇A⦉ →^1 ⦇B⦈    ⦇□_r A⦈ = □_{φ r} ⦇A⦈
⦇x : A⦈ = x :_1 ⦇A⦈       ⦇x : [A]_r⦈ = x :_{φ r} ⦇A⦈
```

The translation of *types and contexts* is parameterised by a *grade map* `φ : R → S` (between
pre-ordered semirings) satisfying a handful of conditions (`GradeMap`):

* `φ = id` gives the translation of Section 3.2.1 (Theorem 3.1);
* `φ r = ⟨r, ω⟩ : R × {0,1,ω}` gives the *linearity-preserving* translation `⦇-⦈'` of
  Section 3.2.2 (Theorem 3.3); there linear assumptions are mapped to `⟨1, 1⟩ = 1`.

The term translation is the same for both (as observed in the paper).
-/

@[expose] public section

namespace Coeffect

universe u v

/-- The graded-base calculus targeted by a linear-base calculus. -/
def LLevel.toG : LLevel → GLevel
  | .base => .modal
  | .core => .core
  | .push => .core

lemma LLevel.toG_modal (F : LLevel) : F.toG.Modal := by cases F <;> trivial

lemma LLevel.toG_core {F : LLevel} (h : F.Core) : F.toG.Core := by
  cases F <;> simp_all [LLevel.Core, LLevel.toG, GLevel.Core]

lemma LLevel.toG_core_of_push {F : LLevel} (h : F.Push) : F.toG.Core :=
  LLevel.toG_core (LLevel.core_of_push h)

/-- A map of grades along which the linear-base type system can be translated. -/
structure GradeMap (R : Type u) (S : Type v) [PreorderedSemiring R] [PreorderedSemiring S] where
  /-- the underlying function -/
  toFun : R → S
  zero_le_map_zero : 0 ≤ toFun 0
  one_le_map_one : 1 ≤ toFun 1
  mono : ∀ {r s : R}, r ≤ s → toFun r ≤ toFun s
  map_add : ∀ r s : R, toFun (r + s) = toFun r + toFun s
  map_mul : ∀ r s : R, toFun (r * s) = toFun r * toFun s
  one_le_map : ∀ {r : R}, 1 ≤ r → 1 ≤ toFun r

open Lin in
/-- The identity grade map (Section 3.2.1). -/
def GradeMap.id (R : Type u) [PreorderedSemiring R] : GradeMap R R where
  toFun := fun r => r
  zero_le_map_zero := le_rfl
  one_le_map_one := le_rfl
  mono := fun h => h
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  one_le_map := fun h => h

open Lin in
/-- The linearity-preserving grade map `r ↦ ⟨r, ω⟩ : R × {0,1,ω}` (Section 3.2.2). -/
def GradeMap.linPair (R : Type u) [PreorderedSemiring R] : GradeMap R (R × Lin) where
  toFun := fun r => (r, ω)
  zero_le_map_zero := ⟨le_rfl, Lin.zero_le_omega⟩
  one_le_map_one := ⟨le_rfl, Lin.one_le_omega⟩
  mono := fun h => ⟨h, le_rfl⟩
  map_add := fun _ _ => by simp
  map_mul := fun _ _ => by simp
  one_le_map := fun h => ⟨h, Lin.one_le_omega⟩

variable {R : Type u} {S : Type v} {F : LLevel}

/-- Term translation `⦇t⦈`. -/
def LTm.toG {n : ℕ} : LTm F n → GTm F.toG n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.toG t₂.toG
  | .lam t => .lam t.toG
  | .box t => .box (LLevel.toG_modal F) t.toG
  | .letbox t₁ t₂ => .letbox (LLevel.toG_modal F) t₁.toG t₂.toG
  | .pair h t₁ t₂ => .pair (LLevel.toG_core h) t₁.toG t₂.toG
  | .letpair h t₁ t₂ => .letpair (LLevel.toG_core h) t₁.toG t₂.toG
  | .unit h => .unit (LLevel.toG_core h)
  | .letunit h t₁ t₂ => .letunit (LLevel.toG_core h) t₁.toG t₂.toG
  | .inl h t => .inl (LLevel.toG_core h) t.toG
  | .inr h t => .inr (LLevel.toG_core h) t.toG
  | .case h t t₁ t₂ => .case (LLevel.toG_core h) t.toG t₁.toG t₂.toG
  | .pushProd h t =>
      .letbox (LLevel.toG_modal F) t.toG
        (.letpair (LLevel.toG_core_of_push h) (.var 0)
          (.pair (LLevel.toG_core_of_push h) (.box (LLevel.toG_modal F) (.var 1))
            (.box (LLevel.toG_modal F) (.var 0))))
  | .pushSum h t =>
      .letbox (LLevel.toG_modal F) t.toG
        (.case (LLevel.toG_core_of_push h) (.var 0)
          (.inl (LLevel.toG_core_of_push h) (.box (LLevel.toG_modal F) (.var 0)))
          (.inr (LLevel.toG_core_of_push h) (.box (LLevel.toG_modal F) (.var 0))))
  | .pushUnit h t =>
      .letbox (LLevel.toG_modal F) t.toG
        (.letunit (LLevel.toG_core_of_push h) (.var 0) (.unit (LLevel.toG_core_of_push h)))

variable [PreorderedSemiring R] [PreorderedSemiring S]

/-- Type translation `⦇A⦈` along a grade map. -/
def LTy.toG (φ : GradeMap R S) : LTy R F → GTy S F.toG
  | .base => .base
  | .lolli A B => .fn 1 (A.toG φ) (B.toG φ)
  | .box r A => .box (LLevel.toG_modal F) (φ.toFun r) (A.toG φ)
  | .tensor h A B => .prod (LLevel.toG_core h) (A.toG φ) (B.toG φ)
  | .unit h => .unit (LLevel.toG_core h)
  | .oplus h A B => .sum (LLevel.toG_core h) (A.toG φ) (B.toG φ)

/-- Context translation of a single assumption: linear assumptions get grade `1`, graded
assumptions `[A]_r` get grade `φ r`, and absent variables grade `0`. -/
def Use.toG (φ : GradeMap R S) : Use R → S
  | .none => 0
  | .lin => 1
  | .grd r => φ.toFun r

/-- Context translation `⦇Γ⦈`: types. -/
def toGCtx (φ : GradeMap R S) {n : ℕ} (Γ : Fin n → LTy R F) : Fin n → GTy S F.toG :=
  fun i => (Γ i).toG φ

/-- Context translation `⦇Γ⦈`: grades. -/
def toGGrades (φ : GradeMap R S) {n : ℕ} (u : Fin n → Use R) : Fin n → S :=
  fun i => (u i).toG φ

lemma toGCtx_cons (φ : GradeMap R S) {n : ℕ} (A : LTy R F) (Γ : Fin n → LTy R F) :
    toGCtx φ (A .: Γ) = A.toG φ .: toGCtx φ Γ := by
  funext i; exact Fin.cases rfl (fun i => rfl) i

lemma toGGrades_cons (φ : GradeMap R S) {n : ℕ} (a : Use R) (u : Fin n → Use R) :
    toGGrades φ (a .: u) = a.toG φ .: toGGrades φ u := by
  funext i; exact Fin.cases rfl (fun i => rfl) i

lemma toGGrades_add (φ : GradeMap R S) {n : ℕ} {u₁ u₂ u : Fin n → Use R} (h : CtxAdd u₁ u₂ u) :
    toGGrades φ u = toGGrades φ u₁ + toGGrades φ u₂ := by
  funext i
  have hi := h i
  simp only [toGGrades, Pi.add_apply]
  revert hi
  generalize u₁ i = a
  generalize u₂ i = b
  generalize u i = c
  intro hi
  cases hi <;> simp [Use.toG, φ.map_add]

lemma toGGrades_add_one_smul (φ : GradeMap R S) {n : ℕ} {u₁ u₂ u : Fin n → Use R}
    (h : CtxAdd u₁ u₂ u) : toGGrades φ u = toGGrades φ u₁ + (1 : S) • toGGrades φ u₂ := by
  rw [one_smul]; exact toGGrades_add φ h

lemma toGGrades_only (φ : GradeMap R S) {n : ℕ} (i : Fin n) :
    toGGrades φ (Use.only i) = Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [toGGrades, Use.only, Use.toG]
  · simp [toGGrades, Use.only, Use.toG, hj]

lemma toGGrades_smul (φ : GradeMap R S) {n : ℕ} (r : R) {u : Fin n → Use R} (hg : Graded u) :
    toGGrades φ (smulCtx r u) = φ.toFun r • toGGrades φ u := by
  funext i
  simp only [toGGrades, smulCtx, Pi.smul_apply, smul_eq_mul]
  have := hg i
  cases hu : u i with
  | none => simp [Use.smul, Use.toG]
  | lin => exact absurd hu this
  | grd s => simp [Use.smul, Use.toG, φ.map_mul]

lemma toGGrades_update (φ : GradeMap R S) {n : ℕ} (u : Fin n → Use R) (i : Fin n) (a : Use R) :
    toGGrades φ (Function.update u i a) = Function.update (toGGrades φ u) i (a.toG φ) := by
  funext j; by_cases hj : j = i
  · subst hj; simp [toGGrades]
  · simp [toGGrades, Function.update_of_ne hj]

/-! ### Typing of the translated `push` combinators -/

section push

variable {G : GLevel} (hm : G.Modal) (hc : G.Core)

lemma single_zero_eq {n : ℕ} (ρ : S) :
    ρ • (Pi.single (0 : Fin (n + 1)) (1 : S) : Fin (n + 1) → S) + 0 = (ρ .: (0 : Fin n → S)) := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.succ_ne_zero]

lemma typed_pushProd_body {n : ℕ} (Γ : Fin n → GTy S G) (ρ : S) (A B : GTy S G) :
    GTyped (GTy.prod hc A B .: Γ) (ρ .: 0)
      (.letpair hc (.var 0) (.pair hc (.box hm (.var 1)) (.box hm (.var 0))))
      (.prod hc (.box hm ρ A) (.box hm ρ B)) := by
  refine (GTyped.letpair (r := ρ) (δ₂ := 0) hc (GTyped.var _ 0) ?_).cast (single_zero_eq ρ)
  refine (GTyped.pair hc (GTyped.pr hm ρ (GTyped.var _ 1)) (GTyped.pr hm ρ (GTyped.var _ 0))).cast ?_
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    simp [Pi.single_apply, Fin.succ_ne_zero]
  all_goals intro e; have := congrArg Fin.val e; simp only [Fin.val_succ, Fin.val_one] at this; exact absurd this (by omega)

lemma typed_pushSum_body {n : ℕ} (Γ : Fin n → GTy S G) (ρ : S) (hρ : 1 ≤ ρ) (A B : GTy S G) :
    GTyped (GTy.sum hc A B .: Γ) (ρ .: 0)
      (.case hc (.var 0) (.inl hc (.box hm (.var 0))) (.inr hc (.box hm (.var 0))))
      (.sum hc (.box hm ρ A) (.box hm ρ B)) := by
  have hb : ∀ C : GTy S G, GTyped (C .: GTy.sum hc A B .: Γ) (ρ .: 0) (.box hm (.var 0))
      (.box hm ρ C) := fun C => by
    refine (GTyped.pr hm ρ (GTyped.var _ 0)).cast ?_
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.succ_ne_zero]
  exact (GTyped.case (r := ρ) (δ₂ := 0) hc (GTyped.var _ 0) (GTyped.inl hc (hb A))
    (GTyped.inr hc (hb B)) hρ).cast (single_zero_eq ρ)

lemma typed_pushUnit_body {n : ℕ} (Γ : Fin n → GTy S G) (ρ : S) :
    GTyped (GTy.unit hc .: Γ) (ρ .: 0) (.letunit hc (.var 0) (.unit hc)) (.unit hc) :=
  (GTyped.letunit hc ρ (GTyped.var _ 0) (GTyped.unit hc)).cast (single_zero_eq ρ)

end push

lemma add_scons_zero {n : ℕ} (δ : Fin n → S) : δ + (0 : Fin n → S) = δ := add_zero δ

/-- **Theorem 3.1 / 3.3 / 5.3 / 5.6 (type preservation).**
`Γ ⊢_L t : A ⟹ ⦇Γ⦈ ⊢_G ⦇t⦈ : ⦇A⦈`, for any grade map `φ` (in particular for `GradeMap.id`, and
for the linearity-preserving `GradeMap.linPair`). -/
theorem LTyped.toG (φ : GradeMap R S) {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R}
    {t : LTm F n} {A : LTy R F} (h : LTyped Γ u t A) :
    GTyped (toGCtx φ Γ) (toGGrades φ u) t.toG (A.toG φ) := by
  induction h with
  | var Γ i => rw [toGGrades_only]; exact GTyped.var _ i
  | abs _ ih =>
    rw [toGCtx_cons, toGGrades_cons] at ih
    exact GTyped.abs ih
  | app _ _ hadd ih₁ ih₂ =>
    rw [toGGrades_add_one_smul φ hadd]; exact GTyped.app ih₁ ih₂
  | weak i _ hi ih =>
    rw [toGGrades_update]
    exact GTyped.approx i ih (by simpa [toGGrades, hi, Use.toG] using φ.zero_le_map_zero)
  | der i _ hi ih =>
    rw [toGGrades_update]
    exact GTyped.approx i ih (by simpa [toGGrades, hi, Use.toG] using φ.one_le_map_one)
  | approx i _ hi hrs ih =>
    rw [toGGrades_update]
    exact GTyped.approx i ih (by simpa [toGGrades, hi, Use.toG] using φ.mono hrs)
  | pr r _ hg ih =>
    rw [toGGrades_smul φ r hg]; exact GTyped.pr _ _ ih
  | letbox _ _ hadd ih₁ ih₂ =>
    rw [toGCtx_cons, toGGrades_cons] at ih₂
    rw [toGGrades_add φ hadd]; exact GTyped.letbox _ ih₁ ih₂
  | pair h _ _ hadd ih₁ ih₂ =>
    rw [toGGrades_add φ hadd]; exact GTyped.pair _ ih₁ ih₂
  | letpair h _ _ hadd ih₁ ih₂ =>
    rw [toGCtx_cons, toGCtx_cons, toGGrades_cons, toGGrades_cons] at ih₂
    rw [toGGrades_add φ hadd, ← one_smul S (toGGrades φ _)]
    exact GTyped.letpair _ ih₁ ih₂
  | @unit k Γ' h =>
    have : toGGrades φ (emptyU : Fin k → Use R) = 0 := by
      funext i; simp [toGGrades, emptyU, Use.toG]
    rw [this]; exact GTyped.unit _
  | letunit h _ _ hadd ih₁ ih₂ =>
    rw [toGGrades_add φ hadd, ← one_smul S (toGGrades φ _)]
    exact GTyped.letunit _ 1 ih₁ ih₂
  | inl h _ ih => exact GTyped.inl _ ih
  | inr h _ ih => exact GTyped.inr _ ih
  | case h _ _ _ hadd ih ih₁ ih₂ =>
    rw [toGCtx_cons, toGGrades_cons] at ih₁ ih₂
    rw [toGGrades_add φ hadd, ← one_smul S (toGGrades φ _)]
    exact GTyped.case _ ih ih₁ ih₂ le_rfl
  | @pushProd _ _ _ _ r _ _ h hc _ ih =>
    refine (GTyped.letbox (δ₂ := 0) _ ih ?_).cast (add_zero _)
    exact typed_pushProd_body _ _ _ (φ.toFun r) _ _
  | @pushSum _ _ _ _ r _ _ h hc hr _ ih =>
    refine (GTyped.letbox (δ₂ := 0) _ ih ?_).cast (add_zero _)
    exact typed_pushSum_body _ _ _ (φ.toFun r) (φ.one_le_map hr) _ _
  | @pushUnit _ _ _ _ r h hc _ ih =>
    refine (GTyped.letbox (δ₂ := 0) _ ih ?_).cast (add_zero _)
    exact typed_pushUnit_body _ _ (φ.toFun r)

end Coeffect

/-! ## Operational correspondence -/

namespace Coeffect

variable {F : LLevel}

theorem LTm.toG_rename {n m : ℕ} (t : LTm F n) (ρ : Fin n → Fin m) :
    (t.rename ρ).toG = t.toG.rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | _ => simp_all [LTm.rename, LTm.toG, GTm.rename]

lemma LTm.toG_upSub {n m : ℕ} (σ : Fin n → LTm F m) :
    (fun i => (LTm.upSub σ i).toG) = GTm.upSub (fun i => (σ i).toG) := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  simp [LTm.toG_rename]

theorem LTm.toG_subst {n m : ℕ} (t : LTm F n) (σ : Fin n → LTm F m) :
    (t.subst σ).toG = t.toG.subst (fun i => (σ i).toG) := by
  induction t generalizing m with
  | var i => rfl
  | _ => simp_all [LTm.subst, LTm.toG, GTm.subst, LTm.toG_upSub, GTm.rename]

lemma LTm.toG_subst1 {n : ℕ} (t : LTm F (n + 1)) (s : LTm F n) :
    (t.subst1 s).toG = t.toG.subst1 s.toG := by
  rw [LTm.toG_subst]; congr 1; funext i; exact Fin.cases rfl (fun i => rfl) i

lemma LTm.toG_subst2 {n : ℕ} (t : LTm F (n + 2)) (s₁ s₂ : LTm F n) :
    (t.subst2 s₁ s₂).toG = t.toG.subst2 s₁.toG s₂.toG := by
  rw [LTm.toG_subst]; congr 1; funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

lemma GSteps.lift {G : GLevel} {b : Prop} {n m : ℕ} (f : GTm G n → GTm G m)
    (hf : ∀ {x y}, GStep b x y → GStep b (f x) (f y)) {x y : GTm G n} (h : GSteps b x y) :
    GSteps b (f x) (f y) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (hf h)

/-- **Theorem 3.1 / 5.3 (operational correspondence)**, for Linear Base and Linear Core:
a single reduction step is simulated by a single step, `t ⇝_L t' ⟹ ⦇t⦈ ⇝_G ⦇t'⦈`. -/
theorem LStep.toG {n : ℕ} (hF : ¬ F.Push) {t t' : LTm F n} (h : LStep t t') :
    GStep False t.toG t'.toG := by
  induction h with
  | beta t₂ t₁ => rw [LTm.toG_subst1]; exact .beta _ _
  | congAppL _ _ ih => exact .congAppL _ ih
  | betaBox t₁ t₂ => rw [LTm.toG_subst1]; exact .betaBox _ _ _
  | congLetL _ _ ih => exact .congLetL _ _ ih
  | prodCong h _ _ ih => exact .prodCong _ _ ih
  | prodBeta h t₁ t₂ t₃ => rw [LTm.toG_subst2]; exact .prodBeta _ _ _ _
  | unitCong h _ _ ih => exact .unitCong _ _ ih
  | unitBeta h t₂ => exact .unitBeta _ _
  | congCase h _ _ _ ih => exact .congCase _ _ _ ih
  | caseInl h t t₁ t₂ => rw [LTm.toG_subst1]; exact .caseInl _ _ _ _
  | caseInr h t t₁ t₂ => rw [LTm.toG_subst1]; exact .caseInr _ _ _ _
  | pushProdCong h => simp_all
  | pushProdBoxCong h => simp_all
  | pushProd h => simp_all
  | pushSumCong h => simp_all
  | pushSumBoxCong h => simp_all
  | pushSumInl h => simp_all
  | pushSumInr h => simp_all
  | pushUnitCong h => simp_all
  | pushUnitBoxCong h => simp_all
  | pushUnit h => simp_all

/-- **Theorem 5.4 (operational correspondence, corrected form)** for Linear Push Core (and hence
for all three linear calculi): the translations of the two sides of a reduction step have a
common reduct, `t ⇝_L t' ⟹ ∃ s, ⦇t⦈ ⇝_G* s ∧ ⦇t'⦈ ⇝_G* s`.
(The paper states `⦇t⦈ ⇝_G* ⦇t'⦈`, which fails for the rules reducing under a box, see
`LStep.toG_counterexample`.) -/
theorem LStep.toG_join {n : ℕ} {t t' : LTm F n} (h : LStep t t') :
    ∃ s, GSteps False t.toG s ∧ GSteps False t'.toG s := by
  induction h with
  | beta t₂ t₁ => exact ⟨_, .single (by rw [LTm.toG_subst1]; exact .beta _ _), .refl⟩
  | congAppL _ _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.app x _) (fun h => .congAppL _ h) h₁,
      GSteps.lift (fun x => GTm.app x _) (fun h => .congAppL _ h) h₂⟩
  | betaBox t₁ t₂ => exact ⟨_, .single (by rw [LTm.toG_subst1]; exact .betaBox _ _ _), .refl⟩
  | congLetL _ _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.letbox _ x _) (fun h => .congLetL _ _ h) h₁,
      GSteps.lift (fun x => GTm.letbox _ x _) (fun h => .congLetL _ _ h) h₂⟩
  | prodCong h _ _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.letpair _ x _) (fun h => .prodCong _ _ h) h₁,
      GSteps.lift (fun x => GTm.letpair _ x _) (fun h => .prodCong _ _ h) h₂⟩
  | prodBeta h t₁ t₂ t₃ =>
    exact ⟨_, .single (by rw [LTm.toG_subst2]; exact .prodBeta _ _ _ _), .refl⟩
  | unitCong h _ _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.letunit _ x _) (fun h => .unitCong _ _ h) h₁,
      GSteps.lift (fun x => GTm.letunit _ x _) (fun h => .unitCong _ _ h) h₂⟩
  | unitBeta h t₂ => exact ⟨_, .single (.unitBeta _ _), .refl⟩
  | congCase h _ _ _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.case _ x _ _) (fun h => .congCase _ _ _ h) h₁,
      GSteps.lift (fun x => GTm.case _ x _ _) (fun h => .congCase _ _ _ h) h₂⟩
  | caseInl h t t₁ t₂ => exact ⟨_, .single (by rw [LTm.toG_subst1]; exact .caseInl _ _ _ _), .refl⟩
  | caseInr h t t₁ t₂ => exact ⟨_, .single (by rw [LTm.toG_subst1]; exact .caseInr _ _ _ _), .refl⟩
  | pushProdCong h _ ih | pushSumCong h _ ih | pushUnitCong h _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.letbox _ x _) (fun h => .congLetL _ _ h) h₁,
      GSteps.lift (fun x => GTm.letbox _ x _) (fun h => .congLetL _ _ h) h₂⟩
  | pushProdBoxCong h _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, .head (.betaBox _ _ _)
        (GSteps.lift (fun x => GTm.letpair _ x _) (fun h => .prodCong _ _ h) h₁),
      .head (.betaBox _ _ _)
        (GSteps.lift (fun x => GTm.letpair _ x _) (fun h => .prodCong _ _ h) h₂)⟩
  | pushSumBoxCong h _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, .head (.betaBox _ _ _)
        (GSteps.lift (fun x => GTm.case _ x _ _) (fun h => .congCase _ _ _ h) h₁),
      .head (.betaBox _ _ _)
        (GSteps.lift (fun x => GTm.case _ x _ _) (fun h => .congCase _ _ _ h) h₂)⟩
  | pushUnitBoxCong h _ ih =>
    obtain ⟨s, h₁, h₂⟩ := ih
    exact ⟨_, .head (.betaBox _ _ _)
        (GSteps.lift (fun x => GTm.letunit _ x _) (fun h => .unitCong _ _ h) h₁),
      .head (.betaBox _ _ _)
        (GSteps.lift (fun x => GTm.letunit _ x _) (fun h => .unitCong _ _ h) h₂)⟩
  | pushProd h hc t₁ t₂ =>
    exact ⟨_, .head (.betaBox _ _ _) (.single (.prodBeta _ _ _ _)), .refl⟩
  | pushSumInl h hc t => exact ⟨_, .head (.betaBox _ _ _) (.single (.caseInl _ _ _ _)), .refl⟩
  | pushSumInr h hc t => exact ⟨_, .head (.betaBox _ _ _) (.single (.caseInr _ _ _ _)), .refl⟩
  | pushUnit h hc => exact ⟨_, .head (.betaBox _ _ _) (.single (.unitBeta _ _)), .refl⟩

end Coeffect

/-! ## Equation preservation -/

namespace Coeffect

variable {F : LLevel}

/-- The axioms of `≡_L` without the `η`-rules for `push⊗`/`push⊕` (the paper's proof of
Theorem 5.4 does not treat these two rules). -/
abbrev LAxSel.noPushEta : LAxSel := { pushEta := False }

theorem LAxF.toG {n : ℕ} {t t' : LTm F n} (h : LAxF LAxSel.noPushEta t t') :
    GEq t.toG t'.toG := by
  cases h with
  | beta a b => rw [LTm.toG_subst1]; exact .ax (.beta _ _)
  | eta he => simp only [LTm.toG, LTm.toG_rename]; exact .ax (.eta _)
  | betaBox a b => rw [LTm.toG_subst1]; exact .ax (.betaBox _ _ _)
  | etaBox he => exact .ax (.etaBox _ _)
  | letCommOne he a b c => simp only [LTm.toG, LTm.toG_rename]; exact .ax (.letCommOne _ _ _ _)
  | letCommTwo he a b c => simp only [LTm.toG, LTm.toG_rename]; exact .ax (.letCommTwo _ _ _ _)
  | letCommBox he a b => exact .ax (.letCommBox _ _ _)
  | betaUnit h => exact .ax (.betaUnit _ _)
  | etaUnit h s => exact .ax (.etaUnit _ _)
  | betaProd h a b c => rw [LTm.toG_subst2]; exact .ax (.betaProd _ _ _ _)
  | etaProd h => exact .ax (.etaProd trivial _ _)
  | betaSumOne h a b c => rw [LTm.toG_subst1]; exact .ax (.betaSumOne _ _ _ _)
  | betaSumTwo h a b c => rw [LTm.toG_subst1]; exact .ax (.betaSumTwo _ _ _ _)
  | etaSum h => exact .ax (.etaSum trivial _ _)
  | pushProdBeta h hc a b =>
    exact GSteps.toGEq (b := False) (.head (.betaBox _ _ _) (.single (.prodBeta _ _ _ _)))
  | pushProdEta he => exact absurd he (by decide)
  | pushSumBetaOne h hc a =>
    exact GSteps.toGEq (b := False) (.head (.betaBox _ _ _) (.single (.caseInl _ _ _ _)))
  | pushSumBetaTwo h hc a =>
    exact GSteps.toGEq (b := False) (.head (.betaBox _ _ _) (.single (.caseInr _ _ _ _)))
  | pushSumEta he => exact absurd he (by decide)
  | pushUnitBeta h hc =>
    exact GSteps.toGEq (b := False) (.head (.betaBox _ _ _) (.single (.unitBeta _ _)))

/-- **Theorem 3.1 / 5.3 / 5.4 (equation preservation).** `t ≡_L t' ⟹ ⦇t⦈ ≡_G ⦇t'⦈`
(for the theory without the `push` η-rules). -/
theorem LCong.toG {n : ℕ} {t t' : LTm F n} (h : LCong (LAxF LAxSel.noPushEta) t t') :
    GEq t.toG t'.toG := by
  induction h with
  | ax h => exact h.toG
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ ih => exact .lam ih
  | box _ ih => exact .box _ ih
  | letbox _ _ ih₁ ih₂ => exact .letbox _ ih₁ ih₂
  | pair h _ _ ih₁ ih₂ => exact .pair _ ih₁ ih₂
  | letpair h _ _ ih₁ ih₂ => exact .letpair _ ih₁ ih₂
  | letunit h _ _ ih₁ ih₂ => exact .letunit _ ih₁ ih₂
  | inl h _ ih => exact .inl _ ih
  | inr h _ ih => exact .inr _ ih
  | case h _ _ _ ih ih₁ ih₂ => exact .case _ ih ih₁ ih₂
  | pushProd h _ ih => exact .letbox _ ih (.refl _)
  | pushSum h _ ih => exact .letbox _ ih (.refl _)
  | pushUnit h _ ih => exact .letbox _ ih (.refl _)

/-- Without `push` constructs (Linear Base, Linear Core) the full theory `≡_L` is preserved. -/
theorem LEq.toG {n : ℕ} (hF : ¬ F.Push) {t t' : LTm F n} (h : LEq t t') :
    GEq t.toG t'.toG := by
  refine LCong.toG (h.mono ?_)
  intro n t t' h
  cases h with
  | pushProdEta _ h' => exact absurd h' (by simp [hF])
  | pushSumEta _ h' => exact absurd h' (by simp [hF])
  | beta => exact .beta _ _
  | eta => exact .eta trivial _
  | betaBox => exact .betaBox _ _
  | etaBox => exact .etaBox trivial _
  | letCommOne => exact .letCommOne trivial _ _ _
  | letCommTwo => exact .letCommTwo trivial _ _ _
  | letCommBox => exact .letCommBox trivial _ _
  | betaUnit => exact .betaUnit _ _
  | etaUnit => exact .etaUnit _ _
  | betaProd => exact .betaProd _ _ _ _
  | etaProd => exact .etaProd _ _
  | betaSumOne => exact .betaSumOne _ _ _ _
  | betaSumTwo => exact .betaSumTwo _ _ _ _
  | etaSum => exact .etaSum _ _
  | pushProdBeta => exact .pushProdBeta _ _ _ _
  | pushSumBetaOne => exact .pushSumBetaOne _ _ _
  | pushSumBetaTwo => exact .pushSumBetaTwo _ _ _
  | pushUnitBeta => exact .pushUnitBeta _ _

end Coeffect
