module

public import RequestProject.Sec3.Translations.LinearToGradedModal
public import RequestProject.Sec2.Translations.GradedToLinear

/-!
# The CPS translation from Linear Base to Graded Base (Section 2.3.2)

Graded Base has no graded modality, so `□_r A` is encoded in continuation-passing style, based
on Plotkin's call-by-name CPS translation (answer type `K`, the base type):

```
⦇K⦈ = (K →¹ K) →¹ K     ⦇A ⊸ B⦈ = ((⦇A⦈ →¹ ⦇B⦈) →¹ K) →¹ K     ⦇□_r A⦈ = (⦇A⦈ →^r K) →¹ K
⦇x⦈ = λk. x k            ⦇λx.t⦈ = λk. k (λx. ⦇t⦈)       ⦇t₁ t₂⦈ = λk. ⦇t₁⦈ (λf. f ⦇t₂⦈ k)
⦇[t]⦈ = λk. k ⦇t⦈        ⦇let [x] = t₁ in t₂⦈ = λk. ⦇t₁⦈ (λx. ⦇t₂⦈ k)
⦇x : A⦈ = x :_1 ⦇A⦈      ⦇x : [A]_r⦈ = x :_r ⦇A⦈
```

(This file reuses the context translation `toGGrades (GradeMap.id R)` of Section 3.)

Main results (Theorem 2.7):
* `LTyped.cps`: type preservation;
* `LStep.cps`: operational correspondence. The paper states `⦇t⦈ ⇝*_βG ⦇t'⦈`; as in the paper's
  own proof (which uses `≡` in the β-step), what holds is that `⦇t⦈` reduces with full
  β-reduction (`GStep True`, i.e. including reduction under `λ`) to a term equal to `⦇t'⦈`
  modulo `≡_G`;
* `LEq.cps`: preservation of the equational theory `≡_L^{β→βη□}` (without `η` for functions and
  without the commuting conversions).
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- The CPS type translation `⦇A⦈` (Linear Base → Graded Base). -/
def LTy.cps [One R] : LTy R .base → GTy R .base
  | .base => .fn 1 (.fn 1 .base .base) .base
  | .lolli A B => .fn 1 (.fn 1 (.fn 1 A.cps B.cps) .base) .base
  | .box r A => .fn 1 (.fn r A.cps .base) .base
  | .tensor h _ _ => absurd h (by decide)
  | .unit h => absurd h (by decide)
  | .oplus h _ _ => absurd h (by decide)

/-- The CPS term translation `⦇t⦈` (Linear Base → Graded Base). In `λk. …` the continuation
`k` is the de Bruijn index `0`. -/
def LTm.cps {n : ℕ} : LTm .base n → GTm .base n
  | .var i => .lam (.app (.var i.succ) (.var 0))
  | .lam t => .lam (.app (.var 0) (.lam (t.cps.rename (upRen Fin.succ))))
  | .app t₁ t₂ =>
      .lam (.app (t₁.cps.rename Fin.succ)
        (.lam (.app (.app (.var 0) (t₂.cps.rename (Fin.succ ∘ Fin.succ))) (.var 1))))
  | .box t => .lam (.app (.var 0) (t.cps.rename Fin.succ))
  | .letbox t₁ t₂ =>
      .lam (.app (t₁.cps.rename Fin.succ) (.lam (.app (t₂.cps.rename (upRen Fin.succ)) (.var 1))))
  | .pair h _ _ => absurd h (by decide)
  | .letpair h _ _ => absurd h (by decide)
  | .unit h => absurd h (by decide)
  | .letunit h _ _ => absurd h (by decide)
  | .inl h _ => absurd h (by decide)
  | .inr h _ => absurd h (by decide)
  | .case h _ _ _ => absurd h (by decide)
  | .pushProd h _ => absurd h (by decide)
  | .pushSum h _ => absurd h (by decide)
  | .pushUnit h _ => absurd h (by decide)

/-- CPS context translation (types). -/
def cpsCtx [One R] {n : ℕ} (Γ : Fin n → LTy R .base) : Fin n → GTy R .base := fun i => (Γ i).cps

variable [PreorderedSemiring R]

/-! ## Type preservation -/

section typing

variable {n : ℕ}

lemma GTyped.weaken1 {F : GLevel} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n}
    {A : GTy R F} (h : GTyped Γ δ t A) (C : GTy R F) :
    GTyped (C .: Γ) (0 .: δ) (t.rename Fin.succ) A :=
  h.rename Fin.succ (Fin.succ_injective _) _ (fun _ => rfl) _ (fun _ => rfl)
    (fun j hj => by
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact absurd rfl (hj j))

lemma GTyped.weaken2 {F : GLevel} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n}
    {A : GTy R F} (h : GTyped Γ δ t A) (C₁ C₂ : GTy R F) :
    GTyped (C₁ .: C₂ .: Γ) (0 .: 0 .: δ) (t.rename (Fin.succ ∘ Fin.succ)) A := by
  have := (h.weaken1 C₂).weaken1 C₁
  rwa [GTm.rename_rename] at this

lemma GTyped.weakenUnder {F : GLevel} {Γ : Fin n → GTy R F} {δ : Fin n → R}
    {t : GTm F (n + 1)} {a : R} {A B : GTy R F} (h : GTyped (A .: Γ) (a .: δ) t B)
    (C : GTy R F) :
    GTyped (A .: C .: Γ) (a .: 0 .: δ) (t.rename (upRen Fin.succ)) B :=
  h.rename (upRen Fin.succ) (upRen_injective (Fin.succ_injective _)) _
    (fun i => Fin.cases rfl (fun _ => rfl) i) _ (fun i => Fin.cases rfl (fun _ => rfl) i)
    (fun j hj => by rw [off_upRen_succ hj]; rfl)

/-- The argument type of a function type (used for the continuation type: `⦇A⦈ = C →¹ K`). -/
def GTy.dom {F : GLevel} : GTy R F → GTy R F
  | .fn _ C _ => C
  | A => A

lemma LTy.cps_eq (A : LTy R .base) : A.cps = .fn 1 A.cps.dom .base := by
  cases A with
  | base => rfl
  | lolli => rfl
  | box => rfl
  | tensor h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | oplus h => exact absurd h (by decide)

lemma cpsCtx_cons (A : LTy R .base) (Γ : Fin n → LTy R .base) :
    cpsCtx (A .: Γ) = A.cps .: cpsCtx Γ := scons_map _ _ _

/-- `⦇x⦈ = λk. x k`, and `λk.x k` is well typed for every `x : ⦇A⦈`. -/
lemma typed_cps_var (Γ : Fin n → GTy R .base) (i : Fin n) (A : LTy R .base) (hA : Γ i = A.cps) :
    GTyped Γ (Pi.single i 1) (.lam (.app (.var i.succ) (.var 0))) A.cps := by
  rw [LTy.cps_eq A]
  refine GTyped.abs ?_
  refine (GTyped.app ((GTyped.var (A.cps.dom .: Γ) i.succ).castTy (A' := .fn 1 A.cps.dom .base) ?_)
    (GTyped.var _ 0)).cast ?_
  · show Γ i = _; rw [hA]; exact LTy.cps_eq A
  · funext j; refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Pi.single_apply, Fin.succ_ne_zero, Fin.succ_inj]

/-- **Theorem 2.7 (type preservation)** of the CPS translation:
`Γ ⊢_L t : A ⟹ ⦇Γ⦈ ⊢_G ⦇t⦈ : ⦇A⦈`. -/
theorem LTyped.cps {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} (h : LTyped Γ u t A) :
    GTyped (cpsCtx Γ) (toGGrades (GradeMap.id R) u) t.cps A.cps := by
  induction h with
  | var Γ i => rw [toGGrades_only]; exact typed_cps_var _ i _ rfl
  | @abs k Γ u t A B _ ih =>
    rw [cpsCtx_cons, toGGrades_cons] at ih
    refine GTyped.abs ?_
    refine (GTyped.app (GTyped.var _ 0) (GTyped.abs (ih.weakenUnder _))).cast ?_
    funext j; refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Fin.succ_ne_zero]
  | @app k Γ u₁ u₂ u t₁ t₂ A B _ _ hadd ih₁ ih₂ =>
    rw [toGGrades_add _ hadd]
    refine (GTyped.abs (A := B.cps.dom) (r := 1) (B := .base) ?_).castTy (LTy.cps_eq B).symm
    have hM := GTyped.app ((GTyped.app (GTyped.var (A.cps.fn 1 B.cps .: B.cps.dom .: cpsCtx Γ) 0)
      (ih₂.weaken2 _ _)).castTy (LTy.cps_eq B)) (GTyped.var _ 1)
    refine (GTyped.app (ih₁.weaken1 B.cps.dom) (GTyped.abs (hM.cast (δ' := 1 .: 1 .: toGGrades (GradeMap.id R) u₂)
      ?_))).cast ?_
    · funext j; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
        simp [Fin.succ_ne_zero, Fin.succ_succ_ne_one]
    · funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
  | weak i _ hi ih =>
    rw [toGGrades_update]
    exact GTyped.approx i ih (by simp [toGGrades, hi, Use.toG, GradeMap.id])
  | der i _ hi ih =>
    rw [toGGrades_update]
    exact GTyped.approx i ih (by simp [toGGrades, hi, Use.toG, GradeMap.id])
  | approx i _ hi hrs ih =>
    rw [toGGrades_update]
    exact GTyped.approx i ih (by simpa [toGGrades, hi, Use.toG, GradeMap.id] using hrs)
  | @pr k Γ u t A r _ hg ih =>
    rw [toGGrades_smul _ r hg]
    refine GTyped.abs (A := .fn r A.cps .base) ?_
    refine (GTyped.app (GTyped.var _ 0) (ih.weaken1 _)).cast ?_
    funext j; refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Fin.succ_ne_zero, GradeMap.id]
  | @letbox k Γ u₁ u₂ u t₁ t₂ r A B _ _ hadd ih₁ ih₂ =>
    rw [cpsCtx_cons, toGGrades_cons] at ih₂
    rw [toGGrades_add _ hadd]
    refine (GTyped.abs (A := B.cps.dom) (r := 1) (B := .base) ?_).castTy (LTy.cps_eq B).symm
    have hN := GTyped.app ((ih₂.weakenUnder B.cps.dom).castTy (LTy.cps_eq B)) (GTyped.var _ 1)
    refine (GTyped.app (ih₁.weaken1 B.cps.dom)
      (GTyped.abs (hN.cast (δ' := r .: 1 .: toGGrades (GradeMap.id R) u₂) ?_))).cast ?_
    · funext j; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
        simp [Fin.succ_succ_ne_one, Use.toG, GradeMap.id]
    · funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
  | pair h => exact absurd h (by decide)
  | letpair h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | letunit h => exact absurd h (by decide)
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)
  | case h => exact absurd h (by decide)
  | pushProd h => exact absurd h (by decide)
  | pushSum h => exact absurd h (by decide)
  | pushUnit h => exact absurd h (by decide)

end typing

/-! ## Syntactic properties -/

section ren

variable {F : GLevel}

lemma GTm.rename_subst_comm {n m k l : ℕ} (t : GTm F n) {σ : Fin n → GTm F k}
    {ρ' : Fin k → Fin l} {ρ : Fin n → Fin m} {σ' : Fin m → GTm F l}
    (h : ∀ i, (σ i).rename ρ' = σ' (ρ i)) : (t.subst σ).rename ρ' = (t.rename ρ).subst σ' := by
  rw [GTm.rename_subst, GTm.subst_rename]; congr 1; funext i; exact h i

/-- Reduction is closed under renaming. -/
theorem GStep.rename {b : Prop} {n m : ℕ} {t t' : GTm F n} (h : GStep b t t')
    (ρ : Fin n → Fin m) : GStep b (t.rename ρ) (t'.rename ρ) := by
  induction h generalizing m with
  | beta => rw [GTm.rename_subst1]; exact .beta _ _
  | congAppL _ _ ih => exact .congAppL _ (ih ρ)
  | congAbs hb _ ih => exact .congAbs hb (ih _)
  | betaBox => rw [GTm.rename_subst1]; exact .betaBox _ _ _
  | congLetL h _ _ ih => exact .congLetL h _ (ih ρ)
  | prodCong h _ _ ih => exact .prodCong h _ (ih ρ)
  | prodBeta => rw [GTm.rename_subst2]; exact .prodBeta _ _ _ _
  | unitCong h _ _ ih => exact .unitCong h _ (ih ρ)
  | unitBeta => exact .unitBeta _ _
  | congCase h _ _ _ ih => exact .congCase h _ _ (ih ρ)
  | caseInl => rw [GTm.rename_subst1]; exact .caseInl _ _ _ _
  | caseInr => rw [GTm.rename_subst1]; exact .caseInr _ _ _ _

theorem GSteps.rename {b : Prop} {n m : ℕ} {t t' : GTm F n} (h : GSteps b t t')
    (ρ : Fin n → Fin m) : GSteps b (t.rename ρ) (t'.rename ρ) :=
  GSteps.lift (fun x => x.rename ρ) (fun h => h.rename ρ) h

end ren

lemma cps_ren_aux₁ {n m : ℕ} (ρ : Fin n → Fin m) :
    upRen Fin.succ ∘ upRen ρ = upRen (upRen ρ) ∘ upRen Fin.succ := by
  funext i; exact Fin.cases rfl (fun _ => rfl) i

lemma cps_ren_aux₂ {n m : ℕ} (ρ : Fin n → Fin m) : Fin.succ ∘ ρ = upRen ρ ∘ Fin.succ := rfl

lemma cps_ren_aux₃ {n m : ℕ} (ρ : Fin n → Fin m) :
    (Fin.succ ∘ Fin.succ) ∘ ρ = upRen (upRen ρ) ∘ (Fin.succ ∘ Fin.succ) := rfl

/-- The CPS translation commutes with renaming. -/
theorem LTm.cps_rename {n m : ℕ} (t : LTm .base n) (ρ : Fin n → Fin m) :
    (t.rename ρ).cps = t.cps.rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | lam t ih =>
    simp only [LTm.rename, LTm.cps, GTm.rename, ih, GTm.rename_rename, cps_ren_aux₁]; rfl
  | app t₁ t₂ ih₁ ih₂ =>
    simp only [LTm.rename, LTm.cps, GTm.rename, ih₁, ih₂, GTm.rename_rename]; rfl
  | box t ih => simp only [LTm.rename, LTm.cps, GTm.rename, ih, GTm.rename_rename]; rfl
  | letbox t₁ t₂ ih₁ ih₂ =>
    simp only [LTm.rename, LTm.cps, GTm.rename, ih₁, ih₂, GTm.rename_rename, cps_ren_aux₁]; rfl
  | pair h => exact absurd h (by decide)
  | letpair h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | letunit h => exact absurd h (by decide)
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)
  | case h => exact absurd h (by decide)
  | pushProd h => exact absurd h (by decide)
  | pushSum h => exact absurd h (by decide)
  | pushUnit h => exact absurd h (by decide)

/-- `⦇x⦈ = λk. x k ≡_η x`. -/
lemma cps_var_eq {n : ℕ} (i : Fin n) : GEq (LTm.var i : LTm .base n).cps (GTm.var i) :=
  .ax (.eta (GTm.var i))

lemma cps_upSub_rel {n m : ℕ} {σ : Fin n → LTm .base m} {τ : Fin n → GTm .base m}
    (h : ∀ i, GEq (σ i).cps (τ i)) (i : Fin (n + 1)) :
    GEq (LTm.upSub σ i).cps (GTm.upSub τ i) := by
  refine Fin.cases (cps_var_eq 0) (fun j => ?_) i
  show GEq (LTm.rename Fin.succ (σ j)).cps (GTm.rename Fin.succ (τ j))
  rw [LTm.cps_rename]; exact (h j).rename _

/-- **Lemma (interpretation preserves substitution, up to `≡`)**: if `⦇σ x⦈ ≡ τ x` for all `x`,
then `⦇t[σ]⦈ ≡ ⦇t⦈[τ]`. -/
theorem LTm.cps_subst {n m : ℕ} (t : LTm .base n) {σ : Fin n → LTm .base m}
    {τ : Fin n → GTm .base m} (h : ∀ i, GEq (σ i).cps (τ i)) :
    GEq (t.subst σ).cps (t.cps.subst τ) := by
  induction t generalizing m with
  | var i => exact (h i).trans (.symm (.ax (.eta (τ i))))
  | lam t ih =>
    have := (ih (cps_upSub_rel h)).rename (upRen Fin.succ)
    rw [GTm.rename_subst_comm _ (ρ := upRen Fin.succ) (σ' := GTm.upSub (GTm.upSub τ))
      (fun i => Fin.cases rfl (fun j => GTm.rename_shift _ _) i)] at this
    exact .lam (.app (.refl _) (.lam this))
  | app t₁ t₂ ih₁ ih₂ =>
    have h₁ := (ih₁ h).rename Fin.succ
    have h₂ := (ih₂ h).rename (Fin.succ ∘ Fin.succ)
    rw [GTm.rename_subst_comm _ (ρ := Fin.succ) (σ' := GTm.upSub τ) (fun i => rfl)] at h₁
    rw [GTm.rename_subst_comm _ (ρ := Fin.succ ∘ Fin.succ) (σ' := GTm.upSub (GTm.upSub τ))
      (fun i => (GTm.rename_rename _ _ _).symm)] at h₂
    exact .lam (.app h₁ (.lam (.app (.app (.refl _) h₂) (.refl _))))
  | box t ih =>
    have h₁ := (ih h).rename Fin.succ
    rw [GTm.rename_subst_comm _ (ρ := Fin.succ) (σ' := GTm.upSub τ) (fun i => rfl)] at h₁
    exact .lam (.app (.refl _) h₁)
  | letbox t₁ t₂ ih₁ ih₂ =>
    have h₁ := (ih₁ h).rename Fin.succ
    rw [GTm.rename_subst_comm _ (ρ := Fin.succ) (σ' := GTm.upSub τ) (fun i => rfl)] at h₁
    have h₂ := (ih₂ (cps_upSub_rel h)).rename (upRen Fin.succ)
    rw [GTm.rename_subst_comm _ (ρ := upRen Fin.succ) (σ' := GTm.upSub (GTm.upSub τ))
      (fun i => Fin.cases rfl (fun j => GTm.rename_shift _ _) i)] at h₂
    exact .lam (.app h₁ (.lam (.app h₂ (.refl _))))
  | pair hc => exact absurd hc (by decide)
  | letpair hc => exact absurd hc (by decide)
  | unit hc => exact absurd hc (by decide)
  | letunit hc => exact absurd hc (by decide)
  | inl hc => exact absurd hc (by decide)
  | inr hc => exact absurd hc (by decide)
  | case hc => exact absurd hc (by decide)
  | pushProd hc => exact absurd hc (by decide)
  | pushSum hc => exact absurd hc (by decide)
  | pushUnit hc => exact absurd hc (by decide)

lemma LTm.cps_subst1 {n : ℕ} (t : LTm .base (n + 1)) (s : LTm .base n) :
    GEq (t.subst1 s).cps (t.cps.subst1 s.cps) :=
  LTm.cps_subst t (fun i => Fin.cases (.refl _) (fun j => cps_var_eq j) i)

/-! ## Operational correspondence -/

lemma GSteps.of_eq {F : GLevel} {b : Prop} {n : ℕ} {t t' : GTm F n} (h : t = t') :
    GSteps b t t' := h ▸ .refl

/-- The common shape of the result of simulating a β-step: `λk. ⦇t⦈[⦇s⦈/x] k`. -/
lemma cps_beta_shape {n : ℕ} (t : LTm .base (n + 1)) (s : LTm .base n) :
    GEq (t.subst1 s).cps (.lam (.app (GTm.shift (t.cps.subst1 s.cps)) (.var 0))) :=
  (LTm.cps_subst1 t s).trans (.symm (.ax (.eta _)))

lemma cps_beta_steps {n : ℕ} (t₂ : LTm .base (n + 1)) (t₁ : LTm .base n) :
    GSteps True (LTm.app (.lam t₂) t₁).cps
      (.lam (.app (GTm.shift (t₂.cps.subst1 t₁.cps)) (.var 0))) := by
  refine .head (GStep.congAbs trivial (GStep.beta _ _)) ?_
  refine .head (GStep.congAbs trivial (GStep.beta _ _)) ?_
  refine .head (GStep.congAbs trivial (GStep.congAppL _ (GStep.beta _ _))) ?_
  convert Relation.ReflTransGen.refl using 3
  simp only [GTm.shift, GTm.subst1, GTm.rename_subst, GTm.subst_rename, GTm.rename_rename,
    GTm.subst_subst]
  congr 1; funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (GTm.rename_eq_subst _ _).trans (congrArg (fun σ => GTm.subst σ t₁.cps) (funext fun j => rfl))
  · rfl

lemma cps_betaBox_steps {n : ℕ} (t₁ : LTm .base n) (t₂ : LTm .base (n + 1)) :
    GSteps True (LTm.letbox (.box t₁) t₂).cps
      (.lam (.app (GTm.shift (t₂.cps.subst1 t₁.cps)) (.var 0))) := by
  refine .head (GStep.congAbs trivial (GStep.beta _ _)) ?_
  refine .head (GStep.congAbs trivial (GStep.beta _ _)) ?_
  apply GSteps.of_eq
  simp only [GTm.subst, GTm.shift, GTm.subst1, GTm.rename_subst, GTm.subst_rename,
    GTm.rename_rename]
  congr 2
  · congr 1; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((GTm.rename_eq_subst _ _).trans
        (congrArg (fun σ => GTm.subst σ t₁.cps) (funext fun j => rfl))).symm
    · rfl

/-- **Theorem 2.7 (operational correspondence)** of the CPS translation, in the form proved in
the paper's appendix: if `t ⇝_L t'` then `⦇t⦈` reduces with full β-reduction (including under
`λ`) to a term `t''` with `⦇t'⦈ ≡_G t''`. -/
theorem LStep.cps {n : ℕ} {t t' : LTm .base n} (h : LStep t t') :
    ∃ t'', GSteps True t.cps t'' ∧ GEq t'.cps t'' := by
  induction h with
  | beta t₂ t₁ => exact ⟨_, cps_beta_steps t₂ t₁, cps_beta_shape t₂ t₁⟩
  | betaBox t₁ t₂ => exact ⟨_, cps_betaBox_steps t₁ t₂, cps_beta_shape t₂ t₁⟩
  | congAppL t₂ _ ih =>
    obtain ⟨s, hs, he⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.lam (GTm.app (x.rename Fin.succ) _))
      (fun h => .congAbs trivial (.congAppL _ (h.rename _))) hs, .lam (.app (he.rename _) (.refl _))⟩
  | congLetL t₂ _ ih =>
    obtain ⟨s, hs, he⟩ := ih
    exact ⟨_, GSteps.lift (fun x => GTm.lam (GTm.app (x.rename Fin.succ) _))
      (fun h => .congAbs trivial (.congAppL _ (h.rename _))) hs, .lam (.app (he.rename _) (.refl _))⟩
  | prodCong h => exact absurd h (by decide)
  | prodBeta h => exact absurd h (by decide)
  | unitCong h => exact absurd h (by decide)
  | unitBeta h => exact absurd h (by decide)
  | congCase h => exact absurd h (by decide)
  | caseInl h => exact absurd h (by decide)
  | caseInr h => exact absurd h (by decide)
  | pushProdCong h => exact absurd h (by decide)
  | pushProdBoxCong h => exact absurd h (by decide)
  | pushProd h => exact absurd h (by decide)
  | pushSumCong h => exact absurd h (by decide)
  | pushSumBoxCong h => exact absurd h (by decide)
  | pushSumInl h => exact absurd h (by decide)
  | pushSumInr h => exact absurd h (by decide)
  | pushUnitCong h => exact absurd h (by decide)
  | pushUnitBoxCong h => exact absurd h (by decide)
  | pushUnit h => exact absurd h (by decide)

/-! ## Equation preservation -/

/-- The theory `≡_L^{β→βη□}`: all axioms except `η` for functions and the commuting
conversions. -/
def LAxSel.cps : LAxSel := { eta := False, letComm := False }

/-- `⦇let [x] = t in [x]⦈ ≡_G ⦇t⦈`. -/
lemma cps_etaBox {n : ℕ} (t : LTm .base n) : GEq (LTm.letbox t (.box (.var 0))).cps t.cps := by
  have e₁ : GEq (GTm.app ((LTm.box (LTm.var 0) : LTm .base (n + 1)).cps.rename (upRen Fin.succ))
      (GTm.var 1)) (GTm.app (GTm.var (Fin.succ 0)) (GTm.var 0)) :=
    (GCong.ax (GAxF.beta _ _)).trans (GCong.app (.refl _) (GCong.ax (GAxF.eta (GTm.var 0))))
  exact (GCong.lam (GCong.app (.refl _) ((GCong.lam e₁).trans (.ax (GAxF.eta (F := .base) (GTm.var (0 : Fin (n + 1)))))))).trans
    (.ax (.eta t.cps))

/-- The axioms of `≡_L^{β→βη□}` are preserved by the CPS translation. -/
theorem LAxF.cps {n : ℕ} {t t' : LTm .base n} (h : LAxF LAxSel.cps t t') : GEq t.cps t'.cps := by
  cases h with
  | beta t₂ t₁ =>
    obtain ⟨_, hs, he⟩ := (LStep.beta t₂ t₁).cps; exact hs.toGEq.trans he.symm
  | betaBox t₁ t₂ =>
    obtain ⟨_, hs, he⟩ := (LStep.betaBox t₁ t₂).cps; exact hs.toGEq.trans he.symm
  | etaBox => exact cps_etaBox _
  | eta he => exact False.elim he
  | letCommOne he => exact False.elim he
  | letCommTwo he => exact False.elim he
  | letCommBox he => exact False.elim he
  | betaUnit h => exact absurd h (by decide)
  | etaUnit h => exact absurd h (by decide)
  | betaProd h => exact absurd h (by decide)
  | etaProd h => exact absurd h (by decide)
  | betaSumOne h => exact absurd h (by decide)
  | betaSumTwo h => exact absurd h (by decide)
  | etaSum h => exact absurd h (by decide)
  | pushProdBeta h => exact absurd h (by decide)
  | pushProdEta _ h => exact absurd h (by decide)
  | pushSumBetaOne h => exact absurd h (by decide)
  | pushSumBetaTwo h => exact absurd h (by decide)
  | pushSumEta _ h => exact absurd h (by decide)
  | pushUnitBeta h => exact absurd h (by decide)

/-- **Theorem 2.7 (equation preservation)** of the CPS translation:
`t ≡_L^{β→βη□} t' ⟹ ⦇t⦈ ≡_G ⦇t'⦈`. -/
theorem LCong.cps {n : ℕ} {t t' : LTm .base n} (h : LCong (LAxF LAxSel.cps) t t') :
    GEq t.cps t'.cps := by
  induction h with
  | ax h => exact h.cps
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ =>
    exact .lam (.app (ih₁.rename _) (.lam (.app (.app (.refl _) (ih₂.rename _)) (.refl _))))
  | lam _ ih => exact .lam (.app (.refl _) (.lam (ih.rename _)))
  | box _ ih => exact .lam (.app (.refl _) (ih.rename _))
  | letbox _ _ ih₁ ih₂ => exact .lam (.app (ih₁.rename _) (.lam (.app (ih₂.rename _) (.refl _))))
  | pair h => exact absurd h (by decide)
  | letpair h => exact absurd h (by decide)
  | letunit h => exact absurd h (by decide)
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)
  | case h => exact absurd h (by decide)
  | pushProd h => exact absurd h (by decide)
  | pushSum h => exact absurd h (by decide)
  | pushUnit h => exact absurd h (by decide)

end Coeffect
