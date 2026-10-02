module

public import RequestProject.Sec2.LinearTyping
public import RequestProject.Sec2.LinearSemantics
public import RequestProject.Sec2.GradedTyping
public import RequestProject.Sec2.GradedSemantics

/-!
# The translation `⟦-⟧` from the graded-base lineage to the linear-base lineage

This is the translation of Section 2.3.1 (Graded Base → Linear Base), extended in Section 3.2.3
to Graded Modal Base → Linear Base and in Section 5.5 to Graded Modal Core → Linear Push Core.
Since we present each lineage as one level-indexed grammar, we define the translation once,
for every level; it maps

* Graded Base (`GLevel.base`) and Graded Modal Base (`GLevel.modal`) to Linear Base, and
* Graded Modal Core (`GLevel.core`) to Linear Push Core.

```
⟦x⟧ = x        ⟦λx.t⟧ = λy. let [x] = y in ⟦t⟧       ⟦t₁ t₂⟧ = ⟦t₁⟧ [⟦t₂⟧]
⟦[t]⟧ = [⟦t⟧]   ⟦let [x] = t₁ in t₂⟧ = let [x] = ⟦t₁⟧ in ⟦t₂⟧
⟦let ⟨x, y⟩ = t₁ in t₂⟧ = let ⟨x', y'⟩ = push⊗ [⟦t₁⟧] in let [x] = x' in let [y] = y' in ⟦t₂⟧
⟦case t of ...⟧ = case push⊕ [⟦t⟧] of {inj₁ x' → let [x] = x' in ⟦t₁⟧; inj₂ y' → ...}
⟦let ⟨⟩ = t₁ in t₂⟧ = let ⟨⟩ = push_unit [⟦t₁⟧] in ⟦t₂⟧
⟦A →^r B⟧ = □_r ⟦A⟧ ⊸ ⟦B⟧        ⟦x :_r A⟧ = x : [⟦A⟧]_r
```
-/

@[expose] public section

namespace Coeffect

universe u

/-- The target linear-base calculus of a graded-base calculus. -/
def GLevel.toL : GLevel → LLevel
  | .base => .base
  | .modal => .base
  | .core => .push

lemma GLevel.toL_core {F : GLevel} (h : F.Core = true) : F.toL.Core = true := by
  cases F <;> simp_all [GLevel.Core, GLevel.toL, LLevel.Core]

lemma GLevel.toL_push {F : GLevel} (h : F.Core = true) : F.toL.Push = true := by
  cases F <;> simp_all [GLevel.Core, GLevel.toL, LLevel.Push]

variable {R : Type u} {F : GLevel}

/-- Type translation `⟦A⟧`. -/
def GTy.toL : GTy R F → LTy R F.toL
  | .base => .base
  | .fn r A B => .lolli (.box r A.toL) B.toL
  | .box _ r A => .box r A.toL
  | .prod h A B => .tensor (GLevel.toL_core h) A.toL B.toL
  | .unit h => .unit (GLevel.toL_core h)
  | .sum h A B => .oplus (GLevel.toL_core h) A.toL B.toL

/-- Term translation `⟦t⟧`. -/
def GTm.toL {n : ℕ} : GTm F n → LTm F.toL n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.toL (.box t₂.toL)
  | .lam t => .lam (.letbox (.var 0) (t.toL.rename (upRen Fin.succ)))
  | .box _ t => .box t.toL
  | .letbox _ t₁ t₂ => .letbox t₁.toL t₂.toL
  | .pair h t₁ t₂ => .pair (GLevel.toL_core h) t₁.toL t₂.toL
  | .letpair h t₁ t₂ =>
      .letpair (GLevel.toL_core h) (.pushProd (GLevel.toL_push h) (.box t₁.toL))
        (.letbox (.var 1) (.letbox (.var 1)
          (t₂.toL.rename (upRen (upRen (Fin.succ ∘ Fin.succ))))))
  | .unit h => .unit (GLevel.toL_core h)
  | .letunit h t₁ t₂ => .letunit (GLevel.toL_core h) (.pushUnit (GLevel.toL_push h) (.box t₁.toL))
      t₂.toL
  | .inl h t => .inl (GLevel.toL_core h) t.toL
  | .inr h t => .inr (GLevel.toL_core h) t.toL
  | .case h t t₁ t₂ =>
      .case (GLevel.toL_core h) (.pushSum (GLevel.toL_push h) (.box t.toL))
        (.letbox (.var 0) (t₁.toL.rename (upRen Fin.succ)))
        (.letbox (.var 0) (t₂.toL.rename (upRen Fin.succ)))

/-- Context translation, types: `⟦Δ⟧`. -/
def toLCtx {n : ℕ} (Γ : Fin n → GTy R F) : Fin n → LTy R F.toL := fun i => (Γ i).toL

/-- Context translation, grades: every assumption becomes a graded assumption `[⟦A⟧]_r`. -/
def grdU {n : ℕ} (δ : Fin n → R) : Fin n → Use R := fun i => Use.grd (δ i)

lemma toLCtx_cons {n : ℕ} (A : GTy R F) (Γ : Fin n → GTy R F) :
    toLCtx (A .: Γ) = A.toL .: toLCtx Γ := scons_map _ _ _

lemma grdU_cons {n : ℕ} (r : R) (δ : Fin n → R) : grdU (r .: δ) = Use.grd r .: grdU δ :=
  scons_map _ _ _

lemma off_upRen_succ {n : ℕ} {j : Fin (n + 2)} (hj : ∀ i, upRen Fin.succ i ≠ j) : j = 1 := by
  refine Fin.cases (fun hj => absurd rfl (hj 0)) (fun j hj => ?_) j hj
  refine Fin.cases (fun _ => rfl) (fun k hk => absurd rfl (hk k.succ)) j hj

lemma off_upRen_upRen_succ_succ {n : ℕ} {j : Fin (n + 4)}
    (hj : ∀ i, upRen (upRen (Fin.succ ∘ Fin.succ)) i ≠ j) : j = 2 ∨ j = 3 := by
  refine Fin.cases (fun hj => absurd rfl (hj 0)) (fun j hj => ?_) j hj
  refine Fin.cases (fun hj => absurd rfl (hj 1)) (fun j hj => ?_) j hj
  refine Fin.cases (fun _ => Or.inl rfl) (fun j hj => ?_) j hj
  refine Fin.cases (fun _ => Or.inr rfl) (fun k hk => absurd rfl (hk k.succ.succ)) j hj

variable [PreorderedSemiring R]

/-- The body `let [x] = y in ⟦t⟧` shared by abstraction and `case` branches. -/
lemma typed_unbox_body {n : ℕ} {Γ : Fin n → LTy R F.toL} {u : Fin n → Use R}
    {t : LTm F.toL (n + 1)} {r : R} {A B : LTy R F.toL}
    (h : LTyped (A .: Γ) (Use.grd r .: u) t B) :
    LTyped (LTy.box r A .: Γ) (Use.lin .: u) (.letbox (.var 0) (t.rename (upRen Fin.succ))) B := by
  refine LTyped.letbox (u₁ := Use.lin .: emptyU) (u₂ := Use.none .: u)
    (LTyped.var' 0 Use.only_zero.symm rfl) ?_ (CtxAdd.cons (.noneRight _) (CtxAdd.emptyLeft _))
  refine h.rename (upRen Fin.succ) (upRen_injective (Fin.succ_injective _)) _ ?_ _ ?_ ?_
  · intro i; refine Fin.cases ?_ ?_ i <;> simp
  · intro i; refine Fin.cases ?_ ?_ i <;> simp
  · intro j hj; rw [off_upRen_succ hj]; simp

/-- **Theorem 2.5 / 3.2 / 5.1 (type preservation).**
`Δ ⊢_G t : A ⟹ ⟦Δ⟧ ⊢_L ⟦t⟧ : ⟦A⟧`. -/
theorem GTyped.toL {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n} {A : GTy R F}
    (h : GTyped Γ δ t A) : LTyped (toLCtx Γ) (grdU δ) t.toL A.toL := by
  induction h with
  | var Γ i => exact LTyped.var_grd _ i
  | abs _ ih =>
    rw [toLCtx_cons, grdU_cons] at ih
    exact LTyped.abs (typed_unbox_body ih)
  | @app _ _ δ₁ δ₂ _ _ r _ _ _ _ ih₁ ih₂ =>
    exact LTyped.app ih₁ ((LTyped.pr r ih₂ (Graded.grd δ₂)).cast (smulCtx_grd r δ₂))
      (CtxAdd.grd _ _)
  | @approx _ _ δ _ _ i s _ hi ih =>
    have e : Function.update (grdU δ) i (Use.grd s) = grdU (Function.update δ i s) := by
      funext j; by_cases hj : j = i
      · subst hj; simp [grdU]
      · simp [grdU, Function.update_of_ne hj]
    exact (LTyped.approx i ih rfl hi).cast e
  | @pr _ _ δ _ _ h r _ ih =>
    exact (LTyped.pr r ih (Graded.grd δ)).cast (smulCtx_grd r δ)
  | letbox h _ _ ih₁ ih₂ =>
    rw [toLCtx_cons, grdU_cons] at ih₂
    exact LTyped.letbox ih₁ ih₂ (CtxAdd.grd _ _)
  | pair h _ _ ih₁ ih₂ => exact LTyped.pair _ ih₁ ih₂ (CtxAdd.grd _ _)
  | @letpair _ _ δ₁ δ₂ _ _ r A B _ h _ _ ih₁ ih₂ =>
    rw [toLCtx_cons, toLCtx_cons, grdU_cons, grdU_cons] at ih₂
    refine LTyped.letpair _ (LTyped.pushProd _ _
      ((LTyped.pr r ih₁ (Graded.grd δ₁)).cast (smulCtx_grd r δ₁))) ?_ (CtxAdd.grd _ _)
    -- `let [x] = x' in let [y] = y' in ⟦t₂⟧`
    refine LTyped.letbox (u₁ := Use.none .: Use.lin .: emptyU)
      (u₂ := Use.lin .: Use.none .: grdU δ₂) (LTyped.var' 1 Use.only_one.symm rfl) ?_
      (CtxAdd.cons (.noneLeft _) (CtxAdd.cons (.noneRight _) (CtxAdd.emptyLeft _)))
    refine LTyped.letbox (u₁ := Use.none .: Use.lin .: emptyU)
      (u₂ := Use.grd r .: Use.none .: Use.none .: grdU δ₂) (LTyped.var' 1 Use.only_one.symm rfl) ?_
      (CtxAdd.cons (.noneLeft _) (CtxAdd.cons (.noneRight _) (CtxAdd.emptyLeft _)))
    refine ih₂.rename _ (upRen_injective (upRen_injective
      ((Fin.succ_injective _).comp (Fin.succ_injective _)))) _ ?_ _ ?_ ?_
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · refine Fin.cases ?_ ?_ i <;> simp
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · refine Fin.cases ?_ ?_ i <;> simp
    · intro j hj
      rcases off_upRen_upRen_succ_succ hj with rfl | rfl <;> rfl
  | unit h =>
    refine (LTyped.unit (Γ := toLCtx _) (GLevel.toL_core h)).weak_many _ (fun j => ?_)
    right; exact ⟨rfl, rfl⟩
  | @letunit _ _ δ₁ δ₂ _ _ _ h r _ _ ih₁ ih₂ =>
    exact LTyped.letunit _ (LTyped.pushUnit _ _
      ((LTyped.pr r ih₁ (Graded.grd δ₁)).cast (smulCtx_grd r δ₁))) ih₂ (CtxAdd.grd _ _)
  | inl h _ ih => exact LTyped.inl _ ih
  | inr h _ ih => exact LTyped.inr _ ih
  | @case _ _ δ₁ δ₂ _ _ _ r A B _ h _ _ _ hr ih ih₁ ih₂ =>
    rw [toLCtx_cons, grdU_cons] at ih₁ ih₂
    exact LTyped.case _ (LTyped.pushSum _ _ hr
      ((LTyped.pr r ih (Graded.grd δ₁)).cast (smulCtx_grd r δ₁)))
      (typed_unbox_body ih₁) (typed_unbox_body ih₂) (CtxAdd.grd _ _)

end Coeffect

/-! ## Operational correspondence -/

namespace Coeffect

universe v
variable {R : Type v} {F : GLevel}

open LTm in
theorem GTm.toL_rename {n m : ℕ} (t : GTm F n) (ρ : Fin n → Fin m) :
    (t.rename ρ).toL = t.toL.rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | app _ _ ih₁ ih₂ => simp [GTm.rename, GTm.toL, LTm.rename, ih₁, ih₂]
  | lam t ih =>
    simp only [GTm.rename, GTm.toL, LTm.rename, ih, LTm.rename_rename, upRen_comp]
    rfl
  | box _ _ ih => simp [GTm.rename, GTm.toL, LTm.rename, ih]
  | letbox _ _ _ ih₁ ih₂ => simp [GTm.rename, GTm.toL, LTm.rename, ih₁, ih₂]
  | pair _ _ _ ih₁ ih₂ => simp [GTm.rename, GTm.toL, LTm.rename, ih₁, ih₂]
  | letpair _ _ _ ih₁ ih₂ =>
    simp only [GTm.rename, GTm.toL, LTm.rename, ih₁, ih₂, LTm.rename_rename, upRen_comp]
    rfl
  | unit _ => rfl
  | letunit _ _ _ ih₁ ih₂ => simp [GTm.rename, GTm.toL, LTm.rename, ih₁, ih₂]
  | inl _ _ ih => simp [GTm.rename, GTm.toL, LTm.rename, ih]
  | inr _ _ ih => simp [GTm.rename, GTm.toL, LTm.rename, ih]
  | case _ _ _ _ ih ih₁ ih₂ =>
    simp only [GTm.rename, GTm.toL, LTm.rename, ih, ih₁, ih₂, LTm.rename_rename, upRen_comp]
    rfl

lemma GTm.toL_upSub {n m : ℕ} (σ : Fin n → GTm F m) :
    (fun i => (GTm.upSub σ i).toL) = LTm.upSub (fun i => (σ i).toL) := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  simp [GTm.toL_rename]

/-- `⟦-⟧` commutes with substitution. -/
theorem GTm.toL_subst {n m : ℕ} (t : GTm F n) (σ : Fin n → GTm F m) :
    (t.subst σ).toL = t.toL.subst (fun i => (σ i).toL) := by
  induction t generalizing m with
  | var i => rfl
  | app _ _ ih₁ ih₂ => simp [GTm.subst, GTm.toL, LTm.subst, ih₁, ih₂]
  | lam t ih =>
    simp only [GTm.subst, GTm.toL, LTm.subst, ih, GTm.toL_upSub, LTm.rename_subst,
      LTm.subst_rename]
    congr 3
    funext i; refine Fin.cases rfl (fun i => ?_) i
    simp [LTm.rename_rename]; rfl
  | box _ _ ih => simp [GTm.subst, GTm.toL, LTm.subst, ih]
  | letbox _ _ _ ih₁ ih₂ => simp [GTm.subst, GTm.toL, LTm.subst, ih₁, ih₂, GTm.toL_upSub]
  | pair _ _ _ ih₁ ih₂ => simp [GTm.subst, GTm.toL, LTm.subst, ih₁, ih₂]
  | letpair _ _ _ ih₁ ih₂ =>
    simp only [GTm.subst, GTm.toL, LTm.subst, ih₁, ih₂, GTm.toL_upSub, LTm.rename_subst,
      LTm.subst_rename]
    congr 4
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    simp [LTm.rename_rename]; rfl
  | unit _ => rfl
  | letunit _ _ _ ih₁ ih₂ => simp [GTm.subst, GTm.toL, LTm.subst, ih₁, ih₂]
  | inl _ _ ih => simp [GTm.subst, GTm.toL, LTm.subst, ih]
  | inr _ _ ih => simp [GTm.subst, GTm.toL, LTm.subst, ih]
  | case _ _ _ _ ih ih₁ ih₂ =>
    simp only [GTm.subst, GTm.toL, LTm.subst, ih, ih₁, ih₂, GTm.toL_upSub, LTm.rename_subst,
      LTm.subst_rename]
    congr 3 <;>
    · funext i; refine Fin.cases rfl (fun i => ?_) i
      simp [LTm.rename_rename]; rfl

lemma GTm.toL_subst1 {n : ℕ} (t : GTm F (n + 1)) (s : GTm F n) :
    (t.subst1 s).toL = t.toL.subst1 s.toL := by
  rw [GTm.toL_subst]; congr 1; funext i; refine Fin.cases rfl (fun i => rfl) i

lemma GTm.toL_subst2 {n : ℕ} (t : GTm F (n + 2)) (s₁ s₂ : GTm F n) :
    (t.subst2 s₁ s₂).toL = t.toL.subst2 s₁.toL s₂.toL := by
  rw [GTm.toL_subst]; congr 1; funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

/-- `let [x] = [s] in ⟦t⟧` (after the abstraction translation) reduces to `[s/x]⟦t⟧`. -/
lemma unbox_body_subst {L : LLevel} {n : ℕ} (T : LTm L (n + 1)) (S : LTm L n) :
    (LTm.letbox (LTm.var 0) (T.rename (upRen Fin.succ))).subst1 (LTm.box S) =
      LTm.letbox (LTm.box S) T := by
  simp only [LTm.subst, LTm.subst_rename]
  congr 1
  conv_rhs => rw [← LTm.subst_var T]
  congr 1; funext i; refine Fin.cases rfl (fun i => ?_) i
  simp [LTm.rename]

lemma letpair_body_subst {L : LLevel} {n : ℕ} (T : LTm L (n + 2)) (S₁ S₂ : LTm L n) :
    ((LTm.upSub (S₂.box .: S₁.box .: LTm.var) 1).letbox
      (LTm.subst (LTm.upSub (LTm.upSub (S₂.box .: S₁.box .: LTm.var)))
        (LTm.rename (upRen (upRen (Fin.succ ∘ Fin.succ))) T))).subst1 S₁ =
      LTm.letbox S₂.box (T.subst (LTm.upSub (S₁ .: LTm.var))) := by
  simp only [LTm.subst, LTm.subst_rename, LTm.subst_subst]
  congr 1
  · simp [LTm.subst1_shift, LTm.rename, LTm.subst]
  · congr 1; funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => ?_) i) i
    simp [LTm.rename, LTm.subst]

lemma subst1_upSub_scons {L : LLevel} {n : ℕ} (T : LTm L (n + 2)) (S₁ S₂ : LTm L n) :
    (T.subst (LTm.upSub (S₁ .: LTm.var))).subst1 S₂ = T.subst2 S₁ S₂ := by
  simp only [LTm.subst_subst]
  congr 1; funext i
  refine Fin.cases rfl (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [LTm.subst1_shift]
  · simp [LTm.rename, LTm.subst]

lemma LSteps.lift {L : LLevel} {n m : ℕ} (f : LTm L n → LTm L m)
    (hf : ∀ {a b}, LStep a b → LStep (f a) (f b)) {a b : LTm L n} (h : LSteps a b) :
    LSteps (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (hf h)

/-- **Theorem 2.5 / 3.2 / 5.1 (operational correspondence).**
`t ⇝_G t' ⟹ ⟦t⟧ ⇝_L* ⟦t'⟧`. -/
theorem GStep.toL {n : ℕ} {t t' : GTm F n} (h : GStep false t t') : LSteps t.toL t'.toL := by
  induction h with
  | beta t₂ t₁ =>
    simp only [GTm.toL, GTm.toL_subst1]
    refine .tail (.single (LStep.beta _ _)) ?_
    rw [unbox_body_subst]; exact LStep.betaBox _ _
  | congAppL _ _ ih => exact LSteps.lift (fun a => LTm.app a _) (fun h => .congAppL _ h) ih
  | congAbs hb => exact absurd hb (by decide)
  | betaBox h t₁ t₂ =>
    simp only [GTm.toL, GTm.toL_subst1]; exact .single (LStep.betaBox _ _)
  | congLetL _ _ _ ih => exact LSteps.lift (fun a => LTm.letbox a _) (fun h => .congLetL _ h) ih
  | prodCong h _ _ ih =>
    exact LSteps.lift (fun a => LTm.letpair _ (LTm.pushProd _ (LTm.box a)) _)
      (fun h => .prodCong _ _ (.pushProdBoxCong _ h)) ih
  | prodBeta h t₁ t₂ t₃ =>
    simp only [GTm.toL, GTm.toL_subst2]
    refine (Relation.ReflTransGen.single (LStep.prodCong _ _ (LStep.pushProd _ _ _ _))).trans ?_
    refine (Relation.ReflTransGen.single (LStep.prodBeta _ _ _ _)).trans ?_
    simp only [LTm.subst]
    refine (Relation.ReflTransGen.single (LStep.betaBox _ _)).trans ?_
    rw [letpair_body_subst, ← subst1_upSub_scons]
    exact .single (LStep.betaBox _ _)
  | unitCong h _ _ ih =>
    exact LSteps.lift (fun a => LTm.letunit _ (LTm.pushUnit _ (LTm.box a)) _)
      (fun h => .unitCong _ _ (.pushUnitBoxCong _ h)) ih
  | unitBeta h t₂ =>
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single
      (LStep.unitCong (GLevel.toL_core h) t₂.toL
        (LStep.pushUnit (GLevel.toL_push h) (GLevel.toL_core h)))) (LStep.unitBeta _ _)
  | congCase h _ _ _ ih =>
    exact LSteps.lift (fun a => LTm.case _ (LTm.pushSum _ (LTm.box a)) _ _)
      (fun h => .congCase _ _ _ (.pushSumBoxCong _ h)) ih
  | caseInl h t t₁ t₂ =>
    simp only [GTm.toL, GTm.toL_subst1]
    refine .tail (.tail (.single (LStep.congCase _ _ _ (LStep.pushSumInl _ _ _)))
      (LStep.caseInl _ _ _ _)) ?_
    rw [unbox_body_subst]; exact LStep.betaBox _ _
  | caseInr h t t₁ t₂ =>
    simp only [GTm.toL, GTm.toL_subst1]
    refine .tail (.tail (.single (LStep.congCase _ _ _ (LStep.pushSumInr _ _ _)))
      (LStep.caseInr _ _ _ _)) ?_
    rw [unbox_body_subst]; exact LStep.betaBox _ _

end Coeffect

/-! ## Equation preservation -/

namespace Coeffect

variable {F : GLevel}

open LTm in
/-- The `λz.[z]` trick of Appendix B: `[let [x] = t₁ in t₂] ≡_L let [x] = t₁ in [t₂]`. -/
lemma LEq.box_letbox {L : LLevel} {n : ℕ} (T₁ : LTm L n) (T₂ : LTm L (n + 1)) :
    LEq (box (letbox T₁ T₂)) (letbox T₁ (box T₂)) := by
  have e1 : LEq (app (lam (box (var 0))) (letbox T₁ T₂)) (box (letbox T₁ T₂)) :=
    .ax (.beta (box (var 0)) _)
  have e2 : LEq (app (lam (box (var 0))) (letbox T₁ T₂))
      (letbox T₁ (app (lam (box (var 0))) T₂)) := .ax (.letCommOne rfl _ _ _)
  have e3 : LEq (app (lam (box (var 0))) T₂) (box T₂) := .ax (.beta (box (var 0)) _)
  exact .trans (.symm e1) (.trans e2 (.letbox (.refl _) e3))

open LTm in
/-- Each axiom of `≡_G^{-η⊗⊕}` is preserved by `⟦-⟧`. -/
theorem GAxF.toL {n : ℕ} {t t' : GTm F n} (h : GAxF false t t') : LEq t.toL t'.toL := by
  cases h with
  | beta a b => exact (GStep.beta (underLam := false) a b).toL.toLEq
  | eta =>
    simp only [GTm.toL, GTm.toL_rename, LTm.rename, rename_rename]
    have e1 : LEq (letbox (var 0) (app (shift (shift t'.toL)) (box (var 0))))
        (app (shift t'.toL) (var 0)) :=
      .trans (.symm (.ax (.letCommOne rfl (shift t'.toL) (var 0) (box (var 0)))))
        (.app (.refl _) (.ax (.etaBox rfl _)))
    have e2 := LCong.trans (LCong.lam e1) (LCong.ax (LAxF.eta rfl t'.toL))
    simpa only [LTm.rename_rename] using e2
  | betaBox h a b => exact (GStep.betaBox (underLam := false) h a b).toL.toLEq
  | etaBox h s => exact .ax (.etaBox rfl _)
  | letCommOne h a b c =>
    simp only [GTm.toL, GTm.toL_rename]
    exact .trans (.app (.refl _) (LEq.box_letbox _ _)) (.ax (.letCommOne rfl _ _ _))
  | letCommTwo h a b c =>
    simp only [GTm.toL, GTm.toL_rename]
    exact .ax (.letCommTwo rfl _ _ _)
  | letCommBox h a b => exact .ax (.letCommBox rfl _ _)
  | betaUnit h => exact (GStep.unitBeta (underLam := false) h t').toL.toLEq
  | etaUnit h s => exact .ax (.etaUnit _ _)
  | betaProd h a b c => exact (GStep.prodBeta (underLam := false) h a b c).toL.toLEq
  | etaProd he h s => exact absurd he (by decide)
  | betaSumOne h a b c => exact (GStep.caseInl (underLam := false) h a b c).toL.toLEq
  | betaSumTwo h a b c => exact (GStep.caseInr (underLam := false) h a b c).toL.toLEq
  | etaSum he h s => exact absurd he (by decide)

/-- **Theorem 2.5 / 3.2 / 5.1 (equation preservation).**
`t ≡_G^{-η⊗⊕} t' ⟹ ⟦t⟧ ≡_L ⟦t'⟧`. (The paper also excludes η for unit; it is in fact preserved.) -/
theorem GCong.toL {n : ℕ} {t t' : GTm F n} (h : GCong (GAxF false) t t') : LEq t.toL t'.toL := by
  induction h with
  | ax h => exact h.toL
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ (.box ih₂)
  | lam _ ih => exact .lam (.letbox (.refl _) (ih.rename _))
  | box h _ ih => exact .box ih
  | letbox h _ _ ih₁ ih₂ => exact .letbox ih₁ ih₂
  | pair h _ _ ih₁ ih₂ => exact .pair _ ih₁ ih₂
  | letpair h _ _ ih₁ ih₂ =>
    exact .letpair _ (.pushProd _ (.box ih₁)) (.letbox (.refl _) (.letbox (.refl _) (ih₂.rename _)))
  | letunit h _ _ ih₁ ih₂ => exact .letunit _ (.pushUnit _ (.box ih₁)) ih₂
  | inl h _ ih => exact .inl _ ih
  | inr h _ ih => exact .inr _ ih
  | case h _ _ _ ih ih₁ ih₂ =>
    exact .case _ (.pushSum _ (.box ih)) (.letbox (.refl _) (ih₁.rename _))
      (.letbox (.refl _) (ih₂.rename _))

/-- Without products and sums the η-rules for them cannot occur, so `≡_G` and `≡_G^{-η⊗⊕}` agree. -/
theorem GAxF.noEta_of_not_core {n : ℕ} (hF : F.Core = false) {t t' : GTm F n}
    (h : GAxF true t t') : GAxF false t t' := by
  cases h with
  | etaProd _ h' _ => exact absurd h' (by simp [hF])
  | etaSum _ h' _ => exact absurd h' (by simp [hF])
  | beta => exact .beta _ _
  | eta => exact .eta _
  | betaBox => exact .betaBox _ _ _
  | etaBox => exact .etaBox _ _
  | letCommOne => exact .letCommOne _ _ _ _
  | letCommTwo => exact .letCommTwo _ _ _ _
  | letCommBox => exact .letCommBox _ _ _
  | betaUnit => exact .betaUnit _ _
  | etaUnit => exact .etaUnit _ _
  | betaProd => exact .betaProd _ _ _ _
  | betaSumOne => exact .betaSumOne _ _ _ _
  | betaSumTwo => exact .betaSumTwo _ _ _ _

/-- For Graded Base and Graded Modal Base (no products/sums) the full theory `≡_G` is preserved. -/
theorem GEq.toL {n : ℕ} (hF : F.Core = false) {t t' : GTm F n} (h : GEq t t') :
    LEq t.toL t'.toL :=
  GCong.toL (h.mono (fun h => GAxF.noEta_of_not_core hF h))

end Coeffect
