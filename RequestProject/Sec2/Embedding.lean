module

public import RequestProject.Sec2.LinearTyping
public import RequestProject.Sec2.LinearSemantics
public import RequestProject.Sec2.GradedTyping
public import RequestProject.Sec2.GradedSemantics

/-!
# Inclusions between the calculi of one lineage (the dotted "subset" arrows)

`Linear Base ⊆ Linear Core ⊆ Linear Push Core` and
`Graded Base ⊆ Graded Modal Base ⊆ Graded Modal Core`.

For levels `F ≤ G` we embed types and terms of level `F` into level `G`, and show that typing
and reduction are preserved, so each smaller calculus is a sub-calculus of the bigger one.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-! ## Linear lineage -/

section linear

variable {F G : LLevel} (hFG : F ≤ G)

/-- Embedding of types along `F ≤ G`. -/
def LTy.embed : LTy R F → LTy R G
  | .base => .base
  | .lolli A B => .lolli (A.embed) (B.embed)
  | .box r A => .box r A.embed
  | .tensor h A B => .tensor (LLevel.core_mono hFG h) A.embed B.embed
  | .unit h => .unit (LLevel.core_mono hFG h)
  | .oplus h A B => .oplus (LLevel.core_mono hFG h) A.embed B.embed

/-- Embedding of terms along `F ≤ G`. -/
def LTm.embed {n : ℕ} : LTm F n → LTm G n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.embed t₂.embed
  | .lam t => .lam t.embed
  | .box t => .box t.embed
  | .letbox t₁ t₂ => .letbox t₁.embed t₂.embed
  | .pair h t₁ t₂ => .pair (LLevel.core_mono hFG h) t₁.embed t₂.embed
  | .letpair h t₁ t₂ => .letpair (LLevel.core_mono hFG h) t₁.embed t₂.embed
  | .unit h => .unit (LLevel.core_mono hFG h)
  | .letunit h t₁ t₂ => .letunit (LLevel.core_mono hFG h) t₁.embed t₂.embed
  | .inl h t => .inl (LLevel.core_mono hFG h) t.embed
  | .inr h t => .inr (LLevel.core_mono hFG h) t.embed
  | .case h t t₁ t₂ => .case (LLevel.core_mono hFG h) t.embed t₁.embed t₂.embed
  | .pushProd h t => .pushProd (LLevel.push_mono hFG h) t.embed
  | .pushSum h t => .pushSum (LLevel.push_mono hFG h) t.embed
  | .pushUnit h t => .pushUnit (LLevel.push_mono hFG h) t.embed

lemma embed_cons_ty {n : ℕ} (A : LTy R F) (Γ : Fin n → LTy R F) :
    (fun i => (A .: Γ) i |>.embed hFG) = (A.embed hFG .: fun i => (Γ i).embed hFG) := by
  funext i; exact Fin.cases rfl (fun i => rfl) i

variable [PreorderedSemiring R]

/-- Inclusion of linear-base calculi preserves typing. -/
theorem LTyped.embed {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n}
    {A : LTy R F} (h : LTyped Γ u t A) :
    LTyped (fun i => (Γ i).embed hFG) u (t.embed hFG) (A.embed hFG) := by
  induction h with
  | var Γ i => exact .var _ i
  | abs _ ih => rw [embed_cons_ty] at ih; exact .abs ih
  | app _ _ hadd ih₁ ih₂ => exact .app ih₁ ih₂ hadd
  | weak i _ hi ih => exact .weak i ih hi
  | der i _ hi ih => exact .der i ih hi
  | pr r _ hg ih => exact .pr r ih hg
  | letbox _ _ hadd ih₁ ih₂ => rw [embed_cons_ty] at ih₂; exact .letbox ih₁ ih₂ hadd
  | approx i _ hi hrs ih => exact .approx i ih hi hrs
  | pair h _ _ hadd ih₁ ih₂ => exact .pair _ ih₁ ih₂ hadd
  | letpair h _ _ hadd ih₁ ih₂ =>
    rw [embed_cons_ty, embed_cons_ty] at ih₂; exact .letpair _ ih₁ ih₂ hadd
  | unit h => exact .unit _
  | letunit h _ _ hadd ih₁ ih₂ => exact .letunit _ ih₁ ih₂ hadd
  | inl h _ ih => exact .inl _ ih
  | inr h _ ih => exact .inr _ ih
  | case h _ _ _ hadd ih ih₁ ih₂ =>
    rw [embed_cons_ty] at ih₁ ih₂; exact .case _ ih ih₁ ih₂ hadd
  | pushProd h hc _ ih => exact .pushProd _ _ ih
  | pushSum h hc hr _ ih => exact .pushSum _ _ hr ih
  | pushUnit h hc _ ih => exact .pushUnit _ _ ih

omit [PreorderedSemiring R] in
theorem LTm.embed_rename {n m : ℕ} (t : LTm F n) (ρ : Fin n → Fin m) :
    (t.rename ρ).embed hFG = (t.embed hFG).rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | _ => simp_all [LTm.rename, LTm.embed]

omit [PreorderedSemiring R] in
lemma LTm.embed_upSub {n m : ℕ} (σ : Fin n → LTm F m) :
    (fun i => (LTm.upSub σ i).embed hFG) = LTm.upSub (fun i => (σ i).embed hFG) := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  simp [LTm.embed_rename]

omit [PreorderedSemiring R] in
/-- Embedding commutes with substitution. -/
theorem LTm.embed_subst {n m : ℕ} (t : LTm F n) (σ : Fin n → LTm F m) :
    (t.subst σ).embed hFG = (t.embed hFG).subst (fun i => (σ i).embed hFG) := by
  induction t generalizing m with
  | var i => rfl
  | _ => simp_all [LTm.subst, LTm.embed, LTm.embed_upSub]


omit [PreorderedSemiring R] in
lemma LTm.embed_subst1 {n : ℕ} (t : LTm F (n + 1)) (s : LTm F n) :
    (t.subst1 s).embed hFG = (t.embed hFG).subst1 (s.embed hFG) := by
  rw [LTm.embed_subst]; congr 1; funext i; exact Fin.cases rfl (fun i => rfl) i

omit [PreorderedSemiring R] in
lemma LTm.embed_subst2 {n : ℕ} (t : LTm F (n + 2)) (s₁ s₂ : LTm F n) :
    (t.subst2 s₁ s₂).embed hFG = (t.embed hFG).subst2 (s₁.embed hFG) (s₂.embed hFG) := by
  rw [LTm.embed_subst]; congr 1; funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

omit [PreorderedSemiring R] in
/-- Inclusion of linear-base calculi preserves reduction. -/
theorem LStep.embed {n : ℕ} {t t' : LTm F n} (h : LStep t t') :
    LStep (t.embed hFG) (t'.embed hFG) := by
  induction h with
  | beta t₂ t₁ => rw [LTm.embed_subst1]; exact .beta _ _
  | betaBox t₁ t₂ => rw [LTm.embed_subst1]; exact .betaBox _ _
  | prodBeta h t₁ t₂ t₃ => rw [LTm.embed_subst2]; exact .prodBeta _ _ _ _
  | caseInl h t t₁ t₂ => rw [LTm.embed_subst1]; exact .caseInl _ _ _ _
  | caseInr h t t₁ t₂ => rw [LTm.embed_subst1]; exact .caseInr _ _ _ _
  | congAppL _ _ ih => exact .congAppL _ ih
  | congLetL _ _ ih => exact .congLetL _ ih
  | prodCong h _ _ ih => exact .prodCong _ _ ih
  | unitCong h _ _ ih => exact .unitCong _ _ ih
  | unitBeta h _ => exact .unitBeta _ _
  | congCase h _ _ _ ih => exact .congCase _ _ _ ih
  | pushProdCong h _ ih => exact .pushProdCong _ ih
  | pushProdBoxCong h _ ih => exact .pushProdBoxCong _ ih
  | pushProd h hc t₁ t₂ => exact .pushProd _ _ _ _
  | pushSumCong h _ ih => exact .pushSumCong _ ih
  | pushSumBoxCong h _ ih => exact .pushSumBoxCong _ ih
  | pushSumInl h hc t => exact .pushSumInl _ _ _
  | pushSumInr h hc t => exact .pushSumInr _ _ _
  | pushUnitCong h _ ih => exact .pushUnitCong _ ih
  | pushUnitBoxCong h _ ih => exact .pushUnitBoxCong _ ih
  | pushUnit h hc => exact .pushUnit _ _

end linear

/-! ## Graded lineage -/

section graded

variable {F G : GLevel} (hFG : F ≤ G)

/-- Embedding of types along `F ≤ G`. -/
def GTy.embed : GTy R F → GTy R G
  | .base => .base
  | .fn r A B => .fn r A.embed B.embed
  | .box h r A => .box (GLevel.modal_mono hFG h) r A.embed
  | .prod h A B => .prod (GLevel.core_mono hFG h) A.embed B.embed
  | .unit h => .unit (GLevel.core_mono hFG h)
  | .sum h A B => .sum (GLevel.core_mono hFG h) A.embed B.embed

/-- Embedding of terms along `F ≤ G`. -/
def GTm.embed {n : ℕ} : GTm F n → GTm G n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.embed t₂.embed
  | .lam t => .lam t.embed
  | .box h t => .box (GLevel.modal_mono hFG h) t.embed
  | .letbox h t₁ t₂ => .letbox (GLevel.modal_mono hFG h) t₁.embed t₂.embed
  | .pair h t₁ t₂ => .pair (GLevel.core_mono hFG h) t₁.embed t₂.embed
  | .letpair h t₁ t₂ => .letpair (GLevel.core_mono hFG h) t₁.embed t₂.embed
  | .unit h => .unit (GLevel.core_mono hFG h)
  | .letunit h t₁ t₂ => .letunit (GLevel.core_mono hFG h) t₁.embed t₂.embed
  | .inl h t => .inl (GLevel.core_mono hFG h) t.embed
  | .inr h t => .inr (GLevel.core_mono hFG h) t.embed
  | .case h t t₁ t₂ => .case (GLevel.core_mono hFG h) t.embed t₁.embed t₂.embed

lemma gembed_cons_ty {n : ℕ} (A : GTy R F) (Γ : Fin n → GTy R F) :
    (fun i => (A .: Γ) i |>.embed hFG) = (A.embed hFG .: fun i => (Γ i).embed hFG) := by
  funext i; exact Fin.cases rfl (fun i => rfl) i

variable [PreorderedSemiring R]

/-- Inclusion of graded-base calculi preserves typing. -/
theorem GTyped.embed {n : ℕ} {Γ : Fin n → GTy R F} {δ : Fin n → R} {t : GTm F n}
    {A : GTy R F} (h : GTyped Γ δ t A) :
    GTyped (fun i => (Γ i).embed hFG) δ (t.embed hFG) (A.embed hFG) := by
  induction h with
  | var Γ i => exact .var _ i
  | abs _ ih => rw [gembed_cons_ty] at ih; exact .abs ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | approx i _ hi ih => exact .approx i ih hi
  | pr h r _ ih => exact .pr _ r ih
  | letbox h _ _ ih₁ ih₂ => rw [gembed_cons_ty] at ih₂; exact .letbox _ ih₁ ih₂
  | pair h _ _ ih₁ ih₂ => exact .pair _ ih₁ ih₂
  | letpair h _ _ ih₁ ih₂ => rw [gembed_cons_ty, gembed_cons_ty] at ih₂; exact .letpair _ ih₁ ih₂
  | unit h => exact .unit _
  | letunit h r _ _ ih₁ ih₂ => exact .letunit _ r ih₁ ih₂
  | inl h _ ih => exact .inl _ ih
  | inr h _ ih => exact .inr _ ih
  | case h _ _ _ hr ih ih₁ ih₂ =>
    rw [gembed_cons_ty] at ih₁ ih₂; exact .case _ ih ih₁ ih₂ hr


omit [PreorderedSemiring R] in
theorem GTm.embed_rename {n m : ℕ} (t : GTm F n) (ρ : Fin n → Fin m) :
    (t.rename ρ).embed hFG = (t.embed hFG).rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | _ => simp_all [GTm.rename, GTm.embed]

omit [PreorderedSemiring R] in
lemma GTm.embed_upSub {n m : ℕ} (σ : Fin n → GTm F m) :
    (fun i => (GTm.upSub σ i).embed hFG) = GTm.upSub (fun i => (σ i).embed hFG) := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  simp [GTm.embed_rename]

omit [PreorderedSemiring R] in
/-- Embedding commutes with substitution. -/
theorem GTm.embed_subst {n m : ℕ} (t : GTm F n) (σ : Fin n → GTm F m) :
    (t.subst σ).embed hFG = (t.embed hFG).subst (fun i => (σ i).embed hFG) := by
  induction t generalizing m with
  | var i => rfl
  | _ => simp_all [GTm.subst, GTm.embed, GTm.embed_upSub]

omit [PreorderedSemiring R] in
lemma GTm.embed_subst1 {n : ℕ} (t : GTm F (n + 1)) (s : GTm F n) :
    (t.subst1 s).embed hFG = (t.embed hFG).subst1 (s.embed hFG) := by
  rw [GTm.embed_subst]; congr 1; funext i; exact Fin.cases rfl (fun i => rfl) i

omit [PreorderedSemiring R] in
lemma GTm.embed_subst2 {n : ℕ} (t : GTm F (n + 2)) (s₁ s₂ : GTm F n) :
    (t.subst2 s₁ s₂).embed hFG = (t.embed hFG).subst2 (s₁.embed hFG) (s₂.embed hFG) := by
  rw [GTm.embed_subst]; congr 1; funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

omit [PreorderedSemiring R] in
/-- Inclusion of graded-base calculi preserves reduction. -/
theorem GStep.embed {b : Bool} {n : ℕ} {t t' : GTm F n} (h : GStep b t t') :
    GStep b (t.embed hFG) (t'.embed hFG) := by
  induction h with
  | beta t₂ t₁ => rw [GTm.embed_subst1]; exact .beta _ _
  | betaBox h t₁ t₂ => rw [GTm.embed_subst1]; exact .betaBox _ _ _
  | prodBeta h t₁ t₂ t₃ => rw [GTm.embed_subst2]; exact .prodBeta _ _ _ _
  | caseInl h t t₁ t₂ => rw [GTm.embed_subst1]; exact .caseInl _ _ _ _
  | caseInr h t t₁ t₂ => rw [GTm.embed_subst1]; exact .caseInr _ _ _ _
  | congAppL _ _ ih => exact .congAppL _ ih
  | congAbs hb _ ih => exact .congAbs hb ih
  | congLetL h _ _ ih => exact .congLetL _ _ ih
  | prodCong h _ _ ih => exact .prodCong _ _ ih
  | unitCong h _ _ ih => exact .unitCong _ _ ih
  | unitBeta h _ => exact .unitBeta _ _
  | congCase h _ _ _ ih => exact .congCase _ _ _ ih

end graded

end Coeffect
