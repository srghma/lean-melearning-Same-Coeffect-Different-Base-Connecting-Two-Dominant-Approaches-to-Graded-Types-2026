module

public import RequestProject.Sec4.PolyTyping
public import RequestProject.Sec3.LinearToGradedModal

/-!
# The translation from Linear Base to Graded Poly Base (Section 4.2)

In Graded Poly Base the graded modality is definable by a Church encoding:

```
⦇□_r A⦈ = ∀β. (⦇A⦈ →^r β) →¹ β         ⦇A ⊸ B⦈ = ⦇A⦈ →¹ ⦇B⦈        ⦇K⦈ = K
```

The term translation needs the result type `B` of `let [x] = t₁ in t₂` (to instantiate `β`),
which is not determined by the term alone, so the paper defines the translation on *typing
derivations*:

```
⦇Π / r·Γ ⊢ [t] : □_r A⦈                 = Λβ. λf. f ⦇Π⦈
⦇Π₁, Π₂ / Γ₁+Γ₂ ⊢ let [x] = t₁ in t₂ : B⦈ = (⦇Π₁⦈ @ ⦇B⦈) (λx. ⦇Π₂⦈)
```

and homomorphically elsewhere (the structural rules do not change the term). Since Lean's typing
judgement is a proposition, we present the translation of derivations as an inductive relation
`LToP Γ u t A p` ("`p` is the translation of a derivation of `Γ ⊢ t : A`"), with one rule per
typing rule. Every derivation has a translation (`LTyped.toP_exists`), and every translation is
well typed (`LToP.typed`, type preservation of Theorem 4.1).
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- Type translation `⦇A⦈` from Linear Base to Graded Poly Base (in any type-variable context;
translated types are closed). -/
def LTy.toP [One R] {k : ℕ} : LTy R .base → PTy R k
  | .base => .base
  | .lolli A B => .fn 1 A.toP B.toP
  | .box r A => .all (.fn 1 (.fn r A.toP (.tvar 0)) (.tvar 0))
  | .tensor h _ _ => absurd h (by decide)
  | .unit h => absurd h (by decide)
  | .oplus h _ _ => absurd h (by decide)

lemma LTy.toP_rename [One R] {k l : ℕ} (A : LTy R .base) (ρ : Fin k → Fin l) :
    (A.toP : PTy R k).rename ρ = A.toP := by
  induction A generalizing k l with
  | base => rfl
  | lolli A B ihA ihB => simp only [LTy.toP, PTy.rename, ihA, ihB]
  | box r A ih => simp only [LTy.toP, PTy.rename, ih]; rfl
  | tensor h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | oplus h => exact absurd h (by decide)

lemma LTy.toP_subst [One R] {k l : ℕ} (A : LTy R .base) (σ : Fin k → PTy R l) :
    (A.toP : PTy R k).subst σ = A.toP := by
  induction A generalizing k l with
  | base => rfl
  | lolli A B ihA ihB => simp only [LTy.toP, PTy.subst, ihA, ihB]
  | box r A ih => simp only [LTy.toP, PTy.subst, ih]; rfl
  | tensor h => exact absurd h (by decide)
  | unit h => exact absurd h (by decide)
  | oplus h => exact absurd h (by decide)

variable [PreorderedSemiring R]

/-- `LToP Γ u t A p`: the Graded Poly Base term `p` is the translation `⦇Π⦈` of a Linear Base
typing derivation `Π` of `Γ ⊢ t : A`; there is one constructor per typing rule of Linear Base. -/
inductive LToP : {k n : ℕ} → (Fin n → LTy R .base) → (Fin n → Use R) → LTm .base n →
    LTy R .base → PTm R k n → Prop
  | var {k n : ℕ} (Γ : Fin n → LTy R .base) (i : Fin n) :
      LToP (k := k) Γ (Use.only i) (.var i) (Γ i) (.var i)
  | abs {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base (n + 1)}
      {A B : LTy R .base} {p : PTm R k (n + 1)} :
      LToP (A .: Γ) (Use.lin .: u) t B p → LToP Γ u (.lam t) (.lolli A B) (.lam p)
  | app {k n : ℕ} {Γ : Fin n → LTy R .base} {u₁ u₂ u : Fin n → Use R} {t₁ t₂ : LTm .base n}
      {A B : LTy R .base} {p₁ p₂ : PTm R k n} :
      LToP Γ u₁ t₁ (.lolli A B) p₁ → LToP Γ u₂ t₂ A p₂ → CtxAdd u₁ u₂ u →
      LToP Γ u (.app t₁ t₂) B (.app p₁ p₂)
  | weak {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
      {A : LTy R .base} {p : PTm R k n} (i : Fin n) :
      LToP Γ u t A p → u i = Use.none → LToP Γ (Function.update u i (Use.grd 0)) t A p
  | der {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
      {A : LTy R .base} {p : PTm R k n} (i : Fin n) :
      LToP Γ u t A p → u i = Use.lin → LToP Γ (Function.update u i (Use.grd 1)) t A p
  | approx {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
      {A : LTy R .base} {p : PTm R k n} (i : Fin n) {r s : R} :
      LToP Γ u t A p → u i = Use.grd r → r ≤ s →
      LToP Γ (Function.update u i (Use.grd s)) t A p
  /-- `⦇[t]⦈ = Λβ. λf. f ⦇t⦈` (the translation of `t` lives under the new type variable `β`) -/
  | pr {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
      {A : LTy R .base} {p : PTm R (k + 1) n} (r : R) :
      LToP Γ u t A p → Graded u →
      LToP (k := k) Γ (smulCtx r u) (.box t) (.box r A)
        (.tlam (.lam (.app (.var 0) (p.rename Fin.succ))))
  /-- `⦇let [x] = t₁ in t₂ : B⦈ = (⦇t₁⦈ @ ⦇B⦈) (λx. ⦇t₂⦈)` -/
  | letbox {k n : ℕ} {Γ : Fin n → LTy R .base} {u₁ u₂ u : Fin n → Use R} {t₁ : LTm .base n}
      {t₂ : LTm .base (n + 1)} {r : R} {A B : LTy R .base} {p₁ : PTm R k n}
      {p₂ : PTm R k (n + 1)} :
      LToP Γ u₁ t₁ (.box r A) p₁ → LToP (A .: Γ) (Use.grd r .: u₂) t₂ B p₂ → CtxAdd u₁ u₂ u →
      LToP Γ u (.letbox t₁ t₂) B (.app (.tapp p₁ B.toP) (.lam p₂))

/-- Every Linear Base typing derivation has a translation (at every type-variable depth). -/
theorem LTyped.toP_exists {n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R}
    {t : LTm .base n} {A : LTy R .base} (h : LTyped Γ u t A) :
    ∀ k, ∃ p : PTm R k n, LToP Γ u t A p := by
  induction h with
  | var Γ i => exact fun k => ⟨_, .var Γ i⟩
  | abs _ ih => exact fun k => let ⟨p, hp⟩ := ih k; ⟨_, .abs hp⟩
  | app _ _ hadd ih₁ ih₂ =>
    exact fun k => let ⟨p₁, h₁⟩ := ih₁ k; let ⟨p₂, h₂⟩ := ih₂ k; ⟨_, .app h₁ h₂ hadd⟩
  | weak i _ hi ih => exact fun k => let ⟨p, hp⟩ := ih k; ⟨_, .weak i hp hi⟩
  | der i _ hi ih => exact fun k => let ⟨p, hp⟩ := ih k; ⟨_, .der i hp hi⟩
  | approx i _ hi hrs ih => exact fun k => let ⟨p, hp⟩ := ih k; ⟨_, .approx i hp hi hrs⟩
  | pr r _ hg ih => exact fun k => let ⟨p, hp⟩ := ih (k + 1); ⟨_, .pr r hp hg⟩
  | letbox _ _ hadd ih₁ ih₂ =>
    exact fun k => let ⟨p₁, h₁⟩ := ih₁ k; let ⟨p₂, h₂⟩ := ih₂ k; ⟨_, .letbox h₁ h₂ hadd⟩
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

lemma PTyped.weaken1 {k n : ℕ} {Γ : Fin n → PTy R k} {δ : Fin n → R} {t : PTm R k n}
    {A : PTy R k} (h : PTyped Γ δ t A) (C : PTy R k) :
    PTyped (C .: Γ) (0 .: δ) (t.rename Fin.succ) A :=
  h.rename Fin.succ (Fin.succ_injective _) _ (fun _ => rfl) _ (fun _ => rfl)
    (fun j hj => by
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact absurd rfl (hj j))

lemma LTy.toP_cons {k n : ℕ} (A : LTy R .base) (Γ : Fin n → LTy R .base) :
    (fun i => ((A .: Γ) i).toP (k := k)) = (A.toP .: fun i => (Γ i).toP) :=
  scons_map _ _ _

/-- **Theorem 4.1 (type preservation)** of the Linear Base → Graded Poly Base translation:
if `p = ⦇Π⦈` for a derivation `Π` of `Γ ⊢_L t : A`, then `⦇Γ⦈ ⊢_{G∀} p : ⦇A⦈`. -/
theorem LToP.typed {k n : ℕ} {Γ : Fin n → LTy R .base} {u : Fin n → Use R} {t : LTm .base n}
    {A : LTy R .base} {p : PTm R k n} (h : LToP Γ u t A p) :
    PTyped (fun i => (Γ i).toP) (toGGrades (GradeMap.id R) u) p A.toP := by
  induction h with
  | var Γ i => rw [toGGrades_only]; exact PTyped.var _ i
  | abs _ ih =>
    rw [LTy.toP_cons, toGGrades_cons] at ih
    exact PTyped.abs ih
  | app _ _ hadd ih₁ ih₂ =>
    rw [toGGrades_add_one_smul _ hadd]; exact PTyped.app ih₁ ih₂
  | weak i _ hi ih =>
    rw [toGGrades_update]
    exact PTyped.approx i ih (by simp [toGGrades, hi, Use.toG, GradeMap.id])
  | der i _ hi ih =>
    rw [toGGrades_update]
    exact PTyped.approx i ih (by simp [toGGrades, hi, Use.toG, GradeMap.id])
  | approx i _ hi hrs ih =>
    rw [toGGrades_update]
    exact PTyped.approx i ih (by simpa [toGGrades, hi, Use.toG, GradeMap.id] using hrs)
  | @pr k n Γ u t A p r _ hg ih =>
    rw [toGGrades_smul _ r hg]
    refine PTyped.tabs ?_
    have e : (fun i => ((Γ i).toP : PTy R k).shift) = fun i => (Γ i).toP :=
      funext fun i => LTy.toP_rename _ _
    rw [e]
    refine PTyped.abs (A := .fn r A.toP (.tvar 0)) ?_
    refine (PTyped.app (PTyped.var _ 0) (ih.weaken1 _)).cast ?_
    funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.succ_ne_zero, GradeMap.id]
  | @letbox k n Γ u₁ u₂ u t₁ t₂ r A B p₁ p₂ _ _ hadd ih₁ ih₂ =>
    rw [LTy.toP_cons, toGGrades_cons] at ih₂
    rw [toGGrades_add_one_smul _ hadd]
    refine PTyped.app ((PTyped.tapp B.toP ih₁).castTy ?_) (PTyped.abs ih₂)
    simp only [PTy.subst1, PTy.subst, LTy.toP_subst]
    rfl

end Coeffect
