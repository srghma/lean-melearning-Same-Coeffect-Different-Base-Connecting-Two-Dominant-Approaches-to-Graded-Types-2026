module

public import RequestProject.Sec2.Linear.Syntax
public import RequestProject.Sec2.Foundations.Semiring

/-!
# Typing of the linear-base lineage (Figure 1, Figure 4, Figure 5)

## Contexts

A Linear Base context `Γ ::= ∅ | Γ, x : A | Γ, x : [A]_r` contains *linear* assumptions
`x : A` and *graded* assumptions `x : [A]_r`. With de Bruijn indices we represent a context on
`n` variables by

* a type assignment `Γ : Fin n → LTy R F`, and
* a usage assignment `u : Fin n → Use R`, where `Use.none` means that the variable is not part
  of the context (it is not in `dom(Γ)`), `Use.lin` means a linear assumption `x : A` and
  `Use.grd r` a graded assumption `x : [A]_r`.

Context addition `Γ₁ + Γ₂` (Definition 2.1) is the partial operation which is pointwise defined
by `none + u = u = u + none` and `[A]_r + [A]_s = [A]_{r+s}`; in particular it is undefined
when both contexts contain the same linear assumption. We represent it as a relation
`CtxAdd u₁ u₂ u` (both summands share the type assignment, which is how the paper's requirement
"shared graded assumptions agree on the type" is enforced).

The predicates `graded(Γ)` and `graded(Γ, r)` (Definition 2.2) and scalar multiplication
`r · Γ` (Definition 2.3) are `Graded`, the weakening rule and `smulCtx`.

Because contexts are unordered in the paper (exchange is admissible), representing them as
functions out of `Fin n` is faithful. The rules `weak`, `der` and `approx` act on a single
assumption; the paper's weakening by a whole context `Γ'` with `graded(Γ', 0)` is obtained by
iterating `weak`.
-/

@[expose] public section

namespace Coeffect

universe u

/-- How a variable occurs in a Linear Base context. -/
inductive Use (R : Type u) : Type u
  /-- the variable is not in the context -/
  | none
  /-- linear assumption `x : A` -/
  | lin
  /-- graded assumption `x : [A]_r` -/
  | grd (r : R)
  deriving DecidableEq

namespace Use

variable {R : Type u}

/-- Pointwise context addition, as a (functional, partial) relation. -/
inductive Add [HAdd R R R] : Use R → Use R → Use R → Prop
  | noneLeft (v : Use R) : Add none v v
  | noneRight (v : Use R) : Add v none v
  | grd (r s : R) : Add (grd r) (grd s) (grd (r + s))

/-- Scalar multiplication of an assumption (only meaningful on graded assumptions). -/
def smul [Mul R] (r : R) : Use R → Use R
  | none => none
  | lin => lin
  | grd s => grd (r * s)

/-- The usage which is `lin` exactly at `i`. -/
def only {n : ℕ} (i : Fin n) : Fin n → Use R := fun j => if j = i then lin else none

end Use

variable {R : Type u}

/-- Context addition `Γ₁ + Γ₂ = Γ` (pointwise). -/
def CtxAdd [HAdd R R R] {n : ℕ} (u₁ u₂ u : Fin n → Use R) : Prop :=
  ∀ i, Use.Add (u₁ i) (u₂ i) (u i)

/-- `graded(Γ)`: the context contains no linear assumptions. -/
def Graded {n : ℕ} (u : Fin n → Use R) : Prop := ∀ i, u i ≠ Use.lin

/-- Scalar multiplication `r · Γ` of a (graded) context. -/
def smulCtx [Mul R] {n : ℕ} (r : R) (u : Fin n → Use R) : Fin n → Use R :=
  fun i => (u i).smul r

/-- The empty context `∅`. -/
def emptyU {n : ℕ} : Fin n → Use R := fun _ => Use.none

variable [PreorderedSemiring R] {F : LLevel}

/-- The typing judgment `Γ ⊢_L t : A` of the linear-base calculi (Figure 1; products, unit and
sums from Figure 4; `push` rules from Figure 5). -/
inductive LTyped : {n : ℕ} → (Fin n → LTy R F) → (Fin n → Use R) → LTm F n → LTy R F → Prop
  /-- `x : A ⊢ x : A` -/
  | var {n : ℕ} (Γ : Fin n → LTy R F) (i : Fin n) : LTyped Γ (Use.only i) (.var i) (Γ i)
  /-- abstraction -/
  | abs {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F (n + 1)} {A B : LTy R F} :
      LTyped (A .: Γ) (Use.lin .: u) t B → LTyped Γ u (.lam t) (.lolli A B)
  /-- application -/
  | app {n : ℕ} {Γ : Fin n → LTy R F} {u₁ u₂ u : Fin n → Use R} {t₁ t₂ : LTm F n} {A B : LTy R F} :
      LTyped Γ u₁ t₁ (.lolli A B) → LTyped Γ u₂ t₂ A → CtxAdd u₁ u₂ u →
      LTyped Γ u (.app t₁ t₂) B
  /-- weakening by a `0`-graded assumption -/
  | weak {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A : LTy R F} (i : Fin n) :
      LTyped Γ u t A → u i = Use.none → LTyped Γ (Function.update u i (Use.grd 0)) t A
  /-- dereliction -/
  | der {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {B : LTy R F} (i : Fin n) :
      LTyped Γ u t B → u i = Use.lin → LTyped Γ (Function.update u i (Use.grd 1)) t B
  /-- promotion -/
  | pr {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A : LTy R F} (r : R) :
      LTyped Γ u t A → Graded u → LTyped Γ (smulCtx r u) (.box t) (.box r A)
  /-- graded modal elimination -/
  | letbox {n : ℕ} {Γ : Fin n → LTy R F} {u₁ u₂ u : Fin n → Use R} {t₁ : LTm F n}
      {t₂ : LTm F (n + 1)} {r : R} {A B : LTy R F} :
      LTyped Γ u₁ t₁ (.box r A) → LTyped (A .: Γ) (Use.grd r .: u₂) t₂ B → CtxAdd u₁ u₂ u →
      LTyped Γ u (.letbox t₁ t₂) B
  /-- approximation -/
  | approx {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A : LTy R F}
      (i : Fin n) {r s : R} :
      LTyped Γ u t A → u i = Use.grd r → r ≤ s → LTyped Γ (Function.update u i (Use.grd s)) t A
  /-- product introduction -/
  | pair {n : ℕ} {Γ : Fin n → LTy R F} {u₁ u₂ u : Fin n → Use R} {t₁ t₂ : LTm F n} {A B : LTy R F}
      (h : F.Core) :
      LTyped Γ u₁ t₁ A → LTyped Γ u₂ t₂ B → CtxAdd u₁ u₂ u →
      LTyped Γ u (.pair h t₁ t₂) (.tensor h A B)
  /-- product elimination -/
  | letpair {n : ℕ} {Γ : Fin n → LTy R F} {u₁ u₂ u : Fin n → Use R} {t₁ : LTm F n}
      {t₂ : LTm F (n + 2)} {A B C : LTy R F} (h : F.Core) :
      LTyped Γ u₁ t₁ (.tensor h A B) → LTyped (B .: A .: Γ) (Use.lin .: Use.lin .: u₂) t₂ C →
      CtxAdd u₁ u₂ u → LTyped Γ u (.letpair h t₁ t₂) C
  /-- unit introduction -/
  | unit {n : ℕ} {Γ : Fin n → LTy R F} (h : F.Core) : LTyped Γ emptyU (.unit h) (.unit h)
  /-- unit elimination -/
  | letunit {n : ℕ} {Γ : Fin n → LTy R F} {u₁ u₂ u : Fin n → Use R} {t₁ t₂ : LTm F n}
      {A : LTy R F} (h : F.Core) :
      LTyped Γ u₁ t₁ (.unit h) → LTyped Γ u₂ t₂ A → CtxAdd u₁ u₂ u →
      LTyped Γ u (.letunit h t₁ t₂) A
  /-- left injection -/
  | inl {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A B : LTy R F}
      (h : F.Core) : LTyped Γ u t A → LTyped Γ u (.inl h t) (.oplus h A B)
  /-- right injection -/
  | inr {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A B : LTy R F}
      (h : F.Core) : LTyped Γ u t B → LTyped Γ u (.inr h t) (.oplus h A B)
  /-- sum elimination -/
  | case {n : ℕ} {Γ : Fin n → LTy R F} {u₁ u₂ u : Fin n → Use R} {t : LTm F n}
      {t₁ t₂ : LTm F (n + 1)} {A B C : LTy R F} (h : F.Core) :
      LTyped Γ u₁ t (.oplus h A B) → LTyped (A .: Γ) (Use.lin .: u₂) t₁ C →
      LTyped (B .: Γ) (Use.lin .: u₂) t₂ C → CtxAdd u₁ u₂ u → LTyped Γ u (.case h t t₁ t₂) C
  /-- `push⊗ : □_r (A ⊗ B) ⊸ □_r A ⊗ □_r B` -/
  | pushProd {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {r : R}
      {A B : LTy R F} (h : F.Push) (hc : F.Core) :
      LTyped Γ u t (.box r (.tensor hc A B)) →
      LTyped Γ u (.pushProd h t) (.tensor hc (.box r A) (.box r B))
  /-- `push⊕ : □_r (A ⊕ B) ⊸ □_r A ⊕ □_r B` (when `1 ⊑ r`) -/
  | pushSum {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {r : R}
      {A B : LTy R F} (h : F.Push) (hc : F.Core) :
      1 ≤ r → LTyped Γ u t (.box r (.oplus hc A B)) →
      LTyped Γ u (.pushSum h t) (.oplus hc (.box r A) (.box r B))
  /-- `push_unit : □_r unit ⊸ unit` -/
  | pushUnit {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {r : R}
      (h : F.Push) (hc : F.Core) :
      LTyped Γ u t (.box r (.unit hc)) → LTyped Γ u (.pushUnit h t) (.unit hc)

namespace LTyped

variable {n : ℕ} {Γ : Fin n → LTy R F} {u u' : Fin n → Use R} {t : LTm F n} {A : LTy R F}

lemma cast (h : LTyped Γ u t A) (e : u = u') : LTyped Γ u' t A := e ▸ h

end LTyped

/-! ## Renaming (weakening and exchange) -/

section Renaming

variable {n m : ℕ}

lemma CtxAdd.pushAlong {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {u₁ u₂ u : Fin n → Use R}
    (h : CtxAdd u₁ u₂ u) {u' : Fin m → Use R} (hu : ∀ i, u' (ρ i) = u i)
    (hoff : ∀ j, (∀ i, ρ i ≠ j) → u' j = Use.none) :
    CtxAdd (pushAlong ρ Use.none u₁) (pushAlong ρ Use.none u₂) u' := by
  intro j
  rcases range_or_off ρ j with ⟨i, rfl⟩ | hj
  · rw [pushAlong_apply hρ, pushAlong_apply hρ, hu]; exact h i
  · rw [pushAlong_off _ _ _ hj, pushAlong_off _ _ _ hj, hoff j hj]; exact Use.Add.noneLeft _

omit [PreorderedSemiring R] in
/-- Helper for the structural rules: decompose a usage `u'` on the target of a renaming whose
value at `ρ i` is `v`. -/
lemma update_preimage {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {u : Fin n → Use R}
    (i : Fin n) (v w : Use R) {u' : Fin m → Use R}
    (hu : ∀ k, u' (ρ k) = Function.update u i v k)
    (hoff : ∀ j, (∀ k, ρ k ≠ j) → u' j = Use.none) (hw : u i = w) :
    (∀ k, Function.update u' (ρ i) w (ρ k) = u k) ∧
    (∀ j, (∀ k, ρ k ≠ j) → Function.update u' (ρ i) w j = Use.none) ∧
    Function.update (Function.update u' (ρ i) w) (ρ i) v = u' := by
  refine ⟨fun k => ?_, fun j hj => ?_, ?_⟩
  · by_cases hk : k = i
    · subst hk; simp [hw]
    · rw [Function.update_of_ne (fun e => hk (hρ e)), hu, Function.update_of_ne hk]
  · rw [Function.update_of_ne (fun e => hj i e.symm), hoff j hj]
  · rw [update_idem']
    have := hu i
    rw [Function.update_self] at this
    rw [← this, update_eq_self']

/-- Typing is preserved by injective renamings (this subsumes weakening by unused variables and
exchange). -/
theorem LTyped.rename {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n} {A : LTy R F}
    (h : LTyped Γ u t A) {m : ℕ} (ρ : Fin n → Fin m) (hρ : Function.Injective ρ)
    (Γ' : Fin m → LTy R F) (hΓ : ∀ i, Γ' (ρ i) = Γ i) (u' : Fin m → Use R)
    (hu : ∀ i, u' (ρ i) = u i) (hoff : ∀ j, (∀ i, ρ i ≠ j) → u' j = Use.none) :
    LTyped Γ' u' (t.rename ρ) A := by
  induction h generalizing m with
  | var Γ i =>
    have : u' = Use.only (ρ i) := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; simp only [Use.only, hρ.eq_iff]
      · rw [hoff j hj]; simp only [Use.only]; rw [if_neg (fun e => hj i e.symm)]
    rw [this, ← hΓ i]; exact LTyped.var Γ' (ρ i)
  | abs _ ih =>
    refine LTyped.abs (ih (upRen ρ) (upRen_injective hρ) _ ?_ _ ?_ ?_)
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ]
    · intro i; refine Fin.cases ?_ ?_ i <;> simp [hu]
    · intro j hj
      induction j using Fin.cases with
      | zero => exact absurd rfl (hj 0)
      | succ j => exact hoff j (fun i e => hj i.succ (by simp [e]))
  | app _ _ hadd ih₁ ih₂ =>
    exact LTyped.app (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₂ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj)) (hadd.pushAlong hρ hu hoff)
  | weak i _ hi ih =>
    obtain ⟨h1, h2, h3⟩ := update_preimage hρ i _ _ hu hoff hi
    rw [← h3]
    exact LTyped.weak (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2) (by simp)
  | der i _ hi ih =>
    obtain ⟨h1, h2, h3⟩ := update_preimage hρ i _ _ hu hoff hi
    rw [← h3]
    exact LTyped.der (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2) (by simp)
  | approx i _ hi hrs ih =>
    obtain ⟨h1, h2, h3⟩ := update_preimage hρ i _ _ hu hoff hi
    rw [← h3]
    exact LTyped.approx (ρ i) (ih ρ hρ Γ' hΓ _ h1 h2) (by simp) hrs
  | @pr _ Γ u t A r _ hg ih =>
    have e : u' = smulCtx r (pushAlong ρ Use.none u) := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; simp [smulCtx, pushAlong_apply hρ]
      · rw [hoff j hj]; simp [smulCtx, pushAlong_off _ _ j hj, Use.smul]
    rw [e]
    refine LTyped.pr r (ih ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj)) ?_
    intro j
    rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
    · rw [pushAlong_apply hρ]; exact hg k
    · rw [pushAlong_off _ _ j hj]; simp
  | letbox _ _ hadd ih₁ ih₂ =>
    refine LTyped.letbox (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
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
  | pair h _ _ hadd ih₁ ih₂ =>
    exact LTyped.pair h (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₂ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj)) (hadd.pushAlong hρ hu hoff)
  | letpair h _ _ hadd ih₁ ih₂ =>
    refine LTyped.letpair h (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₂ (upRen (upRen ρ)) (upRen_injective (upRen_injective hρ)) _ ?_ _ ?_ ?_)
      (hadd.pushAlong hρ hu hoff)
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
  | unit h =>
    have : u' = emptyU := by
      funext j
      rcases range_or_off ρ j with ⟨k, rfl⟩ | hj
      · rw [hu]; rfl
      · exact hoff j hj
    rw [this]; exact LTyped.unit h
  | letunit h _ _ hadd ih₁ ih₂ =>
    exact LTyped.letunit h (ih₁ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₂ ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj)) (hadd.pushAlong hρ hu hoff)
  | inl h _ ih => exact LTyped.inl h (ih ρ hρ Γ' hΓ u' hu hoff)
  | inr h _ ih => exact LTyped.inr h (ih ρ hρ Γ' hΓ u' hu hoff)
  | @case _ _ _ _ _ _ _ _ A B _ h _ _ _ hadd ih ih₁ ih₂ =>
    refine LTyped.case h (ih ρ hρ Γ' hΓ _ (fun i => pushAlong_apply hρ _ _ i)
        (fun j hj => pushAlong_off _ _ j hj))
      (ih₁ (upRen ρ) (upRen_injective hρ) (A .: Γ') ?_ _ ?_ ?_)
      (ih₂ (upRen ρ) (upRen_injective hρ) (B .: Γ') ?_ _ ?_ ?_) (hadd.pushAlong hρ hu hoff)
    all_goals first
      | (intro j hj
         induction j using Fin.cases with
         | zero => exact absurd rfl (hj 0)
         | succ j =>
           simp only [scons_succ]
           exact pushAlong_off _ _ j (fun i e => hj i.succ (by simp [e])))
      | (intro i; refine Fin.cases ?_ ?_ i <;> simp [hΓ, pushAlong_apply hρ])
  | pushProd h hc _ ih => exact LTyped.pushProd h hc (ih ρ hρ Γ' hΓ u' hu hoff)
  | pushSum h hc hr _ ih => exact LTyped.pushSum h hc hr (ih ρ hρ Γ' hΓ u' hu hoff)
  | pushUnit h hc _ ih => exact LTyped.pushUnit h hc (ih ρ hρ Γ' hΓ u' hu hoff)

end Renaming

end Coeffect

namespace Coeffect

universe v
variable {R : Type v} [PreorderedSemiring R] {F : LLevel}

/-! ## Admissible weakening by many `0`-graded assumptions and context helpers -/

/-- Iterated weakening: any `none` assumptions may be turned into `0`-graded assumptions. -/
theorem LTyped.weak_many {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {t : LTm F n}
    {A : LTy R F} (h : LTyped Γ u t A) (u' : Fin n → Use R)
    (hu' : ∀ j, u' j = u j ∨ (u j = Use.none ∧ u' j = Use.grd 0)) : LTyped Γ u' t A := by
  suffices H : ∀ (k : ℕ) (u' : Fin n → Use R),
      (∀ j, u' j = u j ∨ (u j = Use.none ∧ u' j = Use.grd 0)) →
      (∀ j : Fin n, k ≤ j.val → u' j = u j) → LTyped Γ u' t A from
    H n u' hu' (fun j hj => absurd j.isLt (Nat.not_lt.mpr hj))
  intro k
  induction k with
  | zero =>
    intro u' _ hS
    have : u' = u := funext fun j => hS j (Nat.zero_le _)
    rw [this]; exact h
  | succ k ih =>
    intro u' hu' hS
    by_cases hk : k < n
    · let a : Fin n := ⟨k, hk⟩
      have hne : ∀ j : Fin n, j ≠ a → k ≤ j.val → k + 1 ≤ j.val := by
        intro j hja hj
        have : j.val ≠ k := fun e => hja (Fin.ext e)
        omega
      rcases hu' a with e | ⟨hn, hg⟩
      · apply ih u' hu'
        intro j hj
        by_cases hja : j = a
        · subst hja; exact e
        · exact hS j (hne j hja hj)
      · have h1 : LTyped Γ (Function.update u' a Use.none) t A := by
          apply ih
          · intro j
            by_cases hja : j = a
            · subst hja; left; rw [Function.update_self, hn]
            · rw [Function.update_of_ne hja]; exact hu' j
          · intro j hj
            by_cases hja : j = a
            · subst hja; rw [Function.update_self, hn]
            · rw [Function.update_of_ne hja]; exact hS j (hne j hja hj)
        have h2 := LTyped.weak a h1 (Function.update_self _ _ _)
        rwa [update_idem', ← hg, update_eq_self'] at h2
    · apply ih u' hu'
      intro j hj
      exact absurd j.isLt (by omega)

omit [PreorderedSemiring R] in
lemma Use.only_zero {n : ℕ} : (Use.only (0 : Fin (n + 1)) : Fin (n + 1) → Use R) =
    Use.lin .: emptyU := by
  funext j; refine Fin.cases ?_ ?_ j <;> simp [Use.only, emptyU, Fin.succ_ne_zero]

omit [PreorderedSemiring R] in
lemma Use.only_one {n : ℕ} : (Use.only (1 : Fin (n + 2)) : Fin (n + 2) → Use R) =
    Use.none .: Use.lin .: emptyU := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Use.only]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Use.only]
    · simp only [Use.only, scons_succ, emptyU]
      rw [if_neg]
      intro e
      have := congrArg Fin.val e
      simp only [Fin.val_succ, Fin.val_one] at this
      omega

lemma CtxAdd.cons {n : ℕ} {a b c : Use R} {u₁ u₂ u : Fin n → Use R} (h : Use.Add a b c)
    (h' : CtxAdd u₁ u₂ u) : CtxAdd (a .: u₁) (b .: u₂) (c .: u) := by
  intro i; refine Fin.cases ?_ (fun j => ?_) i
  · exact h
  · exact h' j

lemma CtxAdd.emptyLeft {n : ℕ} (u : Fin n → Use R) : CtxAdd emptyU u u :=
  fun _ => Use.Add.noneLeft _

lemma CtxAdd.emptyRight {n : ℕ} (u : Fin n → Use R) : CtxAdd u emptyU u :=
  fun _ => Use.Add.noneRight _

lemma CtxAdd.grd {n : ℕ} (δ₁ δ₂ : Fin n → R) :
    CtxAdd (fun i => Use.grd (δ₁ i)) (fun i => Use.grd (δ₂ i)) (fun i => Use.grd ((δ₁ + δ₂) i)) :=
  fun _ => Use.Add.grd _ _

omit [PreorderedSemiring R] in
lemma Graded.grd {n : ℕ} (δ : Fin n → R) : Graded (fun i => Use.grd (δ i)) :=
  fun _ h => by cases h

lemma smulCtx_grd {n : ℕ} (r : R) (δ : Fin n → R) :
    smulCtx r (fun i => Use.grd (δ i)) = fun i => Use.grd ((r • δ) i) := rfl

/-- The variable rule, with flexible conclusion. -/
lemma LTyped.var' {n : ℕ} {Γ : Fin n → LTy R F} {u : Fin n → Use R} {A : LTy R F} (i : Fin n)
    (hu : u = Use.only i) (hA : A = Γ i) : LTyped Γ u (.var i) A := by
  subst hu hA; exact .var Γ i

/-- A variable used at grade `1` with every other variable weakened at grade `0`. -/
lemma LTyped.var_grd {n : ℕ} (Γ : Fin n → LTy R F) (i : Fin n) :
    LTyped Γ (fun j => Use.grd ((Pi.single i (1 : R) : Fin n → R) j)) (.var i) (Γ i) := by
  have h := LTyped.der i (LTyped.var Γ i) (by simp [Use.only])
  refine h.weak_many _ (fun j => ?_)
  by_cases hj : j = i
  · subst hj; left; simp
  · right; simp [Use.only, hj]

end Coeffect
