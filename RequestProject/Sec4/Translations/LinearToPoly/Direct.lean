module

public import RequestProject.Sec4.Translations.LinearToPoly.Basic
public import RequestProject.Sec2.Graded.Examples

/-!
# A direct-style alternative to the CPS translation `LB → GB`

The CPS translation of Section 2.3.2 (`LinearToGradedCPS.lean`) wraps every type in a
continuation, `⦇A ⊸ B⦈ = ((⦇A⦈ →¹ ⦇B⦈) →¹ K) →¹ K`, because Graded Base has no way to eliminate
an encoded box into an arbitrary result type. A more direct translation keeps functions and
the base type as they are and only encodes the box, polymorphically:

```
⦇A ⊸ B⦈ = ⦇A⦈ →¹ ⦇B⦈        ⦇□_r A⦈ = ∀β. (⦇A⦈ →^r β) →¹ β        ⦇K⦈ = K
⦇x⦈ = x    ⦇λx.t⦈ = λx.⦇t⦈    ⦇t₁ t₂⦈ = ⦇t₁⦈ ⦇t₂⦈
⦇[t]⦈ = Λβ. λf. f ⦇t⦈          ⦇let [x] = t₁ in t₂⦈ = (⦇t₁⦈ @ ⦇B⦈) (λx. ⦇t₂⦈)
⦇∅⦈ = ∅    ⦇Γ, x : A⦈ = ⦇Γ⦈, x :_1 ⦇A⦈    ⦇Γ, x : [A]_r⦈ = ⦇Γ⦈, x :_r ⦇A⦈
```

Two remarks:

* Because of `∀β` and `Λβ`/`@`, the target of this translation is **Graded Poly Base**
  (Graded Base plus System F polymorphism), not Graded Base itself. It is exactly the paper's
  translation `LB → GPB` of Section 4.2, which is formalized in `Basic.lean` and the following
  files as `LTy.toP` (types), `LToP` (terms, on derivations) and `toGGrades (GradeMap.id R)`
  (context grades). Its type preservation, operational correspondence and equation preservation
  are collected in `arrow_LB_GPB` (`Diagram.lean`). This file only restates the clauses in the
  form above and adds two facts about it.
* The `let` clause mentions the result type `B`, so the term translation is defined on typing
  derivations. `LToP.erase_eq` shows that, once the type abstractions and applications are
  erased, the translation depends only on the term: `erase ⦇Π⦈ = direct t` for every
  derivation `Π` of `t`, where `LTm.direct` is the obvious untyped direct-style map.

Finally, `directK_not_typeSound` shows that the polymorphism is needed if we want to stay
direct-style: instantiating `β := K` once and for all (giving the polymorphism-free encoding
`⦇□_r A⦈ = (⦇A⦈ →^r K) →¹ K`, which is a Graded Base type) breaks type preservation, because a
`let [x] = t₁ in t₂` whose result type is not `K` cannot be translated.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-! ## The clauses of the direct translation -/

section clauses

variable [One R] {k : ℕ}

/-- `⦇A ⊸ B⦈ = ⦇A⦈ →¹ ⦇B⦈`. -/
theorem LTy.toP_lolli (A B : LTy R .base) :
    (LTy.lolli A B).toP (k := k) = .fn 1 A.toP B.toP := rfl

/-- `⦇□_r A⦈ = ∀β. (⦇A⦈ →^r β) →¹ β` (`β` is the type variable `0`). -/
theorem LTy.toP_box (r : R) (A : LTy R .base) :
    (LTy.box r A).toP (k := k) = .all (.fn 1 (.fn r A.toP (.tvar 0)) (.tvar 0)) := rfl

/-- `⦇K⦈ = K`. -/
theorem LTy.toP_base : (LTy.base : LTy R .base).toP (k := k) = .base := rfl

end clauses

section context

variable [PreorderedSemiring R]

/-- Context translation: a linear assumption `x : A` becomes `x :_1 ⦇A⦈`. -/
theorem Use.toG_lin : (Use.lin : Use R).toG (GradeMap.id R) = 1 := rfl

/-- Context translation: a graded assumption `x : [A]_r` becomes `x :_r ⦇A⦈`. -/
theorem Use.toG_grd (r : R) : (Use.grd r).toG (GradeMap.id R) = r := rfl

/-- Context translation: a variable outside the context gets grade `0` (it is absent from
`⦇Γ⦈`). -/
theorem Use.toG_none : (Use.none : Use R).toG (GradeMap.id R) = 0 := rfl

end context

/-! ## The term translation only depends on the term, up to type annotations -/

/-- Erase type abstractions and type applications from a Graded Poly Base term, giving a
(Curry-style) Graded Base term. -/
def PTm.erase {k n : ℕ} : PTm R k n → GTm .base n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.erase t₂.erase
  | .lam t => .lam t.erase
  | .tlam t => t.erase
  | .tapp t _ => t.erase

theorem PTm.erase_rename {k n m : ℕ} (t : PTm R k n) (ρ : Fin n → Fin m) :
    (t.rename ρ).erase = t.erase.rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | app _ _ ih₁ ih₂ => simp only [PTm.rename, PTm.erase, GTm.rename, ih₁, ih₂]
  | lam _ ih => simp only [PTm.rename, PTm.erase, GTm.rename, ih]
  | tlam _ ih => simp only [PTm.rename, PTm.erase, ih]
  | tapp _ _ ih => simp only [PTm.rename, PTm.erase, ih]

/-- The untyped direct-style term map: `x ↦ x`, `λx.t ↦ λx.⦇t⦈`, `t₁ t₂ ↦ ⦇t₁⦈ ⦇t₂⦈`,
`[t] ↦ λf. f ⦇t⦈`, `let [x] = t₁ in t₂ ↦ ⦇t₁⦈ (λx. ⦇t₂⦈)`. -/
def LTm.direct {n : ℕ} : LTm .base n → GTm .base n
  | .var i => .var i
  | .lam t => .lam t.direct
  | .app t₁ t₂ => .app t₁.direct t₂.direct
  | .box t => .lam (.app (.var 0) (t.direct.rename Fin.succ))
  | .letbox t₁ t₂ => .app t₁.direct (.lam t₂.direct)
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

/-- For every derivation `Π` of `Γ ⊢ t : A`, erasing the type abstractions and applications
of the direct translation `⦇Π⦈` gives `LTm.direct t`. So the dependence of the translation on
derivations (through `⦇B⦈` in the `let` clause) only affects type annotations. -/
theorem LToP.erase_eq [PreorderedSemiring R] {k n : ℕ} {Γ : Fin n → LTy R .base}
    {u : Fin n → Use R} {t : LTm .base n} {A : LTy R .base} {p : PTm R k n}
    (h : LToP Γ u t A p) : p.erase = t.direct := by
  induction h with
  | var => rfl
  | abs _ ih => simp only [PTm.erase, LTm.direct, ih]
  | app _ _ _ ih₁ ih₂ => simp only [PTm.erase, LTm.direct, ih₁, ih₂]
  | weak _ _ _ ih => exact ih
  | der _ _ _ ih => exact ih
  | approx _ _ _ _ ih => exact ih
  | pr _ _ _ ih => simp only [PTm.erase, LTm.direct, PTm.erase_rename, ih]
  | letbox _ _ _ ih₁ ih₂ => simp only [PTm.erase, LTm.direct, ih₁, ih₂]

/-! ## Without polymorphism the direct translation is not type-preserving -/

/-- The polymorphism-free direct type translation into Graded Base, obtained by fixing the
answer type `β := K`: `⦇□_r A⦈ = (⦇A⦈ →^r K) →¹ K`, `⦇A ⊸ B⦈ = ⦇A⦈ →¹ ⦇B⦈`, `⦇K⦈ = K`. -/
def LTy.directK [One R] : LTy R .base → GTy R .base
  | .base => .base
  | .lolli A B => .fn 1 A.directK B.directK
  | .box r A => .fn 1 (.fn r A.directK .base) .base
  | .tensor h _ _ => absurd h (by decide)
  | .unit h => absurd h (by decide)
  | .oplus h _ _ => absurd h (by decide)

variable [PreorderedSemiring R]

/-- The direct translation cannot target Graded Base by fixing `β := K`. In the context
`z : □_1 (K ⊸ K)`, the Linear Base term `let [x] = z in x` has type `K ⊸ K`, but its direct
translation `z (λx. x)` (`= LTm.direct`) has no Graded Base typing at `⦇K ⊸ K⦈ = K →¹ K` in the
translated context `z : (⦇K ⊸ K⦈ →¹ K) →¹ K`, whatever the grades. -/
theorem directK_not_typeSound :
    let Γ : Fin 1 → LTy R .base := LTy.box 1 (.lolli .base .base) .: Fin.elim0
    let t : LTm .base 1 := .letbox (.var 0) (.var 0)
    LTyped Γ (Use.only 0) t (.lolli .base .base) ∧
      t.direct = .app (.var 0) (.lam (.var 0)) ∧
      ∀ δ : Fin 1 → R, ¬ GTyped (fun i => (Γ i).directK) δ t.direct
        (LTy.directK (.lolli .base .base)) := by
  intro Γ t
  refine ⟨?_, rfl, ?_⟩
  · have h₂ : LTyped ((LTy.lolli .base .base : LTy R .base) .: Γ) (Use.grd 1 .: emptyU)
        (.var 0) (.lolli .base .base) := by
      have := LTyped.der 0 (LTyped.var ((LTy.lolli .base .base : LTy R .base) .: Γ) 0)
        (by simp [Use.only])
      refine (by
        convert this using 1
        funext j; refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simp [Use.only, emptyU, Fin.succ_ne_zero])
    refine LTyped.letbox (LTyped.var Γ 0) h₂ ?_
    intro i
    exact Use.Add.noneRight _
  · intro δ h
    obtain ⟨r, A, δ₁, δ₂, h₁, _, _⟩ := GExample.app_inv h
    obtain ⟨e, _⟩ := GExample.var_inv h₁
    simp only [Γ, LTy.directK] at e
    injection e with _ _ e
    cases e

end Coeffect
