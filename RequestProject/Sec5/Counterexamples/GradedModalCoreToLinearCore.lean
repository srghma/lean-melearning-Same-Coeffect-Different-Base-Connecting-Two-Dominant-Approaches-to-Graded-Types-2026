module

public import RequestProject.Sec3.Translations.LinearToGradedModal

/-!
# No type-sound homomorphic translation from Graded Modal Core to Linear Core (Section 5.4)

The paper first attempts to extend the Graded Base → Linear Base translation `⟦-⟧` to products
and sums *homomorphically*, landing in Linear Core (without `push`):

```
⟦⟨t₁, t₂⟩⟧∘ = ⟨⟦t₁⟧∘, ⟦t₂⟧∘⟩      ⟦let ⟨x, y⟩ = t₁ in t₂⟧∘ = let ⟨x, y⟩ = ⟦t₁⟧∘ in ⟦t₂⟧∘
⟦inj_i t⟧∘ = inj_i ⟦t⟧∘          ⟦case t of {...}⟧∘ = case ⟦t⟧∘ of {...}
⟦A × B⟧∘ = ⟦A⟧∘ ⊗ ⟦B⟧∘           ⟦A + B⟧∘ = ⟦A⟧∘ ⊕ ⟦B⟧∘
```

This translation is *unsound*: the Graded Modal Core term

```
f = λp. let ⟨x, y⟩ = p in ⟨[x], [y]⟩  :  (A × B) →^r (□_r A × □_r B)
```

is well typed, but its translation
`⟦f⟧∘ = λb. let [p] = b in let ⟨x, y⟩ = p in ⟨[x], [y]⟩` is ill typed in Linear Core — in
*every* context and at *every* type (`naive_not_typeSound`): the variables `x, y` bound by the
linear `let ⟨x, y⟩` are linear, and a linear variable can never occur under a box (`[x]` needs
`graded(Γ)`).

This is the "❌ (unsound)" arrow `GMC ⇢ LC` in the diagram.
-/

@[expose] public section

namespace Coeffect

universe u

variable {R : Type u}

/-- The naive homomorphic type translation `⟦-⟧∘` (Graded Modal Core → Linear Core). -/
def GTy.toLNaive : GTy R .core → LTy R .core
  | .base => .base
  | .fn r A B => .lolli (.box r A.toLNaive) B.toLNaive
  | .box _ r A => .box r A.toLNaive
  | .prod _ A B => .tensor trivial A.toLNaive B.toLNaive
  | .unit _ => .unit trivial
  | .sum _ A B => .oplus trivial A.toLNaive B.toLNaive

/-- The naive homomorphic term translation `⟦-⟧∘` (Graded Modal Core → Linear Core): as `⟦-⟧`
on functions and boxes, homomorphic on products, unit and sums. -/
def GTm.toLNaive {n : ℕ} : GTm .core n → LTm .core n
  | .var i => .var i
  | .app t₁ t₂ => .app t₁.toLNaive (.box t₂.toLNaive)
  | .lam t => .lam (.letbox (.var 0) (t.toLNaive.rename (upRen Fin.succ)))
  | .box _ t => .box t.toLNaive
  | .letbox _ t₁ t₂ => .letbox t₁.toLNaive t₂.toLNaive
  | .pair _ t₁ t₂ => .pair trivial t₁.toLNaive t₂.toLNaive
  | .letpair _ t₁ t₂ => .letpair trivial t₁.toLNaive t₂.toLNaive
  | .unit _ => .unit trivial
  | .letunit _ t₁ t₂ => .letunit trivial t₁.toLNaive t₂.toLNaive
  | .inl _ t => .inl trivial t.toLNaive
  | .inr _ t => .inr trivial t.toLNaive
  | .case _ t t₁ t₂ => .case trivial t.toLNaive t₁.toLNaive t₂.toLNaive

/-- The distributivity term `f = λp. let ⟨x, y⟩ = p in ⟨[x], [y]⟩` of Graded Modal Core. -/
def distribProd {n : ℕ} : GTm .core n :=
  .lam (.letpair trivial (.var 0) (.pair trivial (.box trivial (.var 1)) (.box trivial (.var 0))))

variable [PreorderedSemiring R]

/-- `f : (A × B) →^r (□_r A × □_r B)` in Graded Modal Core (in any context, using nothing). -/
theorem distribProd_typed {n : ℕ} (Γ : Fin n → GTy R .core) (r : R) (A B : GTy R .core) :
    GTyped Γ 0 distribProd
      (.fn r (.prod trivial A B) (.prod trivial (.box trivial r A) (.box trivial r B))) :=
  GTyped.abs (typed_pushProd_body (G := .core) trivial trivial Γ r A B)

/-! ## Inversion lemmas for Linear Core typing -/

section inversion

variable {L : LLevel}

lemma Use.add_lin {a b : Use R} (h : Use.Add a b Use.lin) : a = Use.lin ∨ b = Use.lin := by
  cases h <;> simp

/-- A boxed term never uses a linear assumption. -/
lemma LTyped.box_not_lin {n : ℕ} {Γ : Fin n → LTy R L} {u : Fin n → Use R} {s : LTm L n}
    {T : LTy R L} (h : LTyped Γ u (.box s) T) (i : Fin n) : u i ≠ Use.lin := by
  generalize e : (LTm.box s : LTm L n) = t at h
  induction h with
  | weak j _ _ ih | der j _ _ ih | approx j _ _ _ ih =>
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne hij]; exact ih i e
  | @pr _ _ uu _ _ r _ hg _ =>
    intro hl; simp only [smulCtx] at hl
    cases hu : uu i with
    | lin => exact hg i hu
    | none => rw [hu] at hl; cases hl
    | grd s => rw [hu] at hl; cases hl
  | _ => cases e

/-- A pair of boxed terms never uses a linear assumption. -/
lemma LTyped.pair_box_not_lin {n : ℕ} {Γ : Fin n → LTy R L} {u : Fin n → Use R}
    {h' : L.Core} {s₁ s₂ : LTm L n} {T : LTy R L}
    (h : LTyped Γ u (.pair h' (.box s₁) (.box s₂)) T) (i : Fin n) : u i ≠ Use.lin := by
  generalize e : (LTm.pair h' (.box s₁) (.box s₂) : LTm L n) = t at h
  induction h with
  | weak j _ _ ih | der j _ _ ih | approx j _ _ _ ih =>
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne hij]; exact ih i e
  | pair _ h₁ h₂ hadd =>
    cases e
    intro hl
    have := hadd i; rw [hl] at this
    rcases Use.add_lin this with h | h
    · exact h₁.box_not_lin i h
    · exact h₂.box_not_lin i h
  | _ => cases e

/-- Inversion for `λ`: the body is typable in some context. -/
lemma LTyped.lam_inv {n : ℕ} {Γ : Fin n → LTy R L} {u : Fin n → Use R} {s : LTm L (n + 1)}
    {T : LTy R L} (h : LTyped Γ u (.lam s) T) :
    ∃ (Γ' : Fin (n + 1) → LTy R L) (u' : Fin (n + 1) → Use R) (B : LTy R L), LTyped Γ' u' s B := by
  generalize e : (LTm.lam s : LTm L n) = t at h
  induction h with
  | weak _ _ _ ih | der _ _ _ ih | approx _ _ _ _ ih => exact ih e
  | abs hb => cases e; exact ⟨_, _, _, hb⟩
  | _ => cases e

/-- Inversion for `let [x] = t₁ in t₂`: the body is typable in some context. -/
lemma LTyped.letbox_inv {n : ℕ} {Γ : Fin n → LTy R L} {u : Fin n → Use R} {s₁ : LTm L n}
    {s₂ : LTm L (n + 1)} {T : LTy R L} (h : LTyped Γ u (.letbox s₁ s₂) T) :
    ∃ (Γ' : Fin (n + 1) → LTy R L) (u' : Fin (n + 1) → Use R) (B : LTy R L),
      LTyped Γ' u' s₂ B := by
  generalize e : (LTm.letbox s₁ s₂ : LTm L n) = t at h
  induction h with
  | weak _ _ _ ih | der _ _ _ ih | approx _ _ _ _ ih => exact ih e
  | letbox _ hb _ => cases e; exact ⟨_, _, _, hb⟩
  | _ => cases e

/-- Inversion for `let ⟨x, y⟩ = t₁ in t₂`: the body is typable with `x` and `y` linear. -/
lemma LTyped.letpair_inv {n : ℕ} {Γ : Fin n → LTy R L} {u : Fin n → Use R} {h' : L.Core}
    {s₁ : LTm L n} {s₂ : LTm L (n + 2)} {T : LTy R L} (h : LTyped Γ u (.letpair h' s₁ s₂) T) :
    ∃ (Γ' : Fin (n + 2) → LTy R L) (u' : Fin n → Use R) (B : LTy R L),
      LTyped Γ' (Use.lin .: Use.lin .: u') s₂ B := by
  generalize e : (LTm.letpair h' s₁ s₂ : LTm L n) = t at h
  induction h with
  | weak _ _ _ ih | der _ _ _ ih | approx _ _ _ _ ih => exact ih e
  | letpair _ _ hb _ => cases e; exact ⟨_, _, _, hb⟩
  | _ => cases e

end inversion

/-- **The naive translation `GMC ⇢ LC` is not type sound.** The well-typed Graded Modal Core term
`f = λp. let ⟨x, y⟩ = p in ⟨[x], [y]⟩` (`distribProd_typed`) translates to a Linear Core term
which has no typing derivation in any context, at any type. -/
theorem naive_distribProd_untypable {n : ℕ} (Γ : Fin n → LTy R .core) (u : Fin n → Use R)
    (T : LTy R .core) : ¬ LTyped Γ u (distribProd (n := n)).toLNaive T := by
  intro h
  obtain ⟨_, _, _, h₁⟩ := LTyped.lam_inv h
  obtain ⟨_, _, _, h₂⟩ := LTyped.letbox_inv h₁
  obtain ⟨_, _, _, h₃⟩ := LTyped.letpair_inv h₂
  exact LTyped.pair_box_not_lin h₃ 0 rfl

/-- Summary: there is a well-typed Graded Modal Core term whose naive translation is ill typed,
so `⟦-⟧∘` does not preserve typing (in contrast with `GTyped.toL`, the translation into Linear
Push Core). -/
theorem naive_not_typeSound (r : R) (A B : GTy R .core) :
    ∃ (t : GTm .core 0) (T : GTy R .core), GTyped (R := R) Fin.elim0 0 t T ∧
      ∀ (Γ : Fin 0 → LTy R .core) (u : Fin 0 → Use R) (T' : LTy R .core),
        ¬ LTyped Γ u t.toLNaive T' :=
  ⟨distribProd, _, distribProd_typed _ r A B, naive_distribProd_untypable⟩

end Coeffect
