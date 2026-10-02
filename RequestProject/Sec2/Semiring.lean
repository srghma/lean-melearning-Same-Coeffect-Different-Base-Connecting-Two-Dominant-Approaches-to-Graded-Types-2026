module

public import Mathlib

/-!
# Pre-ordered semirings of grades (Section 2.1)

Both lineages of calculi are parameterised by a *pre-ordered semiring*
`(𝓡, ·, 1, +, 0, ⊑)` in which addition and multiplication are monotone
with respect to `⊑`.

We also provide the examples of the paper which are needed later:

* the *linearity semiring* (none-one-tons) `{0, 1, ω}` (Example 2.2);
* the *product* of two pre-ordered semirings (Example 2.4).
-/

@[expose] public section

namespace Coeffect

/-- A pre-ordered semiring: a semiring with a pre-order for which `+` and `*` are monotone. -/
class PreorderedSemiring (R : Type*) extends Semiring R, Preorder R where
  add_mono : ∀ {a b c d : R}, a ≤ b → c ≤ d → a + c ≤ b + d
  mul_mono : ∀ {a b c d : R}, a ≤ b → c ≤ d → a * c ≤ b * d

/-! ## The linearity semiring `{0, 1, ω}` -/

/-- The *none-one-tons* / linearity semiring `{0, 1, ω}`. -/
inductive Lin : Type
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

namespace Lin

/-- Addition: `1 + 1 = ω`, `ω + r = ω = r + ω`, `0` is neutral. -/
def add : Lin → Lin → Lin
  | zero, r => r
  | r, zero => r
  | _, _ => omega

/-- Multiplication: `0` absorbing, `1` neutral, `ω · ω = ω`. -/
def mul : Lin → Lin → Lin
  | zero, _ => zero
  | _, zero => zero
  | one, r => r
  | r, one => r
  | omega, omega => omega

/-- The ordering: `0 ⊑ ω`, `1 ⊑ ω`, plus reflexivity. -/
def le : Lin → Lin → Prop
  | zero, zero => True
  | one, one => True
  | omega, omega => True
  | zero, omega => True
  | one, omega => True
  | _, _ => False

instance : Zero Lin := ⟨zero⟩
instance : One Lin := ⟨one⟩
instance : Add Lin := ⟨add⟩
instance : Mul Lin := ⟨mul⟩

/-- `ω`, the "arbitrary usage" grade. -/
scoped notation "ω" => Lin.omega

instance : CommSemiring Lin where
  add := add
  mul := mul
  zero := zero
  one := one
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  nsmul := nsmulRec
  npow := npowRec

instance : PreorderedSemiring Lin where
  le := le
  le_refl := by intro a; cases a <;> trivial
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [le]
  add_mono := by
    intro a b c d hab hcd
    cases a <;> cases b <;> cases c <;> cases d <;> trivial
  mul_mono := by
    intro a b c d hab hcd
    cases a <;> cases b <;> cases c <;> cases d <;> trivial

lemma zero_le_omega : (0 : Lin) ≤ ω := trivial
lemma one_le_omega : (1 : Lin) ≤ ω := trivial
@[simp] lemma omega_add (r : Lin) : ω + r = ω := by cases r <;> rfl
@[simp] lemma add_omega (r : Lin) : r + ω = ω := by cases r <;> rfl
@[simp] lemma omega_mul_omega : ω * ω = ω := rfl
@[simp] lemma one_add_one : (1 : Lin) + 1 = ω := rfl

end Lin

/-! ## Product of pre-ordered semirings -/

instance PreorderedSemiring.prod (R S : Type*) [PreorderedSemiring R] [PreorderedSemiring S] :
    PreorderedSemiring (R × S) where
  add_mono := fun h1 h2 =>
    ⟨PreorderedSemiring.add_mono h1.1 h2.1, PreorderedSemiring.add_mono h1.2 h2.2⟩
  mul_mono := fun h1 h2 =>
    ⟨PreorderedSemiring.mul_mono h1.1 h2.1, PreorderedSemiring.mul_mono h1.2 h2.2⟩

end Coeffect
