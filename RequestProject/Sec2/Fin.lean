module

public import Mathlib

/-!
# De Bruijn infrastructure on `Fin n`

Terms of all calculi are intrinsically scoped: `Tm n` is the type of terms with (at most)
`n` free variables, represented as de Bruijn indices `Fin n`. In particular `Tm 0` is the
type of closed terms.

This file collects a few generic helpers on functions out of `Fin n`:

* `a .: f` extends an environment `f : Fin n → α` with a new innermost entry `a`;
* `upRen ρ` lifts a renaming under a binder;
* `pushAlong ρ d f` transports an environment along an injective renaming, filling
  positions outside the image of `ρ` with the default `d`.
-/

@[expose] public section

namespace Coeffect

universe u

/-- Extend an environment with a new innermost (index `0`) entry. -/
def scons {α : Sort u} {n : ℕ} (a : α) (f : Fin n → α) : Fin (n + 1) → α :=
  fun i => Fin.cases a f i

@[inherit_doc] infixr:67 " .: " => scons

@[simp] lemma scons_zero {α : Sort u} {n : ℕ} (a : α) (f : Fin n → α) : (a .: f) 0 = a := rfl

@[simp] lemma scons_succ {α : Sort u} {n : ℕ} (a : α) (f : Fin n → α) (i : Fin n) :
    (a .: f) i.succ = f i := rfl

@[simp] lemma scons_one {α : Sort u} {n : ℕ} (a b : α) (f : Fin n → α) :
    (a .: b .: f) 1 = b := rfl

lemma scons_comp_succ {α : Sort u} {n : ℕ} (a : α) (f : Fin n → α) :
    (a .: f) ∘ Fin.succ = f := rfl

lemma scons_eta {α : Sort u} {n : ℕ} (f : Fin (n + 1) → α) : (f 0 .: (f ∘ Fin.succ)) = f := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma scons_map {α β : Sort u} {n : ℕ} (g : α → β) (a : α) (f : Fin n → α) :
    (fun i => g ((a .: f) i)) = (g a .: (g ∘ f)) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp

/-- Lift a renaming under a binder. -/
def upRen {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  0 .: (Fin.succ ∘ ρ)

@[simp] lemma upRen_zero {n m : ℕ} (ρ : Fin n → Fin m) : upRen ρ 0 = 0 := rfl

@[simp] lemma upRen_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    upRen ρ i.succ = (ρ i).succ := rfl

@[simp] lemma upRen_upRen_one {n m : ℕ} (ρ : Fin n → Fin m) : upRen (upRen ρ) 1 = 1 := rfl

lemma upRen_comp {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    upRen ρ' ∘ upRen ρ = upRen (ρ' ∘ ρ) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma upRen_id {n : ℕ} : upRen (id : Fin n → Fin n) = id := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma upRen_comp_succ {n m : ℕ} (ρ : Fin n → Fin m) :
    upRen ρ ∘ Fin.succ = Fin.succ ∘ ρ := rfl

lemma upRen_injective {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) :
    Function.Injective (upRen ρ) := by
  intro i j h
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp_all [Fin.succ_ne_zero]
  · exact (Fin.succ_ne_zero _ h.symm).elim
  · exact hρ h

/-- Transport an environment along a renaming `ρ`, filling positions outside the image with `d`. -/
noncomputable def pushAlong {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) :
    Fin m → α :=
  open Classical in fun j => if h : ∃ i, ρ i = j then f h.choose else d

lemma pushAlong_apply {α : Sort u} {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    (d : α) (f : Fin n → α) (i : Fin n) : pushAlong ρ d f (ρ i) = f i := by
  have h : ∃ i', ρ i' = ρ i := ⟨i, rfl⟩
  simp only [pushAlong, dif_pos h]
  rw [hρ h.choose_spec]

lemma pushAlong_off {α : Sort u} {n m : ℕ} {ρ : Fin n → Fin m} (d : α) (f : Fin n → α) (j : Fin m)
    (hj : ∀ i, ρ i ≠ j) : pushAlong ρ d f j = d := by
  have h : ¬ ∃ i, ρ i = j := fun ⟨i, hi⟩ => hj i hi
  simp only [pushAlong, dif_neg h]

/-- The canonical way of proving a property of every position of `Fin m` w.r.t. a renaming. -/
lemma range_or_off {n m : ℕ} (ρ : Fin n → Fin m) (j : Fin m) :
    (∃ i, ρ i = j) ∨ (∀ i, ρ i ≠ j) := by
  by_cases h : ∃ i, ρ i = j
  · exact Or.inl h
  · exact Or.inr fun i hi => h ⟨i, hi⟩

end Coeffect
