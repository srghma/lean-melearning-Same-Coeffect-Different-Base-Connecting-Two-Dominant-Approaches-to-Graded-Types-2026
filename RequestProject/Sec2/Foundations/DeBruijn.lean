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
* `invTable ρ` is the inverse table of a renaming (built once in `O(n + m)`);
* `pushAlong ρ d f` transports an environment along an injective renaming, filling
  positions outside the image of `ρ` with the default `d` (`O(1)` per lookup after the
  table is built).
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

/-- One step of `invTable`: record that `i` is a preimage of `ρ i`. -/
def invTableStep {n m : ℕ} (ρ : Fin n → Fin m) (v : Vector (Option (Fin n)) m) (i : Fin n) :
    Vector (Option (Fin n)) m :=
  v.set (ρ i) (some i)

/-- The inverse table of a renaming `ρ : Fin n → Fin m`: entry `j` holds some preimage of `j`
(the last one, if `ρ` is not injective) or `none`. Built in `O(n + m)`. -/
def invTable {n m : ℕ} (ρ : Fin n → Fin m) : Vector (Option (Fin n)) m :=
  (List.finRange n).foldl (invTableStep ρ) (Vector.replicate m none)

lemma invTable_sound_aux {n m : ℕ} (ρ : Fin n → Fin m) (l : List (Fin n))
    (v : Vector (Option (Fin n)) m) (hv : ∀ (j : Fin m) i, v[j] = some i → ρ i = j) :
    ∀ (j : Fin m) i, (l.foldl (invTableStep ρ) v)[j] = some i → ρ i = j := by
  induction l generalizing v with
  | nil => exact hv
  | cons x l ih =>
    refine ih _ fun j i h => ?_
    simp only [invTableStep, Fin.getElem_fin, Vector.getElem_set] at h
    split_ifs at h with hx
    · cases h; exact Fin.ext hx
    · exact hv j i h

lemma invTable_complete_aux {n m : ℕ} (ρ : Fin n → Fin m) (l : List (Fin n))
    (v : Vector (Option (Fin n)) m) (i : Fin n) (hi : i ∈ l ∨ v[ρ i] ≠ none) :
    (l.foldl (invTableStep ρ) v)[ρ i] ≠ none := by
  induction l generalizing v with
  | nil => exact hi.resolve_left List.not_mem_nil
  | cons x l ih =>
    refine ih _ ?_
    have hset : (invTableStep ρ v x)[ρ i] = if (ρ x : ℕ) = ρ i then some x else v[ρ i] :=
      Vector.getElem_set _ _
    rcases hi with hi | hi
    · rcases List.mem_cons.1 hi with rfl | hi
      · right; rw [hset, if_pos rfl]; exact Option.some_ne_none _
      · exact Or.inl hi
    · right; rw [hset]; split
      · exact Option.some_ne_none _
      · exact hi

lemma invTable_sound {n m : ℕ} {ρ : Fin n → Fin m} {j : Fin m} {i : Fin n}
    (h : (invTable ρ)[j] = some i) : ρ i = j :=
  invTable_sound_aux ρ _ _ (fun j i h => by simp at h) j i h

lemma invTable_complete {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) : (invTable ρ)[ρ i] ≠ none :=
  invTable_complete_aux ρ _ _ i (Or.inl (List.mem_finRange i))

lemma invTable_apply {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (i : Fin n) :
    (invTable ρ)[ρ i] = some i := by
  cases h : (invTable ρ)[ρ i] with
  | none => exact absurd h (invTable_complete ρ i)
  | some k => rw [hρ (invTable_sound h)]

lemma invTable_off {n m : ℕ} {ρ : Fin n → Fin m} {j : Fin m} (hj : ∀ i, ρ i ≠ j) :
    (invTable ρ)[j] = none := by
  cases h : (invTable ρ)[j] with
  | none => rfl
  | some k => exact absurd (invTable_sound h) (hj k)

/-- Transport an environment along a renaming `ρ`, filling positions outside the image with `d`.
The inverse table of `ρ` is computed once (`O(n + m)`), after which each lookup is `O(1)`. -/
def pushAlong {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) :
    Fin m → α :=
  let tbl := invTable ρ
  fun j => match tbl[j] with
    | some i => f i
    | none => d

lemma pushAlong_apply {α : Sort u} {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    (d : α) (f : Fin n → α) (i : Fin n) : pushAlong ρ d f (ρ i) = f i := by
  simp only [pushAlong, invTable_apply hρ]

lemma pushAlong_off {α : Sort u} {n m : ℕ} {ρ : Fin n → Fin m} (d : α) (f : Fin n → α) (j : Fin m)
    (hj : ∀ i, ρ i ≠ j) : pushAlong ρ d f j = d := by
  simp only [pushAlong, invTable_off hj]

/-- The canonical way of proving a property of every position of `Fin m` w.r.t. a renaming. -/
lemma range_or_off {n m : ℕ} (ρ : Fin n → Fin m) (j : Fin m) :
    (∃ i, ρ i = j) ∨ (∀ i, ρ i ≠ j) := by
  cases h : (invTable ρ)[j] with
  | some i => exact Or.inl ⟨i, invTable_sound h⟩
  | none => exact Or.inr fun i hi => invTable_complete ρ i (hi ▸ h)

/-- Constructive version of `Function.update_idem`. -/
lemma update_idem' {α : Sort u} {β : α → Sort*} [DecidableEq α] {a : α} (v w : β a)
    (f : ∀ x, β x) : Function.update (Function.update f a v) a w = Function.update f a w := by
  funext x
  by_cases h : x = a
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]

/-- Constructive version of `Function.update_eq_self`. -/
lemma update_eq_self' {α : Sort u} {β : α → Sort*} [DecidableEq α] (a : α) (f : ∀ x, β x) :
    Function.update f a (f a) = f := by
  funext x
  by_cases h : x = a
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h]

end Coeffect
