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
abbrev scons : α → (Fin n → α) → Fin (n + 1) → α := Fin.cases -- (motive := fun (_ : Fin (n + 1)) => α)
-- abbrev scons : α → (Fin n → α) → Fin (n + 1) → α := Fin.cons (α := fun _ => α)

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

/-
make renamerX takes Fin with at least 3 elements
0 -> doesnt change 1 and 2 - swaps
outputs Fin with at least 3 elements too
-/

-- def swap01 {n : ℕ} : Fin (n + 2) → Fin (n + 2) :=
--   scons 1 (scons 0 (fun i => i.succ.succ))
--
-- #reduce swap01 (0 : Fin 4)  -- 1 (swapped)
-- #reduce swap01 (1 : Fin 4)  -- 0 (swapped)
-- #reduce swap01 (2 : Fin 4)  -- 2 (unchanged)
-- #reduce swap01 (3 : Fin 4)  -- 3 (unchanged)
--
-- def renamerX {n : ℕ} : Fin (n + 3) → Fin (n + 3) :=
--   -- scons 0 (scons 2 (scons 1 (fun i => i.succ.succ.succ)))
--   upRen swap01
--
-- #reduce renamerX (0 : Fin 4)  -- 0 (unchanged)
-- #reduce renamerX (1 : Fin 4)  -- 2 (swapped)
-- #reduce renamerX (2 : Fin 4)  -- 1 (swapped)
-- #reduce renamerX (3 : Fin 4)  -- 3 (unchanged)

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

/- Transport an environment along a renaming `ρ`, filling positions outside the image with `d`. -/

-- noncomputable def pushAlong {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) :
--     Fin m → α :=
--   open Classical in fun j => if h : ∃ i, ρ i = j then f h.choose else d

def pushAlong {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) :
    Fin m → α :=
  fun j =>
    match Fin.find? (fun i => ρ i = j) with
    | some i => f i
    | none   => d

/-- Tail-recursive helper: scans from index `k` up to `n - 1`. -/
-- def pushAlong.go {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) (j : Fin m) (k : ℕ) : α :=
--   if h : k < n then
--     if ρ ⟨k, h⟩ == j then
--       f ⟨k, h⟩
--     else
--       pushAlong.go ρ d f j (k + 1)
--   else
--     d
-- termination_by n - k
-- /-- Main entry point: starts search at index `0`. -/
-- def pushAlong {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) (j : Fin m) : α :=
--   pushAlong.go ρ d f j 0

-- /-- Tail-recursive binary search: searches range [lo, hi) in O(log n) time.
--     Requires `h_sorted` proving that `ρ` is sorted (strictly increasing). -/
-- def pushAlongBinSearch {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (h_sorted : StrictMono ρ)
--     (d : α) (f : Fin n → α) (j : Fin m) (lo hi : ℕ) (hhi : hi ≤ n) : α :=
--   if h : lo < hi then
--     let mid := (lo + hi) / 2
--     have hmid : mid < n := by omega
--     let mid_fin : Fin n := ⟨mid, hmid⟩
--
--     if ρ mid_fin == j then
--       f mid_fin
--     else if j < ρ mid_fin then
--       -- Target is in left half [lo, mid)
--       pushAlongBinSearch ρ h_sorted d f j lo mid (by omega)
--     else
--       -- Target is in right half [mid + 1, hi)
--       pushAlongBinSearch ρ h_sorted d f j (mid + 1) hi hhi
--   else
--     d
-- termination_by hi - lo
-- /-- Main entry point: requires proof that `ρ` is sorted (`h_sorted`). -/
-- def pushAlongBin {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (h_sorted : StrictMono ρ)
--     (d : α) (f : Fin n → α) (j : Fin m) : α :=
--   pushAlongBinSearch ρ h_sorted d f j 0 n (by omega)

-- def pushAlong {α : Sort u} {n m : ℕ} (ρ : Fin n → Fin m) (d : α) (f : Fin n → α) :
--     Fin m → α :=
--   let table : Vector α m :=
--     (List.finRange n).foldl
--       (fun v i => let ρi := (ρ i); v.set ρi.val (f i) ρi.isLt)
--       (Vector.replicate m d)
--   fun j => table[j]

-- -- Map 0 ↦ 1, 1 ↦ 3
-- def ρ : Fin 2 → Fin 4
--   | ⟨0, _⟩ => 1
--   | ⟨1, _⟩ => 3
--
-- -- Environment assigning "A" and "B"
-- def f : Fin 2 → String
--   | ⟨0, _⟩ => "A"
--   | ⟨1, _⟩ => "B"
--
-- def pushed := pushAlong ρ "empty" f
--
-- #eval pushed 0  -- "empty" (unmapped, got default)
-- #eval pushed 1  -- "A"     (mapped from 0)
-- #eval pushed 2  -- "empty" (unmapped, got default)
-- #eval pushed 3  -- "B"     (mapped from 1)

lemma pushAlong_apply {α : Sort u} {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    (d : α) (f : Fin n → α) (i : Fin n) : pushAlong ρ d f (ρ i) = f i := by
  have h : ∃ i', ρ i' = ρ i := ⟨i, rfl⟩
  simp only [pushAlong]
  simp_all only [exists_apply_eq_apply]
  split
  next x i_1
    heq =>
    simp_all only [Fin.findSome?_eq_some_iff, Option.guard_eq_some_iff, decide_eq_true_eq, Option.guard_eq_none_iff,
      decide_eq_false_iff_not, ↓existsAndEq, true_and]
    obtain ⟨left, right⟩ := heq
    solve_by_elim
  next x heq =>
    simp_all only [Fin.findSome?_eq_none_iff, Option.guard_eq_none_iff, decide_eq_false_iff_not]
    solve_by_elim
  -- rw [hρ h.choose_spec]

lemma pushAlong_off {α : Sort u} {n m : ℕ} {ρ : Fin n → Fin m} (d : α) (f : Fin n → α) (j : Fin m)
    (hj : ∀ i, ρ i ≠ j) : pushAlong ρ d f j = d := by
  have h : ¬ ∃ i, ρ i = j := fun ⟨i, hi⟩ => hj i hi
  simp only [pushAlong]
  grind only [= Fin.find?_eq_some_iff, #3959, #4095]

/-- The canonical way of proving a property of every position of `Fin m` w.r.t. a renaming. -/
lemma range_or_off {n m : ℕ} (ρ : Fin n → Fin m) (j : Fin m) :
    (∃ i, ρ i = j) ∨ (∀ i, ρ i ≠ j) := by
  by_cases h : ∃ i, ρ i = j
  · exact Or.inl h
  · exact Or.inr fun i hi => h ⟨i, hi⟩

end Coeffect
