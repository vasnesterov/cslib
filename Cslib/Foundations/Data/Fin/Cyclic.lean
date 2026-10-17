/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic indices on `Fin n`

`Fin n` with its modular addition is the oriented ring of `n` positions: `x + 1` is the clockwise
successor of `x`. This file collects the facts about this ring used by ring algorithms (tokens
passed around a ring, clocks counting modulo `n`, positions read cyclically).

## Main definitions

* `Fin.cdist x y`: the clockwise (forward) cyclic distance `(y - x) mod n` from `x` to `y`.

## Main statements

* `Fin.add_one_ne_self`: `x + 1 ≠ x` on a ring of at least two positions.
* `Fin.val_iterate_add_one`, `Fin.exists_iterate_add_one_eq`: `j` clockwise steps from `x` reach
  `(x + j) mod n`, and every position is reached.
* `Fin.cdist_eq_ite`: the distance as an explicit natural-number formula.
* `Fin.cdist_lt`, `Fin.cdist_eq_zero`, `Fin.cdist_pos`, `Fin.cdist_right_inj`,
  `Fin.exists_cdist_eq`, `Fin.cdist_add_cdist`, `Fin.cdist_add_cdist_swap`,
  `Fin.cdist_add_one_left`: the basic API of the cyclic distance.
-/

@[expose] public section

namespace Fin

variable {n : ℕ}

/-- On a ring of at least two positions, the clockwise successor `x + 1` differs from `x`. -/
theorem add_one_ne_self [NeZero n] (hn : n ≠ 1) (x : Fin n) : x + 1 ≠ x :=
  add_ne_left.2 (Fin.one_eq_zero_iff.not.2 hn)

/-- `j` clockwise steps from `x` reach position `(x + j) mod n`. -/
theorem val_iterate_add_one [NeZero n] (x : Fin n) (j : ℕ) :
    ((· + 1)^[j] x).val = (x.val + j) % n := by
  induction j generalizing x with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, Fin.val_add, Fin.val_one']
    simp only [Nat.add_mod_mod, Nat.mod_add_mod]; congr 1; omega

/-- Every position is reached from `x` by finitely many clockwise steps. -/
theorem exists_iterate_add_one_eq [NeZero n] (x y : Fin n) : ∃ j : ℕ, (· + 1)^[j] x = y := by
  refine ⟨y.val + n - x.val, Fin.ext ?_⟩
  have := x.isLt; have := y.isLt
  rw [val_iterate_add_one, show x.val + (y.val + n - x.val) = y.val + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

/-! ### Clockwise cyclic distance -/

/-- The clockwise (forward) cyclic distance `(y - x) mod n` from `x` to `y`: the number of
clockwise steps `· + 1` leading from `x` to `y`. It is not symmetric:
`cdist x y + cdist y x = n` for `x ≠ y` (`cdist_add_cdist_swap`). -/
def cdist (x y : Fin n) : ℕ := (y - x : Fin n)

/-- The cyclic distance as an explicit natural-number formula. -/
theorem cdist_eq_ite (x y : Fin n) :
    cdist x y = if x.val ≤ y.val then y.val - x.val else y.val + n - x.val := by
  have hx := x.isLt
  rw [cdist, Fin.val_sub]
  split_ifs with h
  · rw [show n - x.val + y.val = y.val - x.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The cyclic distance is less than the ring size. -/
theorem cdist_lt (x y : Fin n) : cdist x y < n := (y - x).isLt

/-- The distance from a position to itself is zero. -/
@[simp]
theorem cdist_self (x : Fin n) : cdist x x = 0 := by simp [cdist_eq_ite]

/-- The cyclic distance vanishes exactly on the diagonal. -/
@[simp]
theorem cdist_eq_zero {x y : Fin n} : cdist x y = 0 ↔ x = y := by
  have := x.isLt; have := y.isLt
  rw [cdist_eq_ite, Fin.ext_iff]; split_ifs <;> omega

/-- The cyclic distance between distinct positions is positive. -/
theorem cdist_pos {x y : Fin n} : 0 < cdist x y ↔ x ≠ y := by
  rw [Nat.pos_iff_ne_zero, Ne, cdist_eq_zero]

/-- The cyclic distance from a fixed `x` determines the target. -/
theorem cdist_right_injective (x : Fin n) : Function.Injective (cdist x) := by
  intro y y' h
  have := x.isLt; have := y.isLt; have := y'.isLt
  rw [cdist_eq_ite, cdist_eq_ite] at h; apply Fin.ext; split_ifs at h <;> omega

/-- Equal distances from the same `x` mean equal targets. -/
@[simp]
theorem cdist_right_inj {x y y' : Fin n} : cdist x y = cdist x y' ↔ y = y' :=
  (cdist_right_injective x).eq_iff

/-- Every distance `t < n` is attained from every `x`. -/
theorem exists_cdist_eq (x : Fin n) {t : ℕ} (ht : t < n) : ∃ y, cdist x y = t := by
  have := x.isLt
  by_cases h : x.val + t < n
  · exact ⟨⟨x.val + t, h⟩, by rw [cdist_eq_ite]; simp only; split_ifs <;> omega⟩
  · exact ⟨⟨x.val + t - n, by omega⟩, by rw [cdist_eq_ite]; simp only; split_ifs <;> omega⟩

/-- Going from `x` to `z` via `y` takes `cdist x z` steps, or one more full turn. -/
theorem cdist_add_cdist (x y z : Fin n) :
    cdist x y + cdist y z = cdist x z ∨ cdist x y + cdist y z = cdist x z + n := by
  have := x.isLt; have := y.isLt; have := z.isLt
  simp only [cdist_eq_ite]; split_ifs <;> omega

/-- Going from `x` to `y ≠ x` and back takes exactly one full turn. -/
theorem cdist_add_cdist_swap {x y : Fin n} (h : x ≠ y) : cdist x y + cdist y x = n := by
  have := x.isLt; have := y.isLt; have := Fin.val_ne_of_ne h
  simp only [cdist_eq_ite]; split_ifs <;> omega

/-- A clockwise step from `x ≠ y` brings `x` one step closer to `y`. -/
theorem cdist_add_one_left [NeZero n] {x y : Fin n} (h : x ≠ y) :
    cdist (x + 1) y + 1 = cdist x y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne n)).symm⟩
  have := x.isLt; have := y.isLt; have := Fin.val_ne_of_ne h
  rw [cdist_eq_ite, cdist_eq_ite, Fin.val_add_one]
  have hl : x = Fin.last m ↔ x.val = m := by simp [Fin.ext_iff]
  split_ifs at * <;> omega

end Fin
