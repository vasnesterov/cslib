/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

/-!
# An average is pulled towards each of its terms

The averaging step of approximate-agreement analyses (Dolev–Lynch–Pinter–Stark–Weihl, Vaidya–Tseng–
Liang, Mendes–Herlihy, …): if all averaged values lie below `b`, the average stays below `b` by at
least the weight of any one term times that term's distance to `b`. With uniform weights over at
most `n` values this is the bound `avg ≤ b - (b - x j) / n` that makes the spread of the honest
values contract by a factor `1 - 1/n` per round.

## Main statements

* `Finset.sum_mul_le_sub_mul_sub`, `Finset.add_mul_sub_le_sum_mul`: for a convex combination
  `∑ w i * x i` of values in `[a, b]`, `a + w j * (x j - a) ≤ ∑ w i * x i ≤ b - w j * (b - x j)`.
* `Finset.sum_div_card_le_sub_div`, `Finset.add_div_le_sum_div_card`: the same for the
  arithmetic mean `(∑ i ∈ s, x i) / #s` of at most `n` values, with weight `1 / n`.
-/

@[expose] public section

namespace Finset

variable {ι K : Type*}

section Ring

variable [Ring K] [PartialOrder K] [IsOrderedRing K] {s : Finset ι} {w x : ι → K}
  {a b : K} {j : ι}

/-- A convex combination of values `≤ b` is at most `b - w j * (b - x j)`, for each term `j`. -/
theorem sum_mul_le_sub_mul_sub (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, x i ≤ b) (hj : j ∈ s) : ∑ i ∈ s, w i * x i ≤ b - w j * (b - x j) := by
  have e : ∑ i ∈ s, w i * x i = b - ∑ i ∈ s, w i * (b - x i) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hw1, one_mul, sub_sub_cancel]
  rw [e]
  exact sub_le_sub_left (single_le_sum (f := fun i => w i * (b - x i))
    (fun i hi => mul_nonneg (hw0 i hi) (sub_nonneg.2 (hx i hi))) hj) b

/-- A convex combination of values `≥ a` is at least `a + w j * (x j - a)`, for each term `j`. -/
theorem add_mul_sub_le_sum_mul (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, a ≤ x i) (hj : j ∈ s) : a + w j * (x j - a) ≤ ∑ i ∈ s, w i * x i := by
  have h := sum_mul_le_sub_mul_sub (x := fun i => -x i) (b := -a) hw0 hw1
    (fun i hi => neg_le_neg (hx i hi)) hj
  simp only [mul_neg, sum_neg_distrib, neg_sub_neg] at h
  rwa [← neg_add', neg_le_neg_iff] at h

end Ring

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : Finset ι} {x : ι → K}
  {a b : K} {j : ι} {n : ℕ}

/-- The mean of at most `n` values `≤ b` is at most `b - (b - x j) / n`, for each term `j`. -/
theorem sum_div_card_le_sub_div (hx : ∀ i ∈ s, x i ≤ b) (hj : j ∈ s) (hn : #s ≤ n) :
    (∑ i ∈ s, x i) / #s ≤ b - (b - x j) / n := by
  have hs : (0 : K) < #s := by exact_mod_cast card_pos.2 ⟨j, hj⟩
  have h := sum_mul_le_sub_mul_sub (w := fun _ => (#s : K)⁻¹) (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hs.ne']) hx hj
  rw [← mul_sum, inv_mul_eq_div] at h
  refine h.trans (sub_le_sub_left ?_ b)
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (sub_nonneg.2 (hx j hj)) hs (by exact_mod_cast hn)

/-- The mean of at most `n` values `≥ a` is at least `a + (x j - a) / n`, for each term `j`. -/
theorem add_div_le_sum_div_card (hx : ∀ i ∈ s, a ≤ x i) (hj : j ∈ s) (hn : #s ≤ n) :
    a + (x j - a) / n ≤ (∑ i ∈ s, x i) / #s := by
  have h := sum_div_card_le_sub_div (x := fun i => -x i) (b := -a)
    (fun i hi => neg_le_neg (hx i hi)) hj hn
  have e : (-a - -x j) / (n : K) = (x j - a) / n := by ring
  rw [sum_neg_distrib, neg_div, e] at h
  linarith

end Field

end Finset
