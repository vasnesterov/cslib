/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite product distributions and conditioning on coordinates

Independent random variables `X_i` (`i : ι`, finite) with finite ranges `α i` and weights
`μ i : α i → ℝ` (probability mass functions; nonnegativity or total mass `1` are assumed only where
needed). The joint weight of an outcome `x : ∀ i, α i` is `piWeight μ x = ∏ i, μ i (x i)` and the
expectation of `f : (∀ i, α i) → ℝ` is `piExpect μ f = ∑ x, piWeight μ x * f x`; the probability
of an event is the expectation of its indicator.

*Conditioning* on `X_j = b` replaces the weight of coordinate `j` by the point mass
`Pi.single b 1`. This gives exact finite versions of the method of conditional expectations
(derandomization by fixing variables one at a time, e.g. for the Lovász local lemma).

## Main definitions

* `Cslib.Probability.piWeight μ x`, `Cslib.Probability.piExpect μ f`.

## Main statements

* `piExpect_prod` (**independence**): `E[∏ i, f i (X_i)] = ∏ i, E[f i (X_i)]`.
* linearity and monotonicity: `piExpect_add`, `piExpect_mul_left`, `piExpect_sum`, `piExpect_mono`,
  `piExpect_nonneg`, `piExpect_congr` (only outcomes of nonzero weight matter).
* `sum_mul_piExpect_update_single` (**law of total probability**): averaging the conditional
  expectations given `X_j = b` over `b` gives back the expectation.
* `piExpect_update_single_of_forall_update` (**independence of an unused variable**): conditioning
  on a coordinate that `f` does not read does not change `E[f]`.
* `piExpect_single` (all coordinates fixed): `E[f] = f x`.
* averaging over any finite weighted family: `exists_le_of_sum_mul_le` (some outcome is at most
  the average), `exists_pos_of_sum_mul_pos` (positive expectation ⇒ some positive outcome).
-/

@[expose] public section

open Finset

namespace Cslib.Probability

/-! ### Averaging -/

section Averaging

variable {β : Type*} {s : Finset β} {w F : β → ℝ}

/-- **Averaging.** If `w` is a probability vector on `s` with positive entries and the
`w`-average of `F` is at most `c`, then `F y ≤ c` for some `y ∈ s`. -/
theorem exists_le_of_sum_mul_le {c : ℝ} (hw : ∀ y ∈ s, 0 < w y) (hsum : ∑ y ∈ s, w y = 1)
    (h : ∑ y ∈ s, w y * F y ≤ c) : ∃ y ∈ s, F y ≤ c := by
  have hne : s.Nonempty := by
    by_contra h'; rw [not_nonempty_iff_eq_empty] at h'; simp [h'] at hsum
  have : ∑ y ∈ s, w y * F y ≤ ∑ y ∈ s, w y * c := by rwa [← sum_mul, hsum, one_mul]
  obtain ⟨y, hy, hle⟩ := exists_le_of_sum_le hne this
  exact ⟨y, hy, le_of_mul_le_mul_left hle (hw y hy)⟩

/-- **Probabilistic method.** If a weighted sum with nonnegative weights is positive, then some
summand is positive. -/
theorem exists_pos_of_sum_mul_pos (hw : ∀ y ∈ s, 0 ≤ w y) (h : 0 < ∑ y ∈ s, w y * F y) :
    ∃ y ∈ s, 0 < F y := by
  by_contra hc
  push Not at hc
  have : ∑ y ∈ s, w y * F y ≤ 0 :=
    sum_nonpos fun y hy => mul_nonpos_of_nonneg_of_nonpos (hw y hy) (hc y hy)
  linarith

end Averaging

/-! ### Product weights -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The weight `∏ i, μ i (x i)` of an outcome `x` under the product of the weights `μ i`. -/
def piWeight (μ : ∀ i, α i → ℝ) (x : ∀ i, α i) : ℝ := ∏ i, μ i (x i)

/-- The expectation `∑ x, (∏ i, μ i (x i)) * f x` of `f` under the product of the weights `μ i`. -/
noncomputable def piExpect (μ : ∀ i, α i → ℝ) (f : (∀ i, α i) → ℝ) : ℝ :=
  ∑ x, piWeight μ x * f x

variable {μ : ∀ i, α i → ℝ}

omit [DecidableEq ι] [∀ i, Fintype (α i)] in
/-- Product weights of nonnegative weights are nonnegative. -/
theorem piWeight_nonneg (hμ : ∀ i a, 0 ≤ μ i a) (x : ∀ i, α i) : 0 ≤ piWeight μ x :=
  prod_nonneg fun i _ => hμ i (x i)

omit [∀ i, Fintype (α i)] in
/-- Splitting off coordinate `j` of the weight. -/
theorem piWeight_eq_mul_prod_erase (μ : ∀ i, α i → ℝ) (j : ι) (x : ∀ i, α i) :
    piWeight μ x = μ j (x j) * ∏ i ∈ univ.erase j, μ i (x i) :=
  (mul_prod_erase univ (fun i => μ i (x i)) (mem_univ j)).symm

omit [∀ i, Fintype (α i)] in
/-- The weight after replacing the weight of coordinate `j` by `ν`. -/
theorem piWeight_update (μ : ∀ i, α i → ℝ) (j : ι) (ν : α j → ℝ) (x : ∀ i, α i) :
    piWeight (Function.update μ j ν) x = ν (x j) * ∏ i ∈ univ.erase j, μ i (x i) := by
  rw [piWeight_eq_mul_prod_erase _ j, Function.update_self]
  congr 1
  exact prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]

/-- **Independence.** The expectation of a product of functions of distinct coordinates is the
product of their expectations. -/
theorem piExpect_prod (μ : ∀ i, α i → ℝ) (f : ∀ i, α i → ℝ) :
    piExpect μ (fun x => ∏ i, f i (x i)) = ∏ i, ∑ a, μ i a * f i a := by
  simp only [piExpect, piWeight, ← prod_mul_distrib]
  exact (Fintype.prod_sum fun i a => μ i a * f i a).symm

/-- Linearity of `piExpect`: additivity. -/
theorem piExpect_add (μ : ∀ i, α i → ℝ) (f g : (∀ i, α i) → ℝ) :
    piExpect μ (fun x => f x + g x) = piExpect μ f + piExpect μ g := by
  simp only [piExpect, mul_add, sum_add_distrib]

/-- Linearity of `piExpect`: scalar multiples. -/
theorem piExpect_mul_left (μ : ∀ i, α i → ℝ) (c : ℝ) (f : (∀ i, α i) → ℝ) :
    piExpect μ (fun x => c * f x) = c * piExpect μ f := by
  simp only [piExpect, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- Linearity of `piExpect`: finite sums. -/
theorem piExpect_sum {κ : Type*} (μ : ∀ i, α i → ℝ) (s : Finset κ) (f : κ → (∀ i, α i) → ℝ) :
    piExpect μ (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, piExpect μ (f k) := by
  simp only [piExpect, mul_sum]
  exact sum_comm

/-- Monotonicity of `piExpect` for nonnegative weights. -/
theorem piExpect_mono (hμ : ∀ i a, 0 ≤ μ i a) {f g : (∀ i, α i) → ℝ} (h : ∀ x, f x ≤ g x) :
    piExpect μ f ≤ piExpect μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (piWeight_nonneg hμ x)

/-- The expectation of a nonnegative function under nonnegative weights is nonnegative. -/
theorem piExpect_nonneg (hμ : ∀ i a, 0 ≤ μ i a) {f : (∀ i, α i) → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ piExpect μ f :=
  sum_nonneg fun x _ => mul_nonneg (piWeight_nonneg hμ x) (h x)

/-- Only outcomes of nonzero weight matter. -/
theorem piExpect_congr {f g : (∀ i, α i) → ℝ} (h : ∀ x, piWeight μ x ≠ 0 → f x = g x) :
    piExpect μ f = piExpect μ g :=
  sum_congr rfl fun x _ => by
    by_cases hx : piWeight μ x = 0
    · simp [hx]
    · rw [h x hx]

variable [∀ i, DecidableEq (α i)]

/-- **Law of total probability.** Averaging, over the value `b` of coordinate `j`, the
expectation conditioned on `X_j = b` gives back the expectation. -/
theorem sum_mul_piExpect_update_single (μ : ∀ i, α i → ℝ) (j : ι) (f : (∀ i, α i) → ℝ) :
    ∑ b, μ j b * piExpect (Function.update μ j (Pi.single b 1)) f = piExpect μ f := by
  simp only [piExpect, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp only [piWeight_update, Pi.single_apply, piWeight_eq_mul_prod_erase μ j x]
  simp [← mul_assoc]

/-- The value-swap at coordinate `j`, an involution of the outcome space. -/
private def swapAt (j : ι) (a b : α j) : (∀ i, α i) ≃ (∀ i, α i) :=
  Function.Involutive.toPerm (fun x => Function.update x j (Equiv.swap a b (x j))) (by
    intro x
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h])

/-- **Independence of an unused variable.** If `f` does not read coordinate `j` and the weight of
`j` has total mass `1`, conditioning on `X_j = b` does not change the expectation of `f`. -/
theorem piExpect_update_single_of_forall_update (j : ι) (hμ : ∑ a, μ j a = 1)
    {f : (∀ i, α i) → ℝ} (hf : ∀ x a, f (Function.update x j a) = f x) (b : α j) :
    piExpect (Function.update μ j (Pi.single b 1)) f = piExpect μ f := by
  -- the conditional expectation does not depend on the value `b`
  have hconst : ∀ c, piExpect (Function.update μ j (Pi.single c 1)) f =
      piExpect (Function.update μ j (Pi.single b 1)) f := by
    intro c
    unfold piExpect
    rw [← (swapAt j b c).sum_comp]
    refine sum_congr rfl fun x _ => ?_
    have hsw : swapAt j b c x = Function.update x j (Equiv.swap b c (x j)) := rfl
    rw [hsw, hf, piWeight_update, piWeight_update]
    congr 2
    · simp only [Function.update_self, Pi.single_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_right]
    · exact prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [← sum_mul_piExpect_update_single μ j f]
  simp_rw [hconst, ← sum_mul, hμ, one_mul]

/-- With every coordinate fixed (`X_i = x i`), the expectation is the value at `x`. -/
theorem piExpect_single (x : ∀ i, α i) (f : (∀ i, α i) → ℝ) :
    piExpect (fun i => Pi.single (x i) 1) f = f x := by
  classical
  unfold piExpect
  have hw : ∀ y : ∀ i, α i, piWeight (fun i => Pi.single (x i) 1) y = if y = x then 1 else 0 := by
    intro y
    unfold piWeight
    by_cases hy : y = x
    · subst hy; simp
    · obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
        by_contra h; push Not at h; exact hy (funext h)
      rw [ite_eq_right hy]
      exact prod_eq_zero (mem_univ i) (by simp [hi])
  simp_rw [hw]
  simp

end Cslib.Probability
