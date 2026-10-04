/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Negligible functions

Negligible bounds are Mathlib's superpolynomial decay at natural security parameters. This module
collects their closure under comparison, polynomially bounded losses, square roots, and changes
of parameter. It is independent of probability distributions, games, and machine models.

The decay bound may depend on the whole algorithm. Security definitions quantify over that
algorithm before asserting negligibility; this module does not change that quantifier order.
-/

@[expose] public section

namespace Cslib.Crypto

/-- An advantage is negligible when it decays faster than every inverse polynomial in the
security parameter. This is Mathlib's superpolynomial decay, specialized to natural parameters. -/
abbrev Negligible (ε : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) ε

/-- The zero advantage is negligible. -/
@[simp] theorem negligible_zero : Negligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

/-- Geometric decay with ratio strictly between minus one and one is negligible. -/
theorem negligible_geometric {ratio : ℝ} (h : |ratio| < 1) :
    Negligible (fun n => ratio ^ n) :=
  fun degree => tendsto_pow_const_mul_const_pow_of_abs_lt_one degree h

/-- A constant nonzero advantage is not negligible. -/
theorem not_negligible_const {c : ℝ} (hc : c ≠ 0) : ¬ Negligible (fun _ => c) :=
  fun h => hc (by simpa using h 0)

/-- A pointwise smaller nonnegative advantage is negligible. -/
theorem negligible_of_le {ε δ : ℕ → ℝ} (hδ : Negligible δ)
    (hε : ∀ n, 0 ≤ ε n) (hle : ∀ n, ε n ≤ δ n) : Negligible ε :=
  hδ.trans_abs_le fun n => abs_le_abs_of_nonneg (hε n) (hle n)

/-- Taking a square root preserves negligible decay. -/
theorem Negligible.sqrt {ε : ℕ → ℝ} (h : Negligible ε) :
    Negligible (fun n => Real.sqrt (ε n)) := by
  intro degree
  have hroot (n : ℕ) : Real.sqrt ((n : ℝ) ^ (2 * degree) * ε n) =
      (n : ℝ) ^ degree * Real.sqrt (ε n) := by
    rw [pow_mul', Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  simpa [hroot] using (h (2 * degree)).sqrt

/-- Polynomially bounded factors preserve negligible decay, including for signed functions. -/
theorem Negligible.polynomiallyBounded_mul {ε : ℕ → ℝ} {p : ℕ → ℕ}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ) * ε n) := by
  obtain ⟨c, d, hp⟩ := hp
  have hbound : Negligible (fun n => (c : ℝ) * ((n : ℝ) + 1) ^ d * ε n) := by
    convert hε.polynomial_mul (Polynomial.C (c : ℝ) * (Polynomial.X + 1) ^ d) using 1
    ext n
    simp
  refine hbound.trans_abs_le fun n => ?_
  rw [abs_mul, abs_mul]
  gcongr ?_ * _
  exact abs_le_abs_of_nonneg (by positivity) (by exact_mod_cast hp n)

open Filter in
/-- Negligible decay survives reindexing when the new parameter tends to infinity and the old
parameter is polynomially bounded in it. The reindexing function need not be computable. -/
theorem Negligible.comp_of_polynomial_bound {ε : ℕ → ℝ} {index bound : ℕ → ℕ}
    (hε : Negligible ε) (hindex : Tendsto index atTop atTop)
    (hbound : PolynomiallyBounded bound) (hle : ∀ᶠ n in atTop, n ≤ bound (index n)) :
    Negligible (fun n => ε (index n)) := by
  have habs : Negligible (fun n => |ε n|) := hε.trans_abs_le (fun _ => by simp)
  intro degree
  have hlimit := (habs.polynomiallyBounded_mul (hbound.pow degree) 0).comp hindex
  simp only [pow_zero, one_mul, Nat.cast_pow, Function.comp_def] at hlimit
  refine squeeze_zero_norm' ?_ hlimit
  filter_upwards [hle] with n hn
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
  gcongr

open Filter in
/-- Negligible success is eventually smaller than the reciprocal of any positive
polynomially bounded loss. -/
theorem Negligible.eventually_le_inv_polynomial {ε : ℕ → ℝ} (hε : Negligible ε)
    {p : ℕ → ℕ} (hp : PolynomiallyBounded p)
    (hpos : ∀ n, 0 < p n) :
    ∀ᶠ n in atTop, ε n ≤ 1 / (p n : ℝ) := by
  have h := hε.polynomiallyBounded_mul hp 0
  simp only [pow_zero, one_mul] at h
  filter_upwards [h.eventually_le_const zero_lt_one] with n hn
  exact (le_div_iff₀' (by exact_mod_cast hpos n)).mpr hn

open Filter in
/-- Halving the security parameter preserves negligible decay. -/
theorem Negligible.div_two {ε : ℕ → ℝ} (h : Negligible ε) : Negligible (fun n => ε (n / 2)) := by
  apply h.comp_of_polynomial_bound (bound := fun n => 2 * (n + 1))
    (Nat.tendsto_div_const_atTop (by decide)) (by fun_prop)
  exact Eventually.of_forall (fun n => by lia)

end Cslib.Crypto
