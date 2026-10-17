/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ceilings of real logarithms and round counts

Round-complexity statements of approximation algorithms are phrased with `⌈log_b x⌉`: after
`⌈log_b (D / ε)⌉` rounds, each multiplying the spread by `1 / b`, a spread `D` has shrunk below
`ε`. Mathlib relates `⌈Real.logb b x⌉` to `Int.clog` / `Nat.clog` only for a natural base. This
file provides the real-base facts:

* `Real.logb_self_pow`: `log_b (b ^ n) = n`;
* `Real.logb_le_natCast_iff_le_pow`, `Real.natCeil_logb_le_iff_le_pow`,
  `Real.ceil_logb_le_iff_le_pow`: `⌈log_b x⌉ ≤ n ↔ x ≤ b ^ n` (for `b > 1`, `x > 0`), in the
  real, `Nat.ceil` and `Int.ceil` forms (lower bounds on round counts);
* `Real.logb_div_le_iff_le_pow_mul`: `log_b (D / ε) ≤ n ↔ D ≤ b ^ n * ε`;
* `Real.le_pow_natCeil_logb`: `x ≤ b ^ ⌈log_b x⌉₊`, and `Real.le_pow_natCeil_logb_div_mul`:
  `D ≤ b ^ ⌈log_b (D / ε)⌉₊ * ε` (upper bounds on round counts);
* `Real.pow_natCeil_logb_inv_div_mul_le`: contraction by a factor `q ∈ (0, 1)` per round brings a
  spread `D` within `ε` after `⌈log_{1/q} (D / ε)⌉₊` rounds.
-/

@[expose] public section

namespace Real

variable {b x D ε q : ℝ} {n : ℕ}

/-- `log_b (b ^ n) = n`. -/
theorem logb_self_pow (b_pos : 0 < b) (b_ne_one : b ≠ 1) (n : ℕ) : logb b (b ^ n) = n := by
  rw [← rpow_natCast, logb_rpow b_pos b_ne_one]

/-- `log_b x ≤ n ↔ x ≤ b ^ n` for `b > 1` and `x > 0`. -/
theorem logb_le_natCast_iff_le_pow (hb : 1 < b) (hx : 0 < x) : logb b x ≤ n ↔ x ≤ b ^ n := by
  rw [logb_le_iff_le_rpow hb hx, rpow_natCast]

/-- `⌈log_b x⌉₊ ≤ n ↔ x ≤ b ^ n` for `b > 1` and `x > 0`. -/
theorem natCeil_logb_le_iff_le_pow (hb : 1 < b) (hx : 0 < x) :
    ⌈logb b x⌉₊ ≤ n ↔ x ≤ b ^ n := by
  rw [Nat.ceil_le, logb_le_natCast_iff_le_pow hb hx]

/-- `⌈log_b x⌉ ≤ n ↔ x ≤ b ^ n` for `b > 1`, `x > 0` and a natural number `n`. -/
theorem ceil_logb_le_iff_le_pow (hb : 1 < b) (hx : 0 < x) :
    ⌈logb b x⌉ ≤ (n : ℤ) ↔ x ≤ b ^ n := by
  rw [Int.ceil_le, Int.cast_natCast, logb_le_natCast_iff_le_pow hb hx]

/-- `log_b (D / ε) ≤ n ↔ D ≤ b ^ n * ε` for `b > 1` and `D, ε > 0`: if `n` rounds, each dividing
the spread by `b`, bring the spread `D` down to `ε`, then `n ≥ log_b (D / ε)`. -/
theorem logb_div_le_iff_le_pow_mul (hb : 1 < b) (hD : 0 < D) (hε : 0 < ε) :
    logb b (D / ε) ≤ n ↔ D ≤ b ^ n * ε := by
  rw [logb_le_natCast_iff_le_pow hb (div_pos hD hε), div_le_iff₀ hε]

/-- `x ≤ b ^ ⌈log_b x⌉₊` for `b > 1` (and every real `x`). -/
theorem le_pow_natCeil_logb (hb : 1 < b) (x : ℝ) : x ≤ b ^ ⌈logb b x⌉₊ := by
  rcases le_or_gt x 0 with hx | hx
  · exact hx.trans (pow_pos (zero_lt_one.trans hb) _).le
  · exact (natCeil_logb_le_iff_le_pow hb hx).1 le_rfl

/-- `D ≤ b ^ ⌈log_b (D / ε)⌉₊ * ε` for `b > 1` and `ε > 0`: `⌈log_b (D / ε)⌉₊` rounds, each
dividing the spread by `b`, bring a spread `D` down to `ε`. -/
theorem le_pow_natCeil_logb_div_mul (hb : 1 < b) (D : ℝ) (hε : 0 < ε) :
    D ≤ b ^ ⌈logb b (D / ε)⌉₊ * ε := by
  rw [← div_le_iff₀ hε]
  exact le_pow_natCeil_logb hb _

/-- Contraction round count: for `0 < q < 1` and `ε > 0`, `q ^ ⌈log_{1/q} (D / ε)⌉₊ * D ≤ ε`, i.e.
`⌈log_{1/q} (D / ε)⌉₊` rounds, each multiplying the spread by `q`, bring a spread `D` within
`ε`. -/
theorem pow_natCeil_logb_inv_div_mul_le (hq0 : 0 < q) (hq1 : q < 1) (D : ℝ) (hε : 0 < ε) :
    q ^ ⌈logb q⁻¹ (D / ε)⌉₊ * D ≤ ε := by
  have h := le_pow_natCeil_logb_div_mul ((one_lt_inv₀ hq0).2 hq1) D hε
  set k := ⌈logb q⁻¹ (D / ε)⌉₊
  have hk : 0 < q ^ k := pow_pos hq0 k
  calc q ^ k * D ≤ q ^ k * (q⁻¹ ^ k * ε) := mul_le_mul_of_nonneg_left h hk.le
    _ = ε := by rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0.ne', one_pow, one_mul]

end Real
