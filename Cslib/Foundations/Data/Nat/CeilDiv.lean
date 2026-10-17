/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Ceiling division on natural numbers

Mathlib's `a ⌈/⌉ b` (`CeilDiv ℕ ℕ`, `Mathlib/Algebra/Order/Floor/Div.lean`) is definitionally
`(a + b - 1) / b` (`Nat.ceilDiv_eq_add_pred_div`), and its general API is phrased with `•` and
Galois connections. Round-complexity and bit-length bounds use it in a few concrete forms,
collected here.

## Main statements

* `Nat.le_mul_ceilDiv`: `a ≤ b * (a ⌈/⌉ b)` for `0 < b`, and `Nat.le_ceilDiv_mul`;
* `Nat.ceilDiv_mul_le`: `a ⌈/⌉ b * b ≤ a + b - 1`;
* `Nat.ceilDiv_le_of_le_mul`: `a ≤ b * c → a ⌈/⌉ b ≤ c` for `0 < b`;
* `Nat.ceilDiv_mono`: monotonicity in the numerator;
* `Nat.ceilDiv_le_div_add_one`: `a ⌈/⌉ b ≤ a / b + 1`.
-/

@[expose] public section

namespace Nat

variable {a b c : ℕ}

/-- `b * ⌈a / b⌉` is at least `a`. -/
theorem le_mul_ceilDiv (hb : 0 < b) : a ≤ b * (a ⌈/⌉ b) := by
  simpa using le_smul_ceilDiv (b := a) hb

/-- `⌈a / b⌉ * b` is at least `a`. -/
theorem le_ceilDiv_mul (hb : 0 < b) : a ≤ a ⌈/⌉ b * b :=
  (le_mul_ceilDiv hb).trans_eq (Nat.mul_comm _ _)

/-- `⌈a / b⌉ * b` is at most `a + b - 1`. -/
theorem ceilDiv_mul_le (a b : ℕ) : a ⌈/⌉ b * b ≤ a + b - 1 :=
  Nat.div_mul_le_self _ _

/-- `⌈a / b⌉ ≤ c` as soon as `a ≤ b * c`. -/
theorem ceilDiv_le_of_le_mul (hb : 0 < b) (h : a ≤ b * c) : a ⌈/⌉ b ≤ c :=
  (ceilDiv_le_iff_le_mul hb).2 h

/-- Ceiling division is monotone in the numerator. -/
theorem ceilDiv_mono {a a' : ℕ} (b : ℕ) (h : a ≤ a') : a ⌈/⌉ b ≤ a' ⌈/⌉ b :=
  Nat.div_le_div_right (by omega)

/-- `⌈a / b⌉ ≤ ⌊a / b⌋ + 1`. -/
theorem ceilDiv_le_div_add_one (a b : ℕ) : a ⌈/⌉ b ≤ a / b + 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · refine ceilDiv_le_of_le_mul hb ?_
    have := Nat.lt_mul_div_succ a hb
    omega

end Nat
