/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size

/-!
# Additional facts about `Nat.log` and `Nat.clog`

* `Nat.clog_pow_le_mul`: `⌈log_b (x ^ k)⌉ ≤ k ⌈log_b x⌉`;
* `Nat.pow_clog_lt_mul`: `b ^ ⌈log_b x⌉ < b x` for `x ≠ 0`, i.e. the least power of `b` that is
  `≥ x` is less than `b x`;
* `Nat.size_eq_clog_two`, `Nat.size_eq_log_two_add_one`: the bit length `Nat.size n` is
  `⌈log₂ (n + 1)⌉`, and `⌊log₂ n⌋ + 1` for `n ≠ 0`.
-/

@[expose] public section

namespace Nat

/-- `⌈log_b (x ^ k)⌉ ≤ k ⌈log_b x⌉`. -/
theorem clog_pow_le_mul (b x k : ℕ) : clog b (x ^ k) ≤ k * clog b x := by
  rcases le_or_gt b 1 with hb | hb
  · simp [clog_of_left_le_one hb]
  rw [clog_le_iff_le_pow hb, Nat.mul_comm, Nat.pow_mul]
  exact Nat.pow_le_pow_left (le_pow_clog hb x) k

/-- `b ^ ⌈log_b x⌉ < b x` for `b > 1` and `x ≠ 0`. -/
theorem pow_clog_lt_mul {b x : ℕ} (hb : 1 < b) (hx : x ≠ 0) : b ^ clog b x < b * x := by
  rcases le_or_gt x 1 with h | h
  · obtain rfl : x = 1 := by omega
    simpa using hb
  have hpos := clog_pos hb h
  have hlt := pow_pred_clog_lt_self hb h
  calc b ^ clog b x = b * b ^ (clog b x).pred := by
        rw [← pow_succ', succ_pred_eq_of_pos hpos]
    _ < b * x := Nat.mul_lt_mul_of_pos_left hlt (by omega)

/-- The bit length of `n` is `⌈log₂ (n + 1)⌉`. -/
theorem size_eq_clog_two (n : ℕ) : n.size = clog 2 (n + 1) := by
  apply le_antisymm
  · exact size_le.2 (le_pow_clog Nat.one_lt_two (n + 1))
  · exact clog_le_of_le_pow (lt_size_self n)

/-- The bit length of `n ≠ 0` is `⌊log₂ n⌋ + 1`. -/
theorem size_eq_log_two_add_one {n : ℕ} (hn : n ≠ 0) : n.size = log 2 n + 1 := by
  apply le_antisymm
  · exact size_le.2 (lt_pow_succ_log_self Nat.one_lt_two n)
  · exact lt_size.2 (pow_log_le_self 2 hn)

end Nat
