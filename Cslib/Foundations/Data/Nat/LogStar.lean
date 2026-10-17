/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Log

/-!
# The tower function and the iterated logarithm

* `Nat.tower`: `tower 0 = 1`, `tower (k + 1) = 2 ^ tower k`.
* `Nat.logStar`: the iterated binary logarithm `log*` (`logStar n = 0` for `n ≤ 1`, otherwise
  `logStar (log₂ n) + 1`).

## Main statements

* `Nat.lt_tower_logStar_succ`: `n < tower (log* n + 1)`;
* `Nat.clog_le_tower_logStar`: `⌈log₂ n⌉ ≤ tower (log* n)`.
-/

@[expose] public section

namespace Nat

/-- The tower function: `tower 0 = 1`, `tower (k + 1) = 2 ^ tower k`. -/
def tower : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ Nat.tower k

/-- The iterated logarithm: `logStar n = 0` for `n ≤ 1`, otherwise `logStar (log₂ n) + 1`.
E.g. `logStar 2 = 1`, `logStar 4 = 2`, `logStar 16 = 3`, `logStar 65536 = 4`. -/
def logStar (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0 else Nat.logStar (Nat.log 2 n) + 1
decreasing_by exact Nat.log_lt_self 2 (by omega)

example : (Nat.logStar 1, Nat.logStar 2, Nat.logStar 4, Nat.logStar 16, Nat.logStar 65536) =
    (0, 1, 2, 3, 4) := by decide +kernel

/-- `n < tower (log* n + 1)`. -/
theorem lt_tower_logStar_succ (n : ℕ) : n < Nat.tower (Nat.logStar n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.logStar]
    split_ifs with h
    · simp [Nat.tower]; omega
    · have := ih _ (Nat.log_lt_self 2 (by omega))
      calc n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by omega) n
        _ ≤ 2 ^ Nat.tower (Nat.logStar (Nat.log 2 n) + 1) :=
          Nat.pow_le_pow_right (by omega) this
        _ = Nat.tower (Nat.logStar (Nat.log 2 n) + 1 + 1) := rfl

/-- `⌈log₂ n⌉ ≤ tower (log* n)`. -/
theorem clog_le_tower_logStar (n : ℕ) : Nat.clog 2 n ≤ Nat.tower (Nat.logStar n) :=
  Nat.clog_le_of_le_pow (lt_tower_logStar_succ n).le

end Nat
