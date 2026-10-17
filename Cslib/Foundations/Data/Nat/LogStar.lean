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
* `Nat.clog_le_tower_logStar`: `⌈log₂ n⌉ ≤ tower (log* n)`;
* `Nat.tower_succ`, `Nat.lt_tower_succ`, `Nat.tower_strictMono`, `Nat.tower_mono`,
  `Nat.tower_pos`;
* `Nat.logStar_of_le_one`, `Nat.logStar_of_one_lt`: the defining equations of `log*`;
* `Nat.le_logStar_iff`: `m ≤ log* n ↔ tower m ≤ n` for `n ≠ 0` (the Galois connection between
  `tower` and `log*`), with `Nat.tower_logStar_le` and `Nat.logStar_mono`;
* `Nat.iterate_log_logStar_le`: `log₂` iterated `log* n` times brings `n` down to at most `1`.
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

/-! ### API -/

/-- `tower 0 = 1`. -/
@[simp]
theorem tower_zero : tower 0 = 1 := rfl

/-- `tower (k + 1) = 2 ^ tower k`. -/
theorem tower_succ (k : ℕ) : tower (k + 1) = 2 ^ tower k := rfl

/-- `tower k < tower (k + 1)`. -/
theorem lt_tower_succ (k : ℕ) : tower k < tower (k + 1) := Nat.lt_two_pow_self

/-- The tower function is strictly monotone. -/
theorem tower_strictMono : StrictMono tower := strictMono_nat_of_lt_succ lt_tower_succ

/-- The tower function is monotone. -/
theorem tower_mono : Monotone tower := tower_strictMono.monotone

/-- `tower k ≥ 1`. -/
theorem tower_pos (k : ℕ) : 0 < tower k := tower_mono (Nat.zero_le k)

/-- `log* n = 0` for `n ≤ 1`. -/
theorem logStar_of_le_one {n : ℕ} (hn : n ≤ 1) : logStar n = 0 := by
  rw [logStar, dite_eq_left_of_eq_true (eq_true hn)]

/-- `log* n = log* (log₂ n) + 1` for `n > 1`. -/
theorem logStar_of_one_lt {n : ℕ} (hn : 1 < n) : logStar n = logStar (log 2 n) + 1 := by
  rw [logStar, dite_eq_right_of_eq_false (eq_false (by omega))]

/-- `tower (log* n) ≤ n` for `n ≠ 0`. -/
theorem tower_logStar_le {n : ℕ} (hn : n ≠ 0) : tower (logStar n) ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n 1 with h | h
    · rw [logStar_of_le_one h]; simp; omega
    · rw [logStar_of_one_lt h, tower_succ]
      have hlog : log 2 n ≠ 0 := (log_pos (by omega) h).ne'
      calc 2 ^ tower (logStar (log 2 n)) ≤ 2 ^ log 2 n :=
            Nat.pow_le_pow_right (by omega) (ih _ (log_lt_self 2 hn) hlog)
        _ ≤ n := pow_log_le_self 2 hn

/-- `m ≤ log* n ↔ tower m ≤ n` for `n ≠ 0`. -/
theorem le_logStar_iff {m n : ℕ} (hn : n ≠ 0) : m ≤ logStar n ↔ tower m ≤ n := by
  refine ⟨fun h => (tower_mono h).trans (tower_logStar_le hn), fun h => ?_⟩
  have := h.trans_lt (lt_tower_logStar_succ n)
  exact Nat.lt_succ_iff.1 (tower_strictMono.lt_iff_lt.1 this)

/-- The iterated logarithm is monotone. -/
theorem logStar_mono : Monotone logStar := by
  intro m n h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [logStar_of_le_one]
  · exact (le_logStar_iff (by omega)).2 ((tower_logStar_le hm.ne').trans h)

/-- `log₂` iterated `log* n` times maps `n` to a number `≤ 1`. -/
theorem iterate_log_logStar_le (n : ℕ) : (log 2)^[logStar n] n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n 1 with h | h
    · rwa [logStar_of_le_one h]
    · rw [logStar_of_one_lt h, Function.iterate_succ_apply]
      exact ih _ (log_lt_self 2 (by omega))

end Nat
