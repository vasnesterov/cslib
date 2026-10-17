/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

/-!
# Induction around a cycle `ZMod n` with one excluded link

To prove a property `S` of every node of a ring `ZMod n`, it suffices to know it at one node and
that it passes from each node to its neighbour, except across one excluded link `m — m + 1`. This
is the "propagate along the ring" argument of ring algorithms (e.g. content-oblivious computation
on oriented rings).

## Main statements

* `ZMod.chain_ccw`, `ZMod.chain_ccw_all`, `ZMod.chain_ccw_to`: if `S (v + 1) → S v` for every
  `v ≠ m`, then `S` propagates counter-clockwise from `m + 1 + k` down to `m + 1`, and all around
  the ring from `m`.
* `ZMod.chain_cw`, `ZMod.chain_cw_all`: if `S v → S (v + 1)` for every `v ≠ m`, then `S`
  propagates clockwise from `m + 1` all around the ring.
* `ZMod.natCast_ne_zero_of_pos_of_lt`: `(k : ZMod n) ≠ 0` for `0 < k < n`.
-/

@[expose] public section

namespace ZMod

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- A positive natural number below `n` is nonzero in `ZMod n`. -/
lemma natCast_ne_zero_of_pos_of_lt {k : ℕ} (h0 : 0 < k) (hk : k < n) : (k : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd h0 h) (not_le.2 hk)

omit [NeZero n] in
/-- Counter-clockwise propagation: if `S` passes from `v + 1` to `v` for every `v ≠ m`, then it
passes from `m + 1 + k` down to `m + 1`, through every `m + 1 + j`, `j ≤ k`. -/
theorem chain_ccw (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S (v + 1) → S v)
    {k : ℕ} (hk : k < n) (hS : S (m + 1 + k)) : ∀ j ≤ k, S (m + 1 + j) := by
  suffices ∀ i ≤ k, S (m + 1 + ((k - i : ℕ) : ZMod n)) by
    intro j hj
    have := this (k - j) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self hj] at this
  intro i
  induction i with
  | zero => intro _; simpa using hS
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    apply h
    · intro he
      have : ((1 + (k - (i + 1)) : ℕ) : ZMod n) = 0 := by
        push_cast
        have := congrArg (· - m) he
        simp only [sub_self] at this
        rw [← this]; ring
      exact natCast_ne_zero_of_pos_of_lt (by omega) (by omega) this
    · have e : m + 1 + ((k - (i + 1) : ℕ) : ZMod n) + 1 = m + 1 + ((k - i : ℕ) : ZMod n) := by
        rw [show k - i = (k - (i + 1)) + 1 by omega]; push_cast; ring
      rwa [e]

/-- Counter-clockwise propagation all around the ring, starting from the excluded node. -/
theorem chain_ccw_all (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S (v + 1) → S v)
    (hS : S m) (v : ZMod n) : S v := by
  have hn : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) one_pos
  have e : m + 1 + ((n - 1 : ℕ) : ZMod n) = m := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))]; simp
  have := chain_ccw S m h hn (by rw [e]; exact hS) (v - m - 1).val
    (by have := ZMod.val_lt (v - m - 1); omega)
  simpa [ZMod.natCast_zmod_val] using this

/-- Counter-clockwise propagation from any node down to `m + 1`. -/
theorem chain_ccw_to (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S (v + 1) → S v)
    (w : ZMod n) (hS : S w) : S (m + 1) := by
  have := chain_ccw S m h (k := (w - m - 1).val) (ZMod.val_lt _)
    (by simpa [ZMod.natCast_zmod_val] using hS) 0 (Nat.zero_le _)
  simpa using this

omit [NeZero n] in
/-- Clockwise propagation: if `S` passes from `v` to `v + 1` for every `v ≠ m`, then it passes
from `m + 1` to every `m + 1 + j`, `j < n`. -/
theorem chain_cw (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S v → S (v + 1))
    (hS : S (m + 1)) : ∀ j < n, S (m + 1 + j) := by
  intro j
  induction j with
  | zero => intro _; simpa using hS
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have := h _ (by
      intro he
      have : ((1 + j : ℕ) : ZMod n) = 0 := by
        have := congrArg (· - m) he
        simp only [sub_self] at this
        push_cast; rw [← this]; ring
      exact natCast_ne_zero_of_pos_of_lt (by omega) (by omega) this) h1
    rwa [show m + 1 + (j : ZMod n) + 1 = m + 1 + ((j + 1 : ℕ) : ZMod n) by push_cast; ring] at this

/-- Clockwise propagation all around the ring. -/
theorem chain_cw_all (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S v → S (v + 1))
    (hS : S (m + 1)) (v : ZMod n) : S v := by
  have := chain_cw S m h hS (v - m - 1).val (ZMod.val_lt _)
  simpa [ZMod.natCast_zmod_val] using this

end ZMod
