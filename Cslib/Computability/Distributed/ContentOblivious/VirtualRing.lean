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
# The virtual ring of the active nodes of an oriented ring

On the oriented ring `ZMod n` (clockwise = `+1`), a set of *active* nodes `act : ZMod n → Bool`
induces a *virtual ring*: `vnext act v` is the first active node strictly clockwise after `v`,
`vprev act v` the first active node strictly counter-clockwise before `v` (going all the way
around, so a lone active node is its own neighbour). Inactive nodes act as relays.

Main facts (when some node is active): `act_vnext`, `act_vprev`, `vprev_vnext` and `vnext_vprev`
(for active `v`: the two maps are inverse bijections of the active set) and `vnext_eq_self_iff`
(an active node is its own successor iff it is the only active node); `vnext_spec` and
`vprev_spec`: `vnext act v` / `vprev act v` is `v + k` / `v - k` for the least `k ≥ 1` such that
this node is active; `vprev_eq_neg_vnext_neg`: reflecting the ring `v ↦ -v` exchanges `vnext` and
`vprev`.
-/

@[expose] public section

namespace Cslib.ContentOblivious

variable {n : ℕ} (act : ZMod n → Bool)

/-- The first active node strictly clockwise after `v` (or `v` if no node is active). -/
def vnext (v : ZMod n) : ZMod n :=
  if h : ∃ k, k < n ∧ act (v + ((k + 1 : ℕ) : ZMod n)) = true then
    v + ((Nat.find h + 1 : ℕ) : ZMod n)
  else v

/-- The first active node strictly counter-clockwise before `v` (or `v` if no node is active). -/
def vprev (v : ZMod n) : ZMod n :=
  if h : ∃ k, k < n ∧ act (v - ((k + 1 : ℕ) : ZMod n)) = true then
    v - ((Nat.find h + 1 : ℕ) : ZMod n)
  else v

/-- Reflecting the ring `v ↦ -v` exchanges the virtual successor and predecessor. -/
theorem vprev_eq_neg_vnext_neg (act : ZMod n → Bool) (v : ZMod n) :
    vprev act v = -vnext (fun w => act (-w)) (-v) := by
  have e : ∀ k : ℕ, -(-v + (k : ZMod n)) = v - k := fun k => by ring
  simp only [vprev, vnext, e]
  split_ifs <;> simp only [neg_add, neg_neg, sub_eq_add_neg]

variable {act} [NeZero n]

/-- If some node is active, an active node lies within `n` steps clockwise. -/
lemma exists_next_active {u : ZMod n} (hu : act u = true) (v : ZMod n) :
    ∃ k, k < n ∧ act (v + ((k + 1 : ℕ) : ZMod n)) = true := by
  refine ⟨(u - v - 1).val, ZMod.val_lt _, ?_⟩
  push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id]; rw [← hu]; congr 1; ring

/-- If some node is active, an active node lies within `n` steps counter-clockwise. -/
lemma exists_prev_active {u : ZMod n} (hu : act u = true) (v : ZMod n) :
    ∃ k, k < n ∧ act (v - ((k + 1 : ℕ) : ZMod n)) = true := by
  refine ⟨(v - u - 1).val, ZMod.val_lt _, ?_⟩
  push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id]; rw [← hu]; congr 1; ring

/-- The virtual successor is active (when some node is active). -/
lemma act_vnext {u : ZMod n} (hu : act u = true) (v : ZMod n) : act (vnext act v) = true := by
  have h := exists_next_active hu v
  rw [vnext, dite_eq_left_of_eq_true (eq_true h)]; exact (Nat.find_spec h).2

/-- The virtual predecessor is active (when some node is active). -/
lemma act_vprev {u : ZMod n} (hu : act u = true) (v : ZMod n) : act (vprev act v) = true := by
  have h := exists_prev_active hu v
  rw [vprev, dite_eq_left_of_eq_true (eq_true h)]; exact (Nat.find_spec h).2

omit [NeZero n] in
/-- Arithmetic of differences of casts in `ZMod n`. -/
lemma natCast_sub_succ {k m : ℕ} (h : m < k) :
    ((k + 1 : ℕ) : ZMod n) - ((m + 1 : ℕ) : ZMod n) = ((k - m - 1 + 1 : ℕ) : ZMod n) := by
  rw [show k - m - 1 + 1 = (k + 1) - (m + 1) by omega, Nat.cast_sub (by omega)]

/-- The virtual predecessor of the virtual successor of an active node is itself. -/
lemma vprev_vnext {v : ZMod n} (hv : act v = true) : vprev act (vnext act v) = v := by
  have h := exists_next_active hv v
  rw [vnext, dite_eq_left_of_eq_true (eq_true h)]
  set k := Nat.find h with hk
  have h' : ∃ m, m < n ∧ act (v + ((k + 1 : ℕ) : ZMod n) - ((m + 1 : ℕ) : ZMod n)) = true :=
    ⟨k, (Nat.find_spec h).1, by simpa using hv⟩
  rw [vprev, dite_eq_left_of_eq_true (eq_true h')]
  have hle : Nat.find h' ≤ k := Nat.find_min' h' ⟨(Nat.find_spec h).1, by simpa using hv⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hs := (Nat.find_spec h').2
    rw [add_sub_assoc, natCast_sub_succ hlt] at hs
    have hkn := (Nat.find_spec h).1
    exact Nat.find_min h (show k - Nat.find h' - 1 < k by omega) ⟨by omega, hs⟩
  · rw [heq]; simp

/-- The virtual successor of the virtual predecessor of an active node is itself. -/
lemma vnext_vprev {v : ZMod n} (hv : act v = true) : vnext act (vprev act v) = v := by
  have h := exists_prev_active hv v
  rw [vprev, dite_eq_left_of_eq_true (eq_true h)]
  set k := Nat.find h with hk
  have h' : ∃ m, m < n ∧ act (v - ((k + 1 : ℕ) : ZMod n) + ((m + 1 : ℕ) : ZMod n)) = true :=
    ⟨k, (Nat.find_spec h).1, by simpa using hv⟩
  rw [vnext, dite_eq_left_of_eq_true (eq_true h')]
  have hle : Nat.find h' ≤ k := Nat.find_min' h' ⟨(Nat.find_spec h).1, by simpa using hv⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hs := (Nat.find_spec h').2
    rw [show v - ((k + 1 : ℕ) : ZMod n) + ((Nat.find h' + 1 : ℕ) : ZMod n) =
      v - (((k + 1 : ℕ) : ZMod n) - ((Nat.find h' + 1 : ℕ) : ZMod n)) by ring,
      natCast_sub_succ hlt] at hs
    have hkn := (Nat.find_spec h).1
    exact Nat.find_min h (show k - Nat.find h' - 1 < k by omega) ⟨by omega, hs⟩
  · rw [heq]; simp

/-- The virtual successor is injective on active nodes. -/
lemma vnext_injOn {v w : ZMod n} (hv : act v = true) (hw : act w = true)
    (h : vnext act v = vnext act w) : v = w := by
  rw [← vprev_vnext hv, ← vprev_vnext hw, h]

/-- An active node is its own clockwise neighbour iff it is the only active node. -/
lemma vnext_eq_self_iff {v : ZMod n} (hv : act v = true) :
    vnext act v = v ↔ ∀ u, act u = true → u = v := by
  constructor
  · intro hself u hu
    have h := exists_next_active hv v
    rw [vnext, dite_eq_left_of_eq_true (eq_true h)] at hself
    set k := Nat.find h with hk
    have hkn := (Nat.find_spec h).1
    have h0 : ((k + 1 : ℕ) : ZMod n) = 0 := by
      have := congrArg (· - v) hself; simpa using this
    have hkn' : k + 1 = n := by
      have := (ZMod.natCast_eq_zero_iff (k + 1) n).1 h0
      exact ((Nat.le_of_dvd (by omega) this).antisymm' (by omega))
    by_contra hne
    set j := (u - v).val with hj
    have hj0 : j ≠ 0 := by
      intro h0'; apply hne
      have := (ZMod.val_eq_zero (u - v)).1 h0'
      exact (sub_eq_zero.1 this)
    have hjn : j < n := ZMod.val_lt _
    have hact : act (v + ((j - 1 + 1 : ℕ) : ZMod n)) = true := by
      rw [show j - 1 + 1 = j by omega, hj]; simpa using hu
    exact Nat.find_min h (show j - 1 < k by omega) ⟨by omega, hact⟩
  · intro hall
    exact hall _ (act_vnext hv v)

/-- The virtual successor of `v` is `v + k` for the least `k ≥ 1` such that `v + k` is active
(`k ≤ n`; `k = n` iff `v` is the only active node), provided some node is active. -/
theorem vnext_spec {u : ZMod n} (hu : act u = true) (v : ZMod n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ vnext act v = v + k ∧ act (v + k) = true ∧
      ∀ j : ℕ, 0 < j → j < k → act (v + j) = false := by
  have h := exists_next_active hu v
  refine ⟨Nat.find h + 1, Nat.succ_pos _, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2,
    fun j hj hjk => ?_⟩
  · rw [vnext, dite_eq_left h]
  · have := Nat.find_min h (show j - 1 < Nat.find h by omega)
    rw [show j - 1 + 1 = j by omega] at this
    simpa [show j - 1 < n by have := (Nat.find_spec h).1; omega] using this

/-- The virtual predecessor of `v` is `v - k` for the least `k ≥ 1` such that `v - k` is active
(`k ≤ n`), provided some node is active. -/
theorem vprev_spec {u : ZMod n} (hu : act u = true) (v : ZMod n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ vprev act v = v - k ∧ act (v - k) = true ∧
      ∀ j : ℕ, 0 < j → j < k → act (v - j) = false := by
  have h := exists_prev_active hu v
  refine ⟨Nat.find h + 1, Nat.succ_pos _, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2,
    fun j hj hjk => ?_⟩
  · rw [vprev, dite_eq_left h]
  · have := Nat.find_min h (show j - 1 < Nat.find h by omega)
    rw [show j - 1 + 1 = j by omega] at this
    simpa [show j - 1 < n by have := (Nat.find_spec h).1; omega] using this

end Cslib.ContentOblivious
