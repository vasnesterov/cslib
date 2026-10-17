/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.Nat.CeilDiv
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting a residue class in an interval

An interval of length `m` contains at most `⌈m / q⌉` numbers of any residue class modulo `q > 0`.
Mathlib has the exact counts (`Nat.Ico_filter_modEq_card`, `Nat.count_modEq_card`,
`Mathlib/Data/Int/CardIntervalMod.lean`), but phrased through rational ceilings; the bounds below
are the ℕ-valued forms used in scheduling and load-balancing arguments ("every node is the leader at
most `⌈m / n⌉` times among `m` consecutive rounds").

## Main statements

* `Nat.card_le_ceilDiv_of_subset_Ico`: a set of numbers in `[a, b)` that are pairwise congruent
  modulo `q > 0` has at most `(b - a) ⌈/⌉ q` elements;
* `Nat.card_Ico_filter_modEq_le`, `Nat.card_range_filter_modEq_le`: the same for the residue class
  of `v` in `[a, b)` and in `[0, n)`;
* `Nat.card_Ico_filter_modEq_le_div_add_one`: the bound `(b - a) / q + 1`, valid for every `q`.
-/

@[expose] public section

open Finset

namespace Nat

variable {q : ℕ}

/-- A set of numbers in `[a, b)` that are pairwise congruent modulo `q > 0` has at most
`⌈(b - a) / q⌉` elements. -/
theorem card_le_ceilDiv_of_subset_Ico (hq : 0 < q) {s : Finset ℕ} {a b : ℕ} (hs : s ⊆ Ico a b)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≡ y [MOD q]) : #s ≤ (b - a) ⌈/⌉ q := by
  calc #s ≤ #(range ((b - a) ⌈/⌉ q)) := by
        refine card_le_card_of_injOn (fun t => (t - a) / q) (fun t ht => ?_)
          fun t ht t' ht' he => ?_
        · have ht := mem_Ico.1 (hs ht)
          have h1 := Nat.div_mul_le_self (t - a) q
          have h2 := le_ceilDiv_mul (a := b - a) hq
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_of_mul_lt_mul_right (a := q) (by omega)
        · have h1 := (mem_Ico.1 (hs ht)).1
          have h2 := (mem_Ico.1 (hs ht')).1
          have hm : (t - a) % q = (t' - a) % q := by
            refine Nat.ModEq.add_right_cancel' a ?_
            rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
            exact h t ht t' ht'
          have e1 := Nat.div_add_mod (t - a) q
          have e2 := Nat.div_add_mod (t' - a) q
          simp only at he
          rw [he, hm] at e1
          omega
    _ = _ := card_range _

/-- At most `⌈(b - a) / q⌉` numbers in `[a, b)` are congruent to `v` modulo `q > 0`. -/
theorem card_Ico_filter_modEq_le (hq : 0 < q) (a b v : ℕ) :
    #{t ∈ Ico a b | t ≡ v [MOD q]} ≤ (b - a) ⌈/⌉ q :=
  card_le_ceilDiv_of_subset_Ico hq (filter_subset _ _) fun _ hx _ hy =>
    (mem_filter.1 hx).2.trans (mem_filter.1 hy).2.symm

/-- At most `⌈n / q⌉` numbers below `n` are congruent to `v` modulo `q > 0`. -/
theorem card_range_filter_modEq_le (hq : 0 < q) (n v : ℕ) :
    #{t ∈ range n | t ≡ v [MOD q]} ≤ n ⌈/⌉ q := by
  rw [← Nat.Ico_zero_eq_range]
  exact card_Ico_filter_modEq_le hq 0 n v

/-- At most `⌊(b - a) / q⌋ + 1` numbers in `[a, b)` are congruent to `v` modulo `q` (for every
`q`, including `q = 0`). -/
theorem card_Ico_filter_modEq_le_div_add_one (a b v : ℕ) :
    #{t ∈ Ico a b | t ≡ v [MOD q]} ≤ (b - a) / q + 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine (card_le_one.2 fun x hx y hy => ?_).trans (by omega)
    simp only [mem_filter, Nat.modEq_zero_iff] at hx hy
    exact hx.2.trans hy.2.symm
  · exact (card_Ico_filter_modEq_le hq a b v).trans (ceilDiv_le_div_add_one _ _)

end Nat
