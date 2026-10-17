/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.Nat

/-!
# Growth of a sequence until saturation

The flooding arguments of dynamic networks ("in every rooted round the set of informed nodes grows
by at least one node, until it contains everybody", so after `n - 1` rounds everybody is
informed) share one counting step, stated here for a sequence `f : ℕ → ℕ` (typically the
cardinality of a monotone sequence of finsets):

* `Nat.min_add_card_filter_le_of_grow`: if `f` is non-decreasing and increases at every step
  `t → t + 1` with `p (t + 1)` while it is below `n`, then
  `min n (f 0 + #{t ∈ [1, K] | p t}) ≤ f K`;
* `Nat.min_add_le_of_grow`: the case where every step increases `f`: `min n (f 0 + K) ≤ f K`.
-/

@[expose] public section

namespace Nat

open Finset

/-- **Growth until saturation.** If `f` does not decrease before time `K` and increases at every
step `t → t + 1` (`t < K`) with `p (t + 1)` as long as it is below `n`, then `f K` is at least
`f 0` plus the number of such steps, or at least `n`. -/
theorem min_add_card_filter_le_of_grow {f : ℕ → ℕ} {n K : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hmono : ∀ t < K, f t ≤ f (t + 1)) (hgrow : ∀ t < K, p (t + 1) → f t < n → f t < f (t + 1)) :
    min n (f 0 + #{t ∈ Icc 1 K | p t}) ≤ f K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ih := ih (fun t ht => hmono t (by omega)) (fun t ht => hgrow t (by omega))
    have hmK := hmono K (by omega)
    by_cases hK : p (K + 1)
    · have hfil : #{t ∈ Icc 1 (K + 1) | p t} = #{t ∈ Icc 1 K | p t} + 1 := by
        rw [← insert_Icc_right_eq_Icc_add_one (a := 1) (b := K) (by omega), filter_insert,
          ite_eq_left hK, card_insert_of_notMem (by simp)]
      rw [hfil]
      by_cases hlt : f K < n
      · have := hgrow K (by omega) hK hlt
        omega
      · omega
    · have hfil : #{t ∈ Icc 1 (K + 1) | p t} = #{t ∈ Icc 1 K | p t} := by
        rw [← insert_Icc_right_eq_Icc_add_one (a := 1) (b := K) (by omega), filter_insert,
          ite_eq_right hK]
      rw [hfil]
      omega

/-- **Growth until saturation**, every step counting: if `f` increases at every step before time
`K` as long as it is below `n` (and never decreases), then `min n (f 0 + K) ≤ f K`. -/
theorem min_add_le_of_grow {f : ℕ → ℕ} {n K : ℕ} (hmono : ∀ t < K, f t ≤ f (t + 1))
    (hgrow : ∀ t < K, f t < n → f t < f (t + 1)) : min n (f 0 + K) ≤ f K := by
  simpa using min_add_card_filter_le_of_grow (fun _ => True) hmono fun t ht _ => hgrow t ht

end Nat
