/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Byzantine quorums

Counting lemmas behind the "`t + 1` / `2t + 1` / `n - t`" arguments of Byzantine fault-tolerant
protocols (e.g. Bracha's reliable broadcast, graded consensus): `n = Fintype.card P` processes,
at most `t` of which (the set `F`) are faulty, typically with `3 * t < n`. A process is *correct*
if it is not in `F`, so the correct members of a set `S` are `S \ F`, and all correct processes
form `Fᶜ`. We call a set `S` with `n - t ≤ #S` a *quorum*; no new definition is introduced for it.

## Main statements

* `Quorum.exists_notMem_of_lt_card`: a set of more than `t` processes contains a correct one.
* `Quorum.lt_card_sdiff_of_two_mul_lt_card`: a set of more than `2t` processes contains more
  than `t` correct ones.
* `Quorum.exists_notMem_inter_of_lt_card_add_card`: two sets whose sizes add up to more than
  `n + t` share a correct process; in particular (`Quorum.exists_notMem_inter_of_quorums`) two
  quorums do if `3 * t < n`.
* `Quorum.card_sub_le_card_compl`, `Quorum.two_mul_lt_card_compl`: there are at least `n - t`
  (hence, if `3 * t < n`, more than `2t`) correct processes.
* `Quorum.card_le_div_of_pairwiseDisjoint`: at most `n / (t + 1)` pairwise disjoint sets have more
  than `t` processes each (e.g. at most `n / (t + 1)` values are each sent by more than `t`
  processes if every process sends at most one value).
* `Quorum.card_le_div_sub_of_pairwiseDisjoint`: if `3 * t < n`, at most `n / (n - 3t)` pairwise
  disjoint sets have at least `n - 3t` processes each (the *reduction* of a one-round reducing
  broadcast, `Cslib.Distributed.Reduction`).
* `Quorum.min_div_le_three`, `Quorum.card_le_three_of_pairwiseDisjoint`: if `3 * t < n`, then
  `min (n / (t + 1)) (n / (n - 3t)) ≤ 3`, so at most three indices have both more than `t` processes
  in one pairwise disjoint family and at least `n - 3t` in another.
-/

@[expose] public section

namespace Cslib.Distributed.Quorum

open Finset

variable {P : Type*} {F S T : Finset P} {t : ℕ}

/-! ### Correct members of a set -/

/-- A set of more than `t` processes (i.e. of at least `t + 1`) contains a correct process. -/
theorem exists_notMem_of_lt_card (hF : #F ≤ t) (hS : t < #S) : ∃ p ∈ S, p ∉ F :=
  exists_mem_notMem_of_card_lt_card (hF.trans_lt hS)

section DecidableEq

variable [DecidableEq P]

/-- At most `t` members of a set are faulty, so at least `#S - t` of them are correct. -/
theorem card_sub_le_card_sdiff (hF : #F ≤ t) (S : Finset P) : #S - t ≤ #(S \ F) := by
  have := le_card_sdiff F S
  omega

/-- A set of more than `2t` processes (i.e. of at least `2t + 1`) contains more than `t`
correct ones. -/
theorem lt_card_sdiff_of_two_mul_lt_card (hF : #F ≤ t) (hS : 2 * t < #S) : t < #(S \ F) := by
  have := card_sub_le_card_sdiff hF S
  omega

end DecidableEq

/-! ### Intersections -/

variable [Fintype P]

/-- Two sets of processes intersect in at least `#S + #T - n` processes. -/
theorem card_add_card_sub_le_card_inter [DecidableEq P] (S T : Finset P) :
    #S + #T - Fintype.card P ≤ #(S ∩ T) := by
  have := card_union_add_card_inter S T
  have := card_le_univ (S ∪ T)
  omega

/-- Two sets of processes whose sizes add up to more than `n + t` have a correct process in
common. -/
theorem exists_notMem_inter_of_lt_card_add_card (hF : #F ≤ t)
    (h : Fintype.card P + t < #S + #T) : ∃ p, p ∈ S ∧ p ∈ T ∧ p ∉ F := by
  classical
  have := card_add_card_sub_le_card_inter S T
  obtain ⟨p, hp, hpF⟩ := exists_notMem_of_lt_card (S := S ∩ T) hF (by omega)
  exact ⟨p, (mem_inter.1 hp).1, (mem_inter.1 hp).2, hpF⟩

/-- If `3 * t < n`, any two quorums (sets of at least `n - t` processes) have a correct process
in common. -/
theorem exists_notMem_inter_of_quorums (hF : #F ≤ t) (hn : 3 * t < Fintype.card P)
    (hS : Fintype.card P - t ≤ #S) (hT : Fintype.card P - t ≤ #T) :
    ∃ p, p ∈ S ∧ p ∈ T ∧ p ∉ F :=
  exists_notMem_inter_of_lt_card_add_card hF (by omega)

/-- A quorum (a set of at least `n - t` processes) and a set of more than `2t` processes have a
correct process in common. -/
theorem exists_notMem_inter_of_quorum_of_two_mul_lt_card (hF : #F ≤ t)
    (hS : Fintype.card P - t ≤ #S) (hT : 2 * t < #T) : ∃ p, p ∈ S ∧ p ∈ T ∧ p ∉ F :=
  exists_notMem_inter_of_lt_card_add_card hF (by have := card_le_univ T; omega)

/-- If `3 * t < n`, a quorum (a set of at least `n - t` processes) contains more than `t`
correct processes. -/
theorem lt_card_sdiff_of_quorum [DecidableEq P] (hF : #F ≤ t) (hn : 3 * t < Fintype.card P)
    (hS : Fintype.card P - t ≤ #S) : t < #(S \ F) :=
  lt_card_sdiff_of_two_mul_lt_card hF (by omega)

/-! ### The set of correct processes -/

variable [DecidableEq P]

/-- There are at least `n - t` correct processes. -/
theorem card_sub_le_card_compl (hF : #F ≤ t) : Fintype.card P - t ≤ #Fᶜ := by
  rw [card_compl]
  omega

/-- If `3 * t < n`, there are more than `2t` (i.e. at least `2t + 1`) correct processes. -/
theorem two_mul_lt_card_compl (hF : #F ≤ t) (hn : 3 * t < Fintype.card P) : 2 * t < #Fᶜ := by
  have := card_sub_le_card_compl hF
  omega

/-- A set containing all correct processes is a quorum. -/
theorem card_sub_le_card_of_compl_subset (hF : #F ≤ t) (h : Fᶜ ⊆ S) :
    Fintype.card P - t ≤ #S :=
  (card_sub_le_card_compl hF).trans (card_le_card h)

/-! ### Disjoint sets of more than `t` processes -/

omit [DecidableEq P] in
/-- At most `n / (t + 1)` pairwise disjoint sets of processes have more than `t` elements each. -/
theorem card_le_div_of_pairwiseDisjoint {ι : Type*} {X : Finset ι} {S : ι → Finset P}
    (hS : (X : Set ι).PairwiseDisjoint S) (hX : ∀ i ∈ X, t < #(S i)) :
    #X ≤ Fintype.card P / (t + 1) := by
  classical
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos t)]
  calc #X * (t + 1) = #X • (t + 1) := rfl
    _ ≤ ∑ i ∈ X, #(S i) := Finset.card_nsmul_le_sum _ _ _ hX
    _ = #(X.biUnion S) := (Finset.card_biUnion hS).symm
    _ ≤ Fintype.card P := Finset.card_le_univ _

omit [DecidableEq P] in
/-- If `3 * t < n`, at most `n / (n - 3t)` pairwise disjoint sets of processes have at least
`n - 3t` elements each (e.g. at most `n / (n - 3t)` values are each broadcast by at least `n - 3t`
correct processes if every process broadcasts at most one value). -/
theorem card_le_div_sub_of_pairwiseDisjoint {ι : Type*} {X : Finset ι} {S : ι → Finset P}
    (hn : 3 * t < Fintype.card P) (hS : (X : Set ι).PairwiseDisjoint S)
    (hX : ∀ i ∈ X, Fintype.card P - 3 * t ≤ #(S i)) :
    #X ≤ Fintype.card P / (Fintype.card P - 3 * t) := by
  have := card_le_div_of_pairwiseDisjoint (t := Fintype.card P - 3 * t - 1) hS
    fun i hi => by have := hX i hi; omega
  rwa [Nat.sub_add_cancel (by omega)] at this

/-- If `3 * t < n`, then `min (n / (t + 1)) (n / (n - 3t)) ≤ 3`: if `n ≥ 4 (t + 1)`, then
`4 (n - 3t) > n`. Combining a `t + 1` threshold with a reduction to values supported by `n - 3t`
processes thus leaves a constant number of values for every `t < n / 3`. -/
theorem min_div_le_three {n : ℕ} (hn : 3 * t < n) : min (n / (t + 1)) (n / (n - 3 * t)) ≤ 3 := by
  by_contra h
  obtain ⟨h₁, h₂⟩ := Nat.lt_min.1 (not_le.1 h)
  have h₁ := (Nat.le_div_iff_mul_le (Nat.succ_pos t)).1 h₁
  have h₂ := (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hn)).1 h₂
  omega

omit [DecidableEq P] in
/-- If `3 * t < n`, at most three indices `i` have both more than `t` processes in `S i` and at
least `n - 3t` processes in `T i`, for pairwise disjoint families `S` and `T` (e.g. the values
echoed by a process on `t + 1` first `INIT`s, each of which was also broadcast by `n - 3t` correct
processes). -/
theorem card_le_three_of_pairwiseDisjoint {ι : Type*} {X : Finset ι} {S T : ι → Finset P}
    (hn : 3 * t < Fintype.card P) (hS : (X : Set ι).PairwiseDisjoint S)
    (hXS : ∀ i ∈ X, t < #(S i)) (hT : (X : Set ι).PairwiseDisjoint T)
    (hXT : ∀ i ∈ X, Fintype.card P - 3 * t ≤ #(T i)) : #X ≤ 3 :=
  (le_min (card_le_div_of_pairwiseDisjoint hS hXS)
    (card_le_div_sub_of_pairwiseDisjoint hn hT hXT)).trans (min_div_le_three hn)

end Cslib.Distributed.Quorum
