/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Adjacency in the cycle graph `C_n`

Elementary facts about Mathlib's `SimpleGraph.cycleGraph n` on `Fin n`.

## Main statements

* `SimpleGraph.cycleGraph_adj_val`: adjacent vertices have consecutive values, or are `0` and
  `n - 1`.
* `SimpleGraph.cycleGraph_adj_neg`: negation `j ↦ -j` is an automorphism.
* `SimpleGraph.cycleGraph_adj_add_one`: `j ~ j + 1` for `n ≥ 2`.
-/

@[expose] public section

namespace SimpleGraph

variable {n : ℕ}

/-- Adjacency in a cycle graph, in terms of values: consecutive values, or `0` and `n - 1`. -/
theorem cycleGraph_adj_val {x y : Fin n} (h : (cycleGraph n).Adj x y) :
    y.val = x.val + 1 ∨ x.val = y.val + 1 ∨ (x.val = 0 ∧ y.val + 1 = n) ∨
      (y.val = 0 ∧ x.val + 1 = n) := by
  rw [cycleGraph_adj'] at h
  have hx := x.isLt
  have hy := y.isLt
  rcases le_or_gt y x with hxy | hxy <;> rcases le_or_gt x y with hyx | hyx
  · rcases h with h | h
    · rw [Fin.coe_sub_iff_le.2 hxy] at h; omega
    · rw [Fin.coe_sub_iff_le.2 hyx] at h; omega
  · rcases h with h | h
    · rw [Fin.coe_sub_iff_le.2 hxy] at h; omega
    · rw [Fin.coe_sub_iff_lt.2 hyx] at h; omega
  · rcases h with h | h
    · rw [Fin.coe_sub_iff_lt.2 hxy] at h; omega
    · rw [Fin.coe_sub_iff_le.2 hyx] at h; omega
  · exact absurd (hxy.trans hyx) (lt_irrefl _)

/-- Negation `j ↦ -j` preserves adjacency in a cycle graph. -/
theorem cycleGraph_adj_neg [NeZero n] {u v : Fin n} :
    (cycleGraph n).Adj (-u) (-v) ↔ (cycleGraph n).Adj u v := by
  rw [cycleGraph_adj', cycleGraph_adj', neg_sub_neg, neg_sub_neg, or_comm]

/-- In a cycle graph with at least two vertices, `j` and `j + 1` are adjacent. -/
theorem cycleGraph_adj_add_one [NeZero n] (hn : 2 ≤ n) (j : Fin n) :
    (cycleGraph n).Adj j (j + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [cycleGraph_adj]
  right
  simp

end SimpleGraph
