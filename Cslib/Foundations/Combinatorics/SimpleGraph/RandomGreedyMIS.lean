/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.GreedyMIS
public import Cslib.Probability.RandomOrder.FirstInSet

/-!
# Random greedy MIS: the influenced set of a vertex has expected size at most one

For a uniformly random order `π : V ≃ Fin |V|`, consider the greedy MIS of `G[A]` and a vertex `x`.
The set `G.influenced A π x` (vertices whose greedy state is undetermined when the state of `x` is
unknown) is the set of vertices that may have to change when `x` changes its state. We show

  `E_π[ |influenced(π, x)| · 1{x ∈ greedyMIS(π)} · 1{all of B before x} ] ≤ Pr_π[all of B before x]`

(`sum_card_influenced_le`), and `E_π[ |influenced| · 1{x ∈ greedyMIS} ] = 1` for a present `x`
(`sum_card_influenced_eq`). This is the core of Theorem 1 of Censor-Hillel, Haramaty, Karnin,
*Optimal Dynamic Distributed MIS* (PODC 2016): `B = ∅` handles vertex insertions and deletions, and
`B = {other endpoint}` handles edge changes.

Proof: let `W π` be the influenced set for the order where `x` is moved to the front. Then
`x ∈ greedyMIS(π)` iff `x` is `π`-first in `W π`, and in that case `W π` is the influenced set for
`π` (`partialGreedy_eq_of_moveFirst`, `exists_mem_influenced_of_notMem`). `W π` is invariant under
reorderings that keep the relative order inside `W π \ {x}` and inside its complement
(`partialGreedy_eq_of_reorder`, Claims 4–5 of the paper), so `RandomOrder.sum_card_first_le`
applies.
-/

@[expose] public section

open Finset Cslib

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Set V)

/-- The rank function `v ↦ π v` of an order `π`. -/
def orderRank (π : V ≃ Fin (Fintype.card V)) : V → ℕ := fun v => π v

/-- The order `π` with `x` moved to the front (as a rank function). -/
def moveFirst (π : V ≃ Fin (Fintype.card V)) (x : V) : V → ℕ :=
  fun v => if v = x then 0 else (π v : ℕ) + 1

variable {G A}

omit [DecidableEq V] in
theorem orderRank_injective (π : V ≃ Fin (Fintype.card V)) : Function.Injective (orderRank π) :=
  fun _ _ h => π.injective (Fin.ext h)

theorem moveFirst_injective (π : V ≃ Fin (Fintype.card V)) (x : V) :
    Function.Injective (moveFirst π x) := by
  intro u v h
  by_cases hu : u = x <;> by_cases hv : v = x
  · rw [hu, hv]
  · simp [moveFirst, hu, hv] at h
  · simp [moveFirst, hu, hv] at h
  · simp only [moveFirst, hu, hv, ite_false] at h
    exact π.injective (Fin.ext (by omega))

theorem moveFirst_first (π : V ≃ Fin (Fintype.card V)) (x : V) :
    ∀ v, v ≠ x → moveFirst π x x < moveFirst π x v := by
  intro v hv; simp [moveFirst, hv]

theorem moveFirst_lt_iff (π : V ≃ Fin (Fintype.card V)) {x u v : V} (hu : u ≠ x) (hv : v ≠ x) :
    moveFirst π x u < moveFirst π x v ↔ π u < π v := by
  simp [moveFirst, hu, hv]

open Classical in
/-- The influenced set of `x` for the order `π` with `x` moved to the front. -/
noncomputable def influencedFirst (G : SimpleGraph V) (A : Set V) (π : V ≃ Fin (Fintype.card V))
    (x : V) : Finset V :=
  (G.influenced A (moveFirst π x) x).toFinset

theorem mem_influencedFirst {π : V ≃ Fin (Fintype.card V)} {x u : V} :
    u ∈ G.influencedFirst A π x ↔ u ∈ G.influenced A (moveFirst π x) x := by
  classical
  simp [influencedFirst]

theorem self_mem_influencedFirst (π : V ≃ Fin (Fintype.card V)) (x : V) :
    x ∈ G.influencedFirst A π x :=
  mem_influencedFirst.2 (self_mem_influenced x)

/-- Claims 4–5: `influencedFirst` only depends on the relative orders inside and outside of it. -/
theorem influencedFirst_eq_of_reorder (x : V) (π σ : V ≃ Fin (Fintype.card V))
    (h : ∀ u v, u ≠ x → v ≠ x →
      (u ∈ G.influencedFirst A π x ↔ v ∈ G.influencedFirst A π x) → (π u < π v ↔ σ u < σ v)) :
    G.influencedFirst A σ x = G.influencedFirst A π x := by
  have := G.partialGreedy_eq_of_reorder (A := A) (moveFirst_injective π x)
    (moveFirst_first π x) (moveFirst_first σ x) fun u v hu hv huv => by
      rw [moveFirst_lt_iff π hu hv, moveFirst_lt_iff σ hu hv]
      exact h u v hu hv (by simpa only [mem_influencedFirst] using huv)
  ext u
  simp only [mem_influencedFirst, influenced, Set.mem_ofPred_eq, this]

/-- For a present `x`: `x` is in the greedy MIS iff it is first in `influencedFirst`; then
`influencedFirst` is the influenced set for `π` itself. -/
theorem mem_greedyMIS_iff_first {π : V ≃ Fin (Fintype.card V)} {x : V} (hxA : x ∈ A) :
    x ∈ G.greedyMIS A (orderRank π) ↔ ∀ u ∈ G.influencedFirst A π x, π x ≤ π u := by
  have hord : ∀ u v, u ≠ x → v ≠ x →
      (orderRank π u < orderRank π v ↔ moveFirst π x u < moveFirst π x v) := fun u v hu hv => by
    rw [moveFirst_lt_iff π hu hv]; simp [orderRank]
  constructor
  · intro hx u hu
    rw [mem_influencedFirst, influenced, ← G.partialGreedy_eq_of_moveFirst (orderRank_injective π)
      (moveFirst_first π x) hord hx] at hu
    by_contra h
    exact notMem_influenced_of_lt (r := orderRank π) (by simpa [orderRank] using h) hu
  · intro h
    by_contra hx
    obtain ⟨w, hw, hwW⟩ := G.exists_mem_influenced_of_notMem (moveFirst_first π x) hord hxA hx
    exact absurd (h w (mem_influencedFirst.2 hwW)) (by simpa [orderRank] using hw)

open Classical in
theorem influencedFirst_eq_of_mem {π : V ≃ Fin (Fintype.card V)} {x : V}
    (hx : x ∈ G.greedyMIS A (orderRank π)) :
    G.influencedFirst A π x = (G.influenced A (orderRank π) x).toFinset := by
  have hord : ∀ u v, u ≠ x → v ≠ x →
      (orderRank π u < orderRank π v ↔ moveFirst π x u < moveFirst π x v) := fun u v hu hv => by
    rw [moveFirst_lt_iff π hu hv]; simp [orderRank]
  rw [influencedFirst, influenced, influenced, G.partialGreedy_eq_of_moveFirst
    (orderRank_injective π) (moveFirst_first π x) hord hx]

open Classical in
/-- **Core of Theorem 1** (Censor-Hillel–Haramaty–Karnin, PODC 2016). For a uniformly random
order `π`, `E[|influenced(π, x)| · 1{x ∈ greedyMIS(π)} · 1{B before x}] ≤ Pr[B before x]`. -/
theorem sum_card_influenced_le (x : V) (B : Finset V) :
    ∑ π : V ≃ Fin (Fintype.card V),
        (if (∀ y ∈ B, π y < π x) ∧ x ∈ G.greedyMIS A (orderRank π) then
          (G.influenced A (orderRank π) x).toFinset.card else 0)
      ≤ #{π : V ≃ Fin (Fintype.card V) | ∀ y ∈ B, π y < π x} := by
  refine le_trans (Finset.sum_le_sum fun π _ => ?_) (RandomOrder.sum_card_first_le x B
    (fun π => G.influencedFirst A π x) (self_mem_influencedFirst · x)
    (fun π σ h => influencedFirst_eq_of_reorder x π σ h))
  by_cases h : (∀ y ∈ B, π y < π x) ∧ x ∈ G.greedyMIS A (orderRank π)
  · have hxA : x ∈ A := G.greedyMIS_subset A _ h.2
    rw [ite_eq_left h, ite_eq_left ⟨h.1, (mem_greedyMIS_iff_first hxA).1 h.2⟩,
      influencedFirst_eq_of_mem h.2]
  · rw [ite_eq_right h]; exact Nat.zero_le _

open Classical in
/-- For a present vertex `x`: `E[|influenced(π, x)| · 1{x ∈ greedyMIS(π)}] = 1`. -/
theorem sum_card_influenced_eq {x : V} (hxA : x ∈ A) :
    ∑ π : V ≃ Fin (Fintype.card V),
        (if x ∈ G.greedyMIS A (orderRank π) then
          (G.influenced A (orderRank π) x).toFinset.card else 0)
      = (Fintype.card V).factorial := by
  rw [← RandomOrder.sum_card_first_eq x (fun π => G.influencedFirst A π x)
    (self_mem_influencedFirst · x) (fun π σ h => influencedFirst_eq_of_reorder x π σ h)]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases h : x ∈ G.greedyMIS A (orderRank π)
  · rw [ite_eq_left h, ite_eq_left ((mem_greedyMIS_iff_first hxA).1 h), influencedFirst_eq_of_mem h]
  · rw [ite_eq_right h, ite_eq_right (by rwa [← mem_greedyMIS_iff_first hxA])]

end SimpleGraph
