/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Local.LocallyIterative
public import Mathlib.Order.Interval.Set.Nat

/-!
# Standard colour reduction (locally-iterative)

From a proper `m`-colouring (colours in `ℕ`, all `< m`) of a graph of maximum degree `≤ Δ`, the
*standard colour reduction* computes a proper `(Δ + 1)`-colouring in `m - (Δ + 1)` rounds: in round
`t` every vertex of colour `m - 1 - t` (if this colour is `> Δ`) recolours itself with the smallest
colour not used by its neighbours, which is `≤ Δ`. Vertices of one colour class are pairwise
non-adjacent, so they can recolour in parallel. (See e.g. Barenboim–Elkin, *Distributed Graph
Coloring*, Chapter 3.) The algorithm is locally-iterative: it only uses the round number, the own
colour and the set of neighbours' colours.

## Main results

* `firstFree N` — the least natural number not in `N`; `firstFree_notMem`, `firstFree_le_ncard`.
* `colorReduction m Δ` — the algorithm.
* `colorReduction_isProper` — every intermediate colouring is proper.
* `colorReduction_le` — after `m - (Δ + 1)` rounds all colours are `≤ Δ`.
-/

@[expose] public section

namespace Cslib.LocallyIterative

/-- The least natural number not in `N`. -/
noncomputable def firstFree (N : Set ℕ) : ℕ := sInf Nᶜ

theorem firstFree_notMem {N : Set ℕ} (hN : N.Finite) : firstFree N ∉ N :=
  Nat.sInf_mem hN.infinite_compl.nonempty

theorem firstFree_le_ncard {N : Set ℕ} (hN : N.Finite) : firstFree N ≤ N.ncard := by
  by_contra h
  push Not at h
  have hsub : Set.Iic N.ncard ⊆ N := fun k hk => by
    by_contra hk'
    exact absurd (Nat.sInf_le (show k ∈ Nᶜ from hk'))
      (by simp only [Set.mem_Iic] at hk; unfold firstFree at h; omega)
  have := Set.ncard_le_ncard hsub hN
  simp at this

/-- The standard colour reduction from `m` colours to `Δ + 1` colours: in round `t < m - (Δ + 1)`
the vertices of colour `m - 1 - t` recolour themselves with the least colour not used by a
neighbour. -/
noncomputable def colorReduction (m Δ : ℕ) : Algorithm ℕ :=
  ⟨fun t x N => if Δ + 1 + t < m ∧ x = m - 1 - t then firstFree N else x⟩

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
theorem colorReduction_run_succ {m Δ : ℕ} (c₀ : V → ℕ) (t : ℕ) (v : V) :
    (colorReduction m Δ).run G c₀ (t + 1) v =
      if Δ + 1 + t < m ∧ (colorReduction m Δ).run G c₀ t v = m - 1 - t then
        firstFree (nbrColors G ((colorReduction m Δ).run G c₀ t) v)
      else (colorReduction m Δ).run G c₀ t v := rfl

/-- One round of the colour reduction keeps properness and the invariant "colours are `< m - t` or
`≤ Δ`". -/
theorem colorReduction_step {m Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ} (t : ℕ)
    (h : IsProper G ((colorReduction m Δ).run G c₀ t) ∧
      ∀ v, (colorReduction m Δ).run G c₀ t v < m - t ∨ (colorReduction m Δ).run G c₀ t v ≤ Δ) :
    IsProper G ((colorReduction m Δ).run G c₀ (t + 1)) ∧
      ∀ v, (colorReduction m Δ).run G c₀ (t + 1) v < m - (t + 1) ∨
        (colorReduction m Δ).run G c₀ (t + 1) v ≤ Δ := by
  obtain ⟨hp, hb⟩ := h
  have hfree : ∀ v, firstFree (nbrColors G ((colorReduction m Δ).run G c₀ t) v) ≤ Δ := fun v =>
    (firstFree_le_ncard (finite_nbrColors _ v)).trans ((ncard_nbrColors_le _ v).trans (hΔ v))
  constructor
  · intro u v huv
    have hne := hp huv
    rw [colorReduction_run_succ, colorReduction_run_succ]
    split_ifs with hu hv hv
    · exact absurd (hu.2.trans hv.2.symm) hne
    · intro h
      have := mem_nbrColors_of_adj ((colorReduction m Δ).run G c₀ t) huv
      rw [← h] at this
      exact firstFree_notMem (finite_nbrColors _ u) this
    · intro h
      have := mem_nbrColors_of_adj ((colorReduction m Δ).run G c₀ t) huv.symm
      rw [h] at this
      exact firstFree_notMem (finite_nbrColors _ v) this
    · exact hne
  · intro v
    rw [colorReduction_run_succ]
    split_ifs with hv
    · exact Or.inr (hfree v)
    · rcases hb v with h | h
      · by_cases hlt : Δ + 1 + t < m
        · left
          have : (colorReduction m Δ).run G c₀ t v ≠ m - 1 - t := fun e => hv ⟨hlt, e⟩
          omega
        · right; omega
      · exact Or.inr h

/-- Every colouring produced by the standard colour reduction from a proper `m`-colouring is
proper, and after `t` rounds all colours are `< m - t` or `≤ Δ`. -/
theorem colorReduction_invariant {m Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ}
    (hp : IsProper G c₀) (hm : ∀ v, c₀ v < m) (t : ℕ) :
    IsProper G ((colorReduction m Δ).run G c₀ t) ∧
      ∀ v, (colorReduction m Δ).run G c₀ t v < m - t ∨ (colorReduction m Δ).run G c₀ t v ≤ Δ := by
  induction t with
  | zero => exact ⟨hp, fun v => Or.inl (hm v)⟩
  | succ t ih => exact colorReduction_step hΔ t ih

theorem colorReduction_isProper {m Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ}
    (hp : IsProper G c₀) (hm : ∀ v, c₀ v < m) (t : ℕ) :
    IsProper G ((colorReduction m Δ).run G c₀ t) :=
  (colorReduction_invariant hΔ hp hm t).1

/-- **Standard colour reduction.** After `m - (Δ + 1)` rounds (or later) all colours are `≤ Δ`. -/
theorem colorReduction_le {m Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ}
    (hp : IsProper G c₀) (hm : ∀ v, c₀ v < m) {t : ℕ} (ht : m - (Δ + 1) ≤ t) (v : V) :
    (colorReduction m Δ).run G c₀ t v ≤ Δ := by
  rcases (colorReduction_invariant hΔ hp hm t).2 v with h | h
  · omega
  · exact h

end Cslib.LocallyIterative
