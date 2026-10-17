/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# König's line-colouring theorem for `ℕ`-matrices

Combinatorial lemmas about `ℕ`-valued matrices `Matrix α β ℕ`. They are the integral counterpart
of Mathlib's Birkhoff–von Neumann theorem (`doublyStochastic_eq_convexHull_permMatrix`,
`exists_eq_sum_perm_of_mem_doublyStochastic` in `Mathlib/Analysis/Convex/Birkhoff.lean`), which
works over ordered fields and therefore does not give integer decompositions. König's
line-colouring theorem for bipartite multigraphs (a bipartite multigraph of maximum degree `Δ` can
be edge-coloured with `Δ` colours) is `Matrix.exists_split_parts` with `D = 1`.

## Main statements

* `Fintype.exists_le_sum_eq`: a number below a sum splits into parts below the summands;
* `Matrix.exists_transport`: the transportation problem with equal totals has an `ℕ`-solution
  (north-west corner rule);
* `Matrix.exists_regular_above`: a square matrix with row and column sums `≤ K` is entrywise below
  a matrix with all row and column sums equal to `K`;
* `Matrix.exists_perm_decomposition`: a `K`-regular square `ℕ`-matrix is a sum of `K` permutation
  matrices (Birkhoff–König, via Hall's marriage theorem);
* `Matrix.exists_split_parts`: a square `ℕ`-matrix with row and column sums `≤ |ι| * D` splits into
  `|ι|` matrices with row and column sums `≤ D`.
-/

@[expose] public section

open Finset

namespace Fintype

/-- Splitting a number below a sum: if `a ≤ ∑ x, b x` then `a = ∑ x, a' x` with `a' ≤ b`. -/
theorem exists_le_sum_eq {ι : Type*} [Fintype ι] (a : ℕ) (b : ι → ℕ) (h : a ≤ ∑ x, b x) :
    ∃ a' : ι → ℕ, (∀ x, a' x ≤ b x) ∧ ∑ x, a' x = a := by
  classical
  suffices H : ∀ (s : Finset ι) (a : ℕ), a ≤ ∑ x ∈ s, b x →
      ∃ a' : ι → ℕ, (∀ x, a' x ≤ b x) ∧ ∑ x ∈ s, a' x = a from H univ a h
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro a ha
    refine ⟨0, fun _ => Nat.zero_le _, ?_⟩
    simp only [Finset.sum_empty, nonpos_iff_eq_zero] at ha
    simp [ha]
  | insert x0 s hx0 ih =>
    intro a ha
    rw [Finset.sum_insert hx0] at ha
    obtain ⟨a', ha'b, ha's⟩ := ih (a - min a (b x0)) (by omega)
    refine ⟨Function.update a' x0 (min a (b x0)), fun x => ?_, ?_⟩
    · rcases eq_or_ne x x0 with rfl | hx
      · simp
      · simp [hx, ha'b]
    · have hs : ∑ x ∈ s, Function.update a' x0 (min a (b x0)) x = ∑ x ∈ s, a' x :=
        Finset.sum_congr rfl fun x hx => Function.update_of_ne (by rintro rfl; exact hx0 hx) _ _
      rw [Finset.sum_insert hx0, Function.update_self, hs, ha's]
      omega

end Fintype

namespace Matrix

/-- Transportation problem with equal totals (north-west corner rule): given supplies `r` and
demands `c` with the same total, there is an `ℕ`-matrix with row sums `r` and column sums `c`. -/
theorem exists_transport {α β : Type*} [Fintype α] [Fintype β] (r : α → ℕ) (c : β → ℕ)
    (h : ∑ i, r i = ∑ j, c j) :
    ∃ q : Matrix α β ℕ, (∀ i, ∑ j, q i j = r i) ∧ (∀ j, ∑ i, q i j = c j) := by
  classical
  suffices H : ∀ (s : Finset α) (c : β → ℕ), ∑ i ∈ s, r i = ∑ j, c j →
      ∃ q : α → β → ℕ, (∀ i ∈ s, ∑ j, q i j = r i) ∧ (∀ j, ∑ i ∈ s, q i j = c j) by
    obtain ⟨q, h1, h2⟩ := H univ c h
    exact ⟨q, fun i => h1 i (mem_univ i), h2⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro c hc
    refine ⟨0, by simp, fun j => ?_⟩
    simp only [sum_empty] at hc ⊢
    exact ((sum_eq_zero_iff.1 hc.symm) j (mem_univ j)).symm
  | insert i0 s hi0 ih =>
    intro c hc
    rw [sum_insert hi0] at hc
    obtain ⟨a, hac, hasum⟩ := Fintype.exists_le_sum_eq (r i0) c (by omega)
    obtain ⟨q, hq1, hq2⟩ := ih (fun j => c j - a j) (by
      rw [sum_tsub_distrib _ (fun j _ => hac j)]; omega)
    refine ⟨Function.update q i0 a, fun i hi => ?_, fun j => ?_⟩
    · rcases mem_insert.1 hi with rfl | hi'
      · simp [hasum]
      · rw [Function.update_of_ne (by rintro rfl; exact hi0 hi')]; exact hq1 i hi'
    · have hs : ∑ i ∈ s, Function.update q i0 a i j = ∑ i ∈ s, q i j :=
        sum_congr rfl fun i hi => by rw [Function.update_of_ne (by rintro rfl; exact hi0 hi)]
      rw [sum_insert hi0, Function.update_self, hs, hq2 j]
      have := hac j
      omega

/-- Padding: a square matrix with row and column sums `≤ K` is entrywise below a matrix whose
row and column sums are all equal to `K`. -/
theorem exists_regular_above {α : Type*} [Fintype α] (A : Matrix α α ℕ) (K : ℕ)
    (hr : ∀ i, ∑ j, A i j ≤ K) (hc : ∀ j, ∑ i, A i j ≤ K) :
    ∃ B : Matrix α α ℕ, (∀ i j, A i j ≤ B i j) ∧ (∀ i, ∑ j, B i j = K) ∧ (∀ j, ∑ i, B i j = K) := by
  obtain ⟨q, hq1, hq2⟩ :=
    exists_transport (fun i => K - ∑ j, A i j) (fun j => K - ∑ i, A i j) (by
      rw [sum_tsub_distrib _ (fun i _ => hr i), sum_tsub_distrib _ (fun j _ => hc j), sum_comm])
  refine ⟨fun i j => A i j + q i j, fun i j => Nat.le_add_right _ _, fun i => ?_, fun j => ?_⟩
  · rw [sum_add_distrib, hq1 i]; have := hr i; omega
  · rw [sum_add_distrib, hq2 j]; have := hc j; omega

/-- Sum form of `exists_perm_decomposition`. -/
theorem exists_perm_decomposition_sum {α : Type*} [Fintype α] [DecidableEq α] (K : ℕ) :
    ∀ B : Matrix α α ℕ, (∀ i, ∑ j, B i j = K) → (∀ j, ∑ i, B i j = K) →
    ∃ σ : Fin K → Equiv.Perm α, ∀ i j, B i j = ∑ c, if σ c i = j then 1 else 0 := by
  induction K with
  | zero =>
    intro B hr _
    refine ⟨Fin.elim0, fun i j => ?_⟩
    simp only [univ_eq_empty, sum_empty]
    exact (sum_eq_zero_iff.1 (hr i)) j (mem_univ j)
  | succ K ih =>
    intro B hr hc
    -- Hall's condition for the supports of the rows.
    let f : α → Finset α := fun i => univ.filter (fun j => B i j ≠ 0)
    have hf : ∀ S : Finset α, #S ≤ #(S.biUnion f) := by
      intro S
      set T := S.biUnion f
      have h1 : ∑ i ∈ S, ∑ j, B i j = ∑ i ∈ S, ∑ j ∈ T, B i j := by
        refine sum_congr rfl fun i hi => ?_
        symm
        refine sum_subset (subset_univ _) fun j _ hj => ?_
        by_contra hne
        exact hj (mem_biUnion.2 ⟨i, hi, mem_filter.2 ⟨mem_univ _, hne⟩⟩)
      have h2 : ∑ i ∈ S, ∑ j ∈ T, B i j ≤ ∑ i, ∑ j ∈ T, B i j :=
        sum_le_sum_of_subset (subset_univ _)
      have h3 : ∑ i, ∑ j ∈ T, B i j = #T * (K + 1) := by
        refine sum_comm.trans ?_; simp [hc]
      have h4 : ∑ i ∈ S, ∑ j, B i j = #S * (K + 1) := by simp [hr]
      have h5 : #S * (K + 1) ≤ #T * (K + 1) := by omega
      exact Nat.le_of_mul_le_mul_right h5 (Nat.succ_pos K)
    obtain ⟨g, hg, hgf⟩ := (all_card_le_biUnion_card_iff_exists_injective f).1 hf
    have hgB : ∀ i, 1 ≤ B i (g i) := by
      intro i; have := hgf i; simp only [f, mem_filter, mem_univ, true_and] at this; omega
    let σ : Equiv.Perm α := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg)
    have hσ : ∀ i, σ i = g i := fun i => rfl
    have hle : ∀ i j, (if σ i = j then 1 else 0) ≤ B i j := by
      intro i j; split_ifs with h
      · rw [← h, hσ]; exact hgB i
      · exact Nat.zero_le _
    have hr' : ∀ i, ∑ j, (B i j - if σ i = j then 1 else 0) = K := by
      intro i
      rw [sum_tsub_distrib _ (fun j _ => hle i j), hr i]
      simp
    have hc' : ∀ j, ∑ i, (B i j - if σ i = j then 1 else 0) = K := by
      intro j
      rw [sum_tsub_distrib _ (fun i _ => hle i j), hc j]
      simp [← Equiv.eq_symm_apply]
    obtain ⟨τ, hτ⟩ := ih _ hr' hc'
    refine ⟨(Fin.cons σ τ : Fin (K + 1) → Equiv.Perm α), fun i j => ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hτ i j]
    have := hle i j
    omega

/-- Birkhoff–König for `ℕ`-matrices: a `K`-regular square `ℕ`-matrix (all row and column sums
equal to `K`) is a sum of `K` permutation matrices. -/
theorem exists_perm_decomposition {α : Type*} [Fintype α] [DecidableEq α] (B : Matrix α α ℕ)
    (K : ℕ) (hr : ∀ i, ∑ j, B i j = K) (hc : ∀ j, ∑ i, B i j = K) :
    ∃ σ : Fin K → Equiv.Perm α, ∀ i j, B i j = (Finset.univ.filter (fun c => σ c i = j)).card := by
  obtain ⟨σ, hσ⟩ := exists_perm_decomposition_sum K B hr hc
  exact ⟨σ, fun i j => by rw [hσ, card_filter]⟩

/-- Main splitting lemma (König's line-colouring theorem in matrix form; Theorem 3.2 of Lenzen,
*Optimal deterministic routing and sorting on the congested clique*, PODC 2013): a square
`ℕ`-matrix whose row and column sums are at most `|ι| * D` is the sum of `|ι|` matrices whose row
and column sums are at most `D`. -/
theorem exists_split_parts {α ι : Type*} [Fintype α] [Fintype ι]
    (A : Matrix α α ℕ) (D : ℕ)
    (hr : ∀ i, ∑ j, A i j ≤ Fintype.card ι * D) (hc : ∀ j, ∑ i, A i j ≤ Fintype.card ι * D) :
    ∃ P : ι → Matrix α α ℕ, (∀ i j, ∑ x, P x i j = A i j) ∧
      (∀ x i, ∑ j, P x i j ≤ D) ∧ (∀ x j, ∑ i, P x i j ≤ D) := by
  classical
  obtain ⟨B, hAB, hBr, hBc⟩ := exists_regular_above A (Fintype.card ι * D) hr hc
  obtain ⟨σ, hσ⟩ := exists_perm_decomposition_sum _ B hBr hBc
  let e : ι × Fin D ≃ Fin (Fintype.card ι * D) :=
    ((Fintype.equivFin ι).prodCongr (Equiv.refl _)).trans finProdFinEquiv
  let Q : ι → α → α → ℕ := fun x i j => ∑ d : Fin D, if σ (e (x, d)) i = j then 1 else 0
  have hQ : ∀ i j, ∑ x, Q x i j = B i j := by
    intro i j
    rw [hσ i j, ← e.sum_comp (fun c => if σ c i = j then 1 else 0), Fintype.sum_prod_type]
  have hQr : ∀ x i, ∑ j, Q x i j = D := by
    intro x i
    simp only [Q]; rw [sum_comm]; simp
  have hQc : ∀ x j, ∑ i, Q x i j = D := by
    intro x j
    simp only [Q]; rw [sum_comm]; simp [← Equiv.eq_symm_apply]
  have hsplit : ∀ i j, ∃ a' : ι → ℕ, (∀ x, a' x ≤ Q x i j) ∧ ∑ x, a' x = A i j :=
    fun i j => Fintype.exists_le_sum_eq (A i j) (fun x => Q x i j) (by rw [hQ]; exact hAB i j)
  choose P hP1 hP2 using hsplit
  refine ⟨fun x i j => P i j x, hP2, fun x i => ?_, fun x j => ?_⟩
  · exact (sum_le_sum fun j _ => hP1 i j x).trans (hQr x i).le
  · exact (sum_le_sum fun i _ => hP1 i j x).trans (hQc x j).le

end Matrix
