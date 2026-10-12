/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.ApproxConsensus.Iterative
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Trimming the `f` smallest and `f` largest received values

The core step of MSR-type approximate-agreement algorithms (Dolev–Lynch–Pinter–Stark–Weihl 1986,
Vaidya–Tseng–Liang 2012, LeBlanc et al. 2013): sort the values received from the in-neighbours
`N`, drop the `f` smallest and the `f` largest (**ties broken arbitrarily**), and average the rest
with the own value.

`IsTrim N f r Low Mid High` says that `(Low, Mid, High)` is the result of *some* tie-breaking:
`Low`, `High` are disjoint `f`-subsets of `N`, `Mid = N \ (Low ∪ High)`, and
`r(Low) ≤ r(Mid) ≤ r(High)`, `r(Low) ≤ r(High)` element-wise. (Equivalently: there is a sorting of
`N` by `r` whose first `f` elements are `Low` and last `f` are `High`.)

## Main results

* `IsTrim.exists`: a trimming exists when `2f ≤ #N`.
* `IsTrim.card_mid`: `#Mid = #N - 2f`.
* `IsTrim.exists_correct_le`, `IsTrim.exists_le_correct`: with at most `f` faulty nodes, every
  kept value is bounded below (above) by a value of a fault-free in-neighbour.
* `IsTrim.exists_le_mid`, `IsTrim.exists_mid_le`: if `f + 1` nodes of `P ⊆ N` are given and
  `2f + 1 ≤ #N`, some kept value is `≥` (resp. `≤`) the value of some node of `P`.
* `tmean`, `tmean_sub_ge`, `sub_tmean_ge`: the trimmed mean dominates `a · (w - ψ)` for each of
  its terms `w`, `a = 1/(#Mid + 1)`.
-/

@[expose] public section

open Finset

namespace Cslib.ApproxConsensus

variable {V : Type*} [DecidableEq V]

/-- `(Low, Mid, High)` is a valid trimming of the values `r` on `N` (for some tie-break). -/
structure IsTrim (N : Finset V) (f : ℕ) (r : V → ℝ) (Low Mid High : Finset V) : Prop where
  low_sub : Low ⊆ N
  high_sub : High ⊆ N
  disj : Disjoint Low High
  mid_eq : Mid = N \ (Low ∪ High)
  card_low : #Low = f
  card_high : #High = f
  low_le_mid : ∀ l ∈ Low, ∀ m ∈ Mid, r l ≤ r m
  mid_le_high : ∀ m ∈ Mid, ∀ h ∈ High, r m ≤ r h
  low_le_high : ∀ l ∈ Low, ∀ h ∈ High, r l ≤ r h

namespace IsTrim

variable {N : Finset V} {f : ℕ} {r : V → ℝ} {Low Mid High : Finset V}

theorem mid_sub (h : IsTrim N f r Low Mid High) : Mid ⊆ N := by
  rw [h.mid_eq]; exact sdiff_subset

theorem card_mid (h : IsTrim N f r Low Mid High) : #Mid = #N - 2 * f := by
  rw [h.mid_eq, card_sdiff_of_subset (union_subset h.low_sub h.high_sub),
    card_union_of_disjoint h.disj, h.card_low, h.card_high]
  ring_nf

theorem mem_mid (h : IsTrim N f r Low Mid High) {j : V} :
    j ∈ Mid ↔ j ∈ N ∧ j ∉ Low ∧ j ∉ High := by
  rw [h.mid_eq]; simp

/-- Kept values are bounded below by fault-free values: if `j ∈ Mid` and at most `f` nodes are
faulty, some fault-free `k ∈ N` has `r k ≤ r j`. -/
theorem exists_correct_le (h : IsTrim N f r Low Mid High) {F : Finset V} (hF : #F ≤ f)
    {j : V} (hj : j ∈ Mid) : ∃ k ∈ N, k ∉ F ∧ r k ≤ r j := by
  by_cases hjF : j ∈ F
  · have hjL : j ∉ Low := (h.mem_mid.mp hj).2.1
    -- `Low ∩ F ⊆ F.erase j`, which has fewer than `f = #Low` elements
    have : ¬ Low ⊆ F := by
      intro hsub
      have h1 : Low ⊆ F.erase j := fun x hx =>
        mem_erase.mpr ⟨fun hxj => hjL (hxj ▸ hx), hsub hx⟩
      have h2 := card_le_card h1
      rw [card_erase_of_mem hjF, h.card_low] at h2
      have : 0 < #F := card_pos.mpr ⟨j, hjF⟩
      omega
    obtain ⟨k, hkL, hkF⟩ := not_subset.mp this
    exact ⟨k, h.low_sub hkL, hkF, h.low_le_mid k hkL j hj⟩
  · exact ⟨j, h.mid_sub hj, hjF, le_rfl⟩

/-- Kept values are bounded above by fault-free values. -/
theorem exists_le_correct (h : IsTrim N f r Low Mid High) {F : Finset V} (hF : #F ≤ f)
    {j : V} (hj : j ∈ Mid) : ∃ k ∈ N, k ∉ F ∧ r j ≤ r k := by
  by_cases hjF : j ∈ F
  · have hjH : j ∉ High := (h.mem_mid.mp hj).2.2
    have : ¬ High ⊆ F := by
      intro hsub
      have h1 : High ⊆ F.erase j := fun x hx =>
        mem_erase.mpr ⟨fun hxj => hjH (hxj ▸ hx), hsub hx⟩
      have h2 := card_le_card h1
      rw [card_erase_of_mem hjF, h.card_high] at h2
      have : 0 < #F := card_pos.mpr ⟨j, hjF⟩
      omega
    obtain ⟨k, hkH, hkF⟩ := not_subset.mp this
    exact ⟨k, h.high_sub hkH, hkF, h.mid_le_high j hj k hkH⟩
  · exact ⟨j, h.mid_sub hj, hjF, le_rfl⟩

theorem mid_nonempty (h : IsTrim N f r Low Mid High) (hN : 2 * f + 1 ≤ #N) : Mid.Nonempty := by
  rw [← card_pos, h.card_mid]; omega

/-- If at least `f + 1` in-neighbours `P` are given, some kept value is `≥` the value of some
node of `P` (either a node of `P` is kept, or one of them was dropped as "low"). -/
theorem exists_le_mid (h : IsTrim N f r Low Mid High) (hN : 2 * f + 1 ≤ #N) {P : Finset V}
    (hP : P ⊆ N) (hPc : f + 1 ≤ #P) : ∃ p ∈ P, ∃ w ∈ Mid, r p ≤ r w := by
  by_cases hPM : ∃ p ∈ P, p ∈ Mid
  · obtain ⟨p, hp, hpM⟩ := hPM
    exact ⟨p, hp, p, hpM, le_rfl⟩
  · push Not at hPM
    have : ¬ P ⊆ High := by
      intro hsub; have := card_le_card hsub; rw [h.card_high] at this; omega
    obtain ⟨p, hp, hpH⟩ := not_subset.mp this
    have hpL : p ∈ Low := by
      by_contra hpL
      exact hPM p hp (h.mem_mid.mpr ⟨hP hp, hpL, hpH⟩)
    obtain ⟨w, hw⟩ := h.mid_nonempty hN
    exact ⟨p, hp, w, hw, h.low_le_mid p hpL w hw⟩

/-- Symmetric version of `exists_le_mid`. -/
theorem exists_mid_le (h : IsTrim N f r Low Mid High) (hN : 2 * f + 1 ≤ #N) {P : Finset V}
    (hP : P ⊆ N) (hPc : f + 1 ≤ #P) : ∃ p ∈ P, ∃ w ∈ Mid, r w ≤ r p := by
  by_cases hPM : ∃ p ∈ P, p ∈ Mid
  · obtain ⟨p, hp, hpM⟩ := hPM
    exact ⟨p, hp, p, hpM, le_rfl⟩
  · push Not at hPM
    have : ¬ P ⊆ Low := by
      intro hsub; have := card_le_card hsub; rw [h.card_low] at this; omega
    obtain ⟨p, hp, hpL⟩ := not_subset.mp this
    have hpH : p ∈ High := by
      by_contra hpH
      exact hPM p hp (h.mem_mid.mpr ⟨hP hp, hpL, hpH⟩)
    obtain ⟨w, hw⟩ := h.mid_nonempty hN
    exact ⟨p, hp, w, hw, h.mid_le_high w hw p hpH⟩

/-- A trimming exists (sorting with any tie-break) as soon as `2f ≤ #N`. -/
theorem «exists» (N : Finset V) (f : ℕ) (r : V → ℝ) (hN : 2 * f ≤ #N) :
    ∃ Low Mid High, IsTrim N f r Low Mid High := by
  induction f generalizing N with
  | zero =>
    exact ⟨∅, N, ∅, ⟨empty_subset _, empty_subset _, disjoint_empty_left _, by simp, rfl, rfl,
      by simp, by simp, by simp⟩⟩
  | succ f ih =>
    have hN0 : N.Nonempty := by rw [← card_pos]; omega
    obtain ⟨a, haN, ha⟩ := exists_min_image N r hN0
    have hN1 : (N.erase a).Nonempty := by
      rw [← card_pos, card_erase_of_mem haN]; omega
    obtain ⟨b, hbN, hb⟩ := exists_max_image (N.erase a) r hN1
    have hba : b ≠ a := ne_of_mem_erase hbN
    have hbN' : b ∈ N := mem_of_mem_erase hbN
    have hcard : 2 * f ≤ #((N.erase a).erase b) := by
      rw [card_erase_of_mem hbN, card_erase_of_mem haN]; omega
    obtain ⟨L, M, H, hT⟩ := ih ((N.erase a).erase b) hcard
    have hsub : ∀ x ∈ (N.erase a).erase b, x ≠ a ∧ x ≠ b ∧ x ∈ N := by
      intro x hx
      simp only [mem_erase] at hx
      exact ⟨hx.2.1, hx.1, hx.2.2⟩
    have hLa : a ∉ L := fun h => (hsub a (hT.low_sub h)).1 rfl
    have hHb : b ∉ H := fun h => (hsub b (hT.high_sub h)).2.1 rfl
    have hHa : a ∉ H := fun h => (hsub a (hT.high_sub h)).1 rfl
    have hLb : b ∉ L := fun h => (hsub b (hT.low_sub h)).2.1 rfl
    -- `a` is ≤ everything; `b` is ≥ everything except `a`
    have hbge : ∀ x ∈ (N.erase a).erase b, r x ≤ r b := fun x hx =>
      hb x (mem_erase.mpr ⟨(hsub x hx).1, (hsub x hx).2.2⟩)
    refine ⟨insert a L, M, insert b H, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact insert_subset haN (fun x hx => (hsub x (hT.low_sub hx)).2.2)
    · exact insert_subset hbN' (fun x hx => (hsub x (hT.high_sub hx)).2.2)
    · rw [disjoint_insert_left, disjoint_insert_right]
      exact ⟨by simp [hHa, hba.symm], hLb, hT.disj⟩
    · rw [hT.mid_eq]
      ext x
      simp only [mem_sdiff, mem_erase, mem_union, mem_insert]
      constructor
      · rintro ⟨⟨hxb, hxa, hxN⟩, hx⟩; tauto
      · rintro ⟨hxN, hx⟩; tauto
    · rw [card_insert_of_notMem hLa, hT.card_low]
    · rw [card_insert_of_notMem hHb, hT.card_high]
    · intro l hl m hm
      rcases mem_insert.mp hl with rfl | hl
      · exact ha m (hsub m (hT.mid_sub hm)).2.2
      · exact hT.low_le_mid l hl m hm
    · intro m hm h hh
      rcases mem_insert.mp hh with rfl | hh
      · exact hbge m (hT.mid_sub hm)
      · exact hT.mid_le_high m hm h hh
    · intro l hl h hh
      rcases mem_insert.mp hl with rfl | hl
      · rcases mem_insert.mp hh with rfl | hh
        · exact ha h hbN'
        · exact ha h (hsub h (hT.high_sub hh)).2.2
      · rcases mem_insert.mp hh with rfl | hh
        · exact hbge l (hT.low_sub hl)
        · exact hT.low_le_high l hl h hh

end IsTrim

/-- The trimmed mean: average of the own value `v` and the kept values `r j`, `j ∈ Mid`, all with
weight `1 / (#Mid + 1)`. -/
noncomputable def tmean (Mid : Finset V) (r : V → ℝ) (v : ℝ) : ℝ :=
  (v + ∑ j ∈ Mid, r j) / (#Mid + 1)

omit [DecidableEq V] in
theorem tmean_sub_eq (Mid : Finset V) (r : V → ℝ) (v ψ : ℝ) :
    tmean Mid r v - ψ = ((v - ψ) + ∑ j ∈ Mid, (r j - ψ)) / (#Mid + 1) := by
  unfold tmean
  have : (#Mid : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

omit [DecidableEq V] in
/-- If `ψ` is below the own value and all kept values, the trimmed mean exceeds `ψ` by at least
`(w - ψ)/(#Mid+1)` for each term `w` (Lemma 3 of Vaidya–Tseng–Liang). -/
theorem tmean_sub_ge (Mid : Finset V) (r : V → ℝ) (v ψ : ℝ) (hv : ψ ≤ v)
    (hr : ∀ j ∈ Mid, ψ ≤ r j) :
    (v - ψ) / (#Mid + 1) ≤ tmean Mid r v - ψ ∧
      ∀ j ∈ Mid, (r j - ψ) / (#Mid + 1) ≤ tmean Mid r v - ψ := by
  rw [tmean_sub_eq]
  have hpos : (0 : ℝ) < #Mid + 1 := by positivity
  have hs : 0 ≤ ∑ j ∈ Mid, (r j - ψ) := sum_nonneg fun j hj => by linarith [hr j hj]
  refine ⟨div_le_div_of_nonneg_right (by linarith) hpos.le, fun j hj => ?_⟩
  apply div_le_div_of_nonneg_right _ hpos.le
  have := single_le_sum (f := fun j => r j - ψ) (fun k hk => by linarith [hr k hk]) hj
  linarith

omit [DecidableEq V] in
/-- Symmetric version of `tmean_sub_ge` (Lemma 4). -/
theorem sub_tmean_ge (Mid : Finset V) (r : V → ℝ) (v Ψ : ℝ) (hv : v ≤ Ψ)
    (hr : ∀ j ∈ Mid, r j ≤ Ψ) :
    (Ψ - v) / (#Mid + 1) ≤ Ψ - tmean Mid r v ∧
      ∀ j ∈ Mid, (Ψ - r j) / (#Mid + 1) ≤ Ψ - tmean Mid r v := by
  have h := tmean_sub_eq Mid r v Ψ
  have hpos : (0 : ℝ) < #Mid + 1 := by positivity
  have hs : ∑ j ∈ Mid, (r j - Ψ) ≤ 0 := sum_nonpos fun j hj => by linarith [hr j hj]
  have e : Ψ - tmean Mid r v = ((Ψ - v) + ∑ j ∈ Mid, (Ψ - r j)) / (#Mid + 1) := by
    have : ∑ j ∈ Mid, (Ψ - r j) = -∑ j ∈ Mid, (r j - Ψ) := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring
    rw [this]
    have hne : (#Mid : ℝ) + 1 ≠ 0 := hpos.ne'
    rw [eq_div_iff hne] at h ⊢
    linarith
  rw [e]
  have hs' : 0 ≤ ∑ j ∈ Mid, (Ψ - r j) := sum_nonneg fun j hj => by linarith [hr j hj]
  refine ⟨div_le_div_of_nonneg_right (by linarith) hpos.le, fun j hj => ?_⟩
  apply div_le_div_of_nonneg_right _ hpos.le
  have := single_le_sum (f := fun j => Ψ - r j) (fun k hk => by linarith [hr k hk]) hj
  linarith

omit [DecidableEq V] in
/-- The trimmed mean lies between `lo` and `hi` if the own value and all kept values do. -/
theorem tmean_mem_Icc (Mid : Finset V) (r : V → ℝ) (v lo hi : ℝ) (hv : lo ≤ v ∧ v ≤ hi)
    (hr : ∀ j ∈ Mid, lo ≤ r j ∧ r j ≤ hi) : lo ≤ tmean Mid r v ∧ tmean Mid r v ≤ hi := by
  have h1 := (tmean_sub_ge Mid r v lo hv.1 fun j hj => (hr j hj).1).1
  have h2 := (sub_tmean_ge Mid r v hi hv.2 fun j hj => (hr j hj).2).1
  have hpos : (0 : ℝ) < #Mid + 1 := by positivity
  have := div_nonneg (sub_nonneg.mpr hv.1) hpos.le
  have := div_nonneg (sub_nonneg.mpr hv.2) hpos.le
  constructor <;> linarith

end Cslib.ApproxConsensus
