/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Chains of intersecting sets and diameters; growth-rate lemmas

The common core of the valency lower bounds of Függer–Nowak–Schwarz (PODC 2018) in the
Heard-Of model (`Cslib.HeardOf`) and of bivalency/chain arguments in general:

* `edist_le_sum_chain`: along a chain `Y 0, …, Y q` of consecutively intersecting sets, any
  `x ∈ Y 0` and `y ∈ Y q` satisfy `edist x y ≤ ∑ r ≤ q, diam (Y r)`.
* `exists_ediam_le_mul`: if `Z ⊆ ⋃_{i ∈ K} Y i` (`K` finite) and any two indices are connected by
  a chain of length `≤ D` of consecutively intersecting `Y`s, then some `Y i` has
  `diam Z ≤ (D + 1) · diam (Y i)`.
* `exists_seq_of_step`: greedy infinite sequences from a one-step choice.
* `le_limsup_rpow_inv`, `limsup_rpow_inv_le`: `t`-th root growth rates (contraction rates).

## References

* [M. Függer, T. Nowak, M. Schwarz, *Tight Bounds for Asymptotic and Approximate
  Consensus*][FuggerNowakSchwarz2018]
-/

@[expose] public section

namespace Cslib.HeardOf.Chain

open Finset Filter Topology
open scoped ENNReal

variable {V ι : Type*} [PseudoEMetricSpace V]

/-- Along a chain of consecutively intersecting sets the distance between a point of the first and
a point of the last set is at most the sum of the diameters. -/
theorem edist_le_sum_chain (Y : ℕ → Set V) :
    ∀ (q : ℕ), (∀ r < q, (Y r ∩ Y (r + 1)).Nonempty) → ∀ x ∈ Y 0, ∀ y ∈ Y q,
      edist x y ≤ ∑ r ∈ range (q + 1), Metric.ediam (Y r) := by
  intro q
  induction q with
  | zero =>
    intro _ x hx y hy
    simpa using Metric.edist_le_ediam_of_mem hx hy
  | succ q ih =>
    intro hY x hx y hy
    obtain ⟨z, hz1, hz2⟩ := hY q (by omega)
    calc edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
      _ ≤ (∑ r ∈ range (q + 1), Metric.ediam (Y r)) + Metric.ediam (Y (q + 1)) :=
          add_le_add (ih (fun r hr => hY r (by omega)) x hx z hz1)
            (Metric.edist_le_ediam_of_mem hz2 hy)
      _ = ∑ r ∈ range (q + 1 + 1), Metric.ediam (Y r) := (sum_range_succ _ _).symm

/-- `ChainLE K Y D a b`: `a` and `b` are joined by a chain of at most `D` steps inside `K` whose
consecutive sets `Y (c r)`, `Y (c (r+1))` intersect. -/
def ChainLE (K : Finset ι) (Y : ι → Set V) (D : ℕ) (a b : ι) : Prop :=
  ∃ q ≤ D, ∃ c : ℕ → ι, c 0 = a ∧ c q = b ∧ (∀ r ≤ q, c r ∈ K) ∧
    ∀ r < q, (Y (c r) ∩ Y (c (r + 1))).Nonempty

omit [PseudoEMetricSpace V] in
theorem chainLE_of_inter {K : Finset ι} {Y : ι → Set V} {D : ℕ} (hD : 1 ≤ D) {a b : ι}
    (ha : a ∈ K) (hb : b ∈ K) (h : (Y a ∩ Y b).Nonempty) : ChainLE K Y D a b := by
  refine ⟨1, hD, fun r => if r = 0 then a else b, by simp, by simp, ?_, ?_⟩
  · intro r hr; dsimp only; split_ifs <;> assumption
  · intro r hr
    obtain rfl : r = 0 := by omega
    simpa using h

omit [PseudoEMetricSpace V] in
theorem chainLE_refl {K : Finset ι} {Y : ι → Set V} {D : ℕ} {a : ι} (ha : a ∈ K) :
    ChainLE K Y D a a :=
  ⟨0, Nat.zero_le _, fun _ => a, rfl, rfl, fun _ _ => ha, fun r hr => absurd hr (by omega)⟩

omit [PseudoEMetricSpace V] in
theorem chainLE_two {K : Finset ι} {Y : ι → Set V} {D : ℕ} (hD : 2 ≤ D) {a b c : ι}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hab : (Y a ∩ Y b).Nonempty)
    (hbc : (Y b ∩ Y c).Nonempty) : ChainLE K Y D a c := by
  refine ⟨2, hD, fun r => if r = 0 then a else if r = 1 then b else c, by simp, by simp, ?_, ?_⟩
  · intro r hr; dsimp only; split_ifs <;> assumption
  · intro r hr
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · simpa using hab
    · simpa using hbc

/-- **Chain lemma.** If `Z` is covered by the finitely many sets `Y i`, `i ∈ K`, and any two
indices are connected by a chain of length at most `D` of consecutively intersecting sets, then
some `Y i` has at least a `1/(D+1)` fraction of the diameter of `Z`. -/
theorem exists_ediam_le_mul (K : Finset ι) (hK : K.Nonempty) (Y : ι → Set V) (Z : Set V)
    (hZ : Z ⊆ ⋃ i ∈ K, Y i) (D : ℕ) (hc : ∀ a ∈ K, ∀ b ∈ K, ChainLE K Y D a b) :
    ∃ i ∈ K, Metric.ediam Z ≤ (D + 1) * Metric.ediam (Y i) := by
  obtain ⟨i, hi, hmax⟩ := K.exists_max_image (fun i => Metric.ediam (Y i)) hK
  refine ⟨i, hi, Metric.ediam_le fun x hx y hy => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hZ hx)
  obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.1 (hZ hy)
  obtain ⟨q, hq, c, hc0, hcq, hcK, hcY⟩ := hc a ha b hb
  have h1 := edist_le_sum_chain (fun r => Y (c r)) q hcY x (by simpa [hc0] using hxa) y
    (by simpa [hcq] using hyb)
  calc edist x y ≤ ∑ r ∈ range (q + 1), Metric.ediam (Y (c r)) := h1
    _ ≤ ∑ _r ∈ range (q + 1), Metric.ediam (Y i) :=
        sum_le_sum fun r hr => hmax _ (hcK r (by simpa [Nat.lt_succ_iff] using hr))
    _ = (q + 1) * Metric.ediam (Y i) := by simp
    _ ≤ (D + 1) * Metric.ediam (Y i) := by gcongr

/-- Pairwise intersecting version (`D = 1`): some set has half the diameter. -/
theorem exists_ediam_le_two_mul (K : Finset ι) (hK : K.Nonempty) (Y : ι → Set V) (Z : Set V)
    (hZ : Z ⊆ ⋃ i ∈ K, Y i) (hc : ∀ a ∈ K, ∀ b ∈ K, (Y a ∩ Y b).Nonempty) :
    ∃ i ∈ K, Metric.ediam Z ≤ 2 * Metric.ediam (Y i) := by
  have := exists_ediam_le_mul K hK Y Z hZ 1 fun a ha b hb =>
    chainLE_of_inter le_rfl ha hb (hc a ha b hb)
  simpa [one_add_one_eq_two] using this

/-- **Lemma 5 of Függer–Nowak–Schwarz** (abstract form): the diameter of a finite union is
attained by the union of two of the sets. -/
theorem exists_ediam_eq_union (K : Finset ι) (hK : K.Nonempty) (Y : ι → Set V) :
    ∃ a ∈ K, ∃ b ∈ K, Metric.ediam (⋃ i ∈ K, Y i) = Metric.ediam (Y a ∪ Y b) := by
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := (K ×ˢ K).exists_max_image
    (fun p => Metric.ediam (Y p.1 ∪ Y p.2)) (hK.product hK)
  rw [mem_product] at hab
  refine ⟨a, hab.1, b, hab.2, le_antisymm (Metric.ediam_le fun x hx y hy => ?_)
    (Metric.ediam_mono (Set.union_subset (Set.subset_biUnion_of_mem (u := Y) hab.1)
      (Set.subset_biUnion_of_mem (u := Y) hab.2)))⟩
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨d, hd, hyd⟩ := Set.mem_iUnion₂.1 hy
  exact (Metric.edist_le_ediam_of_mem (Set.mem_union_left _ hxc) (Set.mem_union_right _ hyd)).trans
    (hmax (c, d) (mem_product.2 ⟨hc, hd⟩))

/-- Greedy sequences: if from every state satisfying `Inv` some admissible move keeps `Inv` and
loses at most a factor `c` of the potential `δ`, there is an infinite admissible sequence of moves
along which `δ C₀ ≤ c ^ t * δ C_t`. -/
theorem exists_seq_of_step {Γ M : Type*} (mv : M → Γ → Γ) (adm : Set M) (Inv : Γ → Prop)
    (δ : Γ → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, Inv C → ∃ m ∈ adm, Inv (mv m C) ∧ δ C ≤ c * δ (mv m C))
    (C₀ : Γ) (h₀ : Inv C₀) :
    ∃ (s : ℕ → M) (Cs : ℕ → Γ), Cs 0 = C₀ ∧ (∀ t, s t ∈ adm) ∧
      (∀ t, Cs (t + 1) = mv (s t) (Cs t)) ∧ ∀ t, Inv (Cs t) ∧ δ C₀ ≤ c ^ t * δ (Cs t) := by
  classical
  let choose' : {C // Inv C} → M := fun C => (h C.1 C.2).choose
  have hch : ∀ C : {C // Inv C}, choose' C ∈ adm ∧ Inv (mv (choose' C) C.1) ∧
      δ C.1 ≤ c * δ (mv (choose' C) C.1) := fun C => (h C.1 C.2).choose_spec
  let f : {C // Inv C} → {C // Inv C} := fun C => ⟨mv (choose' C) C.1, (hch C).2.1⟩
  let seq : ℕ → {C // Inv C} := fun t => f^[t] ⟨C₀, h₀⟩
  refine ⟨fun t => choose' (seq t), fun t => (seq t).1, rfl, fun t => (hch _).1, ?_, ?_⟩
  · intro t; simp only [seq, Function.iterate_succ_apply']; rfl
  · intro t
    refine ⟨(seq t).2, ?_⟩
    induction t with
    | zero => simp [seq]
    | succ t ih =>
      have hs : (seq (t + 1)).1 = mv (choose' (seq t)) (seq t).1 := by
        simp only [seq, Function.iterate_succ_apply']; rfl
      calc δ C₀ ≤ c ^ t * δ (seq t).1 := ih
        _ ≤ c ^ t * (c * δ (seq (t + 1)).1) := by rw [hs]; gcongr; exact (hch _).2.2
        _ = c ^ (t + 1) * δ (seq (t + 1)).1 := by rw [pow_succ, mul_assoc]

theorem tendsto_rpow_inv_natCast {a : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ∞) :
    Tendsto (fun t : ℕ => a ^ ((t : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hpos : 0 < a.toReal := ENNReal.toReal_pos ha ha'
  have h1 : Tendsto (fun t : ℕ => ((t : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun t : ℕ => a.toReal ^ ((t : ℝ)⁻¹)) atTop (𝓝 (a.toReal ^ (0 : ℝ))) :=
    ((Real.continuousAt_const_rpow hpos.ne').tendsto).comp h1
  rw [Real.rpow_zero] at h2
  have h3 := (ENNReal.continuous_ofReal.tendsto 1).comp h2
  rw [ENNReal.ofReal_one] at h3
  refine h3.congr fun t => ?_
  simp only [Function.comp]
  rw [← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal ha']

/-- Lower bound on a `t`-th root growth rate: if `a · r^t ≤ f t` with `0 < a < ∞`, then
`r ≤ limsup (f t)^(1/t)`. -/
theorem le_limsup_rpow_inv {f : ℕ → ℝ≥0∞} {a r : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ∞)
    (h : ∀ t, a * r ^ t ≤ f t) : r ≤ limsup (fun t : ℕ => f t ^ ((t : ℝ)⁻¹)) atTop := by
  have hlim : Tendsto (fun t : ℕ => a ^ ((t : ℝ)⁻¹) * r) atTop (𝓝 r) := by
    simpa using ENNReal.Tendsto.mul_const (tendsto_rpow_inv_natCast ha ha') (Or.inl one_ne_zero)
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : t ≠ 0 := by omega
  calc a ^ ((t : ℝ)⁻¹) * r = (a * r ^ t) ^ ((t : ℝ)⁻¹) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.pow_rpow_inv_natCast ht0]
    _ ≤ f t ^ ((t : ℝ)⁻¹) := ENNReal.rpow_le_rpow (h t) (by positivity)

/-- Upper bound on a `t`-th root growth rate: if `f t ≤ a · r^t` with `a < ∞`, then
`limsup (f t)^(1/t) ≤ r`. -/
theorem limsup_rpow_inv_le {f : ℕ → ℝ≥0∞} {a r : ℝ≥0∞} (ha' : a ≠ ∞)
    (h : ∀ t, f t ≤ a * r ^ t) : limsup (fun t : ℕ => f t ^ ((t : ℝ)⁻¹)) atTop ≤ r := by
  rcases eq_or_ne a 0 with rfl | ha
  · have : ∀ t, f t = 0 := fun t => le_antisymm (by simpa using h t) bot_le
    calc limsup (fun t : ℕ => f t ^ ((t : ℝ)⁻¹)) atTop
        ≤ limsup (fun _ : ℕ => (0 : ℝ≥0∞)) atTop := by
          refine limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop 1] with t ht
          rw [this t, ENNReal.zero_rpow_of_pos (by positivity)]
      _ ≤ r := by simp
  have hlim : Tendsto (fun t : ℕ => a ^ ((t : ℝ)⁻¹) * r) atTop (𝓝 r) := by
    simpa using ENNReal.Tendsto.mul_const (tendsto_rpow_inv_natCast ha ha') (Or.inl one_ne_zero)
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : t ≠ 0 := by omega
  calc f t ^ ((t : ℝ)⁻¹) ≤ (a * r ^ t) ^ ((t : ℝ)⁻¹) := ENNReal.rpow_le_rpow (h t) (by positivity)
    _ = a ^ ((t : ℝ)⁻¹) * r := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.pow_rpow_inv_natCast ht0]

end Cslib.HeardOf.Chain
