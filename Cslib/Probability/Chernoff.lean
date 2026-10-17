/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A multiplicative Chernoff lower tail for independent events

`Cslib.Probability.measureReal_card_filter_le_le`: under a product of probability measures
`Measure.pi μ`, let `A i` be events on the coordinates and `p i = μ i (A i)`. The number of
`i ∈ s` whose event occurs is at most `K` with probability at most
`2^K · exp(-(∑_{i ∈ s} p i) / 2)`.

The proof is Markov's inequality for `2^{-X}` together with the product formula
`E[2^{-X}] = ∏ (1 - p i / 2) ≤ exp(-∑ p i / 2)`. Mathlib has the general exponential-moment bound
(`ProbabilityTheory.measure_le_le_exp_mul_mgf`), but not this ready-to-use corollary for counts of
independent events.
-/

@[expose] public section

open Finset MeasureTheory

namespace Cslib.Probability

/-- **Multiplicative Chernoff lower tail** for independent events: under `Measure.pi μ`, the number
of `i ∈ s` with `ω i ∈ A i` (a sum of independent Bernoulli(`μ i (A i)`) variables) is at most `K`
with probability at most `2^K · exp(-(∑_{i ∈ s} μ i (A i)) / 2)`. -/
theorem measureReal_card_filter_le_le {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {A : ∀ i, Set (Ω i)} [∀ i, DecidablePred (· ∈ A i)] (hA : ∀ i, MeasurableSet (A i))
    (s : Finset ι) (K : ℕ) :
    (Measure.pi μ).real {ω | #(s.filter fun i => ω i ∈ A i) ≤ K} ≤
      2 ^ K * Real.exp (-(∑ i ∈ s, (μ i).real (A i)) / 2) := by
  classical
  set g : ∀ i, Ω i → ℝ := fun z t => if z ∈ s then (if t ∈ A z then 1 / 2 else 1) else 1 with hg
  set F : (∀ i, Ω i) → ℝ := fun T => ∏ z, g z (T z) with hFdef
  have hF : ∀ T, F T = (1 / 2 : ℝ) ^ #(s.filter fun z => T z ∈ A z) := by
    intro T
    simp only [hFdef, hg]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  have hgm : ∀ z, Measurable (g z) := by
    intro z
    simp only [hg]
    split_ifs
    · exact Measurable.ite (hA z) measurable_const measurable_const
    · exact measurable_const
  have hFm : Measurable F :=
    Finset.measurable_prod _ fun z _ => (hgm z).comp (measurable_pi_apply z)
  have hF0 : ∀ T, 0 ≤ F T := fun T => by rw [hF]; positivity
  have hF1 : ∀ T, F T ≤ 1 := fun T => by rw [hF]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hFi : Integrable F (Measure.pi μ) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun T => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 T)]; exact hF1 T)
  have hgz : ∀ z ∈ s, ∫ t, g z t ∂(μ z) = 1 - (μ z).real (A z) / 2 := by
    intro z hz
    have : g z = fun t => 1 - (1 / 2 : ℝ) * (A z).indicator 1 t := by
      funext t
      simp only [hg, hz, ite_true, Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num
    rw [this, integral_sub (integrable_const _) ((integrable_const _).indicator (hA z)
      |>.const_mul _), integral_const, integral_const_mul, integral_indicator_one (hA z)]
    simp; ring
  have hint : ∫ T, F T ∂(Measure.pi μ) ≤ Real.exp (-(∑ z ∈ s, (μ z).real (A z)) / 2) := by
    simp only [hFdef]
    rw [integral_fintype_prod_eq_prod g]
    have : ∀ z, ∫ t, g z t ∂(μ z) = if z ∈ s then 1 - (μ z).real (A z) / 2 else 1 := by
      intro z
      split_ifs with hz
      · exact hgz z hz
      · simp [hg, hz]
    simp_rw [this]
    rw [Finset.prod_ite_mem, Finset.univ_inter, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib,
      Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun z _ => by linarith [measureReal_le_one (μ := μ z) (s := A z)])
      fun z _ => ?_
    have := Real.add_one_le_exp (-((μ z).real (A z) / 2))
    linarith
  have hsub : {T : ∀ i, Ω i | #(s.filter fun z => T z ∈ A z) ≤ K} ⊆
      {T | (1 / 2 : ℝ) ^ K ≤ F T} := by
    intro T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    rw [hF]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hT
  have hmk := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hF0) hFi
    ((1 / 2 : ℝ) ^ K)
  calc (Measure.pi μ).real {T | #(s.filter fun z => T z ∈ A z) ≤ K}
      ≤ (Measure.pi μ).real {T | (1 / 2 : ℝ) ^ K ≤ F T} := measureReal_mono hsub
    _ = 2 ^ K * ((1 / 2 : ℝ) ^ K * (Measure.pi μ).real {T | (1 / 2 : ℝ) ^ K ≤ F T}) := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ 2 ^ K * Real.exp (-(∑ z ∈ s, (μ z).real (A z)) / 2) := by gcongr; exact hmk.trans hint

end Cslib.Probability
