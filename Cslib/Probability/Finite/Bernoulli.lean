/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Probability.Finite.Product
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent Bernoulli coins and random subsets

Every element `u` of a finite type `ι` flips an independent coin that comes up `true` with
probability `p`. An outcome is a coin vector `c : ι → Bool`, or equivalently the random subset
`S = {u | c u}`. Probabilities and expectations are explicit finite sums; no measure theory is
needed (`coinProb_eq_measure_pi` is the bridge to `MeasureTheory.Measure.pi` of
`PMF.bernoulli`).

## Main definitions

* `Cslib.Probability.coinProb p c = ∏ u, (if c u then p else 1 - p)`: the probability of the coin
  vector `c`; `coinExpect p g = ∑ c, coinProb p c * g c` (a special case of `piExpect`).
* `Cslib.Probability.bernWeight p S = p ^ |S| (1 - p) ^ (|ι| - |S|)`: the probability of the
  random subset `S` (`bernWeight_eq_coinProb`, `sum_bernWeight_mul_eq_coinExpect`).

## Main statements

* `sum_coinProb`, `coinExpect_prod` (independence), linearity and monotonicity of `coinExpect`;
* `coinExpect_forall_eq_true_and_forall_eq_false` (`Pr[all of In true, all of Out false] =
  p^|In| (1-p)^|Out|`), `coinExpect_forall_eq_false`, `coinExpect_coin` (`Pr[c u] = p`);
* `sum_bernWeight_indicator` (`Pr[In ⊆ S ∧ S ∩ Out = ∅] = p^|In| (1-p)^|Out|` for disjoint
  `In`, `Out`), `sum_bernWeight`, `sum_bernWeight_mul_card` (`E|S| = p |ι|`).
-/

@[expose] public section

open Finset

namespace Cslib.Probability

variable {ι : Type*} [Fintype ι]

/-! ### Coin vectors -/

/-- Probability of the coin vector `c` when every element independently flips a `p`-coin. -/
noncomputable def coinProb (p : ℝ) (c : ι → Bool) : ℝ := ∏ u, if c u then p else 1 - p

/-- Expectation of `g` over one coin vector in which every coin is `true` with probability `p`. -/
noncomputable def coinExpect [DecidableEq ι] (p : ℝ) (g : (ι → Bool) → ℝ) : ℝ :=
  ∑ c, coinProb p c * g c

/-- Coin-vector probabilities are nonnegative for `0 ≤ p ≤ 1`. -/
theorem coinProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : ι → Bool) :
    0 ≤ coinProb p c :=
  prod_nonneg fun u _ => by split_ifs <;> linarith

/-- With `p = 1`, only the all-`true` coin vector has positive weight. -/
theorem coinProb_one_ne_zero {c : ι → Bool} (hc : coinProb 1 c ≠ 0) (u : ι) : c u = true := by
  by_contra h
  exact hc (prod_eq_zero (mem_univ u) (by simp [h]))

variable [DecidableEq ι]

/-- `coinExpect` is the expectation under the product of `Bernoulli(p)` weights. -/
theorem coinExpect_eq_piExpect (p : ℝ) (g : (ι → Bool) → ℝ) :
    coinExpect p g = piExpect (fun (_ : ι) (b : Bool) => if b then p else 1 - p) g := rfl

/-- **Independence.** `E[∏ u, g u (c u)] = ∏ u, (p g u true + (1 - p) g u false)`. -/
theorem coinExpect_prod (p : ℝ) (g : ι → Bool → ℝ) :
    coinExpect p (fun c => ∏ u, g u (c u)) = ∏ u, (p * g u true + (1 - p) * g u false) := by
  rw [coinExpect_eq_piExpect, piExpect_prod]
  simp

/-- The probabilities of all coin vectors sum to `1`. -/
theorem sum_coinProb (p : ℝ) : ∑ c : ι → Bool, coinProb p c = 1 := by
  simpa [coinExpect] using coinExpect_prod (ι := ι) p (fun _ _ => 1)

/-- The expectation of a constant is the constant. -/
theorem coinExpect_const (p a : ℝ) : coinExpect (ι := ι) p (fun _ => a) = a := by
  rw [coinExpect, ← sum_mul, sum_coinProb, one_mul]

/-- Linearity of `coinExpect`: additivity. -/
theorem coinExpect_add (p : ℝ) (g h : (ι → Bool) → ℝ) :
    coinExpect p (fun c => g c + h c) = coinExpect p g + coinExpect p h :=
  piExpect_add (fun (_ : ι) (b : Bool) => if b then p else 1 - p) g h

/-- Linearity of `coinExpect`: scalar multiples. -/
theorem coinExpect_mul_left (p a : ℝ) (g : (ι → Bool) → ℝ) :
    coinExpect p (fun c => a * g c) = a * coinExpect p g :=
  piExpect_mul_left (fun (_ : ι) (b : Bool) => if b then p else 1 - p) a g

/-- Linearity of `coinExpect`: finite sums. -/
theorem coinExpect_sum {κ : Type*} (p : ℝ) (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    coinExpect p (fun c => ∑ k ∈ s, g k c) = ∑ k ∈ s, coinExpect p (g k) :=
  piExpect_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p) s g

/-- Monotonicity of `coinExpect` for `0 ≤ p ≤ 1`. -/
theorem coinExpect_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g h : (ι → Bool) → ℝ}
    (hgh : ∀ c, g c ≤ h c) : coinExpect p g ≤ coinExpect p h :=
  piExpect_mono (μ := fun (_ : ι) (b : Bool) => if b then p else 1 - p)
    (fun _ b => by cases b <;> simp <;> linarith) hgh

/-- Only coin vectors of nonzero probability matter. -/
theorem coinExpect_congr {p : ℝ} {g h : (ι → Bool) → ℝ}
    (hgh : ∀ c, coinProb p c ≠ 0 → g c = h c) : coinExpect p g = coinExpect p h :=
  piExpect_congr (μ := fun (_ : ι) (b : Bool) => if b then p else 1 - p) hgh

/-- `Pr[c u = true for all u ∈ In and c u = false for all u ∈ Out] = p ^ |In| (1 - p) ^ |Out|`
for disjoint `In`, `Out`. -/
theorem coinExpect_forall_eq_true_and_forall_eq_false (p : ℝ) {In Out : Finset ι}
    (h : Disjoint In Out) :
    coinExpect p (fun c => if (∀ u ∈ In, c u = true) ∧ ∀ u ∈ Out, c u = false then 1 else 0) =
      p ^ #In * (1 - p) ^ #Out := by
  set g : ι → Bool → ℝ := fun u b =>
    if u ∈ In then (if b then 1 else 0) else if u ∈ Out then (if b then 0 else 1) else 1 with hg
  have hind : (fun c : ι → Bool =>
      if (∀ u ∈ In, c u = true) ∧ ∀ u ∈ Out, c u = false then (1 : ℝ) else 0) =
      fun c => ∏ u, g u (c u) := by
    ext c
    by_cases hc : (∀ u ∈ In, c u = true) ∧ ∀ u ∈ Out, c u = false
    · rw [ite_eq_left hc]
      refine (prod_eq_one fun u _ => ?_).symm
      by_cases hi : u ∈ In
      · simp [hg, hi, hc.1 u hi]
      · by_cases ho : u ∈ Out <;> simp [hg, hi, ho, hc.2 u]
    · rw [ite_eq_right hc]
      refine (prod_eq_zero_iff.2 ?_).symm
      rw [not_and_or] at hc
      rcases hc with hc | hc
      · push Not at hc
        obtain ⟨u, hu, hcu⟩ := hc
        exact ⟨u, mem_univ _, by simp [hg, hu, hcu]⟩
      · push Not at hc
        obtain ⟨u, hu, hcu⟩ := hc
        have hi : u ∉ In := fun hi => disjoint_left.1 h hi hu
        exact ⟨u, mem_univ _, by simp [hg, hi, hu, hcu]⟩
  rw [hind, coinExpect_prod]
  have hfac : ∀ u, p * g u true + (1 - p) * g u false =
      (if u ∈ In then p else 1) * (if u ∈ Out then 1 - p else 1) := by
    intro u
    by_cases hi : u ∈ In
    · have ho : u ∉ Out := disjoint_left.1 h hi
      simp [hg, hi, ho]
    · by_cases ho : u ∈ Out <;> simp [hg, hi, ho]
  simp_rw [hfac, prod_mul_distrib, prod_ite_mem, univ_inter, prod_const]

/-- `Pr[c u = false for all u ∈ A] = (1 - p) ^ |A|`. -/
theorem coinExpect_forall_eq_false (p : ℝ) (A : Finset ι) :
    coinExpect p (fun c => if ∀ u ∈ A, c u = false then 1 else 0) = (1 - p) ^ #A := by
  simpa using coinExpect_forall_eq_true_and_forall_eq_false p (disjoint_empty_left A)

/-- `Pr[c u = true] = p`. -/
theorem coinExpect_coin (p : ℝ) (u : ι) :
    coinExpect p (fun c => if c u = true then 1 else 0) = p := by
  simpa using coinExpect_forall_eq_true_and_forall_eq_false p (disjoint_empty_right {u})

omit [DecidableEq ι] in
/-- Bridge to measure theory: `coinProb p c` is the probability of `{c}` under the product of
`Bernoulli(p)` measures `Ber(true, false, p)`. -/
theorem coinProb_eq_measure_pi (p : unitInterval) (c : ι → Bool) :
    coinProb (p : ℝ) c = (MeasureTheory.Measure.pi fun _ : ι =>
      ProbabilityTheory.bernoulliMeasure true false p).real {c} := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.pi_singleton, ENNReal.toReal_prod,
    coinProb]
  refine prod_congr rfl fun u _ => ?_
  cases c u <;> simp

/-! ### Random subsets -/

omit [DecidableEq ι] in
/-- The probability of the set `S` when each element of `ι` is included independently with
probability `p`. -/
def bernWeight (p : ℝ) (S : Finset ι) : ℝ := p ^ #S * (1 - p) ^ (Fintype.card ι - #S)

/-- The random subset is the set of `true` coins. -/
theorem bernWeight_eq_coinProb (p : ℝ) (S : Finset ι) :
    bernWeight p S = coinProb p (fun u => decide (u ∈ S)) := by
  rw [bernWeight, coinProb, prod_ite (p := fun u => decide (u ∈ S) = true)]
  simp only [decide_eq_true_eq, prod_const, filter_mem_eq_inter, univ_inter]
  congr
  rw [filter_not, card_sdiff_of_subset (by simp)]
  simp [card_univ]

omit [DecidableEq ι] in
/-- Subset weights are nonnegative for `0 ≤ p ≤ 1`. -/
theorem bernWeight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset ι) :
    0 ≤ bernWeight p S :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

/-- Expectations over the random subset are expectations over the coin vector of its
indicator. -/
theorem sum_bernWeight_mul_eq_coinExpect (p : ℝ) (X : Finset ι → ℝ) :
    ∑ S ∈ univ.powerset, bernWeight p S * X S =
      coinExpect p (fun c => X (univ.filter fun u => c u = true)) := by
  rw [coinExpect]
  refine sum_nbij' (fun S u => decide (u ∈ S)) (fun c => univ.filter fun u => c u = true)
    (by simp) (by simp) (fun S _ => by ext; simp) (fun c _ => by ext; simp) (fun S _ => ?_)
  rw [bernWeight_eq_coinProb]
  congr 2
  ext; simp

/-- `Pr[In ⊆ S ∧ S ∩ Out = ∅] = p ^ |In| * (1 - p) ^ |Out|` for disjoint `In`, `Out`. -/
theorem sum_bernWeight_indicator (p : ℝ) (In Out : Finset ι) (h : Disjoint In Out) :
    ∑ S ∈ univ.powerset, bernWeight p S * (if In ⊆ S ∧ Disjoint S Out then 1 else 0) =
      p ^ #In * (1 - p) ^ #Out := by
  rw [sum_bernWeight_mul_eq_coinExpect, ← coinExpect_forall_eq_true_and_forall_eq_false p h]
  congr 1
  ext c
  congr 1
  simp only [subset_iff, mem_filter, mem_univ, true_and, disjoint_left]
  refine propext (and_congr Iff.rfl ⟨fun h' u hu => ?_, fun h' u hcu hu => ?_⟩)
  · by_contra hc
    exact h' (by simpa using hc) hu
  · simp [h' u hu] at hcu

omit [DecidableEq ι] in
/-- The weights of all subsets sum to `1`. -/
theorem sum_bernWeight (p : ℝ) : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S = 1 := by
  simpa [bernWeight] using Finset.sum_pow_mul_eq_add_pow p (1 - p) (univ : Finset ι)

omit [DecidableEq ι] in
/-- The expected size of the random subset is `p |ι|`. -/
theorem sum_bernWeight_mul_card (p : ℝ) :
    ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * (#S : ℝ) = Fintype.card ι * p := by
  classical
  have : ∀ S : Finset ι, (#S : ℝ) = ∑ i, if {i} ⊆ S ∧ Disjoint S ∅ then 1 else 0 := by
    intro S; simp
  simp_rw [this, mul_sum]
  rw [sum_comm]
  simp_rw [sum_bernWeight_indicator p {_} ∅ (disjoint_empty_right _)]
  simp

end Cslib.Probability
