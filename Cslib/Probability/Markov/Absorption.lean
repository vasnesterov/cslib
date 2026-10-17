/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Logic.Relation

/-!
# Finite Markov chains: random-map kernels, absorption, harmonic functions, lumping

A finite Markov chain is a row-stochastic real matrix `T : Matrix S S ℝ`
(`T ∈ Matrix.rowStochastic ℝ S`); `(T ^ t) s s'` is the probability to be in `s'` after `t` steps
when starting in `s`. This file provides:

* `randomMap μ F`: the kernel "draw `ω` with probability `μ ω`, then move from `s` to `F ω s`"
  (the usual way to describe randomized dynamics / random schedulers), with `mulVec` formula,
  stochasticity and positivity of transitions;
* `pow_mulVec_of_harmonic`: harmonic functions (`T *ᵥ h = h`) are invariant under `T ^ t`;
* `exists_pow_pos_of_reflTransGen`: a chain of positive-probability steps gives a positive
  `t`-step probability;
* `tendsto_sum_compl_of_absorbing`: if a set `A` is closed and reachable from everywhere, the mass
  outside `A` tends to `0` (absorption with probability one);
* `tendsto_sum_mul_of_harmonic`: for a harmonic `h`, `∑_{s ∈ A} (T^t) c s * h s → h c`
  (optional stopping for finite absorbing chains: absorption probabilities from harmonic functions);
* `pow_mulVec_comp_of_lump`: lumping (a map `φ` intertwining two chains) is preserved by powers;
* `pow_eq_zero_of_closed`: a set closed under positive-probability steps is never left.
-/

@[expose] public section

namespace Cslib.Probability.Markov

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

section RandomMap

variable {Ω : Type*} [Fintype Ω]

/-- The kernel of a random map: draw `ω` with weight `μ ω` and move from `s` to `F ω s`. -/
noncomputable def randomMap (μ : Ω → ℝ) (F : Ω → S → S) : Matrix S S ℝ :=
  fun s s' => ∑ ω, if F ω s = s' then μ ω else 0

lemma randomMap_mulVec (μ : Ω → ℝ) (F : Ω → S → S) (h : S → ℝ) (s : S) :
    (randomMap μ F *ᵥ h) s = ∑ ω, μ ω * h (F ω s) := by
  simp only [mulVec, dotProduct, randomMap, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [ite_mul, zero_mul, Finset.sum_ite_eq]

lemma randomMap_mem_rowStochastic {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1)
    (F : Ω → S → S) : randomMap μ F ∈ rowStochastic ℝ S := by
  refine ⟨fun s s' => Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [hμ], ?_⟩
  funext s
  rw [randomMap_mulVec]
  simpa using h1

omit [Fintype S] in
lemma randomMap_pos {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (F : Ω → S → S) {ω : Ω} (hω : 0 < μ ω)
    (s : S) : 0 < randomMap μ F s (F ω s) := by
  unfold randomMap
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun ω' => if F ω' s = F ω s then μ ω' else 0)
    (fun ω' _ => by split_ifs <;> simp [hμ]) (Finset.mem_univ ω))
  simpa using hω

omit [Fintype S] in
lemma exists_of_randomMap_pos {μ : Ω → ℝ} {F : Ω → S → S} {s s' : S}
    (h : 0 < randomMap μ F s s') : ∃ ω, 0 < μ ω ∧ F ω s = s' := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  refine (lt_irrefl (0 : ℝ)) (lt_of_lt_of_le h ?_)
  refine Finset.sum_nonpos fun ω _ => ?_
  split_ifs with hω
  · by_contra hlt
    exact hne ω (lt_of_not_ge hlt) hω
  · exact le_rfl

omit [Fintype S] in
lemma randomMap_eq_zero_of_fixed {μ : Ω → ℝ} {F : Ω → S → S} {s : S} (hs : ∀ ω, F ω s = s)
    {s' : S} (hs' : s' ≠ s) : randomMap μ F s s' = 0 := by
  unfold randomMap
  refine Finset.sum_eq_zero fun ω _ => ?_
  simp [hs ω, Ne.symm hs']

end RandomMap

variable {T : Matrix S S ℝ}

lemma pow_mem_rowStochastic (hT : T ∈ rowStochastic ℝ S) (t : ℕ) :
    T ^ t ∈ rowStochastic ℝ S :=
  Submonoid.pow_mem _ hT t

lemma pow_nonneg_entry (hT : T ∈ rowStochastic ℝ S) (t : ℕ) (s s' : S) : 0 ≤ (T ^ t) s s' :=
  nonneg_of_mem_rowStochastic (pow_mem_rowStochastic hT t)

lemma pow_sum_row (hT : T ∈ rowStochastic ℝ S) (t : ℕ) (s : S) : ∑ s', (T ^ t) s s' = 1 :=
  sum_row_of_mem_rowStochastic (pow_mem_rowStochastic hT t) s

/-- Harmonic functions are invariant under all powers. -/
lemma pow_mulVec_of_harmonic {h : S → ℝ} (hh : T *ᵥ h = h) (t : ℕ) : T ^ t *ᵥ h = h := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← mulVec_mulVec, hh, ih]

/-- A chain of positive-probability steps yields a positive multi-step probability. -/
lemma exists_pow_pos_of_reflTransGen (hT : T ∈ rowStochastic ℝ S) {s s' : S}
    (h : Relation.ReflTransGen (fun a b => 0 < T a b) s s') : ∃ t, 0 < (T ^ t) s s' := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hbc ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 1, ?_⟩
    rw [pow_succ, mul_apply]
    exact lt_of_lt_of_le (mul_pos ht hbc) (Finset.single_le_sum
      (f := fun j => (T ^ t) s j * T j _)
      (fun j _ => mul_nonneg (pow_nonneg_entry hT t _ _) (nonneg_of_mem_rowStochastic hT))
      (Finset.mem_univ _))

/-- A set closed under positive-probability steps is never left. -/
lemma pow_eq_zero_of_closed (hT : T ∈ rowStochastic ℝ S) (P : S → Prop)
    (hP : ∀ a b, P a → 0 < T a b → P b) {s : S} (hs : P s) (t : ℕ) {s' : S} (hs' : ¬ P s') :
    (T ^ t) s s' = 0 := by
  induction t generalizing s' with
  | zero =>
    have : s ≠ s' := fun h => hs' (h ▸ hs)
    simp [this]
  | succ t ih =>
    rw [pow_succ, mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : P j
    · have : T j s' = 0 := by
        by_contra hne
        exact hs' (hP j s' hj (lt_of_le_of_ne (nonneg_of_mem_rowStochastic hT) (Ne.symm hne)))
      simp [this]
    · simp [ih hj]

section Absorption

variable (A : Finset S)

/-- Mass outside `A` after `t` steps. -/
private noncomputable def esc (T : Matrix S S ℝ) (t : ℕ) (s : S) : ℝ := ∑ s' ∈ Aᶜ, (T ^ t) s s'

private lemma esc_nonneg (hT : T ∈ rowStochastic ℝ S) (t : ℕ) (s : S) : 0 ≤ esc A T t s :=
  Finset.sum_nonneg fun _ _ => pow_nonneg_entry hT t _ _

private lemma esc_le_one (hT : T ∈ rowStochastic ℝ S) (t : ℕ) (s : S) : esc A T t s ≤ 1 := by
  rw [← pow_sum_row hT t s]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => pow_nonneg_entry hT t _ _

private lemma esc_eq_one_sub (hT : T ∈ rowStochastic ℝ S) (t : ℕ) (s : S) :
    esc A T t s = 1 - ∑ s' ∈ A, (T ^ t) s s' := by
  rw [← pow_sum_row hT t s, ← Finset.sum_compl_add_sum A]
  unfold esc; ring

variable {A}

private lemma esc_mul (t k : ℕ) (s : S) :
    esc A T (t + k) s = ∑ j, (T ^ t) s j * esc A T k j := by
  unfold esc
  simp_rw [pow_add, mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma esc_closed (hT : T ∈ rowStochastic ℝ S) (hclosed : ∀ a ∈ A, ∀ s ∉ A, T a s = 0)
    (t : ℕ) {a : S} (ha : a ∈ A) : esc A T t a = 0 := by
  unfold esc
  refine Finset.sum_eq_zero fun s hs => ?_
  exact pow_eq_zero_of_closed hT (· ∈ A) (fun a b ha hab => by
    by_contra hb; exact (lt_irrefl _) (hclosed a ha b hb ▸ hab)) ha t
    (by simpa using hs)

private lemma esc_mul_le (hT : T ∈ rowStochastic ℝ S) (hclosed : ∀ a ∈ A, ∀ s ∉ A, T a s = 0)
    (t k : ℕ) (s : S) {q : ℝ} (hq : ∀ j, esc A T k j ≤ q) :
    esc A T (t + k) s ≤ q * esc A T t s := by
  rw [esc_mul, ← Finset.sum_compl_add_sum A]
  have h2 : ∑ j ∈ A, (T ^ t) s j * esc A T k j = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [esc_closed hT hclosed k hj, mul_zero]
  rw [h2, add_zero]
  unfold esc
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_comm q]
  exact mul_le_mul_of_nonneg_left (hq j) (pow_nonneg_entry hT t _ _)

private lemma esc_antitone (hT : T ∈ rowStochastic ℝ S) (hclosed : ∀ a ∈ A, ∀ s ∉ A, T a s = 0)
    (s : S) : Antitone fun t => esc A T t s := by
  refine antitone_nat_of_succ_le fun t => ?_
  have := esc_mul_le hT hclosed t 1 s (q := 1) (fun j => esc_le_one A hT 1 j)
  simpa using this

/-- **Absorption.** If `A` is closed and reachable from every state by positive-probability
steps, then the probability of being outside `A` after `t` steps tends to `0`. -/
theorem tendsto_sum_compl_of_absorbing (hT : T ∈ rowStochastic ℝ S)
    (hclosed : ∀ a ∈ A, ∀ s ∉ A, T a s = 0)
    (hreach : ∀ s, ∃ a ∈ A, Relation.ReflTransGen (fun x y => 0 < T x y) s a) (c : S) :
    Tendsto (fun t => ∑ s ∈ Aᶜ, (T ^ t) c s) atTop (𝓝 0) := by
  -- for each state, some time at which the escape mass is `< 1`
  have hlt : ∀ s, ∃ t, esc A T t s < 1 := by
    intro s
    obtain ⟨a, ha, hr⟩ := hreach s
    obtain ⟨t, ht⟩ := exists_pow_pos_of_reflTransGen hT hr
    refine ⟨t, ?_⟩
    rw [esc_eq_one_sub A hT]
    have : (T ^ t) s a ≤ ∑ s' ∈ A, (T ^ t) s s' :=
      Finset.single_le_sum (f := fun s' => (T ^ t) s s') (fun _ _ => pow_nonneg_entry hT t _ _) ha
    linarith
  choose τ hτ using hlt
  set N := (Finset.univ.sup τ) + 1 with hN
  have hNs : ∀ s, esc A T N s < 1 := fun s =>
    lt_of_le_of_lt (esc_antitone hT hclosed s (by
      have := Finset.le_sup (f := τ) (Finset.mem_univ s); omega)) (hτ s)
  -- a uniform bound `q < 1`
  obtain ⟨q, hq0, hq1, hq⟩ : ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ s, esc A T N s ≤ q := by
    rcases isEmpty_or_nonempty S with hS | hS
    · exact ⟨0, le_rfl, one_pos, fun s => (hS.false s).elim⟩
    · obtain ⟨s₀, -, hs₀⟩ := Finset.exists_max_image Finset.univ (fun s => esc A T N s)
        Finset.univ_nonempty
      exact ⟨esc A T N s₀, esc_nonneg A hT N s₀, hNs s₀, fun s => hs₀ s (Finset.mem_univ s)⟩
  have hpow : ∀ k, esc A T (k * N) c ≤ q ^ k := by
    intro k
    induction k with
    | zero => simpa using esc_le_one A hT 0 c
    | succ k ih =>
      rw [Nat.succ_mul, pow_succ, mul_comm (q ^ k)]
      exact (esc_mul_le hT hclosed (k * N) N c hq).trans
        (mul_le_mul_of_nonneg_left ih hq0)
  -- conclude
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq1
  refine ⟨k * N, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero]
  change |esc A T t c| < ε
  rw [abs_of_nonneg (esc_nonneg A hT t c)]
  exact lt_of_le_of_lt ((esc_antitone hT hclosed c ht).trans (hpow k)) hk

/-- **Absorption probabilities from harmonic functions.** If `A` is closed and reachable from every
state, and `h` is harmonic, then `∑_{s ∈ A} (T^t) c s * h s → h c`. -/
theorem tendsto_sum_mul_of_harmonic (hT : T ∈ rowStochastic ℝ S)
    (hclosed : ∀ a ∈ A, ∀ s ∉ A, T a s = 0)
    (hreach : ∀ s, ∃ a ∈ A, Relation.ReflTransGen (fun x y => 0 < T x y) s a)
    {h : S → ℝ} (hh : T *ᵥ h = h) (c : S) :
    Tendsto (fun t => ∑ s ∈ A, (T ^ t) c s * h s) atTop (𝓝 (h c)) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ s, |h s| ≤ B :=
    ⟨∑ s, |h s|, fun s => Finset.single_le_sum (f := fun s => |h s|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)⟩
  have hsplit : ∀ t, ∑ s ∈ A, (T ^ t) c s * h s = h c - ∑ s ∈ Aᶜ, (T ^ t) c s * h s := by
    intro t
    have := congrFun (pow_mulVec_of_harmonic hh t) c
    simp only [mulVec, dotProduct] at this
    rw [← this, ← Finset.sum_compl_add_sum A]; ring
  simp_rw [hsplit]
  rw [show 𝓝 (h c) = 𝓝 (h c - 0) by simp]
  refine Tendsto.sub tendsto_const_nhds ?_
  have hesc := tendsto_sum_compl_of_absorbing hT hclosed hreach c
  rw [Metric.tendsto_atTop] at hesc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hesc (ε / (B + 1)) (by
    have : 0 ≤ B := (abs_nonneg _).trans (hB c)
    positivity)
  refine ⟨N, fun t ht => ?_⟩
  have h1 := hN t ht
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c)
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg_entry hT t _ _)] at h1
  calc |∑ s ∈ Aᶜ, (T ^ t) c s * h s| ≤ ∑ s ∈ Aᶜ, |(T ^ t) c s * h s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Aᶜ, (T ^ t) c s * B := Finset.sum_le_sum fun s _ => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg_entry hT t _ _)]
        exact mul_le_mul_of_nonneg_left (hB s) (pow_nonneg_entry hT t _ _)
    _ = (∑ s ∈ Aᶜ, (T ^ t) c s) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ s ∈ Aᶜ, (T ^ t) c s) * (B + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Finset.sum_nonneg fun _ _ =>
          pow_nonneg_entry hT t _ _)
    _ < ε / (B + 1) * (B + 1) := mul_lt_mul_of_pos_right h1 (by linarith)
    _ = ε := by field_simp

end Absorption

section Lumping

variable {S' : Type*} [Fintype S'] [DecidableEq S'] {T' : Matrix S' S' ℝ}

/-- **Lumping.** If `φ : S → S'` intertwines `T` and `T'` on all functions, then so it does for
all powers. -/
lemma pow_mulVec_comp_of_lump (φ : S → S')
    (hφ : ∀ g : S' → ℝ, ∀ s, (T' *ᵥ g) (φ s) = (T *ᵥ (g ∘ φ)) s) (t : ℕ) (g : S' → ℝ) (s : S) :
    (T' ^ t *ᵥ g) (φ s) = (T ^ t *ᵥ (g ∘ φ)) s := by
  induction t generalizing g with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, pow_succ, ← mulVec_mulVec]
    congr 1
    funext s
    exact hφ g s

/-- Random maps that commute with `φ` are lumpable along `φ`. -/
lemma randomMap_lump {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (F : Ω → S → S) (F' : Ω → S' → S')
    (φ : S → S') (hF : ∀ ω s, φ (F ω s) = F' ω (φ s)) (g : S' → ℝ) (s : S) :
    (randomMap μ F' *ᵥ g) (φ s) = (randomMap μ F *ᵥ (g ∘ φ)) s := by
  simp only [randomMap_mulVec, Function.comp, hF]

/-- `t`-step probability as `mulVec` with an indicator. -/
lemma pow_apply_eq_mulVec (M : Matrix S S ℝ) (s s' : S) :
    M s s' = (M *ᵥ fun x => if x = s' then 1 else 0) s := by
  simp [mulVec, dotProduct]

end Lumping

end Cslib.Probability.Markov
