/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Rounding with a common multiplier ("stationary divisor methods")

Given non-negative weights `w : ι → ℝ` and an offset `c ∈ [0, 1]`, we consider integer vectors `t`
that round `s • w` "with offset `c`" for some multiplier `s ≥ 0`:

  `w i * s + c - 1 ≤ t i ≤ w i * s + c`  for all `i`.

Equivalently `t i = ⌊w i * s + c⌋`, except that `t i` may be one less when `w i * s + c` is an
integer (a *tie*). For `c = 1/2` this is the Webster/Sainte-Laguë method of apportionment, for
`c = 1` Jefferson/D'Hondt, for `c = 0` Adams; the ticket assignments of Swiper
(Tonkikh–Freitas, PODC 2024) are the case `c = αw`.

## Main results

* `Cslib.Apportionment.Rounds`: the predicate above.
* `Cslib.Apportionment.exists_rounds_sum_eq`: if some weight is positive, then **every** total
  `m : ℕ` is attained by such a rounding (every house size is attainable when ties are broken
  arbitrarily).
* `Cslib.Apportionment.rounds_floor`: the plain floor `⌊w i * s + c⌋₊` is such a rounding.
-/

@[expose] public section

namespace Cslib.Apportionment

open Finset

variable {ι : Type*}

/-- `t` rounds `w * s` with offset `c`: `w i * s + c - 1 ≤ t i ≤ w i * s + c` for all `i`. -/
def Rounds (w : ι → ℝ) (c s : ℝ) (t : ι → ℕ) : Prop :=
  ∀ i, w i * s + c - 1 ≤ (t i : ℝ) ∧ (t i : ℝ) ≤ w i * s + c

/-- The plain floor rounding `t i = ⌊w i * s + c⌋₊` is a rounding (when the arguments are `≥ 0`). -/
theorem rounds_floor {w : ι → ℝ} {c s : ℝ} (h : ∀ i, 0 ≤ w i * s + c) :
    Rounds w c s (fun i => ⌊w i * s + c⌋₊) := fun i =>
  ⟨by have := Nat.lt_floor_add_one (w i * s + c); linarith, Nat.floor_le (h i)⟩

/-- With offset `c ≤ 1`, a value strictly below `1` is rounded to `0` (key for `s = 0`). -/
theorem Rounds.eq_zero_of_lt {w : ι → ℝ} {c s : ℝ} {t : ι → ℕ} (ht : Rounds w c s t) {i : ι}
    (hi : w i * s + c < 1) : t i = 0 := by
  have := (ht i).2
  have : (t i : ℝ) < 1 := by linarith
  exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)

/-- One step of the "chain": from any rounding we can move to a (weakly) larger multiplier at which
the same vector is still a rounding and some coordinate can be increased by one. -/
theorem Rounds.exists_step [Finite ι] {w : ι → ℝ} {c s : ℝ} {t : ι → ℕ}
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (ht : Rounds w c s t) :
    ∃ s', s ≤ s' ∧ Rounds w c s' t ∧ ∃ j, (t j : ℝ) + 1 ≤ w j * s' + c := by
  classical
  have := Fintype.ofFinite ι
  by_cases h : ∃ j, (t j : ℝ) + 1 ≤ w j * s + c
  · exact ⟨s, le_rfl, ht, h⟩
  push Not at h
  set P := univ.filter (fun i => 0 < w i) with hP
  have hPne : P.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simp [hP, hi]⟩
  set f : ι → ℝ := fun i => ((t i : ℝ) + 1 - c) / w i with hf
  obtain ⟨j, hjP, hj⟩ := P.exists_mem_eq_inf' hPne f
  have hjw : 0 < w j := by simpa [hP] using hjP
  refine ⟨P.inf' hPne f, ?_, ?_, j, ?_⟩
  · refine Finset.le_inf' _ _ (fun i hi => ?_)
    have hwi : 0 < w i := by simpa [hP] using hi
    rw [hf, le_div_iff₀ hwi]
    linarith [h i]
  · intro i
    refine ⟨?_, ?_⟩
    · rcases (hw i).lt_or_eq with hwi | hwi
      · have hle : P.inf' hPne f ≤ f i := Finset.inf'_le _ (by simp [hP, hwi])
        rw [hf] at hle
        simp only at hle
        rw [le_div_iff₀ hwi] at hle
        linarith
      · rw [← hwi]; have := (ht i).1; rw [← hwi] at this; simpa using this
    · have hs : s ≤ P.inf' hPne f := by
        refine Finset.le_inf' _ _ (fun i hi => ?_)
        have hwi : 0 < w i := by simpa [hP] using hi
        rw [hf, le_div_iff₀ hwi]
        linarith [h i]
      have := (ht i).2
      nlinarith [hw i]
  · rw [hj, hf]
    simp only
    rw [mul_div_cancel₀ _ hjw.ne']
    linarith

/-- **Every total is attained.** If all weights are non-negative and some weight is positive, then
for every offset `c ∈ [0, 1]` and every `m : ℕ` there is a multiplier `s ≥ 0` and a rounding `t` of
`w * s` with offset `c` whose total is exactly `m`. -/
theorem exists_rounds_sum_eq [Fintype ι] {w : ι → ℝ} {c : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hpos : ∃ i, 0 < w i) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (m : ℕ) :
    ∃ s, 0 ≤ s ∧ ∃ t : ι → ℕ, Rounds w c s t ∧ ∑ i, t i = m := by
  classical
  induction m with
  | zero =>
    refine ⟨0, le_rfl, fun _ => 0, fun i => ⟨by simp; linarith, by simp; linarith⟩, by simp⟩
  | succ m ih =>
    obtain ⟨s, hs, t, ht, hsum⟩ := ih
    obtain ⟨s', hss', ht', j, hj⟩ := ht.exists_step hw hpos
    refine ⟨s', hs.trans hss', Function.update t j (t j + 1), fun i => ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | hij
      · simp only [Function.update_self]
        push_cast
        exact ⟨by linarith [(ht' i).1], hj⟩
      · simpa [Function.update_of_ne hij] using ht' i
    · rw [Finset.sum_update_of_mem (mem_univ j), ← hsum,
        ← Finset.add_sum_erase _ _ (mem_univ j), Finset.sdiff_singleton_eq_erase]
      ring

/-! ### One-sided behaviour of `s ↦ ⌊a s + c⌋₊`

The plain floor rounding is right-continuous in the multiplier, and just below a multiplier `σ` it
equals the value at `σ`, minus one exactly when `a σ + c` is an integer. -/

section Floor

open Filter Topology

/-- `s ↦ ⌊a s + c⌋₊` is locally constant to the right of every point (for `a ≥ 0`). -/
theorem floor_eventually_eq_right {a c σ : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ a * σ + c) :
    ∀ᶠ s in 𝓝[≥] σ, ⌊a * s + c⌋₊ = ⌊a * σ + c⌋₊ := by
  rcases ha.lt_or_eq with ha | rfl
  · set f := ⌊a * σ + c⌋₊
    have hf : a * σ + c < f + 1 := Nat.lt_floor_add_one _
    have hδ : 0 < ((f : ℝ) + 1 - (a * σ + c)) / a := div_pos (by linarith) ha
    filter_upwards [Ico_mem_nhdsGE (by linarith : σ < σ + ((f : ℝ) + 1 - (a * σ + c)) / a)]
      with s hs
    have h1 : a * σ ≤ a * s := mul_le_mul_of_nonneg_left hs.1 ha.le
    have h2 : a * s < a * (σ + ((f : ℝ) + 1 - (a * σ + c)) / a) :=
      mul_lt_mul_of_pos_left hs.2 ha
    rw [mul_add, mul_div_cancel₀ _ ha.ne'] at h2
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by linarith [Nat.floor_le hy], by linarith⟩
  · simp

open scoped Classical in
/-- Just below `σ`, `⌊a s + c⌋₊` equals its value at `σ`, minus one iff `a σ + c` is an integer
(for `a ≥ 0`, `0 < c < 1`). Footnote 6 of Swiper. -/
theorem floor_eventually_eq_left {a c σ : ℝ} (ha : 0 ≤ a) (hc0 : 0 < c) (hc1 : c < 1)
    (hσ : 0 ≤ σ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⌊a * (σ - ε) + c⌋₊ =
      if ∃ k : ℕ, a * σ + c = k then ⌊a * σ + c⌋₊ - 1 else ⌊a * σ + c⌋₊ := by
  have hy : 0 < a * σ + c := by positivity
  split_ifs with hk
  · obtain ⟨k, hk⟩ := hk
    rcases ha.lt_or_eq with ha | rfl
    · have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hk; linarith
        · exact h
      filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / a)] with ε hε
      have h1 : a * ε < 1 := by
        have := mul_lt_mul_of_pos_left hε.2 ha
        rwa [mul_one_div_cancel ha.ne'] at this
      have h2 : 0 < a * ε := mul_pos ha hε.1
      rw [hk, Nat.floor_natCast, Nat.floor_eq_iff (by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        nlinarith)]
      push_cast [hk1]
      constructor <;> nlinarith
    · exfalso
      simp only [zero_mul, zero_add] at hk
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk; linarith
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h
        linarith
  · push Not at hk
    rcases ha.lt_or_eq with ha | rfl
    · set f := ⌊a * σ + c⌋₊
      have hfl : (f : ℝ) < a * σ + c := lt_of_le_of_ne (Nat.floor_le hy.le) (fun h => hk f h.symm)
      have hδ : 0 < (a * σ + c - f) / a := div_pos (by linarith) ha
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      have h1 : a * ε < a * σ + c - f := by
        have := mul_lt_mul_of_pos_left hε.2 ha
        rwa [mul_div_cancel₀ _ ha.ne'] at this
      have h2 : 0 < a * ε := mul_pos ha hε.1
      rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg f : (0 : ℝ) ≤ f)])]
      have := Nat.lt_floor_add_one (a * σ + c)
      constructor <;> nlinarith
    · simp

end Floor

end Cslib.Apportionment
