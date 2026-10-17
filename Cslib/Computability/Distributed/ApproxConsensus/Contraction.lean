/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Contraction of the honest range in approximate agreement

Convergence proofs of round-based approximate-agreement algorithms (Dolev et al., MSR/W-MSR,
Vaidya–Tseng–Liang, Mendes–Herlihy, the async digraph algorithms, …) all follow one pattern: if
in some round all honest values lie in an interval `[a, b]`, then after the round they still lie
in `[a, b]` and are pairwise within `c · (b - a)`; hence after `t` rounds the honest values lie in
a subinterval of the initial range `[lo, hi]` of length `c ^ t · (hi - lo)`. This file proves this
once, for arbitrary index types and a (possibly time-dependent) set `H t` of processes whose values
are tracked at time `t` (honest, alive, or having completed phase `t`).

## Main statements

* `exists_Icc_of_forall_sub_le`: values in `[a, b]` that are pairwise within `d` lie in a
  subinterval `[a', b'] ⊆ [a, b]` of length `≤ d` (take the infimum and the supremum);
  `exists_Icc_of_forall_sub_le_of_finite`: the same for finitely many values, without `[a, b]`.
* `exists_sub_le_pow_mul_of_step`: nested intervals at rate `c`; if every interval satisfying an
  invariant `P t` can be replaced by one of length `≤ c · (b - a)` satisfying `P (t + 1)`, then
  `P t` holds for an interval of length `≤ c ^ t · (hi - lo)`.
* `exists_Icc_pow_mul_of_step`, `mem_Icc_and_abs_sub_le_pow_mul_of_step`: the honest values stay
  in the initial range `[lo, hi]`, inside a subinterval of length `c ^ t · (hi - lo)`, so they
  are pairwise within `c ^ t · (hi - lo)`.

Combine with `Real.pow_natCeil_logb_inv_div_mul_le` for the number of rounds needed to reach
`ε`-agreement, and with `Finset.sum_div_card_le_sub_div` for averaging steps.
-/

@[expose] public section

open Set

namespace Cslib.ApproxConsensus

variable {ι : Type*}

/-- Values in `[a, b]` that are pairwise within `d ≥ 0` lie in a subinterval `[a', b'] ⊆ [a, b]`
of length at most `d`. -/
theorem exists_Icc_of_forall_sub_le {s : Set ι} {y : ι → ℝ} {a b d : ℝ} (hab : a ≤ b)
    (hd : 0 ≤ d) (hy : ∀ i ∈ s, y i ∈ Icc a b) (hyd : ∀ i ∈ s, ∀ j ∈ s, y i - y j ≤ d) :
    ∃ a' b', a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ b' - a' ≤ d ∧ ∀ i ∈ s, y i ∈ Icc a' b' := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨a, a, le_rfl, le_rfl, hab, by simpa using hd, fun i hi => hi.elim⟩
  have hne : (y '' s).Nonempty := hs.image y
  have hbdd : BddBelow (y '' s) := ⟨a, forall_mem_image.2 fun i hi => (hy i hi).1⟩
  have hbdd' : BddAbove (y '' s) := ⟨b, forall_mem_image.2 fun i hi => (hy i hi).2⟩
  refine ⟨sInf (y '' s), sSup (y '' s), le_csInf hne (forall_mem_image.2 fun i hi => (hy i hi).1),
    (csInf_le hbdd (mem_image_of_mem y hs.some_mem)).trans
      (le_csSup hbdd' (mem_image_of_mem y hs.some_mem)),
    csSup_le hne (forall_mem_image.2 fun i hi => (hy i hi).2), ?_,
    fun i hi => ⟨csInf_le hbdd (mem_image_of_mem y hi), le_csSup hbdd' (mem_image_of_mem y hi)⟩⟩
  rw [sub_le_iff_le_add]
  refine csSup_le hne (forall_mem_image.2 fun i hi => ?_)
  rw [← sub_le_iff_le_add']
  exact le_csInf hne (forall_mem_image.2 fun j hj => by linarith [hyd i hi j hj])

/-- Finitely many values that are pairwise within `d` lie in an interval of length at most `d`
(from the minimum to the maximum). -/
theorem exists_Icc_of_forall_sub_le_of_finite {s : Set ι} (hs : s.Finite) {y : ι → ℝ} {d : ℝ}
    (hyd : ∀ i ∈ s, ∀ j ∈ s, y i - y j ≤ d) : ∃ a b, b - a ≤ d ∧ ∀ i ∈ s, y i ∈ Icc a b := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, min 0 d, by simp, fun i hi => hi.elim⟩
  obtain ⟨p, hp, hmin⟩ := exists_min_image s y hs hne
  obtain ⟨q, hq, hmax⟩ := exists_max_image s y hs hne
  exact ⟨y p, y q, hyd q hq p hp, fun i hi => ⟨hmin i hi, hmax i hi⟩⟩

/-- **Nested intervals at rate `c`.** If an invariant `P t a b` of intervals `[a, b]` holds for
`[lo, hi]` at time `0`, and every interval satisfying `P t` can be replaced by an interval of
length at most `c · (b - a)` satisfying `P (t + 1)`, then at every time `t` the invariant holds for
an interval of length at most `c ^ t · (hi - lo)`. -/
theorem exists_sub_le_pow_mul_of_step {P : ℕ → ℝ → ℝ → Prop} {c lo hi : ℝ} (hc : 0 ≤ c)
    (h0 : P 0 lo hi) (hstep : ∀ t a b, P t a b → ∃ a' b', P (t + 1) a' b' ∧ b' - a' ≤ c * (b - a))
    (t : ℕ) : ∃ a b, P t a b ∧ b - a ≤ c ^ t * (hi - lo) := by
  induction t with
  | zero => exact ⟨lo, hi, h0, by simp⟩
  | succ t ih =>
    obtain ⟨a, b, hP, hab⟩ := ih
    obtain ⟨a', b', hP', hab'⟩ := hstep t a b hP
    refine ⟨a', b', hP', hab'.trans ?_⟩
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left hab hc

/-- **Contraction of the honest range.** Let `x t i` be the value of process `i` at time `t` and
`H t` the processes tracked at time `t`. Suppose that whenever the values of `H t` lie in an
interval `[a, b]`, the values of `H (t + 1)` lie in `[a, b]` and are pairwise within `c · (b - a)`.
If the values of `H 0` lie in `[lo, hi]`, then at every time `t` the values of `H t` lie in a
subinterval of `[lo, hi]` of length at most `c ^ t · (hi - lo)`. -/
theorem exists_Icc_pow_mul_of_step {H : ℕ → Set ι} {x : ℕ → ι → ℝ} {c lo hi : ℝ} (hc : 0 ≤ c)
    (hlh : lo ≤ hi) (h0 : ∀ i ∈ H 0, x 0 i ∈ Icc lo hi)
    (hstep : ∀ t a b, a ≤ b → (∀ i ∈ H t, x t i ∈ Icc a b) →
      (∀ i ∈ H (t + 1), x (t + 1) i ∈ Icc a b) ∧
        ∀ i ∈ H (t + 1), ∀ j ∈ H (t + 1), x (t + 1) i - x (t + 1) j ≤ c * (b - a))
    (t : ℕ) :
    ∃ a b, lo ≤ a ∧ a ≤ b ∧ b ≤ hi ∧ b - a ≤ c ^ t * (hi - lo) ∧ ∀ i ∈ H t, x t i ∈ Icc a b := by
  obtain ⟨a, b, ⟨h1, h2, h3, h4⟩, h5⟩ :=
    exists_sub_le_pow_mul_of_step (P := fun t a b =>
      lo ≤ a ∧ a ≤ b ∧ b ≤ hi ∧ ∀ i ∈ H t, x t i ∈ Icc a b) hc ⟨le_rfl, hlh, le_rfl, h0⟩
      (fun t a b ⟨hla, hab, hbh, hx⟩ => by
        obtain ⟨hin, hpair⟩ := hstep t a b hab hx
        obtain ⟨a', b', h1, h2, h3, h4, h5⟩ :=
          exists_Icc_of_forall_sub_le hab (mul_nonneg hc (sub_nonneg.2 hab)) hin hpair
        exact ⟨a', b', ⟨hla.trans h1, h2, h3.trans hbh, h5⟩, h4⟩) t
  exact ⟨a, b, h1, h2, h3, h5, h4⟩

/-- **Contraction of the honest range**, pairwise form: under the hypotheses of
`exists_Icc_pow_mul_of_step`, at time `t` the values of `H t` lie in `[lo, hi]` and are pairwise
within `c ^ t · (hi - lo)`. -/
theorem mem_Icc_and_abs_sub_le_pow_mul_of_step {H : ℕ → Set ι} {x : ℕ → ι → ℝ} {c lo hi : ℝ}
    (hc : 0 ≤ c) (hlh : lo ≤ hi) (h0 : ∀ i ∈ H 0, x 0 i ∈ Icc lo hi)
    (hstep : ∀ t a b, a ≤ b → (∀ i ∈ H t, x t i ∈ Icc a b) →
      (∀ i ∈ H (t + 1), x (t + 1) i ∈ Icc a b) ∧
        ∀ i ∈ H (t + 1), ∀ j ∈ H (t + 1), x (t + 1) i - x (t + 1) j ≤ c * (b - a))
    (t : ℕ) :
    (∀ i ∈ H t, x t i ∈ Icc lo hi) ∧
      ∀ i ∈ H t, ∀ j ∈ H t, |x t i - x t j| ≤ c ^ t * (hi - lo) := by
  obtain ⟨a, b, h1, -, h3, h4, h5⟩ := exists_Icc_pow_mul_of_step hc hlh h0 hstep t
  exact ⟨fun i hi => Icc_subset_Icc h1 h3 (h5 i hi), fun i hi j hj =>
    (abs_sub_le_of_le_of_le (h5 i hi).1 (h5 i hi).2 (h5 j hj).1 (h5 j hj).2).trans h4⟩

end Cslib.ApproxConsensus
