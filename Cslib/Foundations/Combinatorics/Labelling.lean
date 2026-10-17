/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Labellings with prescribed class sizes

Lower-bound proofs for distributed protocols routinely split the processes into a fixed number of
labelled groups whose sizes are only constrained by bounds (e.g. "three groups of size at most
`f`, the first two nonempty, the broadcaster in the third"). This file proves once and for all that
such a split exists as soon as the bounds are compatible with the total number of elements.

Labels are natural numbers `0, …, k - 1`; the class of label `i` is `{a | g a = i}`.

## Main statements

* `Finset.exists_labelling`: if `lo i ≤ hi i` for `i < k` and `∑ lo ≤ #t ≤ ∑ hi`, the members of
  `t` can be labelled by `0, …, k - 1` with the class of `i` of size between `lo i` and `hi i`.
* `Fintype.exists_labelling`: the same for all elements of a finite type.
* `Fintype.exists_labelling_apply_eq`: moreover a given element `a₀` gets a given label `i₀`,
  provided `1 ≤ lo i₀`.

The `k = 3` labelling of `Cslib.Byzantine.PartialSync.FLM.exists_label` (three classes of size
`≤ f`, mod-3 form) is a special case.
-/

@[expose] public section

open Finset

variable {α : Type*}

/-- A finset `t` can be labelled by `0, …, k - 1` so that the class of label `i` has between
`lo i` and `hi i` elements, provided `lo i ≤ hi i` and `∑ lo ≤ #t ≤ ∑ hi`. -/
theorem Finset.exists_labelling (t : Finset α) (k : ℕ) (lo hi : ℕ → ℕ)
    (hle : ∀ i < k, lo i ≤ hi i) (hlo : ∑ i ∈ range k, lo i ≤ #t)
    (hhi : #t ≤ ∑ i ∈ range k, hi i) :
    ∃ g : α → ℕ, (∀ a ∈ t, g a < k) ∧
      ∀ i < k, lo i ≤ #{a ∈ t | g a = i} ∧ #{a ∈ t | g a = i} ≤ hi i := by
  classical
  induction k generalizing t with
  | zero =>
    obtain rfl : t = ∅ := card_eq_zero.1 (by simpa using hhi)
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ k ih =>
    rw [sum_range_succ] at hlo hhi
    have hsum : ∑ i ∈ range k, lo i ≤ ∑ i ∈ range k, hi i :=
      sum_le_sum fun i hi => hle i (by simp at hi; omega)
    have hk := hle k k.lt_succ_self
    -- the last class gets as many elements as possible
    obtain ⟨T, hTt, hTc⟩ := exists_subset_card_eq (s := t)
      (n := min (hi k) (#t - ∑ i ∈ range k, lo i)) (by omega)
    have hsd := card_sdiff_of_subset hTt
    obtain ⟨g, hg, hgc⟩ := ih (t \ T) (fun i hi => hle i (by omega)) (by omega) (by omega)
    refine ⟨fun a => if a ∈ T then k else g a, fun a ha => ?_, fun i hi => ?_⟩
    · by_cases haT : a ∈ T
      · simp [haT]
      · simpa [haT] using (hg a (mem_sdiff.2 ⟨ha, haT⟩)).trans k.lt_succ_self
    · by_cases hik : i < k
      · have : {a ∈ t | (if a ∈ T then k else g a) = i} = {a ∈ t \ T | g a = i} := by
          ext a; by_cases haT : a ∈ T <;> simp [haT]; omega
        rw [this]; exact hgc i hik
      · rw [show i = k by omega]
        have : {a ∈ t | (if a ∈ T then k else g a) = k} = T := by
          ext a
          by_cases haT : a ∈ T
          · simp [haT, hTt haT]
          · simpa [haT] using fun ha => (hg a (mem_sdiff.2 ⟨ha, haT⟩)).ne
        rw [this, hTc]; omega

/-- The elements of a finite type can be labelled by `0, …, k - 1` so that the class of label `i`
has between `lo i` and `hi i` elements, provided `lo i ≤ hi i` and `∑ lo ≤ card α ≤ ∑ hi`. -/
theorem Fintype.exists_labelling [Fintype α] (k : ℕ) (lo hi : ℕ → ℕ)
    (hle : ∀ i < k, lo i ≤ hi i) (hlo : ∑ i ∈ range k, lo i ≤ Fintype.card α)
    (hhi : Fintype.card α ≤ ∑ i ∈ range k, hi i) :
    ∃ g : α → ℕ, (∀ a, g a < k) ∧ ∀ i < k, lo i ≤ #{a | g a = i} ∧ #{a | g a = i} ≤ hi i := by
  obtain ⟨g, hg, hgc⟩ := (univ : Finset α).exists_labelling k lo hi hle hlo hhi
  exact ⟨g, fun a => hg a (mem_univ a), hgc⟩

/-- `Fintype.exists_labelling` with a prescribed label `i₀` (whose class must be nonempty,
`1 ≤ lo i₀`) for a given element `a₀`. -/
theorem Fintype.exists_labelling_apply_eq [Fintype α] (k : ℕ) (lo hi : ℕ → ℕ)
    (hle : ∀ i < k, lo i ≤ hi i) (hlo : ∑ i ∈ range k, lo i ≤ Fintype.card α)
    (hhi : Fintype.card α ≤ ∑ i ∈ range k, hi i) (a₀ : α) {i₀ : ℕ} (hi₀ : i₀ < k)
    (hlo₀ : 1 ≤ lo i₀) :
    ∃ g : α → ℕ, g a₀ = i₀ ∧ (∀ a, g a < k) ∧
      ∀ i < k, lo i ≤ #{a | g a = i} ∧ #{a | g a = i} ≤ hi i := by
  classical
  obtain ⟨g, hg, hgc⟩ := Fintype.exists_labelling k lo hi hle hlo hhi
  obtain ⟨b, hb⟩ := Finset.card_pos.1 (by have := (hgc i₀ hi₀).1; omega : 0 < #{a | g a = i₀})
  refine ⟨g ∘ Equiv.swap a₀ b, by simpa using hb, fun a => hg _, fun i hi => ?_⟩
  rw [card_equiv (Equiv.swap a₀ b) (t := {a | g a = i}) (by simp)]
  exact hgc i hi
