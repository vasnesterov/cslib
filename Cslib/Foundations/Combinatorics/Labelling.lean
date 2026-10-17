/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset

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

## Disjoint groups of a prescribed size; labellings into `Fin k`

Partition-style lower-bound arguments ("split the processes into `k + 1` disjoint groups of
`n - f` processes") need `m` pairwise disjoint groups of size `ℓ`, which exist as soon as `m * ℓ`
does not exceed the number of elements (the special case of `Finset.exists_labelling` with `m`
classes of size exactly `ℓ` and one class for the remaining elements):

* `Finset.exists_pairwise_disjoint_card_eq`: `m` pairwise disjoint subsets of `t` of size `ℓ`, if
  `m * ℓ ≤ #t`;
* `Fintype.exists_pairwise_disjoint_card_eq`: the same for all elements of a finite type.

Lower-bound executions usually name their groups by a small finite type, so labels in `Fin k`
(rather than natural numbers `< k`) are more convenient:

* `Fintype.exists_fin_labelling`: `Fintype.exists_labelling` with labels in `Fin k` and bounds
  `lo hi : Fin k → ℕ`;
* `Fintype.exists_fin_labelling_le`: every class has at most `t` elements and the classes of a
  given set `S` of labels are nonempty, provided `#S ≤ card α ≤ k * t`.
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

/-! ### Disjoint groups of a prescribed size; labellings into `Fin k` -/

section FinLabels

open Function

/-- A finset `t` with `m * ℓ ≤ #t` contains `m` pairwise disjoint subsets of size `ℓ`. -/
theorem Finset.exists_pairwise_disjoint_card_eq (t : Finset α) {m ℓ : ℕ} (h : m * ℓ ≤ #t) :
    ∃ G : Fin m → Finset α, (∀ i, G i ⊆ t) ∧ (∀ i, #(G i) = ℓ) ∧ Pairwise (Disjoint on G) := by
  classical
  have hsum (c : ℕ) : ∑ i ∈ range (m + 1), (if i < m then ℓ else c) = m * ℓ + c := by
    rw [sum_range_succ, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl m)),
      sum_congr rfl fun i hi => ite_eq_left_of_eq_true _ _ (eq_true (mem_range.1 hi))]
    simp
  obtain ⟨g, -, hg⟩ := t.exists_labelling (m + 1) (fun i => if i < m then ℓ else 0)
    (fun i => if i < m then ℓ else #t) (fun i _ => by split_ifs <;> omega)
    (by rw [hsum]; omega) (by rw [hsum]; omega)
  refine ⟨fun i => {a ∈ t | g a = i}, fun i => filter_subset _ _, fun i => ?_, fun i j hij => ?_⟩
  · have := hg i (by omega)
    simp only [i.isLt, ite_true] at this
    exact le_antisymm this.2 this.1
  · exact disjoint_filter.2 fun a _ hi hj => hij (Fin.ext (hi.symm.trans hj))

/-- A finite type with `m * ℓ ≤ card α` contains `m` pairwise disjoint subsets of size `ℓ`. -/
theorem Fintype.exists_pairwise_disjoint_card_eq [Fintype α] {m ℓ : ℕ} (h : m * ℓ ≤ card α) :
    ∃ G : Fin m → Finset α, (∀ i, #(G i) = ℓ) ∧ Pairwise (Disjoint on G) := by
  obtain ⟨G, -, hG⟩ := (univ : Finset α).exists_pairwise_disjoint_card_eq (by simpa using h)
  exact ⟨G, hG⟩

/-- `Fintype.exists_labelling` with labels in `Fin k`: the elements of a finite type can be
labelled by `Fin k` so that the class of `i` has between `lo i` and `hi i` elements, provided
`lo i ≤ hi i` and `∑ lo ≤ card α ≤ ∑ hi`. -/
theorem Fintype.exists_fin_labelling [Fintype α] {k : ℕ} (lo hi : Fin k → ℕ)
    (hle : ∀ i, lo i ≤ hi i) (hlo : ∑ i, lo i ≤ card α) (hhi : card α ≤ ∑ i, hi i) :
    ∃ g : α → Fin k, ∀ i, lo i ≤ #{a | g a = i} ∧ #{a | g a = i} ≤ hi i := by
  classical
  let ext (f : Fin k → ℕ) (i : ℕ) : ℕ := if h : i < k then f ⟨i, h⟩ else 0
  have hsum (f : Fin k → ℕ) : ∑ i ∈ range k, ext f i = ∑ i, f i := by
    rw [Finset.sum_range]; simp [ext]
  obtain ⟨g, hg, hc⟩ := Fintype.exists_labelling k (ext lo) (ext hi)
    (fun i hi => by simp only [ext, hi, ↓reduceDIte]; exact hle _) (by rwa [hsum]) (by rwa [hsum])
  refine ⟨fun a => ⟨g a, hg a⟩, fun i => ?_⟩
  simpa [ext, Fin.ext_iff] using hc i i.isLt

/-- The elements of a finite type with `#S ≤ card α ≤ k * t` can be labelled by `Fin k` so that
every class has at most `t` elements and the classes of the labels in `S` are nonempty. -/
theorem Fintype.exists_fin_labelling_le [Fintype α] {k t : ℕ} (S : Finset (Fin k))
    (hS : #S ≤ card α) (hk : card α ≤ k * t) :
    ∃ g : α → Fin k, (∀ i ∈ S, ∃ a, g a = i) ∧ ∀ i, #{a | g a = i} ≤ t := by
  classical
  have ht : S.Nonempty → 1 ≤ t := fun ⟨i, _⟩ => by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · have := (Finset.card_pos.2 ⟨i, ‹_›⟩).trans_le hS; simp at hk; omega
    · exact h
  obtain ⟨g, hg⟩ := Fintype.exists_fin_labelling (fun i => if i ∈ S then 1 else 0) (fun _ => t)
    (fun i => by split_ifs with h; exacts [ht ⟨i, h⟩, Nat.zero_le _])
    (by simpa [Finset.sum_boole] using hS) (by simpa using hk)
  refine ⟨g, fun i hi => ?_, fun i => (hg i).2⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by simpa [hi] using (hg i).1)
  exact ⟨a, (mem_filter.1 ha).2⟩

end FinLabels
