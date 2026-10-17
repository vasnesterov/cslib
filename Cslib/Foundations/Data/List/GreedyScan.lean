/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Finset.Dedup

/-!
# Greedy scans of a list

Many greedy algorithms scan a list `L` once, keeping each entry `a` iff a test `keep A a` passes on
the list `A` of entries kept so far. Greedy spanners are the main example: an edge is kept iff the
graph built so far does not already serve it well enough.

## Main definitions

* `List.greedyScan keep L`: the entries of `L` kept by the scan, in scan order.

## Main statements

* `List.greedyScan_concat`: the step equation (scanning `L ++ [a]`).
* `List.greedyScan_append_eq` / `List.greedyScan_sublist`: the kept entries form a sublist of `L`;
  scanning a longer list only appends (`List.IsPrefix.greedyScan`).
* `List.keep_take_greedyScan`: every kept entry passed the test on the entries kept before it.
* `List.mem_greedyScan_or_not_keep`: every entry of `L` is kept, or it failed the test on the
  entries kept before its position.
* For duplicate-free `L`: `List.mem_greedyScan_take_iff`, `List.keep_of_mem_greedyScan`.
* `List.Pairwise.rel_of_idxOf_lt`: in a sorted list, earlier entries are smaller;
  `Finset.exists_list_nodup_pairwise_le`: sorted inputs exist.
-/

@[expose] public section

namespace List

variable {α : Type*} (keep : List α → α → Prop) [∀ A a, Decidable (keep A a)]

/-- The greedy scan: go through `L` and append `a` to the list `A` of kept entries iff
`keep A a`. -/
def greedyScan (L : List α) : List α :=
  L.foldl (fun A a => if keep A a then A ++ [a] else A) []

/-- Scanning the empty list keeps nothing. -/
@[simp] theorem greedyScan_nil : greedyScan keep [] = [] := rfl

/-- The step equation of the greedy scan. -/
theorem greedyScan_concat (L : List α) (a : α) :
    greedyScan keep (L ++ [a]) =
      if keep (greedyScan keep L) a then greedyScan keep L ++ [a] else greedyScan keep L := by
  unfold greedyScan
  rw [foldl_append]
  rfl

variable {keep}

/-- Scanning `L₁ ++ L₂` appends to the result of scanning `L₁` a sublist of `L₂`. -/
theorem greedyScan_append_eq (L₁ L₂ : List α) :
    ∃ l, l <+ L₂ ∧ greedyScan keep (L₁ ++ L₂) = greedyScan keep L₁ ++ l := by
  induction L₂ using List.reverseRecOn with
  | nil => exact ⟨[], Sublist.slnil, by simp⟩
  | append_singleton L₂ a ih =>
    obtain ⟨l, hl, h⟩ := ih
    rw [← append_assoc, greedyScan_concat, h]
    split_ifs
    · exact ⟨l ++ [a], hl.append (Sublist.refl _), by simp⟩
    · exact ⟨l, hl.trans (sublist_append_left _ _), rfl⟩

/-- The kept entries form a sublist of the scanned list. -/
theorem greedyScan_sublist (L : List α) : greedyScan keep L <+ L := by
  obtain ⟨l, hl, h⟩ := greedyScan_append_eq (keep := keep) [] L
  rw [nil_append, greedyScan_nil, nil_append] at h
  exact h ▸ hl

/-- Kept entries are entries of the scanned list. -/
theorem mem_of_mem_greedyScan {L : List α} {a : α} (h : a ∈ greedyScan keep L) : a ∈ L :=
  (greedyScan_sublist L).subset h

/-- Scanning a longer list only appends kept entries. -/
theorem IsPrefix.greedyScan {L₁ L₂ : List α} (h : L₁ <+: L₂) :
    L₁.greedyScan keep <+: L₂.greedyScan keep := by
  obtain ⟨L, rfl⟩ := h
  obtain ⟨l, -, h⟩ := greedyScan_append_eq (keep := keep) L₁ L
  exact ⟨l, h.symm⟩

/-- Scanning a prefix of `L` gives a prefix of the scan of `L`. -/
theorem greedyScan_take_isPrefix (L : List α) (i : ℕ) :
    greedyScan keep (L.take i) <+: greedyScan keep L :=
  (take_prefix i L).greedyScan

/-- The step equation at position `i`. -/
theorem greedyScan_take_succ (L : List α) {i : ℕ} (hi : i < L.length) :
    greedyScan keep (L.take (i + 1)) =
      if keep (greedyScan keep (L.take i)) L[i] then greedyScan keep (L.take i) ++ [L[i]]
      else greedyScan keep (L.take i) := by
  rw [take_succ_eq_append_getElem hi, greedyScan_concat]

/-- Every kept entry passed the test on the entries kept before it. -/
theorem keep_take_greedyScan (L : List α) (i : ℕ) (hi : i < (greedyScan keep L).length) :
    keep ((greedyScan keep L).take i) (greedyScan keep L)[i] := by
  induction L using List.reverseRecOn generalizing i with
  | nil => simp at hi
  | append_singleton L a ih =>
    simp only [greedyScan_concat] at hi ⊢
    split_ifs at hi ⊢ with ha
    · rw [length_append, length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [take_append_of_le_length hi.le, getElem_append_left hi]
        exact ih i hi
      · simpa using ha
    · exact ih i hi

/-- An entry that passes the test at its position is kept. -/
theorem getElem_mem_greedyScan {L : List α} {i : ℕ} (hi : i < L.length)
    (h : keep (greedyScan keep (L.take i)) L[i]) : L[i] ∈ greedyScan keep L := by
  refine (greedyScan_take_isPrefix L (i + 1)).subset ?_
  rw [greedyScan_take_succ L hi]
  simp [h]

/-- Every entry of `L` is kept, or it failed the test at some position `i` (on the entries kept
before `i`). -/
theorem mem_greedyScan_or_not_keep {L : List α} {a : α} (ha : a ∈ L) :
    a ∈ greedyScan keep L ∨
      ∃ i, ∃ hi : i < L.length, L[i] = a ∧ ¬ keep (greedyScan keep (L.take i)) a := by
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem ha
  by_cases h : keep (greedyScan keep (L.take i)) L[i]
  · exact Or.inl (getElem_mem_greedyScan hi h)
  · exact Or.inr ⟨i, hi, rfl, h⟩

/-- If every entry passes every test, the scan keeps everything. -/
theorem greedyScan_eq_self {L : List α} (h : ∀ A, ∀ a ∈ L, keep A a) : greedyScan keep L = L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L a ih =>
    rw [greedyScan_concat, ih fun A b hb => h A b (mem_append_left _ hb)]
    simp [h _ a (by simp)]

/-- For a duplicate-free list, the entries kept while scanning the prefix `L.take i` are the kept
entries lying in that prefix. -/
theorem mem_greedyScan_take_iff {L : List α} (hL : L.Nodup) {i : ℕ} {a : α} :
    a ∈ greedyScan keep (L.take i) ↔ a ∈ greedyScan keep L ∧ a ∈ L.take i := by
  refine ⟨fun h => ⟨(greedyScan_take_isPrefix L i).subset h, mem_of_mem_greedyScan h⟩, ?_⟩
  rintro ⟨h, hi⟩
  obtain ⟨l, hl, heq⟩ := greedyScan_append_eq (keep := keep) (L.take i) (L.drop i)
  rw [take_append_drop] at heq
  rw [heq, mem_append] at h
  refine h.resolve_right fun ha => ?_
  rw [← take_append_drop i L, nodup_append] at hL
  exact hL.2.2 _ hi _ (hl.subset ha) rfl

/-- In a duplicate-free list, a kept entry passed the test at its position. -/
theorem keep_of_mem_greedyScan [DecidableEq α] {L : List α} (hL : L.Nodup) {a : α}
    (ha : a ∈ greedyScan keep L) : keep (greedyScan keep (L.take (L.idxOf a))) a := by
  have haL : a ∈ L := mem_of_mem_greedyScan ha
  have hi : L.idxOf a < L.length := idxOf_lt_length_of_mem haL
  have h1 : a ∈ greedyScan keep (L.take (L.idxOf a + 1)) :=
    (mem_greedyScan_take_iff hL).2 ⟨ha, (mem_take_iff_idxOf_lt haL).2 (Nat.lt_succ_self _)⟩
  have h2 : a ∉ greedyScan keep (L.take (L.idxOf a)) := fun h =>
    (Nat.lt_irrefl _) ((mem_take_iff_idxOf_lt haL).1 (mem_of_mem_greedyScan h))
  rw [greedyScan_take_succ L hi, getElem_idxOf hi] at h1
  split_ifs at h1 with hk
  · exact hk
  · exact absurd h1 h2

/-- In a list that is pairwise related by `R`, an entry listed before another is `R`-related to
it. -/
theorem Pairwise.rel_of_idxOf_lt [DecidableEq α] {R : α → α → Prop} {L : List α}
    (hL : L.Pairwise R) {a b : α} (ha : a ∈ L) (hb : b ∈ L) (h : L.idxOf a < L.idxOf b) :
    R a b := by
  have hia := idxOf_lt_length_of_mem ha
  have hib := idxOf_lt_length_of_mem hb
  have := pairwise_iff_getElem.mp hL _ _ hia hib h
  rwa [getElem_idxOf hia, getElem_idxOf hib] at this

end List

namespace Finset

/-- Every finite set can be listed without repetitions in non-decreasing order of a key `f` (the
input format of greedy algorithms that scan edges by weight). -/
theorem exists_list_nodup_pairwise_le {α β : Type*} [LinearOrder β] (s : Finset α) (f : α → β) :
    ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L ↔ a ∈ s) ∧ L.Pairwise fun a b => f a ≤ f b := by
  refine ⟨s.toList.mergeSort fun a b => decide (f a ≤ f b),
    (List.mergeSort_perm _ _).nodup_iff.mpr s.nodup_toList, fun a => by simp [List.mem_mergeSort],
    ?_⟩
  simpa using List.pairwise_mergeSort (le := fun a b => decide (f a ≤ f b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
    (fun a b => by simpa using le_total _ _) s.toList

end Finset
