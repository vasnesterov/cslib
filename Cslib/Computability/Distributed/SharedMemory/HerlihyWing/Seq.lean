/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Times

/-!
# Real-time order in sequential histories; identities under filtering

## Main results

* `pair_sublist_iff_idxOf`: `[a, b] <+ l` for a duplicate-free list is a comparison of indices.
* `rt_seqHist`: `a <_S b` in the sequential history `S = seqHist M` iff `a` comes before `b` in
  `idsOf M`.
* `zip_idsOf_filter`, `idsOf_filter`: restricting a sequential history to some processes /
  objects does not change the identities of the remaining operations.
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

/-! ### Pairs in lists -/

section Pairs

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma pair_sublist_iff {l : List α} {a b : α} :
    [a, b].Sublist l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ a ∈ l₁ ∧ b ∈ l₂ := by
  rw [List.cons_sublist_iff]
  simp

lemma pair_sublist_iff_idxOf {l : List α} (hl : l.Nodup) {a b : α} :
    [a, b].Sublist l ↔ a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b := by
  constructor
  · intro h
    obtain ⟨l₁, l₂, rfl, ha, hb⟩ := pair_sublist_iff.1 h
    have hb' : b ∉ l₁ := fun hb' => (List.nodup_append.1 hl).2.2 _ hb' _ hb rfl
    refine ⟨List.mem_append_left _ ha, List.mem_append_right _ hb, ?_⟩
    rw [List.idxOf_append_of_mem ha, List.idxOf_append_of_notMem hb']
    have := List.idxOf_lt_length_of_mem ha
    omega
  · rintro ⟨ha, hb, hlt⟩
    refine pair_sublist_iff.2 ⟨l.take (l.idxOf a + 1), l.drop (l.idxOf a + 1),
      (List.take_append_drop _ _).symm, ?_, ?_⟩
    · have hlen := List.idxOf_lt_length_of_mem ha
      rw [List.mem_iff_getElem]
      exact ⟨l.idxOf a, by simp; omega, by simp [List.getElem_take]⟩
    · have hlen := List.idxOf_lt_length_of_mem hb
      rw [List.mem_iff_getElem]
      refine ⟨l.idxOf b - (l.idxOf a + 1), by simp; omega, ?_⟩
      have : l.idxOf a + 1 + (l.idxOf b - (l.idxOf a + 1)) = l.idxOf b := by omega
      simp [List.getElem_drop, this]

omit [DecidableEq α] in
lemma pair_sublist_asymm {l : List α} (hl : l.Nodup) {a b : α} (h : [a, b].Sublist l) :
    ¬ [b, a].Sublist l := by
  classical
  rw [pair_sublist_iff_idxOf hl] at h ⊢; omega

omit [DecidableEq α] in
lemma pair_sublist_irrefl {l : List α} (hl : l.Nodup) (a : α) : ¬ [a, a].Sublist l := by
  classical
  rw [pair_sublist_iff_idxOf hl]; omega

omit [DecidableEq α] in
lemma pair_sublist_trans {l : List α} (hl : l.Nodup) {a b c : α} (h1 : [a, b].Sublist l)
    (h2 : [b, c].Sublist l) : [a, c].Sublist l := by
  classical
  rw [pair_sublist_iff_idxOf hl] at h1 h2 ⊢; exact ⟨h1.1, h2.2.1, by omega⟩

omit [DecidableEq α] in
lemma pair_sublist_total {l : List α} (hl : l.Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hne : a ≠ b) : [a, b].Sublist l ∨ [b, a].Sublist l := by
  classical
  rw [pair_sublist_iff_idxOf hl, pair_sublist_iff_idxOf hl]
  have : l.idxOf a ≠ l.idxOf b := fun h => hne (List.idxOf_inj ha |>.1 h)
  rcases Nat.lt_or_gt_of_ne this with h | h
  · exact Or.inl ⟨ha, hb, h⟩
  · exact Or.inr ⟨hb, ha, h⟩

end Pairs

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-! ### Real-time order in a sequential history -/

lemma precedes_seqHist_iff_split {M : List (OpRec P X Op Res)} {a b : OpId P X} :
    Precedes (seqHist M) a b ↔ ∃ N N', M = N ++ N' ∧ a ∈ idsOf N ∧ b ∉ idsOf N := by
  constructor
  · rintro ⟨β, γ, h, hc, hni⟩
    obtain ⟨M₁, M₂, rfl, hβ | ⟨e, M₂', rfl, hβ⟩⟩ := seqHist_eq_append h
    · subst hβ
      exact ⟨M₁, M₂, rfl, completed_seqHist.1 hc, fun h' => hni (invoked_seqHist.2 h')⟩
    · subst hβ
      refine ⟨M₁ ++ [e], M₂', by simp, ?_, ?_⟩
      · have : Completed (seqHist M₁) a := by
          simpa [Completed] using hc
        rw [idsOf_concat]; exact List.mem_append_left _ (completed_seqHist.1 this)
      · intro h'
        apply hni
        have := invoked_seqHist.2 h'
        simpa [Invoked, seqHist_singleton] using this
  · rintro ⟨N, N', rfl, ha, hb⟩
    exact ⟨seqHist N, seqHist N', by simp, completed_seqHist.2 ha,
      fun h => hb (invoked_seqHist.1 h)⟩

lemma precedes_seqHist {M : List (OpRec P X Op Res)} {a b : OpId P X} :
    Precedes (seqHist M) a b ↔ a ∈ idsOf M ∧ (b ∈ idsOf M → [a, b].Sublist (idsOf M)) := by
  rw [precedes_seqHist_iff_split]
  constructor
  · rintro ⟨N, N', rfl, ha, hb⟩
    rw [idsOf_append]
    refine ⟨List.mem_append_left _ ha, fun hb' => ?_⟩
    rcases List.mem_append.1 hb' with hb' | hb'
    · exact absurd hb' hb
    · exact pair_sublist_iff.2 ⟨_, _, rfl, ha, hb'⟩
  · rintro ⟨ha, hab⟩
    by_cases hb : b ∈ idsOf M
    · obtain ⟨l₁, l₂, hl, ha1, hb2⟩ := pair_sublist_iff.1 (hab hb)
      have hnd := nodup_idsOf M
      refine ⟨M.take l₁.length, M.drop l₁.length, (List.take_append_drop _ _).symm, ?_⟩
      have h1 : idsOf (M.take l₁.length) = l₁ := by
        have := congrArg (fun M => idsOf M) (List.take_append_drop l₁.length M)
        simp only [idsOf_append] at this
        rw [hl] at this
        have hlen : (idsOf (M.take l₁.length)).length = l₁.length := by
          simp only [length_idsOf, List.length_take]
          have : (idsOf M).length = M.length := length_idsOf M
          rw [hl] at this; simp at this; omega
        exact (List.append_inj this hlen).1
      rw [h1]
      refine ⟨ha1, fun hb1 => ?_⟩
      rw [hl] at hnd
      exact (List.nodup_append.1 hnd).2.2 _ hb1 _ hb2 rfl
    · exact ⟨M, [], by simp, ha, hb⟩

/-- Real-time order in a sequential history is the order of its operations. -/
lemma rt_seqHist {M : List (OpRec P X Op Res)} {a b : OpId P X} :
    RT (seqHist M) a b ↔ [a, b].Sublist (idsOf M) := by
  rw [RT, precedes_seqHist, completed_seqHist]
  constructor
  · rintro ⟨⟨-, h⟩, hb⟩; exact h hb
  · intro h
    have hab := pair_sublist_iff.1 h
    obtain ⟨l₁, l₂, hl, ha, hb⟩ := hab
    refine ⟨⟨by rw [hl]; exact List.mem_append_left _ ha, fun _ => h⟩, ?_⟩
    rw [hl]; exact List.mem_append_right _ hb

/-! ### Identities under filtering by process/object -/

lemma cnt_filter (M : List (OpRec P X Op Res)) (f : P → X → Bool) (p : P) (x : X)
    (h : f p x = true) : cnt (M.filter (fun e => f e.p e.x)) p x = cnt M p x := by
  simp only [cnt, List.countP_filter]
  congr 1; funext e
  by_cases hp : e.p = p <;> by_cases hx : e.x = x <;> simp [hp, hx, h]

lemma zip_idsOf_filter (M : List (OpRec P X Op Res)) (f : P → X → Bool) :
    ((idsOf M).zip M).filter (fun ae => f ae.2.p ae.2.x) =
      (idsOf (M.filter (fun e => f e.p e.x))).zip (M.filter (fun e => f e.p e.x)) := by
  induction M using List.reverseRecOn with
  | nil => rfl
  | append_singleton M e ih =>
    rw [idsOf_concat, List.zip_append (by simp), List.filter_append, ih, List.filter_append]
    by_cases he : f e.p e.x = true
    · simp only [List.zip_cons_cons, List.zip_nil_right, List.filter_cons, he, ↓reduceIte,
        List.filter_nil, idsOf_concat]
      rw [List.zip_append (by simp), cnt_filter M f e.p e.x he]
      simp
    · simp [he]

lemma idsOf_filter (M : List (OpRec P X Op Res)) (f : P → X → Bool) :
    idsOf (M.filter (fun e => f e.p e.x)) = (idsOf M).filter (fun a => f a.p a.x) := by
  have h := congrArg (List.map Prod.fst) (zip_idsOf_filter M f)
  rw [List.map_fst_zip (by simp)] at h
  rw [← h]
  have : ((idsOf M).zip M).filter (fun ae => f ae.2.p ae.2.x) =
      ((idsOf M).zip M).filter (fun ae => f ae.1.p ae.1.x) := by
    apply List.filter_congr
    rintro ⟨a, e⟩ hae
    obtain ⟨h1, h2⟩ := mem_zip_idsOf hae
    simp [h1, h2]
  rw [this]
  have h2 := List.filter_map (f := Prod.fst) (p := fun a : OpId P X => f a.p a.x)
    (l := (idsOf M).zip M)
  rw [List.map_fst_zip (by simp)] at h2
  rw [h2]; rfl

omit [DecidableEq P] in
/-- Legality of a complete sequential history, object by object. -/
lemma legal_seqHist_iff (spec : SeqSpec P X Op Res) (M : List (OpRec P X Op Res)) :
    Legal spec (seqHist M) ↔ ∀ x, seqHist (M.filter (·.x = x)) ∈ spec x := by
  simp [Legal, isSeq_seqHist, restrictX_seqHist]

end Cslib.SharedMemory.HerlihyWing
