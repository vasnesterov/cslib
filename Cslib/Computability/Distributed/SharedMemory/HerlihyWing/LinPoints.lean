/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Nonblocking

/-!
# Linearization points

Definition 7.1 and Claim 1 of Sela–Herlihy–Petrank.

`runMax H l a`: the largest invocation time (in `H`) of the identities in `l` up to and
including `a`. Placing the linearization point of `a` right after the event at that time is
the choice of the proof of Claim 1 by Sela–Herlihy–Petrank ("right after the later of `e_i`'s
invocation and the linearization point of `e_{i-1}`").

## Main results

* `linearizableLP_iff` / `claim1`: Definition 7.1 ⟺ Definition 4.1.

## References

* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

section FoldMax

variable {α : Type*} (f : α → ℕ)

/-- Maximum of `f` over a list (`0` for the empty list). -/
def lmax (l : List α) : ℕ := l.foldr (fun b m => max (f b) m) 0

lemma le_lmax {l : List α} {b : α} (hb : b ∈ l) : f b ≤ lmax f l := by
  induction l with
  | nil => simp at hb
  | cons c l ih =>
    simp only [lmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_max_left _ _
    · exact (ih hb).trans (le_max_right _ _)

lemma lmax_le {l : List α} {c : ℕ} (h : ∀ b ∈ l, f b ≤ c) : lmax f l ≤ c := by
  induction l with
  | nil => simp [lmax]
  | cons b l ih =>
    simp only [lmax, List.foldr_cons] at ih ⊢
    exact max_le (h b (by simp)) (ih fun b' hb' => h b' (by simp [hb']))

lemma exists_lmax_eq {l : List α} (hl : l ≠ []) : ∃ b ∈ l, lmax f l = f b := by
  induction l with
  | nil => exact absurd rfl hl
  | cons c l ih =>
    simp only [lmax, List.foldr_cons] at ih ⊢
    by_cases hle : l.foldr (fun b m => max (f b) m) 0 ≤ f c
    · exact ⟨c, by simp, max_eq_left hle⟩
    · have hl' : l ≠ [] := by rintro rfl; simp at hle
      obtain ⟨b, hb, hbe⟩ := ih hl'
      exact ⟨b, by simp [hb], by rw [max_eq_right (by omega), hbe]⟩

end FoldMax

/-- Running maximum of invocation times along `l`, up to and including `a`. -/
def runMax (H : History P X Op Res) (l : List (OpId P X)) (a : OpId P X) : ℕ :=
  lmax (tInv H) (l.take (l.idxOf a + 1))

lemma mem_take_idxOf {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l.take (l.idxOf a + 1)) : b = a ∨ [b, a].Sublist l := by
  have hbl : b ∈ l := List.mem_of_mem_take hb
  by_cases hba : b = a
  · exact Or.inl hba
  right
  rw [pair_sublist_iff_idxOf hl]
  refine ⟨hbl, ha, ?_⟩
  obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.1 hb
  simp only [List.length_take, List.getElem_take] at hi hib
  have hidx : l.idxOf b = i := by
    rw [← hib]; exact List.Nodup.idxOf_getElem hl _ _
  have : l.idxOf b ≠ l.idxOf a := fun h => hba ((List.idxOf_inj hbl).1 h)
  omega

lemma mem_take_idxOf_of_sublist {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {a b : α} (h : [b, a].Sublist l ∨ b = a) (ha : a ∈ l) : b ∈ l.take (l.idxOf a + 1) := by
  have hb : b ∈ l := by
    rcases h with h | rfl
    exacts [h.subset (by simp), ha]
  have hle : l.idxOf b ≤ l.idxOf a := by
    rcases h with h | rfl
    · exact ((pair_sublist_iff_idxOf hl).1 h).2.2.le
    · exact le_rfl
  rw [List.mem_iff_getElem]
  have := List.idxOf_lt_length_of_mem hb
  exact ⟨l.idxOf b, by simp; omega, by simp⟩

lemma le_runMax {H : History P X Op Res} {l : List (OpId P X)} (hl : l.Nodup) {a b : OpId P X}
    (ha : a ∈ l) (h : [b, a].Sublist l ∨ b = a) : tInv H b ≤ runMax H l a :=
  le_lmax _ (mem_take_idxOf_of_sublist hl h ha)

lemma runMax_mono {H : History P X Op Res} {l : List (OpId P X)} (hl : l.Nodup)
    {a b : OpId P X} (h : [a, b].Sublist l) : runMax H l a ≤ runMax H l b := by
  have hb : b ∈ l := h.subset (by simp)
  have ha : a ∈ l := h.subset (by simp)
  apply lmax_le
  intro c hc
  rcases mem_take_idxOf hl ha hc with rfl | hca
  · exact le_runMax hl hb (Or.inl h)
  · exact le_runMax hl hb (Or.inl (pair_sublist_trans hl hca h))

lemma exists_runMax_eq {H : History P X Op Res} {l : List (OpId P X)} (hl : l.Nodup)
    {a : OpId P X} (ha : a ∈ l) :
    ∃ c, ([c, a].Sublist l ∨ c = a) ∧ runMax H l a = tInv H c := by
  have hne : l.take (l.idxOf a + 1) ≠ [] := by
    have := List.mem_iff_getElem.1 ha
    cases l with
    | nil => simp at ha
    | cons => simp
  obtain ⟨c, hc, hce⟩ := exists_lmax_eq (tInv H) hne
  refine ⟨c, ?_, hce⟩
  rcases mem_take_idxOf hl ha hc with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The running maximum of invocation times stays before the response of `a`, provided no
later operation of `l` is preceded by `a` in real time. -/
lemma runMax_lt_tRes {H : History P X Op Res} (hH : WellFormed H) {l : List (OpId P X)}
    (hl : l.Nodup) (hinv : ∀ c ∈ l, Invoked H c) {a : OpId P X}
    (hrt : ∀ c ∈ l, Precedes H a c → [a, c].Sublist l) (ha : a ∈ l) (hc : Completed H a) :
    runMax H l a < tRes H a := by
  obtain ⟨c, hca, hce⟩ := exists_runMax_eq (H := H) hl ha
  rw [hce]
  rcases hca with hca | rfl
  · by_contra hle
    have hcl : c ∈ l := hca.subset (by simp)
    have hne := tInv_ne_tRes (hinv c hcl) hc
    have hprec : Precedes H a c := precedes_iff.2 ⟨hc, by omega⟩
    exact pair_sublist_asymm hl hca (hrt c hcl hprec)
  · exact tInv_lt_tRes hH hc

/-! ### Claim 1 -/

theorem linearizableLP_iff {spec : SeqSpec P X Op Res} {H : History P X Op Res} :
    LinearizableLP spec H ↔ WellFormed H ∧ ∃ M, IsLinA spec H M := by
  constructor
  · rintro ⟨hH, M, lp, hrecs, hcomp, hpts, hsorted, hlegal⟩
    refine ⟨hH, M, IsLinA.mk' hH hrecs hcomp hlegal ?_⟩
    intro a b hab hb
    have hac := hab.completed
    have ha := hcomp a hac
    have h1 : lp a < tRes H a := by
      have := (hpts a ha).2 hac
      rw [completed_take_iff] at this; push Not at this; exact this hac
    have h2 : tInv H b ≤ lp b := (invoked_take_iff.1 (hpts b hb).1).2
    have h3 := (precedes_iff.1 hab).2
    have hne : a ≠ b := by rintro rfl; omega
    rcases pair_sublist_total (nodup_idsOf M) ha hb hne with h | h
    · exact h
    · have := List.pairwise_iff_forall_sublist.1 hsorted h; omega
  · rintro ⟨hH, M, hM⟩
    refine ⟨hH, M, runMax H (idsOf M), hM.recs, hM.complete, fun a ha => ⟨?_, fun hc => ?_⟩,
      ?_, hM.legal⟩
    · exact invoked_take_iff.2 ⟨hM.recs.invoked ha, le_runMax (nodup_idsOf M) ha (Or.inr rfl)⟩
    · rw [completed_take_iff]; push Not; intro _
      exact runMax_lt_tRes hH (nodup_idsOf M) (fun c hc => hM.recs.invoked hc)
        (fun c hc h => hM.realtime a c h hc) ha hc
    · exact List.pairwise_iff_forall_sublist.2 fun h => runMax_mono (nodup_idsOf M) h

/-- **Claim 1** of Sela–Herlihy–Petrank: linearizability by linearization points
(Definition 7.1) is equivalent to amended linearizability (Definition 4.1). -/
theorem claim1 {spec : SeqSpec P X Op Res} {H : History P X Op Res} :
    LinearizableLP spec H ↔ Linearizable spec H := by
  rw [linearizableLP_iff, linearizable_iff]

end Cslib.SharedMemory.HerlihyWing
