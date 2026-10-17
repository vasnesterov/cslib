/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Equiv
public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.DetSpec

/-!
# Linearizability of sequential histories and of prefixes

Basic facts about Herlihy–Wing linearizability (`Cslib.SharedMemory.HerlihyWing.Linearizable`,
amended definition of Sela–Herlihy–Petrank):

* `wellFormed_seqHist`: complete sequential histories are well formed;
* `Linearizable.of_isExtension`: a history extending (by responses) to a legal complete
  sequential history is linearizable;
* `linearizable_seqHist_iff`: a complete sequential history is linearizable iff it is legal
  (in particular a single illegal operation is not linearizable);
* `SeqSpec.PrefixClosed`, `detSpec_prefixClosed`: prefix-closed sequential specifications
  (e.g. every deterministic one);
* `Linearizable.of_prefix`: for a prefix-closed specification, every prefix of a linearizable
  history is linearizable;
* `restrictX_of_subsingleton`, `legal_seqHist_iff_of_subsingleton`: single-object histories.
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type}

/-! ### Single-object histories -/

/-- On a single object, restricting a history to the object does nothing. -/
lemma restrictX_of_subsingleton [DecidableEq X] [Subsingleton X] (H : History P X Op Res)
    (x : X) : restrictX H x = H :=
  List.filter_eq_self.2 fun _ _ => decide_eq_true (Subsingleton.elim _ _)

/-- On a single object `x`, a complete sequential history is legal iff it belongs to the
specification of `x`. -/
lemma legal_seqHist_iff_of_subsingleton [DecidableEq X] [Subsingleton X]
    {spec : SeqSpec P X Op Res} {M : List (OpRec P X Op Res)} (x : X) :
    Legal spec (seqHist M) ↔ seqHist M ∈ spec x := by
  refine ⟨fun h => ?_, fun h => ⟨isSeq_seqHist M, fun y => ?_⟩⟩
  · have := h.2 x; rwa [restrictX_of_subsingleton] at this
  · rw [restrictX_of_subsingleton, Subsingleton.elim y x]; exact h

variable [DecidableEq P] [DecidableEq X]

/-! ### Sequential histories -/

omit [DecidableEq X] in
/-- A complete sequential history is well formed. -/
lemma wellFormed_seqHist (M : List (OpRec P X Op Res)) : WellFormed (seqHist M) := fun p => by
  rw [restrictP_seqHist]; exact isSeq_seqHist _

/-- A history that extends (by appending responses) to a legal complete sequential history is
linearizable. -/
theorem Linearizable.of_isExtension {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    {M : List (OpRec P X Op Res)} (hH : IsExtension H (seqHist M))
    (hM : Legal spec (seqHist M)) : Linearizable spec H := by
  have hc : complete (seqHist M) = seqHist M := completeAux_seqHist M []
  refine ⟨?_, seqHist M, hH, seqHist M, hM, ?_, ?_⟩
  · obtain ⟨R, hR, -, hwf⟩ := hH
    rw [hR] at hwf; exact hwf.of_append
  · rw [hc]; intro p; rfl
  · rw [hc]; exact fun a b h => h

/-- A legal complete sequential history is linearizable. -/
theorem linearizable_seqHist {spec : SeqSpec P X Op Res} {M : List (OpRec P X Op Res)}
    (hM : Legal spec (seqHist M)) : Linearizable spec (seqHist M) :=
  Linearizable.of_isExtension ⟨[], by simp, by simp, wellFormed_seqHist M⟩ hM

/-- A linearizable complete sequential history is legal: its only possible linearization is
itself, since all its operations are ordered by real time. -/
theorem Linearizable.legal_seqHist {spec : SeqSpec P X Op Res} {M : List (OpRec P X Op Res)}
    (h : Linearizable spec (seqHist M)) : Legal spec (seqHist M) := by
  obtain ⟨-, N, hN⟩ := linearizable_iff.1 h
  have hmem : ∀ a, a ∈ idsOf M ↔ a ∈ idsOf N := fun a =>
    ⟨fun ha => hN.complete a (completed_seqHist.2 ha),
      fun ha => invoked_seqHist.1 (hN.recs.invoked ha)⟩
  have hids : idsOf M = idsOf N := eq_of_pair_sublist (nodup_idsOf M) (nodup_idsOf N) hmem
    fun a b hab => hN.realtime a b
      (precedes_seqHist.2 ⟨hab.subset List.mem_cons_self, fun _ => hab⟩)
      ((hmem b).1 (hab.subset (by simp)))
  suffices hMN : M = N by rw [hMN]; exact hN.legal
  refine eq_of_idsOf_eq hids fun a ha => ?_
  obtain ⟨e, he⟩ := exists_mem_zip_idsOf ((hmem a).1 ha)
  obtain ⟨h1, h2⟩ := hN.recs a e he
  obtain ⟨h3, h4, -⟩ := mem_zip_idsOf_spec he
  exact ⟨h1.trans h3.symm, (h2 (completed_seqHist.2 ha)).trans h4.symm⟩

/-- A complete sequential history is linearizable iff it is legal. -/
theorem linearizable_seqHist_iff {spec : SeqSpec P X Op Res} {M : List (OpRec P X Op Res)} :
    Linearizable spec (seqHist M) ↔ Legal spec (seqHist M) :=
  ⟨Linearizable.legal_seqHist, linearizable_seqHist⟩

/-! ### Prefixes -/

/-- A sequential specification is *prefix closed*: removing operations from the end of a legal
complete sequential history keeps it legal. -/
def SeqSpec.PrefixClosed (spec : SeqSpec P X Op Res) : Prop :=
  ∀ x (M N : List (OpRec P X Op Res)), seqHist (M ++ N) ∈ spec x → seqHist M ∈ spec x

omit [DecidableEq P] [DecidableEq X] in
/-- The specification of a deterministic object is prefix closed. -/
lemma detSpec_prefixClosed {State : Type} (init : State) (δ : State → Op → State × Res) :
    SeqSpec.PrefixClosed (P := P) (fun _ : X => detSpec init δ) := by
  intro x M N h
  rw [seqHist_mem_detSpec, runOK_append] at h
  exact seqHist_mem_detSpec.2 h.1

omit [DecidableEq P] in
/-- For a prefix-closed specification, legality of complete sequential histories is inherited
by prefixes. -/
lemma SeqSpec.PrefixClosed.legal_seqHist {spec : SeqSpec P X Op Res} (hspec : spec.PrefixClosed)
    {M N : List (OpRec P X Op Res)} (h : Legal spec (seqHist (M ++ N))) :
    Legal spec (seqHist M) := by
  rw [legal_seqHist_iff] at h ⊢
  intro x
  have := h x
  rw [List.filter_append] at this
  exact hspec x _ _ this

/-- Given a history `E` and a linearization list `M`, the shortest prefix `N` of `M` containing
all operations of `M` that are completed in `E`: every operation of `N` is completed in `E` or
precedes in `N` an operation completed in `E`. -/
lemma exists_prefix_cover (E : History P X Op Res) (M : List (OpRec P X Op Res)) :
    ∃ N, N <+: M ∧ (∀ a ∈ idsOf M, Completed E a → a ∈ idsOf N) ∧
      (∀ c ∈ idsOf N, Completed E c ∨ ∃ a, Completed E a ∧ [c, a].Sublist (idsOf N)) := by
  induction M using List.reverseRecOn with
  | nil => exact ⟨[], List.prefix_refl _, fun a ha => by simp at ha, fun c hc => by simp at hc⟩
  | append_singleton M e ih =>
    obtain ⟨N, hN, h1, h2⟩ := ih
    by_cases hz : Completed E ⟨e.p, e.x, cnt M e.p e.x⟩
    · refine ⟨M ++ [e], List.prefix_refl _, fun a ha _ => ha, fun c hc => ?_⟩
      rw [idsOf_concat] at hc ⊢
      rcases List.mem_append.1 hc with hc | hc
      · exact Or.inr ⟨_, hz, pair_sublist_iff.2 ⟨idsOf M, _, rfl, hc, List.mem_singleton_self _⟩⟩
      · rw [List.mem_singleton] at hc; subst hc; exact Or.inl hz
    · refine ⟨N, hN.trans (List.prefix_append _ _), fun a ha hca => ?_, h2⟩
      rw [idsOf_concat] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact h1 a ha hca
      · rw [List.mem_singleton] at ha; subst ha; exact absurd hca hz

/-- For a prefix-closed specification, every prefix of a linearizable history is
linearizable. -/
theorem Linearizable.of_prefix {spec : SeqSpec P X Op Res} (hspec : spec.PrefixClosed)
    {E F : History P X Op Res} (hF : Linearizable spec F) (h : E <+: F) :
    Linearizable spec E := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨hwfF, M, hM⟩ := linearizable_iff.1 hF
  have hwfE : WellFormed E := hwfF.of_append
  obtain ⟨N, ⟨T, rfl⟩, h1, h2⟩ := exists_prefix_cover E M
  have hids : idsOf (N ++ T) = idsOf N ++ idsGo N T := idsOf_append N T
  have hnd := nodup_idsOf (N ++ T)
  have hsub : ∀ a ∈ idsOf N, a ∈ idsOf (N ++ T) := fun a ha => by
    rw [hids]; exact List.mem_append_left _ ha
  have hsub2 : ∀ a b, [a, b].Sublist (idsOf N) → [a, b].Sublist (idsOf (N ++ T)) :=
    fun a b hab => by rw [hids]; exact hab.trans (List.sublist_append_left _ _)
  have hinvN : ∀ c ∈ idsOf N, Invoked E c := by
    intro c hc
    rcases h2 c hc with hcc | ⟨a, ha, hca⟩
    · exact hwfE.invoked_of_completed hcc
    · by_contra hni
      have hpre : Precedes (E ++ t) a c := ⟨E, t, rfl, ha, hni⟩
      exact pair_sublist_asymm hnd (hM.realtime a c hpre (hsub c hc)) (hsub2 c a hca)
  refine linearizable_iff.2 ⟨hwfE, N, IsLinA.mk' hwfE ?_ ?_ (hspec.legal_seqHist hM.legal) ?_⟩
  · intro a e hae
    have hae' : (a, e) ∈ (idsOf (N ++ T)).zip (N ++ T) := by
      rw [hids, List.zip_append (by simp)]; exact List.mem_append_left _ hae
    obtain ⟨ho, hr⟩ := hM.recs a e hae'
    have hai : Invoked E a := hinvN a (List.of_mem_zip hae).1
    refine ⟨by rw [opOf_append_of_invoked hai] at ho; exact ho, fun hc => ?_⟩
    have := hr hc.mono
    rw [resOf_append_of_completed hc] at this; exact this
  · intro a ha; exact h1 a (hM.complete a ha.mono) ha
  · intro a b hab hb
    have hab' := hM.realtime a b hab.mono (hsub b hb)
    have ha : a ∈ idsOf N := h1 a (hab'.subset List.mem_cons_self) hab.completed
    have hne : a ≠ b := by rintro rfl; exact pair_sublist_irrefl hnd a hab'
    rcases pair_sublist_total (nodup_idsOf N) ha hb hne with h | h
    · exact h
    · exact absurd hab' (pair_sublist_asymm hnd (hsub2 b a h))

end Cslib.SharedMemory.HerlihyWing
