/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Complete

/-!
# The extension-based definitions vs. their list characterizations

## Main results

* `linearizable_iff`: Definition 4.1 (amended) of Sela–Herlihy–Petrank ⟺ a list `M` with
  `IsLinA`.
* `linearizableHW_iff`: Definition 2.2 (original, Herlihy–Wing) ⟺ a list `M` with `IsLinO`.
* `IsLinA.isLinO`, `Linearizable.linearizableHW`: the amended definition is stronger
  (Section 8 of Sela–Herlihy–Petrank).

Proof ingredients: `lin_of_extension` (definition ⇒ list), `exists_extension` (list ⇒
definition: append the responses recorded in `M` to the linearized pending invocations), and
the key lemma `equiv_complete_of` (`complete(H')` is equivalent to `seqHist M` when `M` lists
exactly the operations of `H'` in program order).

## References

* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

/-! ### Lists of identities -/

/-- Two duplicate-free lists with the same members, such that every pair ordered in the first
list is ordered in the same way in the second, are equal. -/
lemma eq_of_pair_sublist {α : Type*} {l₁ l₂ : List α} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂)
    (hord : ∀ a b, [a, b].Sublist l₁ → [a, b].Sublist l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    symm; rw [List.eq_nil_iff_forall_not_mem]; intro a ha; simpa using (hmem a).2 ha
  | cons a l₁ ih =>
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ((hmem a).1 List.mem_cons_self)
    have ha₁ := (List.nodup_cons.1 h₁).1
    have hs : s = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro c hc
      have hca : c ≠ a := by
        rintro rfl
        exact (List.nodup_append.1 h₂).2.2 _ hc _ List.mem_cons_self rfl
      have hc₁ : c ∈ l₁ := by
        have := (hmem c).2 (List.mem_append_left _ hc)
        exact (List.mem_cons.1 this).resolve_left hca
      have h1 : [a, c].Sublist (s ++ a :: t) :=
        hord a c ((List.singleton_sublist.2 hc₁).cons_cons a)
      have h2 : [c, a].Sublist (s ++ a :: t) :=
        pair_sublist_iff.2 ⟨s, a :: t, rfl, hc, List.mem_cons_self⟩
      exact pair_sublist_asymm h₂ h1 h2
    subst hs
    simp only [List.nil_append] at h₂ hmem hord ⊢
    have hat := (List.nodup_cons.1 h₂).1
    congr 1
    apply ih (List.nodup_cons.1 h₁).2 (List.nodup_cons.1 h₂).2
    · intro b
      constructor
      · intro hb
        exact (List.mem_cons.1 ((hmem b).1 (List.mem_cons_of_mem _ hb))).resolve_left
          (by rintro rfl; exact ha₁ hb)
      · intro hb
        exact (List.mem_cons.1 ((hmem b).2 (List.mem_cons_of_mem _ hb))).resolve_left
          (by rintro rfl; exact hat hb)
    · intro b c hbc
      have hb : b ∈ l₁ := hbc.subset List.mem_cons_self
      rcases List.sublist_cons_iff.1 (hord b c (hbc.cons a)) with h | ⟨r, hr, -⟩
      · exact h
      · simp only [List.cons.injEq] at hr
        exact absurd (hr.1 ▸ hb) ha₁

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- The record of a linearized operation is determined by the sequential history. -/
lemma mem_zip_idsOf_spec {N : List (OpRec P X Op Res)} {a : OpId P X} {e : OpRec P X Op Res}
    (h : (a, e) ∈ (idsOf N).zip N) :
    opOf (seqHist N) a = some e.o ∧ resOf (seqHist N) a = some e.r ∧ a.p = e.p ∧ a.x = e.x := by
  refine ⟨?_, ?_, mem_zip_idsOf h⟩
  all_goals
    induction N using List.reverseRecOn with
    | nil => simp at h
    | append_singleton N f ih =>
      rw [idsOf_concat, List.zip_append (by simp)] at h
      rcases List.mem_append.1 h with h | h
      · have ha := (List.of_mem_zip h).1
        rw [seqHist_append]
        first
          | rw [opOf_append_of_invoked (invoked_seqHist.2 ha)]; exact ih h
          | rw [resOf_append_of_completed (completed_seqHist.2 ha)]; exact ih h
      · simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [opOf, resOf, seqHist_append, opsOf_append, ressOf_append]
        first
          | rw [List.getElem?_append_right (by rw [length_opsOf_seqHist])]
            simp [length_opsOf_seqHist]
          | rw [List.getElem?_append_right (by rw [length_ressOf_seqHist])]
            simp [length_ressOf_seqHist]

lemma exists_mem_zip_idsOf {M : List (OpRec P X Op Res)} {a : OpId P X} (h : a ∈ idsOf M) :
    ∃ e, (a, e) ∈ (idsOf M).zip M := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have hi' : i < M.length := by simpa using hi
  refine ⟨M[i], ?_⟩
  have : ((idsOf M).zip M)[i]'(by simp; omega) = ((idsOf M)[i], M[i]) := List.getElem_zip
  rw [← this]; exact List.getElem_mem _

/-- A list of records is determined by its identities and by the operations and responses of
its sequential history. -/
lemma eq_of_idsOf_eq {N N' : List (OpRec P X Op Res)} (hids : idsOf N = idsOf N')
    (h : ∀ a ∈ idsOf N, opOf (seqHist N) a = opOf (seqHist N') a ∧
      resOf (seqHist N) a = resOf (seqHist N') a) : N = N' := by
  have hlen : N.length = N'.length := by
    rw [← length_idsOf N, ← length_idsOf N', hids]
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi : i < (idsOf N).length := by simpa using h1
  have hz : ((idsOf N)[i], N[i]) ∈ (idsOf N).zip N := by
    have : ((idsOf N).zip N)[i]'(by simp; omega) = ((idsOf N)[i], N[i]) := List.getElem_zip
    rw [← this]; exact List.getElem_mem _
  have hz' : ((idsOf N)[i], N'[i]) ∈ (idsOf N').zip N' := by
    have hi' : i < (idsOf N').length := by simpa using h2
    have : ((idsOf N').zip N')[i]'(by simp; omega) = ((idsOf N')[i], N'[i]) := List.getElem_zip
    have hii : (idsOf N)[i] = (idsOf N')[i] := List.getElem_of_eq hids _
    rw [hii, ← this]
    exact List.getElem_mem _
  obtain ⟨ho, hr, hp, hx⟩ := mem_zip_idsOf_spec hz
  obtain ⟨ho', hr', hp', hx'⟩ := mem_zip_idsOf_spec hz'
  obtain ⟨e1, e2⟩ := h _ (List.getElem_mem _)
  rw [e1, ho'] at ho
  rw [e2, hr'] at hr
  cases h₁ : N[i]; cases h₂ : N'[i]
  simp only [h₁, h₂, Option.some.injEq] at ho hr hp hx hp' hx'
  simp_all

lemma Matches.invoked {H : History P X Op Res} {M : List (OpRec P X Op Res)}
    (h : Matches H M)
    {a : OpId P X} (ha : a ∈ idsOf M) : Invoked H a := by
  obtain ⟨e, he⟩ := exists_mem_zip_idsOf ha
  exact Invoked.of_opOf (h a e he).1

/-! ### From the extension-based definitions to lists -/

omit [DecidableEq X] in
/-- A legal (sequential) history equivalent to `complete(H')` has no pending invocation. -/
lemma eq_seqHist_of_equiv_complete {H' S : History P X Op Res} (hwf : WellFormed H')
    (hEq : Equiv (complete H') S) (hS : IsSeq S) : ∃ M, S = seqHist M := by
  obtain ⟨M, h | ⟨p, x, o, h⟩⟩ := hS
  · exact ⟨M, h⟩
  · obtain ⟨N, hN, -⟩ := hwf.restrictP_complete p
    have := hEq p
    rw [hN, h, restrictP_append, restrictP_seqHist, restrictP_singleton] at this
    simp only [Event.proc_inv, ↓reduceIte] at this
    exact absurd this (seqHist_ne_concat_inv _ _ _ _ _)

lemma mem_idsOf_iff_of_equiv {H' : History P X Op Res} {M : List (OpRec P X Op Res)}
    (hEq : Equiv (complete H') (seqHist M)) (a : OpId P X) : a ∈ idsOf M ↔ Completed H' a := by
  rw [← completed_seqHist, ← hEq.completed_iff, completed_complete]

/-- The common part of both definitions, read as properties of the list `M`. -/
lemma lin_of_extension {H H' : History P X Op Res} {M : List (OpRec P X Op Res)}
    (hext : IsExtension H H') (hEq : Equiv (complete H') (seqHist M)) :
    Matches H M ∧ (∀ a, Completed H a → a ∈ idsOf M) ∧
      (∀ a b, a.p = b.p → Precedes H a b → b ∈ idsOf M → [a, b].Sublist (idsOf M)) ∧
      (∀ a b, Precedes H a b → b ∈ idsOf M → RT (complete H') a b) := by
  obtain ⟨R, rfl, hR, hwf⟩ := hext
  have hmem := mem_idsOf_iff_of_equiv hEq
  have hop : ∀ a, opOf (H ++ R) a = opOf H a := by
    intro a; simp [opOf, opsOf_eq_nil_of_isRes hR]
  have hrt : ∀ a b, Precedes H a b → b ∈ idsOf M → RT (complete (H ++ R)) a b := by
    intro a b h hb
    have hbc := (hmem b).1 hb
    exact ⟨(hwf.precedes_complete_iff hbc).2 h.mono, completed_complete.2 hbc⟩
  refine ⟨?_, fun a ha => (hmem a).2 ha.mono, ?_, hrt⟩
  · intro a e hae
    obtain ⟨ho, hr, -⟩ := mem_zip_idsOf_spec hae
    have hac := (hmem a).1 (List.of_mem_zip hae).1
    refine ⟨?_, fun hc => ?_⟩
    · rw [← hop, ← hwf.opOf_complete hac, hEq.opOf_eq, ho]
    · rw [← resOf_append_of_completed (H' := R) hc, ← resOf_complete, hEq.resOf_eq, hr]
  · intro a b hab h hb
    obtain ⟨h1, h2⟩ := hrt a b h hb
    have h1' := (precedes_restrictP_iff (H := complete (H ++ R)) (p := b.p) hab rfl).2 h1
    have h2' : Completed (restrictP (complete (H ++ R)) b.p) b := completed_restrictP.2 ⟨rfl, h2⟩
    rw [hEq b.p, restrictP_seqHist] at h1' h2'
    have := rt_seqHist.1 ⟨h1', h2'⟩
    have hf := idsOf_filter M (fun q _ => decide (q = b.p))
    rw [hf] at this
    exact this.trans (List.filter_sublist)

/-! ### From lists to the extension-based definitions -/

/-- Appending the response of a pending invocation. -/
lemma WellFormed.res_step {H : History P X Op Res} (hH : WellFormed H) {a : OpId P X}
    (hi : Invoked H a) (hc : ¬ Completed H a) (r : Res) :
    WellFormed (H ++ [.res a.p a.x r]) ∧
      (∀ b, Completed (H ++ [.res a.p a.x r]) b ↔ Completed H b ∨ b = a) ∧
      resOf (H ++ [.res a.p a.x r]) a = some r := by
  obtain ⟨M, o, hM, hk, -, hlen⟩ := hH.pending_spec hi hc
  refine ⟨wellFormed_concat_res.2 ⟨hH, M, o, hM⟩, fun b => ?_, ?_⟩
  · simp only [Completed, ressOf_append, ressOf_cons, ressOf_nil, Event.resOf_res,
      List.length_append]
    by_cases h : a.p = b.p ∧ a.x = b.x
    · obtain ⟨h1, h2⟩ := h
      rcases a with ⟨p, x, k⟩; rcases b with ⟨q, y, l⟩
      simp only at h1 h2 hk hlen ⊢; subst h1 h2
      simp only [and_self, ↓reduceIte, Option.toList_some, List.length_singleton,
        hlen, OpId.mk.injEq, true_and, List.length_nil]
      omega
    · simp only [h, ↓reduceIte, Option.toList_none, List.length_nil,
        add_zero, iff_self_or]
      rintro rfl; exact absurd ⟨rfl, rfl⟩ h
  · simp only [resOf, ressOf_append, ressOf_cons, ressOf_nil, Event.resOf_res, and_self,
      ↓reduceIte, Option.toList_some, List.append_nil]
    rw [List.getElem?_append_right (by rw [hlen, hk])]
    simp [hlen, hk]

/-- Appending responses to pending invocations of distinct processes. -/
lemma WellFormed.res_list {H : History P X Op Res} (hH : WellFormed H)
    (L : List (OpId P X × OpRec P X Op Res)) (hL : ∀ u ∈ L, Invoked H u.1 ∧ ¬ Completed H u.1)
    (hd : L.Pairwise (fun u v => u.1.p ≠ v.1.p)) :
    WellFormed (H ++ L.map (fun u => .res u.1.p u.1.x u.2.r)) ∧
      (∀ b, Completed (H ++ L.map (fun u => .res u.1.p u.1.x u.2.r)) b ↔
        Completed H b ∨ ∃ u ∈ L, u.1 = b) ∧
      (∀ u ∈ L, resOf (H ++ L.map (fun u => .res u.1.p u.1.x u.2.r)) u.1 = some u.2.r) := by
  induction L generalizing H with
  | nil => simp [hH]
  | cons u L ih =>
    obtain ⟨hu1, hu2⟩ := hL u List.mem_cons_self
    obtain ⟨hw1, hc1, hr1⟩ := hH.res_step hu1 hu2 u.2.r
    rw [List.pairwise_cons] at hd
    have hL' : ∀ v ∈ L, Invoked (H ++ [.res u.1.p u.1.x u.2.r]) v.1 ∧
        ¬ Completed (H ++ [.res u.1.p u.1.x u.2.r]) v.1 := by
      intro v hv
      refine ⟨(hL v (List.mem_cons_of_mem _ hv)).1.mono, ?_⟩
      rw [hc1]
      rintro (h | h)
      · exact (hL v (List.mem_cons_of_mem _ hv)).2 h
      · exact hd.1 v hv (by rw [h])
    obtain ⟨ih1, ih2, ih3⟩ := ih hw1 hL' hd.2
    have e : H ++ (u :: L).map (fun u => Event.res u.1.p u.1.x u.2.r) =
        (H ++ [.res u.1.p u.1.x u.2.r]) ++ L.map (fun u => .res u.1.p u.1.x u.2.r) := by simp
    rw [e]
    refine ⟨ih1, fun b => ?_, ?_⟩
    · rw [ih2, hc1]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | rfl) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inr h
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [resOf_append_of_completed ((hc1 _).2 (Or.inr rfl)), hr1]
      · exact ih3 v hv

/-- The key lemma: `complete(H')` is equivalent to `seqHist M` if `M` lists exactly the
operations of `H'`, with their operations and responses, respecting program order. -/
lemma equiv_complete_of {H' : History P X Op Res} {M : List (OpRec P X Op Res)}
    (hwf : WellFormed H') (hrecs : Matches H' M) (hmem : ∀ a, a ∈ idsOf M ↔ Completed H' a)
    (hpo : ∀ a b, a.p = b.p → Precedes H' a b → b ∈ idsOf M → [a, b].Sublist (idsOf M)) :
    Equiv (complete H') (seqHist M) := by
  intro p
  obtain ⟨N, hN, -⟩ := hwf.restrictP_complete p
  rw [hN, restrictP_seqHist]
  congr 1
  have hids : idsOf (M.filter (·.p = p)) = (idsOf M).filter (fun a => decide (a.p = p)) := by
    have := idsOf_filter M (fun q _ => decide (q = p)); simpa using this
  have memN : ∀ a, a ∈ idsOf N ↔ a.p = p ∧ Completed H' a := by
    intro a
    rw [← completed_seqHist, ← hN, completed_restrictP, completed_complete, eq_comm]
  have hidsEq : idsOf N = idsOf (M.filter (·.p = p)) := by
    rw [hids]
    apply eq_of_pair_sublist (nodup_idsOf N) ((nodup_idsOf M).filter _)
    · intro a; rw [memN, List.mem_filter, hmem]; simp [and_comm]
    · intro a b hab
      have ha : a ∈ idsOf N := hab.subset (by simp)
      have hb : b ∈ idsOf N := hab.subset (by simp)
      obtain ⟨hap, -⟩ := (memN a).1 ha
      obtain ⟨hbp, hbc⟩ := (memN b).1 hb
      have hrt := rt_seqHist.2 hab
      rw [← hN] at hrt
      have hpre : Precedes H' a b :=
        (hwf.precedes_complete_iff hbc).1 ((precedes_restrictP_iff hap hbp).1 hrt.1)
      have := (hpo a b (hap.trans hbp.symm) hpre ((hmem b).2 hbc)).filter
        (fun a => decide (a.p = p))
      simpa [hap, hbp] using this
  apply eq_of_idsOf_eq hidsEq
  intro a ha
  obtain ⟨hap, hac⟩ := (memN a).1 ha
  subst hap
  obtain ⟨e, he⟩ := exists_mem_zip_idsOf ((hmem a).2 hac)
  obtain ⟨ho, hr, -⟩ := mem_zip_idsOf_spec he
  obtain ⟨ho', hr'⟩ := hrecs a e he
  rw [← hN, ← restrictP_seqHist, opOf_restrictP, opOf_restrictP, resOf_restrictP,
    resOf_restrictP, hwf.opOf_complete hac, resOf_complete, ho, hr, ho', hr' hac]
  exact ⟨rfl, rfl⟩

/-- Construction of the extension: append responses (from `M`) to the linearized pending
invocations. -/
lemma exists_extension {H : History P X Op Res} {M : List (OpRec P X Op Res)}
    (hH : WellFormed H) (hrecs : Matches H M) (hcomp : ∀ a, Completed H a → a ∈ idsOf M)
    (hpo : ∀ a b, a.p = b.p → Precedes H a b → b ∈ idsOf M → [a, b].Sublist (idsOf M)) :
    ∃ H', IsExtension H H' ∧ Equiv (complete H') (seqHist M) := by
  set L := ((idsOf M).zip M).filter (fun u => !decide (Completed H u.1)) with hLdef
  have hLmem : ∀ u ∈ L, u ∈ (idsOf M).zip M ∧ ¬ Completed H u.1 := by
    intro u hu; simpa [hLdef] using List.mem_filter.1 hu
  have hL : ∀ u ∈ L, Invoked H u.1 ∧ ¬ Completed H u.1 := fun u hu =>
    ⟨Invoked.of_opOf (hrecs u.1 u.2 (hLmem u hu).1).1, (hLmem u hu).2⟩
  have hnd : (L.map Prod.fst).Nodup := by
    have : (L.map Prod.fst).Sublist (idsOf M) := by
      have := (List.filter_sublist (l := (idsOf M).zip M)
        (p := fun u => !decide (Completed H u.1))).map Prod.fst
      rwa [List.map_fst_zip (by simp)] at this
    exact this.nodup (nodup_idsOf M)
  have hd : L.Pairwise (fun u v => u.1.p ≠ v.1.p) := by
    rw [List.Nodup, List.pairwise_map] at hnd
    refine hnd.imp_of_mem ?_
    intro u v hu hv hne hp
    exact hne (hH.pending_eq (hL u hu).1 (hL u hu).2 (hL v hv).1 (hL v hv).2 hp)
  obtain ⟨hwf, hcomp', hres⟩ := hH.res_list L hL hd
  refine ⟨_, ⟨_, rfl, fun e he => by obtain ⟨u, -, rfl⟩ := List.mem_map.1 he; rfl, hwf⟩, ?_⟩
  have hmem : ∀ a, a ∈ idsOf M ↔
      Completed (H ++ L.map (fun u => .res u.1.p u.1.x u.2.r)) a := by
    intro a
    rw [hcomp']
    constructor
    · intro ha
      by_cases hc : Completed H a
      · exact Or.inl hc
      · obtain ⟨e, he⟩ := exists_mem_zip_idsOf ha
        exact Or.inr ⟨(a, e), List.mem_filter.2 ⟨he, by simp [hc]⟩, rfl⟩
    · rintro (hc | ⟨u, hu, rfl⟩)
      · exact hcomp a hc
      · exact (List.of_mem_zip (hLmem u hu).1).1
  apply equiv_complete_of hwf ?_ hmem ?_
  · intro a e hae
    obtain ⟨ho, hr⟩ := hrecs a e hae
    have hi : Invoked H a := Invoked.of_opOf ho
    refine ⟨by rw [opOf_append_of_invoked hi, ho], fun hc => ?_⟩
    by_cases hcH : Completed H a
    · rw [resOf_append_of_completed hcH, hr hcH]
    · exact hres (a, e) (List.mem_filter.2 ⟨hae, by simp [hcH]⟩)
  · intro a b hab h hb
    obtain ⟨e, he⟩ := exists_mem_zip_idsOf hb
    exact hpo a b hab (h.of_append_of_invoked (Invoked.of_opOf (hrecs b e he).1)) hb

/-! ### Main equivalences -/

/-- Amended linearizability (Definition 4.1) in terms of a linearization list. -/
theorem linearizable_iff {spec : SeqSpec P X Op Res} {H : History P X Op Res} :
    Linearizable spec H ↔ WellFormed H ∧ ∃ M, IsLinA spec H M := by
  constructor
  · rintro ⟨hH, H', hext, S, hleg, hEq, hL2⟩
    obtain ⟨M, rfl⟩ := eq_seqHist_of_equiv_complete
      (by obtain ⟨_, _, _, h⟩ := hext; exact h) hEq hleg.1
    obtain ⟨hrecs, hcomp, hpo, hrt⟩ := lin_of_extension hext hEq
    exact ⟨hH, M, ⟨hrecs, hcomp, hleg, hpo⟩,
      fun a b h hb => rt_seqHist.1 (hL2 a b (hrt a b h hb))⟩
  · rintro ⟨hH, M, hM⟩
    obtain ⟨H', hext, hEq⟩ := exists_extension hH hM.recs hM.complete hM.procOrder
    refine ⟨hH, H', hext, seqHist M, hM.legal, hEq, ?_⟩
    rintro a b ⟨h1, h2⟩
    obtain ⟨R, rfl, -, hwf⟩ := hext
    have hbc := completed_complete.1 h2
    have hbM := (mem_idsOf_iff_of_equiv hEq b).2 hbc
    have := (hwf.precedes_complete_iff hbc).1 h1
    exact rt_seqHist.2
      (hM.realtime a b (this.of_append_of_invoked (hM.recs.invoked hbM)) hbM)

/-- Original linearizability (Definition 2.2) in terms of a linearization list. -/
theorem linearizableHW_iff {spec : SeqSpec P X Op Res} {H : History P X Op Res} :
    LinearizableHW spec H ↔ WellFormed H ∧ ∃ M, IsLinO spec H M := by
  constructor
  · rintro ⟨hH, H', hext, S, hleg, hEq, hL2⟩
    obtain ⟨M, rfl⟩ := eq_seqHist_of_equiv_complete
      (by obtain ⟨_, _, _, h⟩ := hext; exact h) hEq hleg.1
    obtain ⟨hrecs, hcomp, hpo, -⟩ := lin_of_extension hext hEq
    exact ⟨hH, M, ⟨hrecs, hcomp, hleg, hpo⟩, fun a b h hb => rt_seqHist.1 (hL2 a b ⟨h, hb⟩)⟩
  · rintro ⟨hH, M, hM⟩
    obtain ⟨H', hext, hEq⟩ := exists_extension hH hM.recs hM.complete hM.procOrder
    exact ⟨hH, H', hext, seqHist M, hM.legal, hEq,
      fun a b h => rt_seqHist.2 (hM.realtime a b h.1 h.2)⟩

/-- Program order is a special case of the amended real-time condition, so `IsLinA` only needs
`recs`, `complete`, `legal` and `realtime` (the well-formedness argument is kept for
convenience of the callers). -/
theorem IsLinA.mk' {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    {M : List (OpRec P X Op Res)} (_hH : WellFormed H) (hrecs : Matches H M)
    (hcomplete : ∀ a, Completed H a → a ∈ idsOf M) (hlegal : Legal spec (seqHist M))
    (hrt : ∀ a b, Precedes H a b → b ∈ idsOf M → [a, b].Sublist (idsOf M)) :
    IsLinA spec H M :=
  ⟨⟨hrecs, hcomplete, hlegal, fun a b _ h hb => hrt a b h hb⟩, hrt⟩

theorem IsLinA.isLinO {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    {M : List (OpRec P X Op Res)} (h : IsLinA spec H M) : IsLinO spec H M :=
  ⟨h.toLinCore, fun a b hab hb => h.realtime a b hab (h.complete b hb)⟩

/-- Section 8: every history linearizable by the amended definition is linearizable by the
original one. -/
theorem Linearizable.linearizableHW {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (h : Linearizable spec H) : LinearizableHW spec H := by
  obtain ⟨hH, M, hM⟩ := linearizable_iff.1 h
  exact linearizableHW_iff.2 ⟨hH, M, hM.isLinO⟩

end Cslib.SharedMemory.HerlihyWing
