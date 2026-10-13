/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Equiv
public import Mathlib.Data.List.Nodup

/-!
# Amended linearizability is nonblocking

Theorem 5.2 of Sela–Herlihy–Petrank (Theorem 2 of Herlihy–Wing, for the amended definition).

## Main results

* `Linearizable.nonblocking`: if `H` is linearizable (Definition 4.1) and `inv p x o` is a
  pending invocation of a total operation, then some response `res p x r` can be appended so
  that the result is linearizable.
* `IsLinA.nonblocking`: the same, for linearization lists.

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- In a list of identities paired with records, an identity determines its record. -/
lemma zip_unique {α β : Type*} {l : List α} {M : List β} (hl : l.Nodup) {a : α} {e f : β}
    (he : (a, e) ∈ l.zip M) (hf : (a, f) ∈ l.zip M) : e = f := by
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
  obtain ⟨j, hj, hjf⟩ := List.mem_iff_getElem.1 hf
  simp only [List.getElem_zip, Prod.mk.injEq] at hie hjf
  have hij : i = j := by
    have := (List.Nodup.getElem_inj_iff hl (hi := by simp at hi; omega)
      (hj := by simp at hj; omega)).1 (hie.1.trans hjf.1.symm)
    exact this
  subst hij; exact hie.2.symm.trans hjf.2

lemma mem_idsOf_of_zip {M : List (OpRec P X Op Res)} {a : OpId P X} {e : OpRec P X Op Res}
    (h : (a, e) ∈ (idsOf M).zip M) : a ∈ idsOf M := (List.of_mem_zip h).1

/-- List form of Theorem 5.2. -/
theorem IsLinA.nonblocking {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    {M : List (OpRec P X Op Res)} (hH : WellFormed H) (hM : IsLinA spec H M) {p : P} {x : X}
    {o : Op} {N : List (OpRec P X Op Res)} (hpend : restrictP H p = seqHist N ++ [.inv p x o])
    (htot : Total spec p x o) :
    ∃ r M', WellFormed (H ++ [.res p x r]) ∧ IsLinA spec (H ++ [.res p x r]) M' := by
  set a : OpId P X := ⟨p, x, cnt N p x⟩ with ha_def
  obtain ⟨hai, hac, hao⟩ := PendingInv.spec hH hpend
  have hwf : ∀ r, WellFormed (H ++ [.res p x r]) :=
    fun r => wellFormed_concat_res.2 ⟨hH, N, o, hpend⟩
  have hres_len : (ressOf H p x).length = cnt N p x := by
    rw [ressOf_eq_restrictP, hpend, ressOf_append, List.length_append,
      length_ressOf_seqHist]; simp
  -- facts about the extended history
  have hops' : ∀ r b, opOf (H ++ [.res p x r]) b = opOf H b := by
    intro r b; simp [opOf]
  have hcomp' : ∀ r b, Completed (H ++ [.res p x r]) b ↔ Completed H b ∨ b = a := by
    intro r b
    rcases b with ⟨q, y, k⟩
    simp only [Completed, ressOf_append, ressOf_cons, Event.resOf_res, ressOf_nil,
      List.append_nil, List.length_append, ha_def, OpId.mk.injEq]
    by_cases hq : p = q ∧ x = y
    · obtain ⟨rfl, rfl⟩ := hq; simp only [and_self, ↓reduceIte, Option.toList_some,
        List.length_singleton, true_and, hres_len]; omega
    · have : ¬ (q = p ∧ y = x) := fun h => hq ⟨h.1.symm, h.2.symm⟩
      simp only [hq, ↓reduceIte, Option.toList_none, List.length_nil, add_zero]
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, rfl, -⟩)
        · exact h
        · exact absurd ⟨rfl, rfl⟩ this
  have hresOf' : ∀ r b, Completed H b → resOf (H ++ [.res p x r]) b = resOf H b :=
    fun r b hb => resOf_append_of_completed hb
  have hresa : ∀ r, resOf (H ++ [.res p x r]) a = some r := by
    intro r
    simp only [resOf, ressOf_append, ha_def, ressOf_cons, Event.resOf_res, and_self,
      ↓reduceIte, Option.toList_some, ressOf_nil, List.append_nil]
    rw [List.getElem?_append_right (by omega)]; simp [hres_len]
  have hprec' : ∀ r c b, Invoked H b → Precedes (H ++ [.res p x r]) c b → Precedes H c b :=
    fun r c b hb h => h.of_append_of_invoked hb
  by_cases hin : a ∈ idsOf M
  · -- the pending invocation is linearized: keep the same linearization
    obtain ⟨e, he⟩ := exists_mem_zip_idsOf hin
    refine ⟨e.r, M, hwf _, IsLinA.mk' (hwf _) ?_ ?_ hM.legal ?_⟩
    · intro b f hbf
      refine ⟨by rw [hops']; exact (hM.recs b f hbf).1, fun hb => ?_⟩
      rcases (hcomp' _ b).1 hb with hb | rfl
      · rw [hresOf' _ _ hb]; exact (hM.recs b f hbf).2 hb
      · rw [hresa, zip_unique (nodup_idsOf M) he hbf]
    · intro b hb
      rcases (hcomp' _ b).1 hb with hb | rfl
      · exact hM.complete b hb
      · exact hin
    · intro c b hcb hb
      exact hM.realtime c b (hprec' _ c b (hM.recs.invoked hb) hcb) hb
  · -- append the pending invocation, with a response given by totality
    have hcnt : cnt M p x = cnt N p x := by
      apply le_antisymm
      · by_contra hlt; push Not at hlt
        exact hin (mem_idsOf.2 hlt)
      · by_contra hlt; push Not at hlt
        have : (⟨p, x, cnt M p x⟩ : OpId P X) ∈ idsOf M :=
          hM.complete _ (by simp only [Completed]; omega)
        rw [mem_idsOf] at this; exact lt_irrefl _ this
    have hlegx := (legal_seqHist_iff spec M).1 hM.legal x
    obtain ⟨r, hr⟩ := htot (M.filter (·.x = x)) (by simp) hlegx
    set e : OpRec P X Op Res := ⟨p, x, o, r⟩ with he_def
    have hids : idsOf (M ++ [e]) = idsOf M ++ [a] := by
      rw [idsOf_concat, hcnt]
    refine ⟨r, M ++ [e], hwf r, IsLinA.mk' (hwf r) ?_ ?_ ?_ ?_⟩
    · intro b f hbf
      rw [hids, List.zip_append (by simp), List.mem_append] at hbf
      rcases hbf with hbf | hbf
      · refine ⟨by rw [hops']; exact (hM.recs b f hbf).1, fun hb => ?_⟩
        rcases (hcomp' _ b).1 hb with hb | rfl
        · rw [hresOf' _ _ hb]; exact (hM.recs b f hbf).2 hb
        · exact absurd (mem_idsOf_of_zip hbf) hin
      · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
          Prod.mk.injEq] at hbf
        obtain ⟨rfl, rfl⟩ := hbf
        exact ⟨by rw [hops']; exact hao, fun _ => hresa r⟩
    · intro b hb
      rw [hids]
      rcases (hcomp' _ b).1 hb with hb | rfl
      · exact List.mem_append_left _ (hM.complete b hb)
      · simp
    · rw [legal_seqHist_iff]
      intro y
      by_cases hy : x = y
      · subst hy; simpa [List.filter_append, he_def] using hr
      · have := (legal_seqHist_iff spec M).1 hM.legal y
        simpa [List.filter_append, he_def, hy] using this
    · intro c b hcb hb
      rw [hids] at hb ⊢
      rcases List.mem_append.1 hb with hb | hb
      · exact (hM.realtime c b (hprec' _ c b (hM.recs.invoked hb) hcb) hb).trans
          (List.sublist_append_left _ _)
      · rw [List.mem_singleton] at hb; subst hb
        have hc := (hprec' _ c a hai hcb).completed
        exact pair_sublist_iff.2 ⟨idsOf M, [a], rfl, hM.complete c hc, by simp⟩

/-- **Theorem 5.2** (Sela–Herlihy–Petrank; Herlihy–Wing Theorem 2) for the amended
definition: if `⟨x inv P⟩` is a pending invocation of a total operation in a linearizable
history `H`, then there is a response `⟨x res P⟩` such that `H · ⟨x res P⟩` is linearizable. -/
theorem Linearizable.nonblocking {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (h : Linearizable spec H) {p : P} {x : X} {o : Op} (hpend : PendingInv H p x o)
    (htot : Total spec p x o) : ∃ r, Linearizable spec (H ++ [.res p x r]) := by
  obtain ⟨hH, M, hM⟩ := linearizable_iff.1 h
  obtain ⟨N, hN⟩ := hpend
  obtain ⟨r, M', hwf, hM'⟩ := hM.nonblocking hH hN htot
  exact ⟨r, linearizable_iff.2 ⟨hwf, M', hM'⟩⟩

end Cslib.SharedMemory.HerlihyWing
