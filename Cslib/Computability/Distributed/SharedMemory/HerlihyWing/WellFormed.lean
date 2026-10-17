/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Basic
public import Mathlib.Data.List.Induction

/-!
# Sequential and well-formed histories

## Main results

* `isSeq_concat_inv`, `isSeq_concat_res`, `wellFormed_concat_inv`, `wellFormed_concat_res`:
  well-formedness, step by step.
* Counting consequences of well-formedness (`WellFormed.counts`,
  `WellFormed.invoked_of_completed`, pending invocations `WellFormed.pending_eq`,
  `WellFormed.pending_spec`).
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-! ### Sequential histories -/

omit [DecidableEq P] [DecidableEq X] in
lemma isSeq_nil : IsSeq ([] : History P X Op Res) := ⟨[], Or.inl rfl⟩

omit [DecidableEq P] [DecidableEq X] in
lemma isSeq_seqHist (M : List (OpRec P X Op Res)) : IsSeq (seqHist M) := ⟨M, Or.inl rfl⟩

omit [DecidableEq P] [DecidableEq X] in
lemma isSeq_concat_inv {s : History P X Op Res} {p : P} {x : X} {o : Op} :
    IsSeq (s ++ [.inv p x o]) ↔ ∃ M, s = seqHist M := by
  constructor
  · rintro ⟨M, h | ⟨p', x', o', h⟩⟩
    · exact absurd h.symm (seqHist_ne_concat_inv _ _ _ _ _)
    · exact ⟨M, (List.append_inj' h rfl).1⟩
  · rintro ⟨M, rfl⟩; exact ⟨M, Or.inr ⟨p, x, o, rfl⟩⟩

omit [DecidableEq P] [DecidableEq X] in
lemma isSeq_concat_res {s : History P X Op Res} {p : P} {x : X} {r : Res} :
    IsSeq (s ++ [.res p x r]) ↔ ∃ M o, s = seqHist M ++ [.inv p x o] := by
  constructor
  · rintro ⟨M, h | ⟨p', x', o', h⟩⟩
    · obtain ⟨M', o, -, h⟩ := seqHist_eq_concat_res h.symm
      exact ⟨M', o, h⟩
    · have := (List.append_inj' h rfl).2; simp at this
  · rintro ⟨M, o, rfl⟩
    exact ⟨M ++ [⟨p, x, o, r⟩], Or.inl (by simp)⟩

omit [DecidableEq P] [DecidableEq X] in
lemma IsSeq.of_concat {s : History P X Op Res} {e : Event P X Op Res} (h : IsSeq (s ++ [e])) :
    IsSeq s := by
  cases e with
  | inv p x o => obtain ⟨M, rfl⟩ := isSeq_concat_inv.1 h; exact isSeq_seqHist M
  | res p x r =>
    obtain ⟨M, o, rfl⟩ := isSeq_concat_res.1 h; exact ⟨M, Or.inr ⟨p, x, o, rfl⟩⟩

/-! ### Well-formed histories -/

omit [DecidableEq X] in
lemma restrictP_concat (H : History P X Op Res) (e : Event P X Op Res) (p : P) :
    restrictP (H ++ [e]) p = restrictP H p ++ (if e.proc = p then [e] else []) := by
  simp [restrictP_singleton]

omit [DecidableEq X] in
lemma wellFormed_nil : WellFormed ([] : History P X Op Res) := fun _ => isSeq_nil

omit [DecidableEq X] in
lemma WellFormed.of_concat {H : History P X Op Res} {e : Event P X Op Res}
    (h : WellFormed (H ++ [e])) : WellFormed H := by
  intro q
  have := h q
  rw [restrictP_concat] at this
  split_ifs at this
  · exact this.of_concat
  · simpa using this

omit [DecidableEq X] in
lemma WellFormed.of_append {H H' : History P X Op Res} (h : WellFormed (H ++ H')) :
    WellFormed H := by
  induction H' using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton H' e ih =>
    exact ih (WellFormed.of_concat (e := e) (by simpa using h))

omit [DecidableEq X] in
lemma wellFormed_concat_inv {H : History P X Op Res} {p : P} {x : X} {o : Op} :
    WellFormed (H ++ [.inv p x o]) ↔ WellFormed H ∧ ∃ M, restrictP H p = seqHist M := by
  constructor
  · intro h
    refine ⟨h.of_concat, ?_⟩
    have := h p
    rw [restrictP_concat] at this
    simpa using isSeq_concat_inv.1 (by simpa using this)
  · rintro ⟨hH, M, hM⟩ q
    rw [restrictP_concat]
    by_cases hq : p = q
    · subst hq; simp only [Event.proc_inv, ↓reduceIte, hM]; exact isSeq_concat_inv.2 ⟨M, rfl⟩
    · simp [hq, hH q]

omit [DecidableEq X] in
lemma wellFormed_concat_res {H : History P X Op Res} {p : P} {x : X} {r : Res} :
    WellFormed (H ++ [.res p x r]) ↔
      WellFormed H ∧ ∃ M o, restrictP H p = seqHist M ++ [.inv p x o] := by
  constructor
  · intro h
    refine ⟨h.of_concat, ?_⟩
    have := h p
    rw [restrictP_concat] at this
    simpa using isSeq_concat_res.1 (by simpa using this)
  · rintro ⟨hH, M, o, hM⟩ q
    rw [restrictP_concat]
    by_cases hq : p = q
    · subst hq; simp only [Event.proc_res, ↓reduceIte, hM]; exact isSeq_concat_res.2 ⟨M, o, rfl⟩
    · simp [hq, hH q]

omit [DecidableEq X] in
/-- All records of the process subhistory of `p` belong to `p`. -/
lemma restrictP_eq_seqHist_proc {H : History P X Op Res} {p : P} {M : List (OpRec P X Op Res)}
    {t : History P X Op Res} (h : restrictP H p = seqHist M ++ t) : ∀ e ∈ M, e.p = p := by
  intro e he
  have : Event.inv e.p e.x e.o ∈ restrictP H p := by
    rw [h]; exact List.mem_append_left _ (List.mem_flatMap.2 ⟨e, he, by simp [OpRec.events]⟩)
  exact of_decide_eq_true (List.mem_filter.1 this).2

omit [DecidableEq X] in
/-- The structure of a process subhistory of a well-formed history. -/
lemma WellFormed.restrictP_eq {H : History P X Op Res} (hH : WellFormed H) (p : P) :
    ∃ M : List (OpRec P X Op Res), (∀ e ∈ M, e.p = p) ∧
      (restrictP H p = seqHist M ∨ ∃ x o, restrictP H p = seqHist M ++ [.inv p x o]) := by
  obtain ⟨M, h | ⟨q, x, o, h⟩⟩ := hH p
  · exact ⟨M, restrictP_eq_seqHist_proc (t := []) (by simpa using h), Or.inl h⟩
  · have hq : q = p := by
      have : Event.inv q x o ∈ restrictP H p := by rw [h]; simp
      exact of_decide_eq_true (List.mem_filter.1 this).2
    subst hq
    exact ⟨M, restrictP_eq_seqHist_proc h, Or.inr ⟨x, o, h⟩⟩

lemma opsOf_eq_restrictP (H : History P X Op Res) (p : P) (x : X) :
    opsOf H p x = opsOf (restrictP H p) p x := by simp

lemma ressOf_eq_restrictP (H : History P X Op Res) (p : P) (x : X) :
    ressOf H p x = ressOf (restrictP H p) p x := by simp

/-- Counting form of well-formedness: for each process, either all its operations completed,
or exactly one (on object `y`, the `cnt M p y`-th one) is pending. -/
lemma WellFormed.counts {H : History P X Op Res} (hH : WellFormed H) (p : P) :
    ∃ M : List (OpRec P X Op Res),
      ((∀ x, opsOf H p x = (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).map (·.o) ∧
          ressOf H p x = (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).map (·.r)) ∨
       ∃ y o, restrictP H p = seqHist M ++ [.inv p y o] ∧
         (∀ x, opsOf H p x =
              (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).map (·.o) ++
                (if y = x then [o] else []) ∧
            ressOf H p x =
              (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).map (·.r))) := by
  obtain ⟨M, -, h | ⟨y, o, h⟩⟩ := hH.restrictP_eq p
  · refine ⟨M, Or.inl fun x => ?_⟩
    rw [opsOf_eq_restrictP, ressOf_eq_restrictP, h, opsOf_seqHist, ressOf_seqHist]
    exact ⟨rfl, rfl⟩
  · refine ⟨M, Or.inr ⟨y, o, h, fun x => ?_⟩⟩
    rw [opsOf_eq_restrictP, ressOf_eq_restrictP, h, opsOf_append, ressOf_append, opsOf_seqHist,
      ressOf_seqHist]
    by_cases hy : y = x <;> simp [opsOf, ressOf, hy]

lemma WellFormed.length_ressOf_le {H : History P X Op Res} (hH : WellFormed H) (p : P) (x : X) :
    (ressOf H p x).length ≤ (opsOf H p x).length := by
  obtain ⟨M, h | ⟨y, o, -, h⟩⟩ := hH.counts p
  · rw [(h x).1, (h x).2]; simp
  · rw [(h x).1, (h x).2]; simp

lemma WellFormed.length_opsOf_le {H : History P X Op Res} (hH : WellFormed H) (p : P) (x : X) :
    (opsOf H p x).length ≤ (ressOf H p x).length + 1 := by
  obtain ⟨M, h | ⟨y, o, -, h⟩⟩ := hH.counts p
  · rw [(h x).1, (h x).2]; simp
  · rw [(h x).1, (h x).2]; split_ifs <;> simp

lemma WellFormed.invoked_of_completed {H : History P X Op Res} (hH : WellFormed H)
    {a : OpId P X} (h : Completed H a) : Invoked H a :=
  lt_of_lt_of_le h (hH.length_ressOf_le _ _)

/-- A pending instance of a well-formed history is the last event of its process. -/
lemma WellFormed.pending_spec {H : History P X Op Res} (hH : WellFormed H) {a : OpId P X}
    (hi : Invoked H a) (hc : ¬ Completed H a) :
    ∃ M o, restrictP H a.p = seqHist M ++ [.inv a.p a.x o] ∧ a.k = cnt M a.p a.x ∧
      opOf H a = some o ∧ (∀ x, (ressOf H a.p x).length = cnt M a.p x) := by
  obtain ⟨M, h | ⟨y, o, hM, h⟩⟩ := hH.counts a.p
  · exfalso; apply hc
    simp only [Invoked, Completed, (h a.x).1, (h a.x).2, List.length_map] at hi ⊢; exact hi
  · have hlen := (h a.x)
    simp only [Invoked, Completed, hlen.1, hlen.2, List.length_append, List.length_map] at hi hc
    have hy : y = a.x := by by_contra hy; simp [hy] at hi; omega
    subst hy
    simp only [↓reduceIte, List.length_singleton] at hi
    have hk : a.k = cnt M a.p a.x := by rw [cnt_eq_length]; omega
    refine ⟨M, o, hM, hk, ?_, fun x => by rw [(h x).2]; simp [cnt_eq_length]⟩
    simp only [opOf, hlen.1, ↓reduceIte]
    rw [List.getElem?_append_right (by simp; omega)]
    simp [hk, cnt_eq_length]

/-- Each process has at most one pending invocation. -/
lemma WellFormed.pending_eq {H : History P X Op Res} (hH : WellFormed H) {a b : OpId P X}
    (hia : Invoked H a) (hca : ¬ Completed H a) (hib : Invoked H b) (hcb : ¬ Completed H b)
    (hp : a.p = b.p) : a = b := by
  obtain ⟨M, o, hM, hk, -⟩ := hH.pending_spec hia hca
  obtain ⟨M', o', hM', hk', -⟩ := hH.pending_spec hib hcb
  rcases a with ⟨p, x, k⟩; rcases b with ⟨q, y, l⟩
  simp only at hp hM hM' hk hk'; subst hp
  rw [hM] at hM'
  obtain ⟨h1, h2⟩ := List.append_inj' hM' rfl
  have := seqHist_injective h1; subst this
  simp only [List.cons.injEq, Event.inv.injEq, true_and, and_true] at h2
  obtain ⟨rfl, -⟩ := h2
  simp [hk, hk']

/-- The pending invocation of a process, in terms of `PendingInv`. -/
lemma PendingInv.spec {H : History P X Op Res} (_hH : WellFormed H) {p : P} {x : X} {o : Op}
    {M : List (OpRec P X Op Res)} (h : restrictP H p = seqHist M ++ [.inv p x o]) :
    Invoked H ⟨p, x, cnt M p x⟩ ∧ ¬ Completed H ⟨p, x, cnt M p x⟩ ∧
      opOf H ⟨p, x, cnt M p x⟩ = some o := by
  have hops : opsOf H p x = opsOf (seqHist M) p x ++ [o] := by
    rw [opsOf_eq_restrictP, h]; simp [opsOf]
  have hres : ressOf H p x = ressOf (seqHist M) p x := by
    rw [ressOf_eq_restrictP, h]; simp [ressOf]
  refine ⟨?_, ?_, ?_⟩
  · simp [Invoked, hops, length_opsOf_seqHist]
  · simp [Completed, hres, length_ressOf_seqHist]
  · simp only [opOf, hops]
    rw [List.getElem?_append_right (by simp [length_opsOf_seqHist])]
    simp [length_opsOf_seqHist]

end Cslib.SharedMemory.HerlihyWing
