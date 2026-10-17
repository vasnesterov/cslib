/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Building linearizations incrementally (linearization points)

Lemmas to maintain a linearization `L` of a growing execution `α`:

* `IsLinearization.append_inv` / `append_tau`: invocations and internal steps keep `L` a
  linearization;
* `IsLinearization.push`: a pending, not yet linearized operation can be appended to `L` (its
  *linearization point*);
* `IsLinearization.append_ret`: a response keeps `L` a linearization if the returning operation
  is already in `L` and the specification gives it this response at its position in `L`.

-/

@[expose] public section

namespace Cslib.SharedMemory

open List

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- `SeqOK` only depends on the responses of the listed instances. -/
lemma seqOK_congr {α α' : List (Label P A)} (q : A.State) (L : List (OpId P × A.Op))
    (h : ∀ y ∈ L, respOf α y.1 = respOf α' y.1) : SeqOK α q L ↔ SeqOK α' q L := by
  induction L generalizing q with
  | nil => simp [SeqOK]
  | cons y L ih =>
    obtain ⟨x, o⟩ := y
    simp only [SeqOK]
    rw [h (x, o) (by simp), ih _ (fun y hy => h y (by simp [hy]))]

lemma completed_iff_respOf {α : List (Label P A)} {x : OpId P} :
    Completed α x ↔ (respOf α x).isSome := by
  simp [Completed, respOf]

lemma respOf_append_ret (α : List (Label P A)) (p : P) (r : A.Resp) (y : OpId P) :
    respOf (α ++ [.ret p r]) y =
      if y = (p, (respsOf α p).length) then some r else respOf α y := by
  obtain ⟨q, k⟩ := y
  simp only [respOf, respsOf_append, respsOf_cons, Label.retOf_ret, respsOf_nil, append_nil,
    Prod.mk.injEq]
  by_cases hq : p = q
  · subst hq
    simp only [ite_true, Option.toList_some, true_and]
    rcases lt_trichotomy k (respsOf α p).length with h | rfl | h
    · rw [getElem?_append_left h, ite_eq_right (by omega)]
    · simp
    · rw [ite_eq_right (by omega), getElem?_eq_none (by simp; omega), getElem?_eq_none (by omega)]
  · simp [hq, Ne.symm hq]

namespace IsLinearization

variable {α : List (Label P A)} {L : List (OpId P × A.Op)}

lemma mem_invoked (hL : IsLinearization α L) {x : OpId P} (hx : x ∈ L.map Prod.fst) :
    Invoked α x := hL.invoked_of_mem hx

/-- Appending a label that does not change the history of instances in `L` and creates no new
completed instance. -/
lemma append_of_hist {ℓ : Label P A} (hL : IsLinearization α L)
    (hops : ∀ x, Invoked α x → opOf (α ++ [ℓ]) x = opOf α x)
    (hresp : ∀ x, respOf (α ++ [ℓ]) x = respOf α x) :
    IsLinearization (α ++ [ℓ]) L where
  nodup := hL.nodup
  op_eq y hy := by rw [hops _ (hL.mem_invoked (mem_map.2 ⟨y, hy, rfl⟩))]; exact hL.op_eq y hy
  complete a ha := by
    apply hL.complete
    rw [completed_iff_respOf, ← hresp a]; exact completed_iff_respOf.1 ha
  realtime a b hab hb := hL.realtime a b (hab.of_append_of_invoked (hL.mem_invoked hb)) hb
  seq := (seqOK_congr _ _ (fun y _ => hresp y.1)).2 hL.seq

lemma append_inv (hL : IsLinearization α L) (p : P) (o : A.Op) :
    IsLinearization (α ++ [.inv p o]) L :=
  hL.append_of_hist (fun _ hx => opOf_append_of_invoked hx)
    (fun x => by simp [respOf, respsOf_append])

lemma append_tau (hL : IsLinearization α L) (p : P) :
    IsLinearization (α ++ [.tau p]) L :=
  hL.append_of_hist (fun _ hx => opOf_append_of_invoked hx)
    (fun x => by simp [respOf, respsOf_append])

/-- A linearization point: a pending instance not yet in `L` can be appended to `L`. -/
lemma push (hL : IsLinearization α L) {x : OpId P} {o : A.Op} (hx : opOf α x = some o)
    (hxL : x ∉ L.map Prod.fst) (hxc : ¬ Completed α x) :
    IsLinearization α (L ++ [(x, o)]) where
  nodup := by
    rw [map_append, nodup_append]
    exact ⟨hL.nodup, by simp, by
      simp only [map_cons, map_nil, mem_singleton]; rintro a ha b rfl rfl; exact hxL ha⟩
  op_eq y hy := by
    rcases mem_append.1 hy with hy | hy
    · exact hL.op_eq y hy
    · simp only [mem_cons, not_mem_nil, or_false] at hy; subst hy; exact hx
  complete a ha := by rw [map_append]; exact mem_append_left _ (hL.complete a ha)
  realtime a b hab hb := by
    rw [map_append] at hb ⊢
    rcases mem_append.1 hb with hb | hb
    · exact (hL.realtime a b hab hb).trans (sublist_append_left _ _)
    · simp only [map_cons, map_nil, mem_cons, not_mem_nil, or_false] at hb; subst hb
      have ha := hL.complete a hab.completed
      exact sublist_pair_iff.2 ⟨L.map Prod.fst, [(b, o)].map Prod.fst, rfl, ha, by simp⟩
  seq := by
    rw [seqOK_append]
    refine ⟨hL.seq, ?_, trivial⟩
    intro r hr
    exact absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc

/-- A response: the returning instance `(p, k)` (`k` = number of earlier responses of `p`) must
already be linearized, and the specification must give it response `r` at its position. -/
lemma append_ret (hL : IsLinearization α L) {p : P} {r : A.Resp}
    (L₁ L₂ : List (OpId P × A.Op)) (o : A.Op)
    (hsplit : L = L₁ ++ ((p, (respsOf α p).length), o) :: L₂)
    (hr : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = r) :
    IsLinearization (α ++ [.ret p r]) L := by
  set x : OpId P := (p, (respsOf α p).length) with hx
  have hnd := hL.nodup
  rw [hsplit, map_append, map_cons, nodup_append] at hnd
  have hx1 : x ∉ L₁.map Prod.fst := fun h => hnd.2.2 x h x (by simp) rfl
  have hx2 : x ∉ L₂.map Prod.fst := (nodup_cons.1 hnd.2.1).1
  have hxL : x ∈ L.map Prod.fst := by rw [hsplit]; simp
  have hresp : ∀ y, y ≠ x → respOf (α ++ [.ret p r]) y = respOf α y := by
    intro y hy; rw [respOf_append_ret, ite_eq_right hy]
  have hopsx : ∀ y, opOf (α ++ [.ret p r]) y = opOf α y := by
    intro y; simp [opOf, opsOf_append]
  refine ⟨hL.nodup, fun y hy => by rw [hopsx]; exact hL.op_eq y hy, ?_, ?_, ?_⟩
  · intro a ha
    by_cases hax : a = x
    · rw [hax]; exact hxL
    · apply hL.complete
      rw [completed_iff_respOf, ← hresp a hax]; exact completed_iff_respOf.1 ha
  · intro a b hab hb
    exact hL.realtime a b (hab.of_append_of_invoked (hL.mem_invoked hb)) hb
  · have hseq := hL.seq
    rw [hsplit, seqOK_append] at hseq ⊢
    have hc1 : ∀ y ∈ L₁, respOf (α ++ [.ret p r]) y.1 = respOf α y.1 :=
      fun y hy => hresp _ (fun h => hx1 (h ▸ mem_map.2 ⟨y, hy, rfl⟩))
    have hc2 : ∀ y ∈ L₂, respOf (α ++ [.ret p r]) y.1 = respOf α y.1 :=
      fun y hy => hresp _ (fun h => hx2 (h ▸ mem_map.2 ⟨y, hy, rfl⟩))
    refine ⟨(seqOK_congr _ _ hc1).2 hseq.1, ?_, (seqOK_congr _ _ hc2).2 hseq.2.2⟩
    intro r' hr'
    rw [respOf_append_ret, ite_eq_left rfl] at hr'
    cases hr'; exact hr

end IsLinearization

end Cslib.SharedMemory
