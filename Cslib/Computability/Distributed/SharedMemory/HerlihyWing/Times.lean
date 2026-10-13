/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.WellFormed
public import Mathlib.Data.Nat.Find

/-!
# Event times and real-time order

`tInv H a` (`tRes H a`) is the length of the shortest prefix of `H` in which `a` is invoked
(completed), i.e. one plus the position of the invocation (response) event of `a`; it is
`H.length + 1` if there is no such event.

## Main results

* `precedes_iff`: real-time order is a comparison of times.
* `tInv_inj`, `tRes_inj`, `tInv_lt_tRes`: times of distinct events are distinct, and an
  operation of a well-formed history is invoked before it responds.
* `not_precedes_self`, `Precedes.not_precedes`, `Precedes.trans`: real-time order in a
  well-formed history is a strict partial order; `precedes_or_precedes`: invoked operations of
  one process are totally ordered.
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

lemma Invoked.of_prefix {β H : History P X Op Res} {a : OpId P X} (h : β <+: H)
    (ha : Invoked β a) : Invoked H a := by
  obtain ⟨t, rfl⟩ := h; exact ha.mono

lemma Completed.of_prefix {β H : History P X Op Res} {a : OpId P X} (h : β <+: H)
    (ha : Completed β a) : Completed H a := by
  obtain ⟨t, rfl⟩ := h; exact ha.mono

omit [DecidableEq X] in
lemma WellFormed.take {H : History P X Op Res} (hH : WellFormed H) (n : ℕ) :
    WellFormed (H.take n) :=
  WellFormed.of_append (H' := H.drop n) (by simpa using hH)

/-- Time of the invocation of `a`: the length of the shortest prefix of `H` in which `a` is
invoked (`H.length + 1` if never). -/
def tInv (H : History P X Op Res) (a : OpId P X) : ℕ :=
  Nat.find (p := fun n => Invoked (H.take n) a ∨ H.length < n)
    ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩

/-- Time of the response of `a`: the length of the shortest prefix of `H` in which `a` is
completed (`H.length + 1` if never). -/
def tRes (H : History P X Op Res) (a : OpId P X) : ℕ :=
  Nat.find (p := fun n => Completed (H.take n) a ∨ H.length < n)
    ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩

lemma invoked_take_iff {H : History P X Op Res} {a : OpId P X} {n : ℕ} :
    Invoked (H.take n) a ↔ Invoked H a ∧ tInv H a ≤ n := by
  constructor
  · intro h
    exact ⟨h.of_prefix (List.take_prefix _ _), Nat.find_min' _ (Or.inl h)⟩
  · rintro ⟨hi, hle⟩
    rcases Nat.find_spec (p := fun n => Invoked (H.take n) a ∨ H.length < n)
      ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩ with h | h
    · exact h.of_prefix (List.take_prefix_take_left hle)
    · rw [List.take_of_length_le (by unfold tInv at hle; omega)]; exact hi

lemma completed_take_iff {H : History P X Op Res} {a : OpId P X} {n : ℕ} :
    Completed (H.take n) a ↔ Completed H a ∧ tRes H a ≤ n := by
  constructor
  · intro h
    exact ⟨h.of_prefix (List.take_prefix _ _), Nat.find_min' _ (Or.inl h)⟩
  · rintro ⟨hi, hle⟩
    rcases Nat.find_spec (p := fun n => Completed (H.take n) a ∨ H.length < n)
      ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩ with h | h
    · exact h.of_prefix (List.take_prefix_take_left hle)
    · rw [List.take_of_length_le (by unfold tRes at hle; omega)]; exact hi

lemma tInv_le_length {H : History P X Op Res} {a : OpId P X} (h : Invoked H a) :
    tInv H a ≤ H.length :=
  Nat.find_min' _ (Or.inl (by rw [List.take_of_length_le le_rfl]; exact h))

lemma tRes_le_length {H : History P X Op Res} {a : OpId P X} (h : Completed H a) :
    tRes H a ≤ H.length :=
  Nat.find_min' _ (Or.inl (by rw [List.take_of_length_le le_rfl]; exact h))

lemma length_lt_tInv {H : History P X Op Res} {a : OpId P X} (h : ¬ Invoked H a) :
    H.length < tInv H a := by
  rcases Nat.find_spec (p := fun n => Invoked (H.take n) a ∨ H.length < n)
    ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩ with h' | h'
  · exact absurd (h'.of_prefix (List.take_prefix _ _)) h
  · exact h'

lemma length_lt_tRes {H : History P X Op Res} {a : OpId P X} (h : ¬ Completed H a) :
    H.length < tRes H a := by
  rcases Nat.find_spec (p := fun n => Completed (H.take n) a ∨ H.length < n)
    ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩ with h' | h'
  · exact absurd (h'.of_prefix (List.take_prefix _ _)) h
  · exact h'

lemma invoked_iff_tInv_le {H : History P X Op Res} {a : OpId P X} :
    Invoked H a ↔ tInv H a ≤ H.length :=
  ⟨tInv_le_length, fun h => by by_contra h'; have := length_lt_tInv h'; omega⟩

lemma completed_iff_tRes_le {H : History P X Op Res} {a : OpId P X} :
    Completed H a ↔ tRes H a ≤ H.length :=
  ⟨tRes_le_length, fun h => by by_contra h'; have := length_lt_tRes h'; omega⟩

/-- Real-time order as a comparison of times. -/
lemma precedes_iff {H : History P X Op Res} {a b : OpId P X} :
    Precedes H a b ↔ Completed H a ∧ tRes H a < tInv H b := by
  constructor
  · rintro ⟨β, γ, rfl, hc, hni⟩
    have hβ : (β ++ γ).take β.length = β := by simp
    rw [← hβ] at hc hni
    rw [completed_take_iff] at hc
    rw [invoked_take_iff] at hni
    refine ⟨hc.1, ?_⟩
    by_cases hb : Invoked (β ++ γ) b
    · have := hc.2; have := not_and.1 hni hb; omega
    · have h3 := length_lt_tInv hb; have := hc.2; simp only [List.length_append] at h3; omega
  · rintro ⟨hc, hlt⟩
    refine ⟨H.take (tRes H a), H.drop (tRes H a), (List.take_append_drop _ _).symm, ?_, ?_⟩
    · exact completed_take_iff.2 ⟨hc, le_rfl⟩
    · rw [invoked_take_iff]; omega

lemma rt_iff {H : History P X Op Res} {a b : OpId P X} :
    RT H a b ↔ Completed H a ∧ Completed H b ∧ tRes H a < tInv H b := by
  simp only [RT, precedes_iff]; tauto

lemma tInv_pos (H : History P X Op Res) (a : OpId P X) : 0 < tInv H a := by
  by_contra h
  have h0 : tInv H a = 0 := by omega
  rcases Nat.find_spec (p := fun n => Invoked (H.take n) a ∨ H.length < n)
    ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩ with h' | h'
  · change Invoked (H.take (tInv H a)) a at h'
    rw [h0] at h'; simp [Invoked] at h'
  · change H.length < tInv H a at h'; omega

lemma tRes_pos (H : History P X Op Res) (a : OpId P X) : 0 < tRes H a := by
  by_contra h
  have h0 : tRes H a = 0 := by omega
  rcases Nat.find_spec (p := fun n => Completed (H.take n) a ∨ H.length < n)
    ⟨H.length + 1, Or.inr (Nat.lt_succ_self _)⟩ with h' | h'
  · change Completed (H.take (tRes H a)) a at h'
    rw [h0] at h'; simp [Completed] at h'
  · change H.length < tRes H a at h'; omega

lemma invOf_eq_some {e : Event P X Op Res} {p : P} {x : X} {o : Op} (h : e.invOf p x = some o) :
    e = .inv p x o := by
  cases e with
  | inv q y o' =>
    simp only [Event.invOf_inv, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl
  | res => simp at h

lemma resOf_eq_some {e : Event P X Op Res} {p : P} {x : X} {r : Res} (h : e.resOf p x = some r) :
    e = .res p x r := by
  cases e with
  | res q y r' =>
    simp only [Event.resOf_res, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl
  | inv => simp at h

/-- The event at time `tInv H a` is the invocation of `a`. -/
lemma tInv_spec {H : History P X Op Res} {a : OpId P X} (h : Invoked H a) :
    ∃ o, H[tInv H a - 1]? = some (.inv a.p a.x o) ∧
      (opsOf (H.take (tInv H a - 1)) a.p a.x).length = a.k := by
  obtain ⟨m, hm⟩ : ∃ m, tInv H a = m + 1 := ⟨tInv H a - 1, by have := tInv_pos H a; omega⟩
  have hle := tInv_le_length h
  have h1 : Invoked (H.take (m + 1)) a := invoked_take_iff.2 ⟨h, by omega⟩
  have h2 : ¬ Invoked (H.take m) a := by rw [invoked_take_iff]; omega
  rw [hm, Nat.add_sub_cancel]
  obtain ⟨e, he⟩ : ∃ e, H[m]? = some e := ⟨H[m], List.getElem?_eq_getElem (by omega)⟩
  rw [List.take_add_one, he] at h1
  simp only [Invoked, Option.toList_some, opsOf_append, opsOf_cons, opsOf_nil, List.append_nil,
    List.length_append] at h1 h2
  cases hi : e.invOf a.p a.x with
  | none => simp [hi] at h1; omega
  | some o =>
    simp [hi] at h1
    exact ⟨o, by rw [he, invOf_eq_some hi], by omega⟩

/-- The event at time `tRes H a` is the response of `a`. -/
lemma tRes_spec {H : History P X Op Res} {a : OpId P X} (h : Completed H a) :
    ∃ r, H[tRes H a - 1]? = some (.res a.p a.x r) ∧
      (ressOf (H.take (tRes H a - 1)) a.p a.x).length = a.k := by
  obtain ⟨m, hm⟩ : ∃ m, tRes H a = m + 1 := ⟨tRes H a - 1, by have := tRes_pos H a; omega⟩
  have hle := tRes_le_length h
  have h1 : Completed (H.take (m + 1)) a := completed_take_iff.2 ⟨h, by omega⟩
  have h2 : ¬ Completed (H.take m) a := by rw [completed_take_iff]; omega
  rw [hm, Nat.add_sub_cancel]
  obtain ⟨e, he⟩ : ∃ e, H[m]? = some e := ⟨H[m], List.getElem?_eq_getElem (by omega)⟩
  rw [List.take_add_one, he] at h1
  simp only [Completed, Option.toList_some, ressOf_append, ressOf_cons, ressOf_nil,
    List.append_nil, List.length_append] at h1 h2
  cases hi : e.resOf a.p a.x with
  | none => simp [hi] at h1; omega
  | some r =>
    simp [hi] at h1
    exact ⟨r, by rw [he, resOf_eq_some hi], by omega⟩

/-- Distinct invoked instances have distinct invocation times. -/
lemma tInv_inj {H : History P X Op Res} {a b : OpId P X} (ha : Invoked H a) (hb : Invoked H b)
    (h : tInv H a = tInv H b) : a = b := by
  obtain ⟨o, h1, h2⟩ := tInv_spec ha
  obtain ⟨o', h1', h2'⟩ := tInv_spec hb
  rw [h, h1'] at h1
  simp only [Option.some.injEq, Event.inv.injEq] at h1
  obtain ⟨hp, hx, -⟩ := h1
  rcases a with ⟨p, x, k⟩; rcases b with ⟨q, y, l⟩
  simp only at hp hx h2 h2'; subst hp hx
  rw [h] at h2; simp only [OpId.mk.injEq, true_and]; omega

lemma tRes_inj {H : History P X Op Res} {a b : OpId P X} (ha : Completed H a)
    (hb : Completed H b) (h : tRes H a = tRes H b) : a = b := by
  obtain ⟨o, h1, h2⟩ := tRes_spec ha
  obtain ⟨o', h1', h2'⟩ := tRes_spec hb
  rw [h, h1'] at h1
  simp only [Option.some.injEq, Event.res.injEq] at h1
  obtain ⟨hp, hx, -⟩ := h1
  rcases a with ⟨p, x, k⟩; rcases b with ⟨q, y, l⟩
  simp only at hp hx h2 h2'; subst hp hx
  rw [h] at h2; simp only [OpId.mk.injEq, true_and]; omega

lemma tInv_ne_tRes {H : History P X Op Res} {a b : OpId P X} (ha : Invoked H a)
    (hb : Completed H b) : tInv H a ≠ tRes H b := by
  intro h
  obtain ⟨o, h1, -⟩ := tInv_spec ha
  obtain ⟨r, h1', -⟩ := tRes_spec hb
  rw [h, h1'] at h1; simp at h1

lemma tInv_lt_tRes {H : History P X Op Res} (hH : WellFormed H) {a : OpId P X}
    (h : Completed H a) : tInv H a < tRes H a := by
  have hc : Completed (H.take (tRes H a)) a := completed_take_iff.2 ⟨h, le_rfl⟩
  have hi := (invoked_take_iff.1 ((hH.take _).invoked_of_completed hc))
  have := tInv_ne_tRes hi.1 h
  omega

/-- Program order: of two invoked instances of the same process, the one invoked first
completes before the other is invoked. -/
lemma precedes_of_tInv_lt {H : History P X Op Res} (hH : WellFormed H) {a b : OpId P X}
    (hp : a.p = b.p) (ha : Invoked H a) (hb : Invoked H b) (hlt : tInv H a < tInv H b) :
    Precedes H a b := by
  obtain ⟨o, h1, -⟩ := tInv_spec hb
  set m := tInv H b - 1 with hm
  have hpos := tInv_pos H b
  have hle := tInv_le_length hb
  have htake : H.take (m + 1) = H.take m ++ [.inv b.p b.x o] := by
    rw [List.take_add_one, h1]; rfl
  have hwf := hH.take (m + 1)
  rw [htake, wellFormed_concat_inv] at hwf
  obtain ⟨-, M, hM⟩ := hwf
  refine ⟨H.take m, H.drop m, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · have hi : Invoked (H.take m) a := invoked_take_iff.2 ⟨ha, by omega⟩
    simp only [Completed, Invoked] at hi ⊢
    rw [opsOf_eq_restrictP, hp, hM, length_opsOf_seqHist] at hi
    rw [ressOf_eq_restrictP, hp, hM, length_ressOf_seqHist]
    exact hi
  · rw [invoked_take_iff]; omega

lemma precedes_or_precedes {H : History P X Op Res} (hH : WellFormed H) {a b : OpId P X}
    (hp : a.p = b.p) (ha : Invoked H a) (hb : Invoked H b) (hne : a ≠ b) :
    Precedes H a b ∨ Precedes H b a := by
  rcases lt_trichotomy (tInv H a) (tInv H b) with h | h | h
  · exact Or.inl (precedes_of_tInv_lt hH hp ha hb h)
  · exact absurd (tInv_inj ha hb h) hne
  · exact Or.inr (precedes_of_tInv_lt hH hp.symm hb ha h)

lemma not_precedes_self {H : History P X Op Res} (hH : WellFormed H) (a : OpId P X) :
    ¬ Precedes H a a := by
  rw [precedes_iff]; rintro ⟨hc, hlt⟩; have := tInv_lt_tRes hH hc; omega

lemma Precedes.not_precedes {H : History P X Op Res} (hH : WellFormed H) {a b : OpId P X}
    (h : Precedes H a b) : ¬ Precedes H b a := by
  rw [precedes_iff] at h ⊢
  rintro ⟨hc, hlt⟩
  have := tInv_lt_tRes hH hc; have := tInv_lt_tRes hH h.1; omega

lemma Precedes.trans {H : History P X Op Res} (hH : WellFormed H) {a b c : OpId P X}
    (h1 : Precedes H a b) (h2 : Precedes H b c) : Precedes H a c := by
  rw [precedes_iff] at h1 h2 ⊢
  have := tInv_lt_tRes hH h2.1; exact ⟨h1.1, by omega⟩

/-- Times are unchanged by appending events. -/
lemma tInv_append {H H' : History P X Op Res} {a : OpId P X} (h : Invoked H a) :
    tInv (H ++ H') a = tInv H a := by
  have hle := tInv_le_length h
  apply le_antisymm
  · have : Invoked ((H ++ H').take (tInv H a)) a := by
      rw [List.take_append_of_le_length hle]; exact invoked_take_iff.2 ⟨h, le_rfl⟩
    exact (invoked_take_iff.1 this).2
  · have h' : Invoked (H ++ H') a := h.mono
    have hle' : tInv (H ++ H') a ≤ H.length := (invoked_take_iff.1 (by
      rw [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl]; exact h)).2
    have : Invoked ((H ++ H').take (tInv (H ++ H') a)) a := invoked_take_iff.2 ⟨h', le_rfl⟩
    rw [List.take_append_of_le_length hle'] at this
    exact (invoked_take_iff.1 this).2

lemma tRes_append {H H' : History P X Op Res} {a : OpId P X} (h : Completed H a) :
    tRes (H ++ H') a = tRes H a := by
  have hle := tRes_le_length h
  apply le_antisymm
  · have : Completed ((H ++ H').take (tRes H a)) a := by
      rw [List.take_append_of_le_length hle]; exact completed_take_iff.2 ⟨h, le_rfl⟩
    exact (completed_take_iff.1 this).2
  · have h' : Completed (H ++ H') a := h.mono
    have hle' : tRes (H ++ H') a ≤ H.length := (completed_take_iff.1 (by
      rw [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl]; exact h)).2
    have : Completed ((H ++ H').take (tRes (H ++ H') a)) a := completed_take_iff.2 ⟨h', le_rfl⟩
    rw [List.take_append_of_le_length hle'] at this
    exact (completed_take_iff.1 this).2

end Cslib.SharedMemory.HerlihyWing
