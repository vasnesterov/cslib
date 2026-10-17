/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.History

/-!
# General facts about linearizations

* `WellFormed.precedes_of_lt`: operations of one process are ordered in real time (program
  order).
* `IsLinearization.filter_proc`: in any linearization of a well-formed history, the instances
  of a process `p` appear in program order and form a prefix `(p,0), …, (p,m-1)` of its
  invoked operations, containing all completed ones.
* `IsLinearization.linState_eq`: if every operation of processes other than `c` is read-only,
  the abstract state reached by any linearization is the state reached by a prefix of `c`'s
  operations containing all completed ones.
* `IsLinearization.resp_eq`: in the same situation, the response of a completed operation of
  another process is the response it would get from a state reached by a prefix of `c`'s
  operations; if that operation started after `c`'s first `M₀` operations had returned, the
  prefix has length at least `M₀`.

These are the facts used by lower-bound proofs that schedule one "changer" process against
"readers".

-/

@[expose] public section

namespace Cslib.SharedMemory

open List

section ListLemmas

variable {X : Type}

lemma sublist_pair_iff {a b : X} {l : List X} :
    [a, b].Sublist l ↔ ∃ r₁ r₂, l = r₁ ++ r₂ ∧ a ∈ r₁ ∧ b ∈ r₂ := by
  rw [cons_sublist_iff]; simp [singleton_sublist]

/-- In a duplicate-free list, two elements cannot appear in both orders. -/
lemma not_sublist_pair_both {a b : X} {l : List X} (hl : l.Nodup) (h₁ : [a, b].Sublist l)
    (h₂ : [b, a].Sublist l) : False := by
  obtain ⟨r₁, r₂, rfl, ha, hb⟩ := sublist_pair_iff.1 h₁
  obtain ⟨s₁, s₂, hs, hb', ha'⟩ := sublist_pair_iff.1 h₂
  rcases append_eq_append_iff.1 hs with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · rw [nodup_append] at hl
    exact hl.2.2 a ha a (by simp [ha']) rfl
  · rw [nodup_append] at hl
    exact hl.2.2 b (by simp [hb']) b hb rfl

/-- If `a` comes before `x` in a duplicate-free list `l₁ ++ x :: l₂`, then `a ∈ l₁`. -/
lemma mem_left_of_sublist_pair {a x : X} {l₁ l₂ : List X} (hl : (l₁ ++ x :: l₂).Nodup)
    (h : [a, x].Sublist (l₁ ++ x :: l₂)) : a ∈ l₁ := by
  have ha : a ∈ l₁ ++ x :: l₂ := h.subset (by simp)
  rcases mem_append.1 ha with ha | ha
  · exact ha
  · exfalso
    rcases mem_cons.1 ha with rfl | ha
    · have := hl.sublist h; simp at this
    · apply not_sublist_pair_both hl h
      exact (cons_sublist_cons.2 (singleton_sublist.2 ha)).trans (sublist_append_right _ _)

/-- A duplicate-free, downward-closed list of naturals is a permutation of `range n`. -/
lemma mem_iff_lt_length_of_downClosed {l : List ℕ} (hl : l.Nodup)
    (hd : ∀ j ∈ l, ∀ j' < j, j' ∈ l) (j : ℕ) : j ∈ l ↔ j < l.length := by
  constructor
  · intro hj
    have : range (j + 1) ⊆ l := by
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 (mem_range.1 hk) with hk | rfl
      · exact hd j hj k hk
      · exact hj
    have := (nodup_range).length_le_of_subset this
    simp at this; omega
  · intro hj
    by_contra hn
    have : l ⊆ range j := by
      intro k hk
      rw [mem_range]
      by_contra hk'
      rcases Nat.lt_or_ge j k with h | h
      · exact hn (hd k hk j h)
      · exact hn (by rwa [show j = k by omega])
    have := hl.length_le_of_subset this
    simp at this; omega

lemma filterMap_getElem?_range (l : List X) (m : ℕ) :
    (range m).filterMap (fun j => l[j]?) = l.take m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_succ, filterMap_append, ih, take_add_one]
    cases h : l[m]? <;> simp [h]

end ListLemmas

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-! ## Program order -/

lemma exists_split_filterMap {X Y : Type} (f : X → Option Y) (l : List X) (k : ℕ)
    (hk : k < (l.filterMap f).length) :
    ∃ l₁ x l₂ y, l = l₁ ++ x :: l₂ ∧ f x = some y ∧ (l₁.filterMap f).length = k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    cases hx : f x with
    | none =>
      simp only [filterMap_cons, hx] at hk
      obtain ⟨l₁, x', l₂, y, rfl, h1, h2⟩ := ih k hk
      exact ⟨x :: l₁, x', l₂, y, rfl, h1, by simp [hx, h2]⟩
    | some y =>
      rcases k with _ | k
      · exact ⟨[], x, l, y, rfl, hx, rfl⟩
      · simp only [filterMap_cons, hx, length_cons] at hk
        obtain ⟨l₁, x', l₂, y', rfl, h1, h2⟩ := ih k (by omega)
        exact ⟨x :: l₁, x', l₂, y', rfl, h1, by simp [hx, h2]⟩

/-- Program order: in a well-formed history, an operation of `p` precedes (in real time) every
later invoked operation of `p`. -/
lemma WellFormed.precedes_of_lt {α : List (Label P A)} (hα : WellFormed α) {p : P}
    {j j' : ℕ} (hjj : j < j') (hinv : Invoked α (p, j')) : Precedes α (p, j) (p, j') := by
  obtain ⟨β, ℓ, γ, o, rfl, hℓ, hlen⟩ := exists_split_filterMap (Label.invOf p) α j' hinv
  have hwf := (hα β ℓ γ rfl p).1 (by simp [hℓ])
  refine ⟨β, ℓ :: γ, rfl, ?_, ?_⟩
  · simp only [Completed]; rw [← hwf]; exact hlen ▸ hjj
  · simp only [Invoked, not_lt]; exact (show (opsOf β p).length = j' from hlen).symm ▸ le_refl _

/-! ## Structure of linearizations -/

/-- Legality of a concatenation. -/
lemma seqOK_append {α : List (Label P A)} (q : A.State) (L₁ L₂ : List (OpId P × A.Op)) :
    SeqOK α q (L₁ ++ L₂) ↔ SeqOK α q L₁ ∧ SeqOK α (A.runOps q (L₁.map Prod.snd)) L₂ := by
  induction L₁ generalizing q with
  | nil => simp [SeqOK]
  | cons y L₁ ih =>
    obtain ⟨x, o⟩ := y
    simp only [cons_append, SeqOK, ih, map_cons, ObjSpec.runOps_cons, and_assoc]

namespace IsLinearization

variable {α : List (Label P A)} {L : List (OpId P × A.Op)}

lemma invoked_of_mem (hL : IsLinearization α L) {x : OpId P} (hx : x ∈ L.map Prod.fst) :
    Invoked α x := by
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  have := hL.op_eq y hy
  simp only [opOf] at this
  exact (List.getElem?_eq_some_iff.1 this).1

/-- Linearizations are closed under program-order predecessors. -/
lemma pred_sublist (hα : WellFormed α) (hL : IsLinearization α L) {p : P} {j j' : ℕ}
    (hj : (p, j) ∈ L.map Prod.fst) (hjj : j' < j) :
    [(p, j'), (p, j)].Sublist (L.map Prod.fst) :=
  hL.realtime _ _ (hα.precedes_of_lt hjj (hL.invoked_of_mem hj)) hj

/-- The instances of process `p` in a linearization. -/
def procIds (L : List (OpId P × A.Op)) (p : P) : List (OpId P) :=
  (L.map Prod.fst).filter (fun x => x.1 = p)

/-- In a linearization of a well-formed history, the instances of `p` are exactly
`(p,0), …, (p,m-1)` in this order. -/
lemma procIds_eq (hα : WellFormed α) (hL : IsLinearization α L) (p : P) :
    procIds L p = (range (procIds L p).length).map (fun j => (p, j)) := by
  set S := procIds L p with hS
  have hSsub : S.Sublist (L.map Prod.fst) := filter_sublist
  have hSnd : S.Nodup := hL.nodup.sublist hSsub
  have hfst : ∀ x ∈ S, x.1 = p := fun x hx => by simpa using (mem_filter.1 hx).2
  have hmemS : ∀ j, (p, j) ∈ S ↔ (p, j) ∈ L.map Prod.fst := fun j => by simp [hS, procIds]
  -- second components
  set T := S.map Prod.snd with hT
  have hST : ∀ j, (p, j) ∈ S ↔ j ∈ T := by
    intro j; constructor
    · intro h; exact mem_map.2 ⟨_, h, rfl⟩
    · intro h; obtain ⟨x, hx, rfl⟩ := mem_map.1 h
      have := hfst x hx; obtain ⟨x1, x2⟩ := x; simp only at this; subst this; exact hx
  have hTnd : T.Nodup := by
    refine hSnd.map_on ?_
    intro x hx y hy hxy
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    have h1 := hfst _ hx; have h2 := hfst _ hy
    simp_all
  have hTd : ∀ j ∈ T, ∀ j' < j, j' ∈ T := by
    intro j hj j' hj'
    rw [← hST, hmemS] at hj ⊢
    exact (hL.pred_sublist hα hj hj').subset (by simp)
  have hTlen : T.length = S.length := by simp [hT]
  have hpw : Pairwise (fun x y : OpId P => x.2 < y.2) S := by
    rw [pairwise_iff_forall_sublist]
    intro x y hxy
    have hx := hfst x (hxy.subset (by simp))
    have hy := hfst y (hxy.subset (by simp))
    rcases lt_trichotomy x.2 y.2 with h | h | h
    · exact h
    · exfalso
      have hxy' : x = y := Prod.ext (hx.trans hy.symm) h
      subst hxy'; have := hSnd.sublist hxy; simp at this
    · exfalso
      have h1 : [x, y].Sublist (L.map Prod.fst) := hxy.trans hSsub
      have ex : x = (p, x.2) := Prod.ext hx rfl
      have ey : y = (p, y.2) := Prod.ext hy rfl
      rw [ex, ey] at h1
      have h2 := hL.pred_sublist hα (h1.subset (by simp : (p, x.2) ∈ [(p, x.2), (p, y.2)])) h
      exact not_sublist_pair_both hL.nodup h1 h2
  apply Perm.eq_of_pairwise (le := fun x y : OpId P => x.2 < y.2)
  · intro a b _ _ h1 h2; omega
  · exact hpw
  · rw [pairwise_map]; exact (pairwise_lt_range).imp id
  · rw [perm_ext_iff_of_nodup hSnd ((nodup_range).map (fun a b h => by simpa using h))]
    intro x
    obtain ⟨x1, x2⟩ := x
    simp only [mem_map, mem_range, Prod.mk.injEq]
    constructor
    · intro hx
      have := hfst _ hx; simp only at this; subst this
      exact ⟨x2, by rw [← hTlen, ← mem_iff_lt_length_of_downClosed hTnd hTd, ← hST]; exact hx,
        rfl, rfl⟩
    · rintro ⟨j, hj, rfl, rfl⟩
      rw [hST, mem_iff_lt_length_of_downClosed hTnd hTd, hTlen]; exact hj

/-- The number of instances of `p` in a linearization is between the number of completed and
the number of invoked operations of `p`. -/
lemma procIds_length (hL : IsLinearization α L) (hα : WellFormed α) (p : P) :
    (respsOf α p).length ≤ (procIds L p).length ∧ (procIds L p).length ≤ (opsOf α p).length := by
  have heq := hL.procIds_eq hα p
  constructor
  · by_contra h
    push Not at h
    have hc : Completed α (p, (procIds L p).length) := h
    have := hL.complete _ hc
    have hm : (p, (procIds L p).length) ∈ procIds L p := mem_filter.2 ⟨this, by simp⟩
    rw [heq] at hm; simp at hm
  · rcases Nat.eq_zero_or_pos (procIds L p).length with h | h
    · rw [h]; exact Nat.zero_le _
    · have hm : (p, (procIds L p).length - 1) ∈ procIds L p := by
        rw [heq]; simp; omega
      have := hL.invoked_of_mem (mem_filter.1 hm).1
      simp only [Invoked] at this; omega

/-- The operations of the `p`-entries of `L` are `p`'s operations, in order. -/
lemma map_snd_filter_eq (hL : IsLinearization α L) (hα : WellFormed α) (p : P)
    (L₁ L₂ : List (OpId P × A.Op)) (hsplit : L = L₁ ++ L₂) :
    (L₁.filter (fun y => y.1.1 = p)).map Prod.snd =
      (opsOf α p).take (procIds L₁ p).length := by
  -- the ids of `L₁`'s `p`-entries form a prefix of `procIds L p`
  have hpre : procIds L₁ p <+: procIds L p := by
    rw [hsplit]; simp only [procIds, map_append, filter_append]; exact prefix_append _ _
  have hids : procIds L₁ p = (range (procIds L₁ p).length).map (fun j => (p, j)) := by
    have heq := hL.procIds_eq hα p
    obtain ⟨t, ht⟩ := hpre
    have : procIds L₁ p = (procIds L p).take (procIds L₁ p).length := by
      rw [← ht]; simp
    rw [this, heq, ← map_take, take_range]
    simp only [length_map, length_range]
  -- each entry's operation is given by `opOf`
  have hop : ∀ y ∈ L₁.filter (fun y => y.1.1 = p), opOf α y.1 = some y.2 :=
    fun y hy => hL.op_eq y (by rw [hsplit]; exact mem_append_left _ (mem_filter.1 hy).1)
  have h1 : (L₁.filter (fun y => y.1.1 = p)).map Prod.snd =
      ((L₁.filter (fun y => y.1.1 = p)).map Prod.fst).filterMap (opOf α) := by
    rw [filterMap_map]
    symm
    rw [filterMap_eq_map_iff_forall_eq_some]
    · intro y hy; exact hop y hy
  rw [h1]
  have h2 : (L₁.filter (fun y => y.1.1 = p)).map Prod.fst = procIds L₁ p := by
    simp only [procIds, filter_map]; rfl
  rw [h2, hids, filterMap_map]
  have : (opOf α ∘ fun j => (p, j)) = fun j => (opsOf α p)[j]? := by
    funext j; simp [opOf]
  rw [this, filterMap_getElem?_range, length_map, length_range]

/-- If all operations of processes other than `c` in `L` are read-only, the state after a prefix
`L₁` of `L` is the state after the first `|procIds L₁ c|` operations of `c`. -/
lemma runOps_prefix (hL : IsLinearization α L) (hα : WellFormed α) (c : P)
    (hro : ∀ y ∈ L, y.1.1 ≠ c → A.ReadOnly y.2) (L₁ L₂ : List (OpId P × A.Op))
    (hsplit : L = L₁ ++ L₂) (q : A.State) :
    A.runOps q (L₁.map Prod.snd) = A.runOps q ((opsOf α c).take (procIds L₁ c).length) := by
  rw [← hL.map_snd_filter_eq hα c L₁ L₂ hsplit, ObjSpec.runOps_map_filter]
  intro y hy hpr
  exact hro y (by rw [hsplit]; exact mem_append_left _ hy) (by simpa using hpr)

/-- **State of a linearization.** If all operations of processes other than `c` are read-only,
any linearization ends in the state reached by a prefix of `c`'s operations that contains all
completed ones. -/
theorem linState_eq (hL : IsLinearization α L) (hα : WellFormed α) (c : P)
    (hro : ∀ y ∈ L, y.1.1 ≠ c → A.ReadOnly y.2) :
    ∃ m, (respsOf α c).length ≤ m ∧ m ≤ (opsOf α c).length ∧
      linState L = A.runOps A.init ((opsOf α c).take m) :=
  ⟨_, (hL.procIds_length hα c).1, (hL.procIds_length hα c).2,
    hL.runOps_prefix hα c hro L [] (by simp) A.init⟩

/-- **Response of a reader.** If all operations of processes other than `c` are read-only, a
completed operation `x` of another process gets the response it would get after some prefix of
`c`'s operations; if `c`'s first `M₀` operations precede `x`, the prefix has length `≥ M₀`. -/
theorem resp_eq (hL : IsLinearization α L) (hα : WellFormed α) (c : P)
    (hro : ∀ y ∈ L, y.1.1 ≠ c → A.ReadOnly y.2) {x : OpId P} {r : A.Resp}
    (hx : respOf α x = some r) (M₀ : ℕ) (hpre : ∀ j < M₀, Precedes α (c, j) x) :
    ∃ j, M₀ ≤ j ∧ j ≤ (opsOf α c).length ∧ ∃ o, opOf α x = some o ∧
      r = (A.δ (A.runOps A.init ((opsOf α c).take j)) o).2 := by
  have hxc : Completed α x := by
    simp only [respOf] at hx; exact (List.getElem?_eq_some_iff.1 hx).1
  obtain ⟨y, hy, hyx⟩ := mem_map.1 (hL.complete x hxc)
  obtain ⟨L₁, L₂, hsplit⟩ := append_of_mem hy
  have hseq := (seqOK_append (α := α) A.init L₁ (y :: L₂)).1 (hsplit ▸ hL.seq)
  obtain ⟨x', o⟩ := y
  simp only at hyx; subst hyx
  have hr := hseq.2.1 r hx
  refine ⟨(procIds L₁ c).length, ?_, ?_, o, hL.op_eq _ hy, ?_⟩
  · rcases Nat.eq_zero_or_pos M₀ with h0 | h0
    · omega
    · have hp := hL.realtime _ _ (hpre (M₀ - 1) (by omega)) (mem_map.2 ⟨_, hy, rfl⟩)
      rw [hsplit, map_append, map_cons] at hp
      have hnd := hL.nodup; rw [hsplit, map_append, map_cons] at hnd
      have hm := mem_left_of_sublist_pair hnd hp
      have hm' : (c, M₀ - 1) ∈ procIds L₁ c := by simp [procIds, hm]
      have heq := hL.procIds_eq hα c
      have hpre' : procIds L₁ c <+: procIds L c := by
        rw [hsplit]; simp only [procIds, map_append, filter_append]; exact prefix_append _ _
      -- `procIds L₁ c` is a prefix of `(range m).map (c, ·)`, hence of the same form
      obtain ⟨t, ht⟩ := hpre'
      have hform : procIds L₁ c = (procIds L c).take (procIds L₁ c).length := by
        rw [← ht]; simp
      rw [hform, heq, ← map_take, take_range] at hm'
      simp only [mem_map, mem_range, Prod.mk.injEq, true_and, lt_min_iff] at hm'
      omega
  · have h1 : (procIds L₁ c).length ≤ (procIds L c).length := by
      simp only [procIds, hsplit, map_append, filter_append, length_append]; omega
    exact h1.trans (hL.procIds_length hα c).2
  · rw [← hr, hL.runOps_prefix hα c hro L₁ _ hsplit]

/-- Operations in a linearization are invoked operations. -/
lemma op_mem (hL : IsLinearization α L) {y : OpId P × A.Op} (hy : y ∈ L) : y.2 ∈ opsOf α y.1.1 := by
  have := hL.op_eq y hy
  simp only [opOf] at this
  exact mem_of_getElem? this

/-- If all operations of processes other than `c` are read-only and all of `c`'s operations have
returned, every linearization ends in the state reached by `c`'s operations. -/
lemma linState_of_changer (hL : IsLinearization α L) (hα : WellFormed α) (c : P)
    (hro : ∀ p, p ≠ c → ∀ o ∈ opsOf α p, A.ReadOnly o)
    (hcomp : (respsOf α c).length = (opsOf α c).length) :
    linState L = A.runOps A.init (opsOf α c) := by
  obtain ⟨m, h1, h2, h3⟩ := hL.linState_eq hα c (fun y hy hyc => hro _ hyc _ (hL.op_mem hy))
  rw [h3, show m = (opsOf α c).length by omega, take_length]

end IsLinearization

end Cslib.SharedMemory
