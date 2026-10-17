/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Quorum arithmetic and vote counting

Fault-tolerant protocols for `n` processes with at most `f` faulty ones argue with *quorums*: sets
of processes large enough that any two of them, or any one of them and the set of correct
processes, share a (correct) member. Every such argument is an instance of the inclusion–exclusion
bound `#s + #t ≤ #(s ∩ t) + n` together with "a set larger than the faulty set has a correct
member". This file states these facts once, over `[Fintype α]` (`n = Fintype.card α`) and a
faulty set `F : Finset α` (or `B : Set α`, for models that keep the Byzantine processes in a set).

## Main statements

* `Finset.card_add_card_le_card_inter_add_card_univ`: `#s + #t ≤ #(s ∩ t) + n`.
* `Finset.exists_mem_notMem_of_card_le_of_lt`: a set with more than `f ≥ #F` members has a member
  outside `F`.
* `Finset.exists_mem_inter_notMem_of_card_le`: two sets with `#s + #t > n + f` share a member
  outside `F`.
* `Set.ncard` variants for a faulty set `B : Set α`: `Finset.card_filter_mem_le_ncard`,
  `Finset.exists_mem_notMem_of_ncard_le_of_lt`, `Finset.exists_mem_inter_notMem_of_ncard_le`.
* Threshold regimes (namespace `Cslib.Quorum`): `exists_mem_inter_notMem_of_quorum`
  (`Q`-quorums, `n + f < 2Q`), `exists_mem_inter_notMem_of_three_mul_lt` (`(n - f)`-quorums,
  `3f < n`), `inter_nonempty_of_two_mul_lt` (`(n - f)`-quorums, `2f < n`),
  `inter_nonempty_of_card_le_four_mul_add_one` (`(2f + 1)`-quorums, `n ≤ 4f + 1`),
  `card_sub_two_mul_le_card_inter` (`(n - f)`-quorums meet in `n - 2f` members).

## Vote counting

Voting steps of fault-tolerant protocols count how many members of a set `s` (the processes heard
from, the received messages, …) report a value `b`, and select a value reported often enough.

* `Finset.countEq s f b`: the number of `a ∈ s` with `f a = b`.
* `Finset.threshold? s f k`: some value `b` reported (as `some b`) by at least `k` members of `s`,
  or `none` if there is none. Votes are `Option`-valued: `none` is "no vote".
* `Finset.majority? s f`: the value reported by a strict majority of `s`, if any
  (`= threshold? s f (#s / 2 + 1)`).
* `Finset.plurality s f d`: a most frequent value of `f` on `s` (`d` if `s = ∅`).

Main statements about them:

* `Finset.countEq_add_countEq_le`, `Finset.eq_of_card_lt_countEq_add_countEq`: two distinct
  values are reported by at most `#s` members together; two "heavy" values coincide.
* `Finset.exists_mem_notMem_of_card_lt_countEq`: a value reported more than `#F` times is reported
  by a member outside `F`.
* `Finset.majority?_eq_of_notMem`: if the members outside `F` are a strict majority of `s` and
  all report `o`, the majority value is `o`.
* `Finset.plurality_eq_of_card_lt_two_mul_countEq`: a strict-majority value is the plurality.
* `Finset.find?_map_eq_threshold?`, `Finset.find?_map_eq_majority?`: the computable "first
  candidate above the threshold" scan of a protocol computes `threshold?` / `majority?`.

## Correct members and honest votes

A fault-tolerant protocol with a faulty set `F` (a `Finset α`, or a `B : Set α` bounded through
`Set.ncard`) constantly uses that

* at least `n - #F` processes are correct, and a set `s` has at least `#s - #F` correct members;
* a received vector `f` that agrees with the true values `g` on the correct senders counts every
  value `b` at least as often as the correct holders of `b`, and at most `#F` more often.

Main statements:

* `Finset.card_filter_notMem_univ`: `#{x | x ∉ F} = n - #F`;
  `Finset.card_sub_le_card_filter_notMem`: `n - f ≤ #{x | x ∉ F}` for `#F ≤ f`;
  `Finset.card_sub_card_le_card_filter_notMem`: `#s - #F ≤ #{x ∈ s | x ∉ F}`;
  `Finset.card_sub_card_le_of_forall_notMem`: a set containing every correct process (or,
  `Finset.card_sub_card_le_of_injective_of_forall_notMem`, the identifiers of every correct
  process) has at least `n - #F` members.
* `Set.ncard` versions for a faulty set `B : Set α`: `Finset.card_sub_ncard_le_card_filter_notMem`,
  `Finset.card_sub_le_card_filter_notMem_of_ncard_le`.
* `Finset.countEq_congr`, `Finset.countEq_eq_card`: congruence and the "everybody votes `b`" count.
* `Finset.card_sub_card_le_countEq` (and `Finset.card_sub_ncard_le_countEq`): if every correct
  member of `s` reports `b`, then `b` is reported at least `#s - #F` times.
* `Finset.card_filter_notMem_and_le_countEq`, `Finset.countEq_le_card_filter_notMem_and_add_card`:
  the count of `b` in a received vector agreeing with the truth on correct senders is between the
  number of correct holders of `b` and that number plus `#F`.
* `Finset.countEq_sub_card_le_countEq` (and `Finset.countEq_sub_ncard_le_countEq`): two vectors
  that agree on the correct members of `s` have counts differing by at most `#F`.
* `Finset.exists_sum_card_filter_exists_ne_zero_le`: double counting of sender–receiver pairs that
  ever exchange a message, against the number of messages sent up to some finite time.
* `Finset.pluralityMin s f d`: the *smallest* most frequent value (a deterministic, computable
  `Finset.plurality` for linearly ordered values), with `countEq_le_countEq_pluralityMin`,
  `pluralityMin_eq_of_card_lt_two_mul_countEq` and `pluralityMin_congr` (it only depends on the
  values on `s`).
-/

@[expose] public section

namespace Finset

variable {α : Type*} [DecidableEq α] {s t u F : Finset α} {f q : ℕ}

/-! ### Inclusion–exclusion -/

/-- Two subsets of `u` exceed `u` by at most their intersection: `#s + #t ≤ #(s ∩ t) + #u`. -/
theorem card_add_card_le_card_inter_add_card_of_subset (hs : s ⊆ u) (ht : t ⊆ u) :
    #s + #t ≤ #(s ∩ t) + #u := by
  have h₁ := card_union_add_card_inter s t
  have h₂ := card_le_card (union_subset hs ht)
  omega

omit [DecidableEq α] in
/-- A set with more than `f` members has a member outside any `F` with `#F ≤ f`. -/
theorem exists_mem_notMem_of_card_le_of_lt (hF : #F ≤ f) (hs : f < #s) : ∃ a ∈ s, a ∉ F :=
  exists_mem_notMem_of_card_lt_card (hF.trans_lt hs)

/-! ### Faulty sets given as `Set`s -/

section Finite

variable [Finite α]

omit [DecidableEq α] in
/-- The members of `s` in `B` are at most `B.ncard`. -/
theorem card_filter_mem_le_ncard (B : Set α) [DecidablePred (· ∈ B)] (s : Finset α) :
    #{a ∈ s | a ∈ B} ≤ B.ncard := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun a ha => (mem_filter.1 ha).2)

omit [DecidableEq α] in
/-- A set with more than `f` members has a member outside any `B : Set α` with `B.ncard ≤ f`. -/
theorem exists_mem_notMem_of_ncard_le_of_lt {B : Set α} (hB : B.ncard ≤ f) (hs : f < #s) :
    ∃ a ∈ s, a ∉ B := by
  classical
  have := card_filter_mem_le_ncard B s
  obtain ⟨a, ha, haB⟩ := exists_mem_notMem_of_card_le_of_lt (F := {a ∈ s | a ∈ B}) le_rfl
    (show #{a ∈ s | a ∈ B} < #s by omega)
  exact ⟨a, ha, fun h => haB (mem_filter.2 ⟨ha, h⟩)⟩

end Finite

section Fintype

variable [Fintype α]

/-- **Quorum intersection bound**: `#s + #t ≤ #(s ∩ t) + n` for `n = Fintype.card α`. -/
theorem card_add_card_le_card_inter_add_card_univ (s t : Finset α) :
    #s + #t ≤ #(s ∩ t) + Fintype.card α :=
  card_univ (α := α) ▸ card_add_card_le_card_inter_add_card_of_subset (subset_univ s)
    (subset_univ t)

/-- Two sets of total size `> n` intersect. -/
theorem inter_nonempty_of_card_univ_lt_card_add_card (h : Fintype.card α < #s + #t) :
    (s ∩ t).Nonempty :=
  inter_nonempty_of_card_lt_card_add_card (subset_univ s) (subset_univ t) (by simpa using h)

omit [DecidableEq α] in
/-- Two sets with `#s + #t > n + f` share a member outside any `F` with `#F ≤ f`. -/
theorem exists_mem_inter_notMem_of_card_le (hF : #F ≤ f) (h : Fintype.card α + f < #s + #t) :
    ∃ a ∈ s, a ∈ t ∧ a ∉ F := by
  classical
  have := card_add_card_le_card_inter_add_card_univ s t
  obtain ⟨a, ha, haF⟩ := exists_mem_notMem_of_card_le_of_lt hF (show f < #(s ∩ t) by omega)
  exact ⟨a, (mem_inter.1 ha).1, (mem_inter.1 ha).2, haF⟩

omit [DecidableEq α] in
/-- Two sets with `#s + #t > n + f` share a member outside any `B : Set α` with `B.ncard ≤ f`. -/
theorem exists_mem_inter_notMem_of_ncard_le {B : Set α} (hB : B.ncard ≤ f)
    (h : Fintype.card α + f < #s + #t) : ∃ a ∈ s, a ∈ t ∧ a ∉ B := by
  classical
  have := card_add_card_le_card_inter_add_card_univ s t
  obtain ⟨a, ha, haB⟩ := exists_mem_notMem_of_ncard_le_of_lt hB (show f < #(s ∩ t) by omega)
  exact ⟨a, (mem_inter.1 ha).1, (mem_inter.1 ha).2, haB⟩

end Fintype

end Finset

/-! ### Threshold regimes -/

namespace Cslib.Quorum

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α] {s t F : Finset α} {f q : ℕ}

omit [DecidableEq α] in
/-- Two `q`-quorums with `n + f < 2q` share a member outside `F`, `#F ≤ f`. -/
theorem exists_mem_inter_notMem_of_quorum (hn : Fintype.card α + f < 2 * q) (hF : #F ≤ f)
    (hs : q ≤ #s) (ht : q ≤ #t) : ∃ a ∈ s, a ∈ t ∧ a ∉ F :=
  exists_mem_inter_notMem_of_card_le hF (by omega)

omit [DecidableEq α] in
/-- Two `(n - f)`-quorums with `3f < n` share a member outside `F`, `#F ≤ f`. -/
theorem exists_mem_inter_notMem_of_three_mul_lt (hn : 3 * f < Fintype.card α) (hF : #F ≤ f)
    (hs : Fintype.card α - f ≤ #s) (ht : Fintype.card α - f ≤ #t) : ∃ a ∈ s, a ∈ t ∧ a ∉ F :=
  exists_mem_inter_notMem_of_card_le hF (by omega)

/-- Two `(n - f)`-quorums meet in at least `n - 2f` members. -/
theorem card_sub_two_mul_le_card_inter (hs : Fintype.card α - f ≤ #s)
    (ht : Fintype.card α - f ≤ #t) : Fintype.card α - 2 * f ≤ #(s ∩ t) := by
  have := card_add_card_le_card_inter_add_card_univ s t
  omega

/-- Two `(n - f)`-quorums intersect when `2f < n`. -/
theorem inter_nonempty_of_two_mul_lt (hn : 2 * f < Fintype.card α)
    (hs : Fintype.card α - f ≤ #s) (ht : Fintype.card α - f ≤ #t) : (s ∩ t).Nonempty :=
  inter_nonempty_of_card_univ_lt_card_add_card (by omega)

/-- Two `(2f + 1)`-quorums intersect when `n ≤ 4f + 1`. -/
theorem inter_nonempty_of_card_le_four_mul_add_one (hn : Fintype.card α ≤ 4 * f + 1)
    (hs : 2 * f + 1 ≤ #s) (ht : 2 * f + 1 ≤ #t) : (s ∩ t).Nonempty :=
  inter_nonempty_of_card_univ_lt_card_add_card (by omega)

end Cslib.Quorum

namespace Finset

variable {α β : Type*} [DecidableEq β] {s t F : Finset α} {f : α → β} {b c : β} {k : ℕ}

/-! ### Counting -/

/-- `s.countEq f b`: the number of members `a` of `s` with `f a = b`. -/
def countEq (s : Finset α) (f : α → β) (b : β) : ℕ := #{a ∈ s | f a = b}

/-- Unfolding `countEq`. -/
theorem countEq_def : s.countEq f b = #{a ∈ s | f a = b} := rfl

/-- Nobody in the empty set reports anything. -/
@[simp] theorem countEq_empty : (∅ : Finset α).countEq f b = 0 := rfl

/-- At most `#s` members of `s` report `b`. -/
theorem countEq_le_card : s.countEq f b ≤ #s := card_filter_le _ _

/-- `countEq` is monotone in the set of voters. -/
@[gcongr]
theorem countEq_mono (h : s ⊆ t) : s.countEq f b ≤ t.countEq f b :=
  card_le_card (filter_subset_filter _ h)

/-- A value with a positive count is reported by some member of `s`. -/
theorem exists_mem_of_countEq_pos (h : 0 < s.countEq f b) : ∃ a ∈ s, f a = b := by
  obtain ⟨a, ha⟩ := card_pos.1 h
  exact ⟨a, (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

/-- Two distinct values are reported by at most `#s` members of `s` together. -/
theorem countEq_add_countEq_le (h : b ≠ c) : s.countEq f b + s.countEq f c ≤ #s := by
  classical
  rw [countEq, countEq, ← card_union_of_disjoint]
  · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  · exact disjoint_filter.2 fun a _ hb hc => h (hb.symm.trans hc)

/-- Two values reported by more than `#s` members of `s` together coincide. -/
theorem eq_of_card_lt_countEq_add_countEq (h : #s < s.countEq f b + s.countEq f c) : b = c := by
  by_contra hbc
  have := countEq_add_countEq_le (s := s) (f := f) hbc
  omega

/-- A value reported by more than `#F` members of `s` is reported by a member outside `F`. -/
theorem exists_mem_notMem_of_card_lt_countEq (h : #F < s.countEq f b) :
    ∃ a ∈ s, a ∉ F ∧ f a = b := by
  obtain ⟨a, ha, haF⟩ := exists_mem_notMem_of_card_lt_card h
  exact ⟨a, (mem_filter.1 ha).1, haF, (mem_filter.1 ha).2⟩

section DecidableEq

variable [DecidableEq α]

/-- Shrinking `s` to `t` loses at most `#(s \ t)` votes for `b`. -/
theorem countEq_le_countEq_add_card_sdiff (s t : Finset α) :
    s.countEq f b ≤ t.countEq f b + #(s \ t) := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  rw [mem_filter] at ha
  by_cases hat : a ∈ t
  · exact mem_union_left _ (mem_filter.2 ⟨hat, ha.2⟩)
  · exact mem_union_right _ (mem_sdiff.2 ⟨ha.1, hat⟩)

/-- If every member of `s` outside `F` reports `b`, then `b` is reported at least
`#(s \ F)` times. -/
theorem card_sdiff_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = b) : #(s \ F) ≤ s.countEq f b :=
  card_le_card fun a ha => by
    rw [mem_sdiff] at ha
    exact mem_filter.2 ⟨ha.1, h a ha.1 ha.2⟩

end DecidableEq

/-! ### Threshold selection -/

section Selectors

variable {f : α → Option β}

open Classical in
/-- `s.threshold? f k`: some value `b` such that `some b` is reported by at least `k` members of
`s` (chosen arbitrarily), or `none` if there is no such value. -/
noncomputable def threshold? (s : Finset α) (f : α → Option β) (k : ℕ) : Option β :=
  if h : ∃ b, k ≤ s.countEq f (some b) then some h.choose else none

/-- A selected value reaches the threshold. -/
theorem le_countEq_of_threshold?_eq_some (h : s.threshold? f k = some b) :
    k ≤ s.countEq f (some b) := by
  unfold threshold? at h
  split_ifs at h with h'
  cases h
  exact h'.choose_spec

/-- Nothing is selected iff no value reaches the threshold. -/
theorem threshold?_eq_none_iff : s.threshold? f k = none ↔ ∀ b, s.countEq f (some b) < k := by
  unfold threshold?
  split_ifs with h
  · simp only [false_iff, not_forall, not_lt]
    exact h
  · push Not at h
    simpa using h

/-- If `b` reaches the threshold and no other value does, the selected value is `b`. -/
theorem threshold?_eq_some_of_forall (hb : k ≤ s.countEq f (some b))
    (hu : ∀ c, c ≠ b → s.countEq f (some c) < k) : s.threshold? f k = some b := by
  cases h : s.threshold? f k with
  | none => exact absurd hb (not_le.2 (threshold?_eq_none_iff.1 h b))
  | some c =>
    by_contra hcb
    exact absurd (le_countEq_of_threshold?_eq_some h)
      (not_le.2 (hu c fun e => hcb (congrArg some e)))

/-- With a threshold above `#s / 2` the selected value is unique. -/
theorem threshold?_eq_some (hk : #s < 2 * k) (hb : k ≤ s.countEq f (some b)) :
    s.threshold? f k = some b :=
  threshold?_eq_some_of_forall hb fun c hc => by
    have := countEq_add_countEq_le (s := s) (f := f) (Option.some_injective _ |>.ne hc)
    omega

/-- A selected value (for a positive threshold) is reported by some member of `s`. -/
theorem exists_mem_of_threshold?_eq_some (hk : 0 < k) (h : s.threshold? f k = some b) :
    ∃ a ∈ s, f a = some b :=
  exists_mem_of_countEq_pos ((le_countEq_of_threshold?_eq_some h).trans_lt' hk)

/-! ### Strict majority -/

/-- `s.majority? f`: the value reported (as `some b`) by a strict majority of `s`, if any. -/
noncomputable def majority? (s : Finset α) (f : α → Option β) : Option β :=
  s.threshold? f (#s / 2 + 1)

/-- The majority value is `b` iff `b` is reported by a strict majority of `s`. -/
theorem majority?_eq_some_iff : s.majority? f = some b ↔ #s < 2 * s.countEq f (some b) := by
  constructor
  · intro h
    have := le_countEq_of_threshold?_eq_some h
    omega
  · intro h
    exact threshold?_eq_some (by omega) (by omega)

/-- There is no majority value iff no value is reported by a strict majority of `s`. -/
theorem majority?_eq_none_iff : s.majority? f = none ↔ ∀ b, 2 * s.countEq f (some b) ≤ #s := by
  rw [majority?, threshold?_eq_none_iff]
  exact forall_congr' fun _ => by omega

/-- If the members of `s` outside `F` form a strict majority of `s` and all report `o`, then the
majority value is `o`. -/
theorem majority?_eq_of_notMem [DecidableEq α] {o : Option β} (hF : #s < 2 * #(s \ F))
    (h : ∀ a ∈ s, a ∉ F → f a = o) : s.majority? f = o := by
  have hc := card_sdiff_le_countEq h
  cases o with
  | some b => exact majority?_eq_some_iff.2 (by omega)
  | none =>
    refine majority?_eq_none_iff.2 fun b => ?_
    have := countEq_add_countEq_le (s := s) (f := f) (b := some b) (c := none) (by simp)
    omega

/-- The majority value is reported by some member of `s`. -/
theorem exists_mem_of_majority?_eq_some (h : s.majority? f = some b) : ∃ a ∈ s, f a = some b :=
  exists_mem_of_threshold?_eq_some (by omega) h

/-! ### Computable selectors -/

/-- Votes `some (g a)` for `some b` are the votes `g a` for `b`. -/
@[simp] theorem countEq_some (g : α → β) (b : β) :
    s.countEq (fun a => some (g a)) (some b) = s.countEq g b := by
  simp [countEq]

/-- **Scanning for a heavy value.** Protocols compute a threshold value by scanning a list `L`
covering `s` for the first `a ∈ s` whose value `g a` is reported at least `k` times. When
`#s < 2 * k` (at most one value reaches the threshold), this is `s.threshold? (some ∘ g) k`. -/
theorem find?_map_eq_threshold? {g : α → β} {L : List α} (hL : ∀ a ∈ s, a ∈ L) {p : α → Bool}
    (hp : ∀ a, p a = true ↔ a ∈ s ∧ k ≤ s.countEq g (g a)) (hk : #s < 2 * k) :
    (L.find? p).map g = s.threshold? (fun a => some (g a)) k := by
  cases h : L.find? p with
  | some a =>
    have := (hp a).1 (List.find?_some h)
    exact (threshold?_eq_some hk (by rw [countEq_some]; exact this.2)).symm
  | none =>
    refine (threshold?_eq_none_iff.2 fun b => ?_).symm
    rw [countEq_some]
    by_contra hb
    push Not at hb
    obtain ⟨a, ha, rfl⟩ := exists_mem_of_countEq_pos (show 0 < s.countEq g b by omega)
    exact List.find?_eq_none.1 h a (hL a ha) ((hp a).2 ⟨ha, hb⟩)

/-- **Scanning for a strict majority.** The first `a ∈ s` in a list covering `s` whose value
`g a` is reported by a strict majority of `s` gives `s.majority? (some ∘ g)`. -/
theorem find?_map_eq_majority? {g : α → β} {L : List α} (hL : ∀ a ∈ s, a ∈ L) {p : α → Bool}
    (hp : ∀ a, p a = true ↔ a ∈ s ∧ #s < 2 * s.countEq g (g a)) :
    (L.find? p).map g = s.majority? (fun a => some (g a)) :=
  find?_map_eq_threshold? hL
    (fun a => (hp a).trans (and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩))
    (by omega)

end Selectors

/-! ### Plurality -/

/-- `s.plurality f d`: a most frequent value of `f` on `s` (ties broken arbitrarily), or `d` if
`s` is empty. -/
noncomputable def plurality (s : Finset α) (f : α → β) (d : β) : β :=
  if h : s.Nonempty then f (s.exists_max_image (fun a => s.countEq f (f a)) h).choose else d

/-- The plurality value is reported at least as often as any other value. -/
theorem countEq_le_countEq_plurality (hs : s.Nonempty) (d b : β) :
    s.countEq f b ≤ s.countEq f (s.plurality f d) := by
  rcases Nat.eq_zero_or_pos (s.countEq f b) with h | h
  · omega
  obtain ⟨a, ha, rfl⟩ := exists_mem_of_countEq_pos h
  simp only [plurality, hs, ↓reduceDIte]
  exact (s.exists_max_image (fun a => s.countEq f (f a)) hs).choose_spec.2 a ha

/-- A value reported by a strict majority of `s` is the plurality. -/
theorem plurality_eq_of_card_lt_two_mul_countEq {d : β} (h : #s < 2 * s.countEq f b) :
    s.plurality f d = b := by
  have hs : s.Nonempty := by
    rw [← card_pos]; have := countEq_le_card (s := s) (f := f) (b := b); omega
  by_contra hne
  have h₁ := countEq_le_countEq_plurality (f := f) hs d b
  have h₂ := countEq_add_countEq_le (s := s) (f := f) hne
  omega

end Finset

namespace Finset

/-! ### Correct members -/

section Correct

variable {α : Type*} [DecidableEq α] {S F : Finset α} {f : ℕ}

/-- A set `s` has at least `#s - #F` members outside `F`. -/
theorem card_sub_card_le_card_filter_notMem (s F : Finset α) : #s - #F ≤ #{x ∈ s | x ∉ F} :=
  filter_notMem_eq_sdiff (s := s) (t := F) ▸ le_card_sdiff F s

variable [Fintype α]

/-- The processes outside `F` form `Fᶜ`. -/
theorem filter_notMem_univ_eq_compl (F : Finset α) : ({x | x ∉ F} : Finset α) = Fᶜ := by
  ext; simp

/-- There are exactly `n - #F` processes outside `F`, `n = Fintype.card α`. -/
theorem card_filter_notMem_univ (F : Finset α) : #{x | x ∉ F} = Fintype.card α - #F := by
  rw [filter_notMem_univ_eq_compl, card_compl]

/-- There are at least `n - f` processes outside `F` when `#F ≤ f`. -/
theorem card_sub_le_card_filter_notMem (hF : #F ≤ f) : Fintype.card α - f ≤ #{x | x ∉ F} := by
  rw [card_filter_notMem_univ]; omega

omit [DecidableEq α] in
/-- A set containing every process outside `F` has at least `n - #F` members. -/
theorem card_sub_card_le_of_forall_notMem (h : ∀ x ∉ F, x ∈ S) : Fintype.card α - #F ≤ #S := by
  classical
  exact card_compl F ▸ card_le_card fun x hx => h x (mem_compl.1 hx)

omit [DecidableEq α] in
/-- A set containing the (injective) images of all processes outside `F`, e.g. their
identifiers, has at least `n - #F` members. -/
theorem card_sub_card_le_of_injective_of_forall_notMem {β : Type*} {T : Finset β} {g : α → β}
    (hg : Function.Injective g) (h : ∀ x ∉ F, g x ∈ T) : Fintype.card α - #F ≤ #T := by
  classical
  calc Fintype.card α - #F = #(Fᶜ.image g) := by rw [card_image_of_injective _ hg, card_compl]
    _ ≤ #T := card_le_card <| image_subset_iff.2 fun x hx => h x (mem_compl.1 hx)

end Correct

section Ncard

variable {α : Type*} (B : Set α) [DecidablePred (· ∈ B)] {f : ℕ}

/-- A set `s` has at least `#s - B.ncard` members outside `B`. -/
theorem card_sub_ncard_le_card_filter_notMem [Finite α] (s : Finset α) :
    #s - B.ncard ≤ #{x ∈ s | x ∉ B} := by
  have h₁ := card_filter_add_card_filter_not (s := s) (· ∈ B)
  have h₂ := card_filter_mem_le_ncard B s
  omega

variable {B}

/-- There are at least `n - f` processes outside `B` when `B.ncard ≤ f`. -/
theorem card_sub_le_card_filter_notMem_of_ncard_le [Fintype α] (hB : B.ncard ≤ f) :
    Fintype.card α - f ≤ #{x | x ∉ B} := by
  have := card_sub_ncard_le_card_filter_notMem B univ
  rw [card_univ] at this
  omega

end Ncard

/-! ### Counting votes with a faulty set -/

section Counting

variable {α β : Type*} [DecidableEq β] {s : Finset α} {f g : α → β} {b : β}

/-- `countEq` only depends on the reports of the members of `s`. -/
theorem countEq_congr (h : ∀ a ∈ s, f a = g a) (b : β) : s.countEq f b = s.countEq g b := by
  rw [countEq, countEq, filter_congr fun a ha => by rw [h a ha]]

/-- If every member of `s` reports `b`, then `b` is reported `#s` times. -/
theorem countEq_eq_card (h : ∀ a ∈ s, f a = b) : s.countEq f b = #s := by
  rw [countEq, filter_true_of_mem h]

section Finset

variable [DecidableEq α] {F : Finset α}

omit [DecidableEq α] in
/-- If every member of `s` outside `F` reports `b`, then `b` is reported at least `#s - #F`
times. -/
theorem card_sub_card_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = b) : #s - #F ≤ s.countEq f b := by
  classical
  exact (le_card_sdiff F s).trans (card_sdiff_le_countEq h)

/-- If `f` agrees with `g` on the members of `s` outside `F`, then `f` reports `b` at least as
often as the members of `s` outside `F` hold `b` under `g`. -/
theorem card_filter_notMem_and_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = g a) (b : β) :
    #{a ∈ s | a ∉ F ∧ g a = b} ≤ s.countEq f b :=
  card_le_card fun a ha => by
    simp only [mem_filter] at ha ⊢
    exact ⟨ha.1, (h a ha.1 ha.2.1).trans ha.2.2⟩

/-- If `f` agrees with `g` on the members of `s` outside `F`, then `f` reports `b` at most `#F`
more often than the members of `s` outside `F` hold `b` under `g`. -/
theorem countEq_le_card_filter_notMem_and_add_card (h : ∀ a ∈ s, a ∉ F → f a = g a) (b : β) :
    s.countEq f b ≤ #{a ∈ s | a ∉ F ∧ g a = b} + #F := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  rw [mem_filter] at ha
  by_cases haF : a ∈ F
  · exact mem_union_right _ haF
  · exact mem_union_left _ (mem_filter.2 ⟨ha.1, haF, (h a ha.1 haF).symm.trans ha.2⟩)

omit [DecidableEq α] in
/-- Two vote vectors that agree on the members of `s` outside `F` have counts differing by at
most `#F`. -/
theorem countEq_sub_card_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = g a) (b : β) :
    s.countEq f b - #F ≤ s.countEq g b := by
  classical
  have h₁ : s.countEq f b ≤ #{a ∈ s | a ∉ F ∧ f a = b} + #F :=
    countEq_le_card_filter_notMem_and_add_card (g := f) (fun _ _ _ => rfl) b
  have h₂ : #{a ∈ s | a ∉ F ∧ f a = b} ≤ s.countEq g b :=
    card_filter_notMem_and_le_countEq (fun a ha haF => (h a ha haF).symm) b
  omega

end Finset

section Ncard

variable [Finite α] {B : Set α} [DecidablePred (· ∈ B)]

omit [DecidablePred (· ∈ B)] in
/-- If every member of `s` outside `B` reports `b`, then `b` is reported at least
`#s - B.ncard` times. -/
theorem card_sub_ncard_le_countEq (h : ∀ a ∈ s, a ∉ B → f a = b) :
    #s - B.ncard ≤ s.countEq f b := by
  classical
  exact (card_sub_ncard_le_card_filter_notMem B s).trans <| card_le_card fun a ha => by
    rw [mem_filter] at ha ⊢
    exact ⟨ha.1, h a ha.1 ha.2⟩

omit [DecidablePred (· ∈ B)] in
/-- Two vote vectors that agree on the members of `s` outside `B` have counts differing by at
most `B.ncard`. -/
theorem countEq_sub_ncard_le_countEq (h : ∀ a ∈ s, a ∉ B → f a = g a) (b : β) :
    s.countEq f b - B.ncard ≤ s.countEq g b := by
  classical
  have h₁ := card_sub_ncard_le_card_filter_notMem B {a ∈ s | f a = b}
  refine h₁.trans (card_le_card fun a ha => ?_)
  simp only [mem_filter] at ha ⊢
  exact ⟨ha.1.1, (h a ha.1.1 ha.2).symm.trans ha.1.2⟩

end Ncard

end Counting

/-! ### Counting sender–receiver pairs -/

section Pairs

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- **Counting sender–receiver pairs.** Let `f τ q p` be the number of messages that `q` sends
to `p` at time `τ`. If `X` and `Y` are disjoint, then up to some finite time `N` the members of `X`
send (to processes other than themselves) at least as many messages as there are pairs
`(q, p) ∈ X × Y` such that `q` sends something to `p` at some time. -/
theorem exists_sum_card_filter_exists_ne_zero_le (X Y : Finset α) (hXY : Disjoint X Y)
    (f : ℕ → α → α → ℕ) :
    ∃ N, ∑ p ∈ Y, #{q ∈ X | ∃ τ, f τ q p ≠ 0} ≤
      ∑ τ ∈ range N, ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), f τ q p := by
  let τ₀ : α × α → ℕ := fun qp => if hh : ∃ τ, f τ qp.1 qp.2 ≠ 0 then Classical.choose hh else 0
  let N := (univ : Finset (α × α)).sup τ₀ + 1
  refine ⟨N, ?_⟩
  have key : ∀ q p, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) ≤ ∑ τ ∈ range N, f τ q p := by
    intro q p
    split_ifs with hh
    · have hlt : τ₀ (q, p) < N := Nat.lt_succ_of_le (le_sup (f := τ₀) (mem_univ (q, p)))
      have hτ : τ₀ (q, p) = Classical.choose hh := by simp [τ₀, hh]
      calc 1 ≤ f (τ₀ (q, p)) q p := by
              rw [hτ]; exact Nat.one_le_iff_ne_zero.mpr (Classical.choose_spec hh)
        _ ≤ ∑ τ ∈ range N, f τ q p :=
              single_le_sum (f := fun τ => f τ q p) (fun _ _ => Nat.zero_le _) (mem_range.mpr hlt)
    · exact Nat.zero_le _
  calc ∑ p ∈ Y, #{q ∈ X | ∃ τ, f τ q p ≠ 0}
      = ∑ p ∈ Y, ∑ q ∈ X, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) := by
        refine sum_congr rfl fun p _ => ?_
        rw [card_eq_sum_ones, sum_filter]
    _ = ∑ q ∈ X, ∑ p ∈ Y, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) := sum_comm
    _ ≤ ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), ∑ τ ∈ range N, f τ q p := by
        refine sum_le_sum fun q hq => ?_
        calc ∑ p ∈ Y, (if ∃ τ, f τ q p ≠ 0 then 1 else 0)
            ≤ ∑ p ∈ Y, ∑ τ ∈ range N, f τ q p := sum_le_sum fun p _ => key q p
          _ ≤ ∑ p ∈ univ.filter (· ≠ q), ∑ τ ∈ range N, f τ q p := by
              refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => Nat.zero_le _
              refine mem_filter.mpr ⟨mem_univ _, fun h => ?_⟩
              subst h
              exact disjoint_left.mp hXY hq hp
    _ = ∑ τ ∈ range N, ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), f τ q p := by
        rw [sum_comm (s := range N)]
        refine sum_congr rfl fun q _ => ?_
        rw [sum_comm (s := range N)]

end Pairs

/-! ### Plurality with smallest-value tie-breaking -/

section PluralityMin

variable {α β : Type*} [LinearOrder β] {s : Finset α} {f g : α → β}

/-- The most frequent values of `f` on a nonempty `s` form a nonempty set. -/
theorem image_filter_countEq_eq_sup_nonempty (f : α → β) (hs : s.Nonempty) :
    ({a ∈ s | s.countEq f (f a) = s.sup fun a => s.countEq f (f a)}.image f).Nonempty := by
  obtain ⟨a, ha, he⟩ := s.exists_mem_eq_sup hs (fun a => s.countEq f (f a))
  exact ⟨f a, mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, he.symm⟩, rfl⟩⟩

/-- `s.pluralityMin f d`: the smallest value among the most frequent values of `f` on `s` (`d` if
`s` is empty). Unlike `Finset.plurality`, ties are broken deterministically. -/
def pluralityMin (s : Finset α) (f : α → β) (d : β) : β :=
  if h : s.Nonempty then
    ({a ∈ s | s.countEq f (f a) = s.sup fun a => s.countEq f (f a)}.image f).min'
      (image_filter_countEq_eq_sup_nonempty f h)
  else d

/-- `pluralityMin` is the value of a most frequent element of `s`. -/
theorem exists_mem_pluralityMin_eq (hs : s.Nonempty) (d : β) :
    ∃ a ∈ s, f a = s.pluralityMin f d ∧
      s.countEq f (f a) = s.sup fun a => s.countEq f (f a) := by
  simp only [pluralityMin, hs, ↓reduceDIte]
  obtain ⟨a, ha, he⟩ := mem_image.mp (min'_mem _ (image_filter_countEq_eq_sup_nonempty f hs))
  exact ⟨a, (mem_filter.mp ha).1, he, (mem_filter.mp ha).2⟩

/-- The value `pluralityMin` is reported at least as often as any other value. -/
theorem countEq_le_countEq_pluralityMin (hs : s.Nonempty) (d b : β) :
    s.countEq f b ≤ s.countEq f (s.pluralityMin f d) := by
  obtain ⟨a, -, he, hmax⟩ := exists_mem_pluralityMin_eq (f := f) hs d
  rcases Nat.eq_zero_or_pos (s.countEq f b) with h | h
  · omega
  obtain ⟨a', ha', rfl⟩ := exists_mem_of_countEq_pos h
  rw [← he, hmax]
  exact le_sup (f := fun a => s.countEq f (f a)) ha'

/-- A value reported by a strict majority of `s` is `pluralityMin`. -/
theorem pluralityMin_eq_of_card_lt_two_mul_countEq {d b : β} (h : #s < 2 * s.countEq f b) :
    s.pluralityMin f d = b := by
  have hs : s.Nonempty := by
    rw [← card_pos]; have := countEq_le_card (s := s) (f := f) (b := b); omega
  by_contra hne
  have h₁ := countEq_le_countEq_pluralityMin (f := f) hs d b
  have h₂ := countEq_add_countEq_le (s := s) (f := f) hne
  omega

/-- On a nonempty set, `pluralityMin` only depends on the values on that set (not on the
default). -/
theorem pluralityMin_congr {d d' : β} (hs : s.Nonempty) (h : ∀ a ∈ s, f a = g a) :
    s.pluralityMin f d = s.pluralityMin g d' := by
  have hc : ∀ a ∈ s, s.countEq f (f a) = s.countEq g (g a) := fun a ha => by
    unfold countEq
    exact congrArg card (filter_congr fun a' ha' => by rw [h a' ha', h a ha])
  have hsup : (s.sup fun a => s.countEq f (f a)) = s.sup fun a => s.countEq g (g a) :=
    sup_congr rfl hc
  have hS : {a ∈ s | s.countEq f (f a) = s.sup fun a => s.countEq f (f a)}.image f =
      {a ∈ s | s.countEq g (g a) = s.sup fun a => s.countEq g (g a)}.image g := by
    rw [hsup, filter_congr fun a ha => by rw [hc a ha]]
    exact image_congr fun a ha => h a (mem_filter.mp ha).1
  simp only [pluralityMin, hs, ↓reduceDIte]
  congr 1

end PluralityMin

end Finset
