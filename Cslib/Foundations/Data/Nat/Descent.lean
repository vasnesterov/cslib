/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.OrderIsoNat

/-!
# Eventually non-increasing sequences of natural numbers

A sequence `f : ℕ → ℕ` that is non-increasing from some index `N` on is eventually constant
(`Nat.eventually_const_of_succ_le`); consequently it can decrease only finitely often
(`Nat.eventually_not_of_succ_le`, `Nat.not_frequently_lt_of_succ_le`). These are the termination
arguments ("potential functions") behind wait-freedom and lock-freedom proofs. Dually, a bounded
sequence that is non-decreasing from some index on is eventually constant
(`Nat.eventually_const_of_le_succ`).

`Nat.exists_lt_and_not_succ_of_not` is the discrete intermediate value property used in valency
arguments ("the last configuration along an execution from which `v` can still be decided");
`Nat.exists_last_of_le` gives the last index of an interval at which a property holds.

Both follow from Mathlib's antitone chain condition (`WellFoundedLT.antitone_chain_condition`).

## Eventual stabilization along `ℕ`-indexed times

Liveness proofs over infinite executions (time `t : ℕ`) repeatedly use the following facts, stated
in the `∃ T ≥ N, ∀ m ≥ T, …` form of `Nat.eventually_const_of_succ_le`:

* `Nat.eventually_of_imp_succ`: a property preserved from `N` on that holds once (at a time `≥ N`)
  holds from then on;
* `Nat.eventually_forall_of_finite`: finitely many "eventually forever" properties hold
  simultaneously from some time on; `Finite.exists_forall_of_monotone`,
  `Set.Finite.exists_forall_of_monotone`: finitely many monotone properties of times, each true at
  some time, are all true at a common time;
* `WellFoundedLT.eventually_const_of_succ_le`, `WellFoundedGT.eventually_const_of_le_succ`: an
  eventually non-increasing (non-decreasing) sequence in a well-founded (co-well-founded) order is
  eventually constant (e.g. Boolean flags, or maps `A → Bool` over a finite set of agents);
* `Finset.eventually_const_of_subset_succ`: an eventually increasing sequence of finite sets of
  bounded cardinality is eventually constant (`Finset.eventually_const_of_subset_succ_of_finite`
  when the ambient type is finite);
* `Int.exists_eq_and_succ_eq_of_le_add_one`: the discrete intermediate value theorem for integer
  sequences that increase by at most one per step.
-/

@[expose] public section

namespace Nat

variable {f : ℕ → ℕ} {N : ℕ}

/-- A sequence of natural numbers that is non-increasing from `N` on is eventually constant. -/
theorem eventually_const_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (f := fun k => f (N + k))
    (antitone_nat_of_succ_le fun k => h (N + k) (by omega))
  refine ⟨N + n, by omega, fun m hm => ?_⟩
  have := hn (m - N) (by omega)
  rw [show N + (m - N) = m by omega] at this
  exact this.symm

/-- A sequence of natural numbers that is non-increasing from `N` on and strictly decreases at
every index `m ≥ N` satisfying `p m` satisfies `p` only finitely often. -/
theorem eventually_not_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) {p : ℕ → Prop}
    (hp : ∀ m ≥ N, p m → f (m + 1) < f m) : ∃ T ≥ N, ∀ m ≥ T, ¬ p m := by
  obtain ⟨T, hT, hc⟩ := eventually_const_of_succ_le h
  refine ⟨T, hT, fun m hm hpm => ?_⟩
  have := hp m (by omega) hpm
  rw [hc m hm, hc (m + 1) (by omega)] at this
  exact lt_irrefl _ this

/-- A sequence of natural numbers that is non-increasing from `N` on cannot decrease infinitely
often. -/
theorem not_frequently_lt_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ¬ ∀ M, ∃ m ≥ M, f (m + 1) < f m := by
  intro hs
  obtain ⟨T, hT, hc⟩ := eventually_not_of_succ_le h (p := fun m => f (m + 1) < f m)
    fun _ _ hm => hm
  obtain ⟨m, hm, hlt⟩ := hs T
  exact hc m hm hlt

/-- A bounded sequence of natural numbers that is non-decreasing from `N` on is eventually
constant. -/
theorem eventually_const_of_le_succ {B : ℕ} (hB : ∀ m ≥ N, f m ≤ B)
    (h : ∀ m ≥ N, f m ≤ f (m + 1)) : ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨T, hT, hc⟩ := eventually_const_of_succ_le (f := fun m => B - f m) (N := N)
    fun m hm => by have := h m hm; have := hB m hm; have := hB (m + 1) (by omega); omega
  refine ⟨T, hT, fun m hm => ?_⟩
  have := hc m hm; have := hB m (by omega); have := hB T hT
  omega

/-- **Discrete intermediate value property.** If `p 0` holds and `p K` fails, then there is a
last index `m < K` at which `p` holds before failing at `m + 1`. -/
theorem exists_lt_and_not_succ_of_not {p : ℕ → Prop} {K : ℕ} (h0 : p 0) (hK : ¬ p K) :
    ∃ m < K, p m ∧ ¬ p (m + 1) := by
  induction K with
  | zero => exact absurd h0 hK
  | succ K ih =>
    by_cases hp : p K
    · exact ⟨K, K.lt_succ_self, hp, hK⟩
    · obtain ⟨m, hm, h⟩ := ih hp
      exact ⟨m, by omega, h⟩

/-- **Last index.** If `p a` holds and `a ≤ b`, there is a last index `m ∈ [a, b]` at which `p`
holds: `p` fails on `(m, b]`. -/
theorem exists_last_of_le {p : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : p a) :
    ∃ m, a ≤ m ∧ m ≤ b ∧ p m ∧ ∀ k, m < k → k ≤ b → ¬ p k := by
  classical
  have hs := Nat.findGreatest_spec (P := fun k => a ≤ k ∧ p k) hab ⟨le_rfl, ha⟩
  refine ⟨_, hs.1, Nat.findGreatest_le b, hs.2, fun k hk hkb hpk => ?_⟩
  exact Nat.findGreatest_is_greatest hk hkb ⟨hs.1.trans hk.le, hpk⟩

end Nat

namespace Nat

/-- A property that is preserved from `N` on and holds at some time `≥ N` holds from some time
`T ≥ N` on. -/
theorem eventually_of_imp_succ {p : ℕ → Prop} {N : ℕ} (h : ∀ m ≥ N, p m → p (m + 1))
    (hex : ∃ m ≥ N, p m) : ∃ T ≥ N, ∀ m ≥ T, p m := by
  obtain ⟨T, hT, hp⟩ := hex
  refine ⟨T, hT, fun m hm => ?_⟩
  induction m, hm using Nat.le_induction with
  | base => exact hp
  | succ m hm ih => exact h m (hT.trans hm) ih

/-- Finitely many properties each of which holds from some time on hold simultaneously from some
time `T ≥ N` on. -/
theorem eventually_forall_of_finite {ι : Type*} [Finite ι] {p : ι → ℕ → Prop}
    (h : ∀ i, ∃ T, ∀ m ≥ T, p i m) (N : ℕ) : ∃ T ≥ N, ∀ m ≥ T, ∀ i, p i m := by
  have hev : ∀ᶠ m in Filter.atTop, N ≤ m ∧ ∀ i, p i m :=
    (Filter.eventually_ge_atTop N).and
      (Filter.eventually_all.2 fun i => Filter.eventually_atTop.2 (h i))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N T, le_max_left _ _, fun m hm => (hT m (le_of_max_le_right hm)).2⟩

end Nat

section Monotone

variable {ι α : Type*} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α] {p : ι → α → Prop}

/-- Finitely many monotone properties (of times in a directed order), each of which holds at some
time, hold simultaneously at a common time. -/
theorem Set.Finite.exists_forall_of_monotone {s : Set ι} (hs : s.Finite)
    (hp : ∀ i ∈ s, Monotone (p i)) (h : ∀ i ∈ s, ∃ a, p i a) : ∃ a, ∀ i ∈ s, p i a :=
  ((Filter.eventually_all_finite hs).2 fun i hi => Filter.eventually_atTop.2 <|
    (h i hi).imp fun _ ha _ hb => hp i hi hb ha).exists

/-- Finitely many monotone properties (of times in a directed order), each of which holds at some
time, hold simultaneously at a common time. -/
theorem Finite.exists_forall_of_monotone [Finite ι] (hp : ∀ i, Monotone (p i))
    (h : ∀ i, ∃ a, p i a) : ∃ a, ∀ i, p i a := by
  simpa using Set.finite_univ.exists_forall_of_monotone (fun i _ => hp i) fun i _ => h i

end Monotone

/-- A sequence in a well-founded order that is non-increasing from `N` on is eventually
constant. -/
theorem WellFoundedLT.eventually_const_of_succ_le {α : Type*} [PartialOrder α] [WellFoundedLT α]
    {f : ℕ → α} {N : ℕ} (h : ∀ m ≥ N, f (m + 1) ≤ f m) : ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (f := fun k => f (N + k))
    (antitone_nat_of_succ_le fun k => h (N + k) (by omega))
  refine ⟨N + n, by omega, fun m hm => ?_⟩
  have := hn (m - N) (by omega)
  rw [show N + (m - N) = m by omega] at this
  exact this.symm

/-- A sequence in a co-well-founded order that is non-decreasing from `N` on is eventually
constant. -/
theorem WellFoundedGT.eventually_const_of_le_succ {α : Type*} [PartialOrder α] [WellFoundedGT α]
    {f : ℕ → α} {N : ℕ} (h : ∀ m ≥ N, f m ≤ f (m + 1)) : ∃ T ≥ N, ∀ m ≥ T, f m = f T :=
  WellFoundedLT.eventually_const_of_succ_le (α := αᵒᵈ) h

namespace Finset

variable {α : Type*} {f : ℕ → Finset α} {N : ℕ}

/-- A sequence of finite sets of bounded cardinality that is increasing from `N` on is eventually
constant. -/
theorem eventually_const_of_subset_succ {B : ℕ} (hB : ∀ m ≥ N, #(f m) ≤ B)
    (h : ∀ m ≥ N, f m ⊆ f (m + 1)) : ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨T, hT, hc⟩ := Nat.eventually_const_of_le_succ (f := fun m => #(f m)) hB
    fun m hm => card_le_card (h m hm)
  refine ⟨T, hT, fun m hm => ?_⟩
  have hsub : f T ⊆ f m := by
    induction m, hm using Nat.le_induction with
    | base => exact Subset.rfl
    | succ m hm ih => exact ih.trans (h m (hT.trans hm))
  exact (eq_of_subset_of_card_le hsub (hc m hm).le).symm

/-- A sequence of finite subsets of a finite type that is increasing from `N` on is eventually
constant. -/
theorem eventually_const_of_subset_succ_of_finite [Finite α] (h : ∀ m ≥ N, f m ⊆ f (m + 1)) :
    ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  have := Fintype.ofFinite α
  exact WellFoundedGT.eventually_const_of_le_succ h

end Finset

/-- **Discrete intermediate value theorem.** An integer sequence that increases by at most one per
step on `[a, b)`, with `f a ≤ j < f b`, crosses `j` upwards at some `s ∈ [a, b)`:
`f s = j` and `f (s + 1) = j + 1`. -/
theorem Int.exists_eq_and_succ_eq_of_le_add_one {f : ℕ → ℤ} {a b : ℕ} {j : ℤ} (hab : a ≤ b)
    (hf : ∀ s, a ≤ s → s < b → f (s + 1) ≤ f s + 1) (ha : f a ≤ j) (hb : j < f b) :
    ∃ s, a ≤ s ∧ s < b ∧ f s = j ∧ f (s + 1) = j + 1 := by
  induction b, hab using Nat.le_induction with
  | base => omega
  | succ n hn ih =>
    by_cases h : j < f n
    · obtain ⟨s, h1, h2, h3, h4⟩ := ih (fun s hs hsn => hf s hs (by omega)) h
      exact ⟨s, h1, by omega, h3, h4⟩
    · have := hf n hn (by omega)
      exact ⟨n, hn, by omega, by omega, by omega⟩
