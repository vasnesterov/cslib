/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SyncCrash.Model
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Flooding a bit ("max-floodset") in the synchronous crash model

A protocol-independent analysis of the following sub-protocol, run in rounds `T + 1, …, T + R`:
every *participant* that currently holds the bit `1` sends a message to every other process;
a participant holds `1` at time `t ≥ T` iff it started with `1` (`v0`) or received a message in one
of the rounds `T + 1, …, t`. Non-participants send nothing in these rounds.

The protocol-specific part is the hypothesis `FloodRounds` (which messages are sent). Results:
* `FloodRounds.agree`: if some round in `T + 1 … T + R` has no crash, all participants alive at time
  `T + R` hold the same bit (uniform agreement);
* `FloodRounds.not_val`: if all participants start with `0`, nobody ever holds `1` (validity);
* `FloodRounds.val_of_correct`: if a correct participant starts with `1`, every participant holds
  `1` from time `T + 1` on (the "biased-to-1" property);
* `exists_clean_round`: fewer than `R` crashes in rounds `T + 1 … T + R` leave a clean round.
-/

@[expose] public section

namespace Cslib.SyncCrash

variable {P I M O : Type*} {alg : Cslib.Byzantine.LockStep.Protocol P I M O}

/-- The bit held by `z` at time `t` (for `t ≥ T`): its initial bit or a message received in a
flooding round before `t`. -/
def floodVal (alg : Cslib.Byzantine.LockStep.Protocol P I M O) (r : Run P I) (T : ℕ)
    (v0 : P → Prop) (z : P) (t : ℕ) : Prop :=
  v0 z ∨ ∃ t', T ≤ t' ∧ t' < t ∧ ∃ y, Sent alg r y z t'

/-- In rounds `T + 1 … T + R`, exactly the participants holding `1` send, to everybody. -/
def FloodRounds (alg : Cslib.Byzantine.LockStep.Protocol P I M O) (r : Run P I) (T R : ℕ)
    (part v0 : P → Prop) : Prop :=
  ∀ t, T ≤ t → t < T + R → ∀ y z,
    Sent alg r y z t ↔ (y ≠ z ∧ r.Deliv y z t ∧ part y ∧ floodVal alg r T v0 y t)

namespace FloodRounds

variable {r : Run P I} {T R : ℕ} {part v0 : P → Prop}

lemma floodVal_mono {z : P} {t t' : ℕ} (h : floodVal alg r T v0 z t) (ht : t ≤ t') :
    floodVal alg r T v0 z t' := by
  rcases h with h | ⟨s, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h1, by omega, h3⟩

lemma floodVal_succ {z : P} {t : ℕ} (ht : T ≤ t) :
    floodVal alg r T v0 z (t + 1) ↔ floodVal alg r T v0 z t ∨ ∃ y, Sent alg r y z t := by
  constructor
  · rintro (h | ⟨s, h1, h2, y, hy⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | rfl
      · exact Or.inl (Or.inr ⟨s, h1, h, y, hy⟩)
      · exact Or.inr ⟨y, hy⟩
  · rintro (h | ⟨y, hy⟩)
    · exact floodVal_mono h (by omega)
    · exact Or.inr ⟨t, ht, by omega, y, hy⟩

/-- Validity: if no participant starts with `1`, no participant ever holds `1` (up to time
`T + R`). -/
lemma not_val (hF : FloodRounds alg r T R part v0) (h0 : ∀ y, part y → ¬ v0 y) :
    ∀ t ≤ T + R, ∀ z, part z → ¬ floodVal alg r T v0 z t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht z hz hv
    rcases hv with h | ⟨s, h1, h2, y, hy⟩
    · exact h0 z hz h
    · obtain ⟨-, -, hpy, hvy⟩ := (hF s h1 (by omega) y z).1 hy
      exact ih s h2 (by omega) y hpy hvy

/-- Biased to `1`: if a correct participant starts with `1`, every process holds `1` from time
`T + 1` on (if `R ≥ 1`). -/
lemma val_of_correct (hF : FloodRounds alg r T R part v0) (hR : 0 < R) {y : P} (hy : part y)
    (hy0 : v0 y) (hyc : ¬ r.Faulty y) (z : P) {t : ℕ} (ht : T + 1 ≤ t) :
    floodVal alg r T v0 z t := by
  by_cases hzy : z = y
  · subst hzy; exact Or.inl hy0
  · refine Or.inr ⟨T, le_rfl, by omega, y, ?_⟩
    exact (hF T le_rfl (by omega) y z).2
      ⟨Ne.symm hzy, Run.deliv_of_not_faulty hyc z T, hy, Or.inl hy0⟩

/-- Uniform agreement after a clean round: if no process crashes in round `t₀ + 1` for some
`T ≤ t₀ < T + R`, then every process holds `1` at time `T + R` as soon as some participant alive at
time `T + R` does (in particular, all participants alive at time `T + R` hold the same bit). -/
lemma agree (hF : FloodRounds alg r T R part v0) {t₀ : ℕ} (ht₀ : T ≤ t₀) (ht₀' : t₀ < T + R)
    (hclean : ∀ p, r.crash p ≠ some (t₀ + 1)) {z z' : P} (hz : part z)
    (ha : r.Alive z (T + R)) (hv : floodVal alg r T v0 z (T + R)) :
    floodVal alg r T v0 z' (T + R) := by
  -- some participant alive at `t₀` holds `1` at `t₀`
  have key : ∃ y, part y ∧ r.Alive y t₀ ∧ floodVal alg r T v0 y t₀ := by
    by_contra hno
    push Not at hno
    have : ∀ t, t₀ ≤ t → t ≤ T + R → ∀ y, part y → r.Alive y t → ¬ floodVal alg r T v0 y t := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact fun _ y hy ha => hno y hy ha
      | succ t ht ih =>
        intro htR y hy hay hvy
        rcases (floodVal_succ (by omega)).1 hvy with h | ⟨s, hs⟩
        · exact ih (by omega) y hy (hay.mono (by omega)) h
        · obtain ⟨-, hd, hps, hvs⟩ := (hF t (by omega) (by omega) s y).1 hs
          exact ih (by omega) s hps hd.1 hvs
    exact this (T + R) (by omega) le_rfl z hz ha hv
  obtain ⟨y, hy, hay, hvy⟩ := key
  by_cases hzy : z' = y
  · subst hzy; exact floodVal_mono hvy (by omega)
  · have hs : Sent alg r y z' t₀ := (hF t₀ ht₀ ht₀' y z').2
      ⟨Ne.symm hzy, ⟨hay, fun hc => hclean y hc.1⟩, hy, hvy⟩
    exact Or.inr ⟨t₀, ht₀, ht₀', y, hs⟩

end FloodRounds

open Classical in
/-- Pigeonhole: if fewer than `R` processes crash in rounds `T + 1 … T + R`, one of these rounds has
no crash. -/
lemma exists_clean_round [Fintype P] (r : Run P I) {T R : ℕ}
    (h : (Finset.univ.filter (fun p => ∃ c, r.crash p = some c ∧ T < c ∧ c ≤ T + R)).card < R) :
    ∃ t₀, T ≤ t₀ ∧ t₀ < T + R ∧ ∀ p, r.crash p ≠ some (t₀ + 1) := by
  by_contra hno
  push Not at hno
  let F := Finset.univ.filter (fun p => ∃ c, r.crash p = some c ∧ T < c ∧ c ≤ T + R)
  let g : P → ℕ := fun p => (r.crash p).getD 0
  have hsurj : Finset.Ioc T (T + R) ⊆ F.image g := by
    intro c hc
    rw [Finset.mem_Ioc] at hc
    obtain ⟨p, hp⟩ := hno (c - 1) (by omega) (by omega)
    rw [Finset.mem_image]
    refine ⟨p, ?_, ?_⟩
    · simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c - 1 + 1, hp, by omega, by omega⟩
    · simp [g, hp]; omega
  have h1 : (Finset.Ioc T (T + R)).card ≤ F.card :=
    (Finset.card_le_card hsurj).trans Finset.card_image_le
  have h2 : F.card < R := h
  simp at h1
  omega

end Cslib.SyncCrash
