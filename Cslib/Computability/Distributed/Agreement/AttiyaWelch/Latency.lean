/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.AttiyaWelch.Safety

/-! # The Attiya–Welch graded consensus protocol AW′: latency

Timed termination of AW′ (`Cslib.Distributed.AttiyaWelch.protocol`) for `3t < n`: if every correct
process has proposed by time `τ` and no correct process abandons by `T0 + 9δ`, where
`T0 = max τ gst`, then every correct process decides by `T0 + 9δ` (`AttiyaWelch.Timely.decides`).
This is the timed form of the claim of [Civit et al.][CivitEtAl2024] (appendix, "Existing
primitives") that AW "terminates in 9 asynchronous rounds". Every correct process sends `ECHO_1`
by `T0 + δ`, `ECHO_2` by `T0 + 2δ`, `ECHO_3` by `T0 + 4δ`, `ECHO_4` by `T0 + 5δ` and `ECHO_5` by
`T0 + 7δ`, and decides by `T0 + 9δ`. Since every correct process has proposed by `T0`, the gate
on its sends (no message before the proposal) is open in this window
(`Timely.proposed_eq_true`): a fired guard has sent its `ECHO`, at the latest at the proposal.

## Main definitions

* `AttiyaWelch.Timely ρ δ T0`: the hypotheses of the latency analysis.

## Main statements

* `Timely.ac_totality`: if two values or `⊥` are approved by a correct process (`AC`), then `⊥`
  is approved by every correct process two message delays later.
* `Timely.exists_echo_one`, `Timely.echo_two`, `Timely.echo_three`, `Timely.echo_four`,
  `Timely.echo_five`: every correct process sends its message of phase `k` in time.
* `Timely.decides`: every correct process decides by `T0 + 9δ`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
* [H. Attiya, J. L. Welch, *Multi-Valued Connected Consensus: A New Perspective on Crusader
  Agreement and Adopt-Commit*, OPODIS 2023][AttiyaWelch2023]
-/

@[expose] public section

namespace Cslib.Distributed

namespace AttiyaWelch

open GradedConsensus Finset

variable {P Value : Type} [DecidableEq P] [DecidableEq Value] [Fintype P]

/-! ### Latency `9δ` -/

section Latency

variable {t δ : ℕ}

/-- The hypotheses of the latency analysis, with `T0 = max τ' gst` for the last proposal time
`τ'`: the run is valid, `3t < n`, every correct process has proposed by `T0`, and no correct
process abandons at any time `≤ T0 + 9δ`. -/
structure Timely (ρ : Run (protocol P Value t)) (δ T0 : ℕ) : Prop where
  /-- The run is valid. -/
  valid : ρ.Valid t δ
  /-- Fewer than a third of the processes are faulty. -/
  three_mul_lt : 3 * t < Fintype.card P
  /-- The analysis starts after GST. -/
  gst_le : ρ.gst ≤ T0
  /-- Every correct process has proposed by `T0`. -/
  proposed : ∀ p ∉ ρ.faulty, ∃ v, ∃ τ ≤ T0, .req (.propose v) ∈ ρ.input p τ
  /-- No correct process abandons by `T0 + 9δ`. -/
  noAbandon : ∀ p ∉ ρ.faulty, ∀ τ ≤ T0 + 9 * δ, .req .abandon ∉ ρ.input p τ

namespace Timely

variable {ρ : Run (protocol P Value t)} {T0 : ℕ} (H : Timely ρ δ T0) {p q r : P}
  {τ T T' : ℕ} {k : Phase} {a b : Option Value} {m : Msg Value} {v : Value} {g : Bool}
include H

theorem exists_correct : ∃ p, p ∉ ρ.faulty := by
  obtain ⟨p, -, hp⟩ := Quorum.exists_notMem_of_lt_card (S := Finset.univ)
    H.valid.card_faulty_le (by have := H.three_mul_lt; simp; omega)
  exact ⟨p, hp⟩

theorem nonempty : Nonempty Value := by
  obtain ⟨p, hp⟩ := H.exists_correct
  obtain ⟨v, -⟩ := H.proposed p hp
  exact ⟨v⟩

/-- Correct processes have not abandoned up to time `T0 + 9δ` (inclusive). -/
theorem ab_eq_false (hp : p ∉ ρ.faulty) (hτ : τ ≤ T0 + 9 * δ + 1) : (ρ.state p τ).ab = false := by
  cases h : (ρ.state p τ).ab
  · rfl
  · obtain ⟨τ', hτ', h'⟩ := ab_state.1 h
    exact absurd h' (H.noAbandon p hp τ' (by omega))

/-- Correct processes have accepted their proposals after `T0`, so the gate on their sends is
open. -/
theorem proposed_eq_true (hp : p ∉ ρ.faulty) (hτ : T0 < τ) : (ρ.state p τ).proposed = true := by
  obtain ⟨v, τ', hτ', h⟩ := H.proposed p hp
  exact Run.state_of_stable (Q := fun s : (protocol P Value t).State => s.proposed = true)
    (fun _ _ _ h => proposed_step.2 (.inl h))
    (proposed_of_propose h (H.ab_eq_false hp (by omega))) (by omega)

/-- *Delivery* in the latency window. -/
theorem mem_rcv (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty) (h : SendAll ρ q m τ) (hτ : τ ≤ T)
    (hT : T0 ≤ T) (hT' : T + δ ≤ T') : q ∈ (ρ.state p (T' + 1)).rcv m :=
  rcv_mono (by omega) _ (mem_rcv_of_sendAll H.valid hp hq h hτ (H.gst_le.trans hT))

/-- If every correct process sent `m` by `T`, every correct process has a quorum of `m` after
`T + δ`. -/
theorem quorum_of_forall (hp : p ∉ ρ.faulty) (hT : T0 ≤ T) (hT' : T + δ ≤ T')
    (hall : ∀ q ∉ ρ.faulty, ∃ τ ≤ T, SendAll ρ q m τ) :
    Fintype.card P - t ≤ #((ρ.state p (T' + 1)).rcv m) := by
  refine Quorum.card_sub_le_card_of_compl_subset H.valid.card_faulty_le fun q hq => ?_
  rw [Finset.mem_compl] at hq
  obtain ⟨τ, hτ, hs⟩ := hall q hq
  exact H.mem_rcv hp hq hs hτ hT hT'

/-- If every correct process sent some `ECHO_k` by `T`, then `Tot k` holds at every correct
process after `T + δ`. -/
theorem tot_of_forall (hp : p ∉ ρ.faulty) (hT : T0 ≤ T) (hT' : T + δ ≤ T')
    (hall : ∀ q ∉ ρ.faulty, ∃ b, ∃ τ ≤ T, SendAll ρ q (.echo k b) τ) :
    Tot t (ρ.state p (T' + 1)).rcv k := by
  refine ⟨ρ.faultyᶜ, Quorum.card_sub_le_card_compl H.valid.card_faulty_le, fun q hq => ?_⟩
  rw [Finset.mem_compl] at hq
  obtain ⟨b, τ, hτ, hs⟩ := hall q hq
  exact ⟨b, H.mem_rcv hp hq hs hτ hT hT'⟩

/-- *Quiescence* in the latency window, for guard A1. -/
theorem sendAll_of_amp (hp : p ∉ ρ.faulty) (hT0 : T0 ≤ T) (hT : T ≤ T0 + 9 * δ)
    (h : Amp t (ρ.state p (T + 1)).rcv a) : ∃ τ ≤ T, SendAll ρ p (.echo .one a) τ := by
  have := H.nonempty
  obtain ⟨τ, hτ, hs⟩ := exists_sendAll_of_mem_sent (H.proposed_eq_true hp (by omega))
    (mem_sent_of_amp (ρ.reachable_state p (T + 1)) (H.ab_eq_false hp (by omega)) h)
  exact ⟨τ, by omega, hs⟩

/-- *Quiescence* in the latency window, for the guards of phases `2`–`5`. -/
theorem sendAll_of_cand (hk : k ≠ .one) (hp : p ∉ ρ.faulty) (hT0 : T0 ≤ T)
    (hT : T ≤ T0 + 9 * δ) (h : Cand t (ρ.state p (T + 1)).rcv k a) :
    ∃ b, ∃ τ ≤ T, SendAll ρ p (.echo k b) τ := by
  obtain ⟨b, hb⟩ := sent_nonempty_of_cand (by have := H.three_mul_lt; omega)
    (ρ.reachable_state p (T + 1)) hk (H.ab_eq_false hp (by omega)) h
  obtain ⟨τ, hτ, hs⟩ := exists_sendAll_of_mem_sent (H.proposed_eq_true hp (by omega)) hb
  exact ⟨b, τ, by omega, hs⟩

/-- *Quiescence* in the latency window, for the decision guard. -/
theorem decides_of_dec (hp : p ∉ ρ.faulty) (hT : T ≤ T0 + 9 * δ)
    (h : Dec t (ρ.state p (T + 1)).rcv p v g) :
    ∃ v g, ∃ τ ≤ T, .ind (.decide v g) ∈ ρ.output p τ := by
  obtain ⟨τ, hτ, v, g, h⟩ := exists_ind_of_dec
    (dec_isSome_of_dec (ρ.reachable_state p (T + 1)) (H.ab_eq_false hp (by omega)) h)
  exact ⟨v, g, τ, by omega, h⟩

/-- The correct senders of a quorum of `ECHO_k a` recorded by a correct process by time `T + 1`
are more than `t`, and every correct process has recorded them after time `T + δ`. -/
theorem lt_card_rcv_of_quo (hq : q ∉ ρ.faulty) (h : Quo t (ρ.state q τ).rcv k a)
    (hτ : τ ≤ T + 1) (hT : T0 ≤ T) (hT' : T + δ ≤ T') (hp : p ∉ ρ.faulty) :
    t < #((ρ.state p (T' + 1)).rcv (.echo k a)) := by
  have hsub : (ρ.state q τ).rcv (.echo k a) \ ρ.faulty ⊆ (ρ.state p (T' + 1)).rcv (.echo k a) := by
    intro r hr
    rw [Finset.mem_sdiff] at hr
    obtain ⟨τ', hτ', hs⟩ := exists_sendAll_of_mem_rcv H.valid hq hr.2 hr.1
    exact H.mem_rcv hp hr.2 hs (by omega) hT hT'
  exact (Quorum.lt_card_sdiff_of_quorum H.valid.card_faulty_le H.three_mul_lt h).trans_le
    (card_le_card hsub)

/-- If `Amp ⊥` holds at every correct process after `T + δ`, then `⊥` is approved by every
correct process after `T + 2δ`. -/
theorem quo_none_of_amp (hT : T0 ≤ T) (hT' : T + δ ≤ T0 + 9 * δ) (hT'' : T + 2 * δ ≤ T')
    (h : ∀ q ∉ ρ.faulty, Amp t (ρ.state q (T + δ + 1)).rcv none) (hp : p ∉ ρ.faulty) :
    Quo t (ρ.state p (T' + 1)).rcv .one none :=
  H.quorum_of_forall hp (T := T + δ) (by omega) (by omega) fun q hq =>
    H.sendAll_of_amp hq (by omega) hT' (h q hq)

/-- *`AC` totality*: `AC` at a correct process by time `T + 1` holds at every correct process
after `T + 2δ`. Indeed, every correct process then receives more than `t` `ECHO_1 ⊥`, or more
than `t` `ECHO_1` for each of two different values, so it echoes `⊥`, and `⊥` is approved
everywhere. -/
theorem ac_totality (hq : q ∉ ρ.faulty) (h : AC t (ρ.state q τ).rcv) (hτ : τ ≤ T + 1)
    (hT : T0 ≤ T) (hT' : T + δ ≤ T0 + 9 * δ) (hT'' : T + 2 * δ ≤ T') (hp : p ∉ ρ.faulty) :
    AC t (ρ.state p (T' + 1)).rcv := by
  refine .inr (H.quo_none_of_amp hT hT' hT'' (fun p' hp' => ?_) hp)
  rcases h with ⟨a, b, hab, ha, hb⟩ | h
  · exact .inr (.inr ⟨a, b, hab, H.lt_card_rcv_of_quo hq ha hτ hT le_rfl hp',
      H.lt_card_rcv_of_quo hq hb hτ hT le_rfl hp'⟩)
  · exact .inr (.inl (H.lt_card_rcv_of_quo hq h hτ hT le_rfl hp'))

/-- Every correct process sent its `INIT` by `T0`. -/
theorem sendAll_init (hp : p ∉ ρ.faulty) : ∃ x, ∃ τ ≤ T0, SendAll ρ p (.init x) τ := by
  obtain ⟨v, τ, hτ, h⟩ := H.proposed p hp
  obtain ⟨τ', hτ', x, hs⟩ :=
    exists_sendAll_init_of_proposed (proposed_of_propose h (H.ab_eq_false hp (by omega)))
  exact ⟨x, τ', by omega, hs⟩

/-- *Phase 1*: some value `a0` is echoed by every correct process by `T0 + δ`. -/
theorem exists_echo_one : ∃ a0, ∀ p ∉ ρ.faulty, ∃ τ ≤ T0 + δ, SendAll ρ p (.echo .one a0) τ := by
  have := H.nonempty
  choose! xv hxv using fun p (hp : p ∉ ρ.faulty) => H.sendAll_init hp
  have hrec : ∀ p ∉ ρ.faulty, ∀ q ∉ ρ.faulty, q ∈ (ρ.state p (T0 + δ + 1)).rcv (.init (xv q)) := by
    intro p hp q hq
    obtain ⟨τ, hτ, hs⟩ := hxv q hq
    exact H.mem_rcv hp hq hs hτ le_rfl le_rfl
  by_cases hA : ∃ x, t < #(ρ.faultyᶜ.filter fun q => xv q = x)
  · -- case A: `t + 1` correct processes proposed `x`
    obtain ⟨x, hx⟩ := hA
    refine ⟨some x, fun p hp => H.sendAll_of_amp hp (by omega) (by omega) ?_⟩
    refine hx.trans_le (card_le_card fun q hq => ?_)
    simp only [Finset.mem_filter, Finset.mem_compl] at hq
    exact hq.2 ▸ hrec p hp q hq.1
  · -- case B: `Evid` holds everywhere
    push Not at hA
    refine ⟨none, fun p hp => H.sendAll_of_amp hp (by omega) (by omega) (.inl fun y => ?_)⟩
    refine ⟨ρ.faultyᶜ.filter fun q => ¬ xv q = y, ?_, fun q hq => ?_⟩
    · have h₁ := Finset.card_filter_add_card_filter_not (s := ρ.faultyᶜ) (fun q => xv q = y)
      have h₂ := Quorum.card_sub_le_card_compl H.valid.card_faulty_le (F := ρ.faulty)
      have h₃ := hA y
      have := H.three_mul_lt
      omega
    · simp only [Finset.mem_filter, Finset.mem_compl] at hq
      exact ⟨xv q, hq.2, hrec p hp q hq.1⟩

/-- *Phase 2*: every correct process sent `ECHO_2` by `T0 + 2δ`. -/
theorem echo_two (hp : p ∉ ρ.faulty) : ∃ b, ∃ τ ≤ T0 + 2 * δ, SendAll ρ p (.echo .two b) τ := by
  obtain ⟨a0, ha0⟩ := H.exists_echo_one
  have hq : Quo t (ρ.state p (T0 + 2 * δ + 1)).rcv .one a0 :=
    H.quorum_of_forall hp (T := T0 + δ) (by omega) (by omega) ha0
  exact H.sendAll_of_cand (by decide) hp (by omega) (by omega) (a := a0) hq

/-- *Phase 3*, unanimous case: if all correct processes sent `ECHO_2 b` by `T0 + 2δ`, every
correct process sent `ECHO_3` by `T0 + 3δ`. -/
theorem echo_three_of_forall (hb : ∀ q ∉ ρ.faulty, ∃ τ ≤ T0 + 2 * δ, SendAll ρ q (.echo .two b) τ)
    (hp : p ∉ ρ.faulty) : ∃ c, ∃ τ ≤ T0 + 3 * δ, SendAll ρ p (.echo .three c) τ := by
  have hq : Quo t (ρ.state p (T0 + 3 * δ + 1)).rcv .two b :=
    H.quorum_of_forall hp (T := T0 + 2 * δ) (by omega) (by omega) hb
  exact H.sendAll_of_cand (by decide) hp (by omega) (by omega) (a := b) (.inl hq)

/-- *Phase 3*, dichotomy: either all correct processes sent the same `ECHO_2` value by
`T0 + 2δ` (U), or `AC` holds everywhere by `T0 + 4δ` (M): two different values were approved by
correct processes by `T0 + 2δ`, so every correct process echoes `⊥` by `T0 + 3δ`. -/
theorem echo_two_dichotomy :
    (∃ b, ∀ q ∉ ρ.faulty, ∃ τ ≤ T0 + 2 * δ, SendAll ρ q (.echo .two b) τ) ∨
      ∀ p ∉ ρ.faulty, AC t (ρ.state p (T0 + 4 * δ + 1)).rcv := by
  choose! bv τv hτv hbv using fun p (hp : p ∉ ρ.faulty) => H.echo_two hp
  obtain ⟨q0, hq0⟩ := H.exists_correct
  by_cases hU : ∀ q ∉ ρ.faulty, bv q = bv q0
  · exact .inl ⟨bv q0, fun q hq => ⟨τv q, hτv q hq, hU q hq ▸ hbv q hq⟩⟩
  · push Not at hU
    obtain ⟨q1, hq1, hne⟩ := hU
    have supp : ∀ q ∉ ρ.faulty, ∀ p ∉ ρ.faulty,
        t < #((ρ.state p (T0 + 2 * δ + δ + 1)).rcv (.echo .one (bv q))) :=
      fun q hq p hp => H.lt_card_rcv_of_quo hq (cand_of_sendAll (hbv q hq))
        (T := T0 + 2 * δ) (by have := hτv q hq; omega) (by omega) le_rfl hp
    exact .inr fun p hp => .inr (H.quo_none_of_amp (T := T0 + 2 * δ) (by omega) (by omega)
      (by omega) (fun p' hp' => .inr (.inr ⟨bv q1, bv q0, hne, supp q1 hq1 p' hp',
        supp q0 hq0 p' hp'⟩)) hp)

/-- *Phase 3*: every correct process sent `ECHO_3` by `T0 + 4δ`. -/
theorem echo_three (hp : p ∉ ρ.faulty) : ∃ c, ∃ τ ≤ T0 + 4 * δ, SendAll ρ p (.echo .three c) τ := by
  rcases H.echo_two_dichotomy with ⟨b, hb⟩ | hM
  · obtain ⟨c, τ, hτ, hs⟩ := H.echo_three_of_forall hb hp
    exact ⟨c, τ, by omega, hs⟩
  · exact H.sendAll_of_cand (by decide) hp (by omega) (by omega) (a := none) (.inr ⟨rfl, hM p hp⟩)

/-- If a correct process sends `ECHO_3 ⊥`, then `AC` holds everywhere by `T0 + 5δ`. -/
theorem ac_of_sendAll_three (hr : r ∉ ρ.faulty) (h : SendAll ρ r (.echo .three none) τ)
    (hp : p ∉ ρ.faulty) : AC t (ρ.state p (T0 + 5 * δ + 1)).rcv := by
  rcases H.echo_two_dichotomy with ⟨b, hb⟩ | hM
  · -- (U): `r` sent its `ECHO_3` by `T0 + 3δ`
    obtain ⟨c, τ', hτ', hs⟩ := H.echo_three_of_forall hb hr
    obtain ⟨rfl, rfl⟩ := sendAll_echo_unique (by decide) h hs
    rcases cand_of_sendAll h with hq2 | ⟨-, h2⟩
    · -- E2-branch with `⊥`: the common `ECHO_2` value is `⊥`
      obtain ⟨q, hq, _, -, hs'⟩ :=
        exists_correct_of_lt_card H.valid hr (lt_card_of_quo H.three_mul_lt hq2)
      obtain ⟨τq, -, hsq⟩ := hb q hq
      obtain ⟨rfl, -⟩ := sendAll_echo_unique (by decide) hs' hsq
      obtain ⟨τp, hτp, hsp⟩ := hb p hp
      exact AC.mono (rcv_mono (by omega)) (.inr (cand_of_sendAll hsp))
    · -- approved-branch
      exact H.ac_totality hr h2 (T := T0 + 3 * δ) (by omega) (by omega) (by omega) (by omega) hp
  · exact (hM p hp).mono (rcv_mono (by omega))

/-- Two correct processes that sent `ECHO_k` with different values, `k ∈ {3, 4, 5}`: one of them
sent `ECHO_k ⊥`. -/
theorem exists_sendAll_none (hk : k = .three ∨ k = .four ∨ k = .five) {cv : P → Option Value}
    {τv : P → ℕ} (hcv : ∀ q ∉ ρ.faulty, SendAll ρ q (.echo k (cv q)) (τv q))
    (hq : q ∉ ρ.faulty) (hq' : r ∉ ρ.faulty) (hne : cv q ≠ cv r) :
    ∃ q' ∉ ρ.faulty, ∃ τ, SendAll ρ q' (.echo k none) τ := by
  rcases sendAll_eq_none_or H.valid H.three_mul_lt hk hq hq' (hcv q hq) (hcv r hq') hne with h | h
  · exact ⟨q, hq, τv q, h ▸ hcv q hq⟩
  · exact ⟨r, hq', τv r, h ▸ hcv r hq'⟩

/-- *Phase 4*: every correct process sent `ECHO_4` by `T0 + 5δ`. -/
theorem echo_four (hp : p ∉ ρ.faulty) : ∃ c, ∃ τ ≤ T0 + 5 * δ, SendAll ρ p (.echo .four c) τ := by
  choose! cv τv hτv hcv using fun p (hp : p ∉ ρ.faulty) => H.echo_three hp
  have htot : Tot t (ρ.state p (T0 + 5 * δ + 1)).rcv .three :=
    H.tot_of_forall hp (T := T0 + 4 * δ) (by omega) (by omega)
      fun q hq => ⟨cv q, τv q, hτv q hq, hcv q hq⟩
  obtain ⟨q0, hq0⟩ := H.exists_correct
  by_cases hU : ∀ q ∉ ρ.faulty, cv q = cv q0
  · have hq : Quo t (ρ.state p (T0 + 5 * δ + 1)).rcv .three (cv q0) :=
      H.quorum_of_forall hp (T := T0 + 4 * δ) (by omega) (by omega)
        fun q hq => ⟨τv q, hτv q hq, hU q hq ▸ hcv q hq⟩
    exact H.sendAll_of_cand (by decide) hp (by omega) (by omega) (a := cv q0) (.inr hq)
  · push Not at hU
    obtain ⟨q1, hq1, hne⟩ := hU
    obtain ⟨r, hr, τr, hsr⟩ := H.exists_sendAll_none (.inl rfl) hcv hq1 hq0 hne
    exact H.sendAll_of_cand (by decide) hp (by omega) (by omega) (a := none)
      (.inl ⟨rfl, htot, H.ac_of_sendAll_three hr hsr hp⟩)

/-- If a correct process sends `ECHO_4 ⊥`, then `AC` holds everywhere by `T0 + 7δ`. -/
theorem ac_of_sendAll_four (hr : r ∉ ρ.faulty) (h : SendAll ρ r (.echo .four none) τ)
    (hp : p ∉ ρ.faulty) : AC t (ρ.state p (T0 + 7 * δ + 1)).rcv := by
  obtain ⟨c, τ', hτ', hs⟩ := H.echo_four hr
  obtain ⟨rfl, rfl⟩ := sendAll_echo_unique (by decide) h hs
  rcases cand_of_sendAll h with ⟨-, -, hac⟩ | hq3
  · exact H.ac_totality hr hac (T := T0 + 5 * δ) (by omega) (by omega) (by omega) (by omega) hp
  · obtain ⟨q, hq, _, -, hs'⟩ :=
      exists_correct_of_lt_card H.valid hr (lt_card_of_quo H.three_mul_lt hq3)
    exact (H.ac_of_sendAll_three hq hs' hp).mono (rcv_mono (by omega))

/-- *Phase 5*: every correct process sent `ECHO_5` by `T0 + 7δ`. -/
theorem echo_five (hp : p ∉ ρ.faulty) : ∃ c, ∃ τ ≤ T0 + 7 * δ, SendAll ρ p (.echo .five c) τ := by
  choose! cv τv hτv hcv using fun p (hp : p ∉ ρ.faulty) => H.echo_four hp
  have htot : Tot t (ρ.state p (T0 + 7 * δ + 1)).rcv .four :=
    H.tot_of_forall hp (T := T0 + 5 * δ) (by omega) (by omega)
      fun q hq => ⟨cv q, τv q, hτv q hq, hcv q hq⟩
  obtain ⟨q0, hq0⟩ := H.exists_correct
  by_cases hU : ∀ q ∉ ρ.faulty, cv q = cv q0
  · have hq : Quo t (ρ.state p (T0 + 6 * δ + 1)).rcv .four (cv q0) :=
      H.quorum_of_forall hp (T := T0 + 5 * δ) (by omega) (by omega)
        fun q hq => ⟨τv q, hτv q hq, hU q hq ▸ hcv q hq⟩
    obtain ⟨c, τ, hτ, hs⟩ := H.sendAll_of_cand (k := .five) (T := T0 + 6 * δ) (by decide) hp
      (by omega) (by omega) (a := cv q0) (.inl hq)
    exact ⟨c, τ, by omega, hs⟩
  · push Not at hU
    obtain ⟨q1, hq1, hne⟩ := hU
    obtain ⟨r, hr, τr, hsr⟩ := H.exists_sendAll_none (.inr (.inl rfl)) hcv hq1 hq0 hne
    exact H.sendAll_of_cand (by decide) hp (by omega) (by omega) (a := none)
      (.inr ⟨rfl, htot, H.ac_of_sendAll_four hr hsr hp⟩)

/-- If a correct process sends `ECHO_5 ⊥`, then `AC` holds everywhere by `T0 + 9δ`. -/
theorem ac_of_sendAll_five (hr : r ∉ ρ.faulty) (h : SendAll ρ r (.echo .five none) τ)
    (hp : p ∉ ρ.faulty) : AC t (ρ.state p (T0 + 9 * δ + 1)).rcv := by
  obtain ⟨c, τ', hτ', hs⟩ := H.echo_five hr
  obtain ⟨rfl, rfl⟩ := sendAll_echo_unique (by decide) h hs
  rcases cand_of_sendAll h with hq4 | ⟨-, -, hac⟩
  · obtain ⟨q, hq, _, -, hs'⟩ :=
      exists_correct_of_lt_card H.valid hr (lt_card_of_quo H.three_mul_lt hq4)
    exact (H.ac_of_sendAll_four hq hs' hp).mono (rcv_mono (by omega))
  · exact H.ac_totality hr hac (T := T0 + 7 * δ) (by omega) (by omega) (by omega) (by omega) hp

/-- *Decision*: every correct process decides by `T0 + 9δ`. -/
theorem decides (hp : p ∉ ρ.faulty) :
    ∃ v g, ∃ τ ≤ T0 + 9 * δ, .ind (.decide v g) ∈ ρ.output p τ := by
  choose! ev τv hτv hev using fun p (hp : p ∉ ρ.faulty) => H.echo_five hp
  obtain ⟨x, τx, hτx, hsx⟩ := H.sendAll_init hp
  have hself : p ∈ (ρ.state p (T0 + 9 * δ + 1)).rcv (.init x) :=
    H.mem_rcv hp hp hsx hτx le_rfl (by omega)
  have htot : Tot t (ρ.state p (T0 + 9 * δ + 1)).rcv .five :=
    H.tot_of_forall hp (T := T0 + 7 * δ) (by omega) (by omega)
      fun q hq => ⟨ev q, τv q, hτv q hq, hev q hq⟩
  obtain ⟨q0, hq0⟩ := H.exists_correct
  by_cases hU : ∀ q ∉ ρ.faulty, ev q = ev q0
  · -- all correct `ECHO_5` carry the same value: D2 or D0
    have hq : Quo t (ρ.state p (T0 + 9 * δ + 1)).rcv .five (ev q0) :=
      H.quorum_of_forall hp (T := T0 + 7 * δ) (by omega) (by omega)
        fun q hq => ⟨τv q, hτv q hq, hU q hq ▸ hev q hq⟩
    cases h0 : ev q0 with
    | none =>
      exact H.decides_of_dec hp le_rfl (v := x) (g := false) ⟨⟨x, hself⟩, .inr ⟨h0 ▸ hq, hself⟩⟩
    | some v =>
      rw [h0] at hq
      exact H.decides_of_dec hp le_rfl (v := v) (g := true) ⟨⟨x, hself⟩, hq⟩
  · -- they carry `some v°` and `⊥`: D1
    push Not at hU
    obtain ⟨q1, hq1, hne⟩ := hU
    obtain ⟨r₁, hr₁, v, τ₁, hτ₁, hs₁, r₂, hr₂, τ₂, hs₂⟩ : ∃ r₁ ∉ ρ.faulty, ∃ v τ₁, τ₁ ≤ T0 + 7 * δ ∧
        SendAll ρ r₁ (.echo .five (some v)) τ₁ ∧
        ∃ r₂ ∉ ρ.faulty, ∃ τ₂, SendAll ρ r₂ (.echo .five none) τ₂ := by
      rcases sendAll_eq_none_or H.valid H.three_mul_lt (.inr (.inr rfl)) hq1 hq0 (hev q1 hq1)
        (hev q0 hq0) hne with h | h
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 fun h' => hne (h.trans h'.symm)
        exact ⟨q0, hq0, v, τv q0, hτv q0 hq0, hv ▸ hev q0 hq0, q1, hq1, τv q1, h ▸ hev q1 hq1⟩
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 fun h' => hne (h'.trans h.symm)
        exact ⟨q1, hq1, v, τv q1, hτv q1 hq1, hv ▸ hev q1 hq1, q0, hq0, τv q0, h ▸ hev q0 hq0⟩
    have hq4 : Quo t (ρ.state r₁ (τ₁ + 1)).rcv .four (some v) := by
      rcases cand_of_sendAll hs₁ with h | ⟨h, -⟩
      · exact h
      · cases h
    refine H.decides_of_dec hp le_rfl (v := v) (g := false)
      ⟨⟨x, hself⟩, .inl ⟨htot, H.ac_of_sendAll_five hr₂ hs₂ hp, ⟨r₁, ?_⟩, ?_⟩⟩
    · exact H.mem_rcv hp hr₁ hs₁ (T := T0 + 7 * δ) hτ₁ (by omega) (by omega)
    · exact H.lt_card_rcv_of_quo hr₁ hq4 (T := T0 + 7 * δ) (by omega) (by omega) (by omega) hp

end Timely

end Latency

end AttiyaWelch

end Cslib.Distributed
