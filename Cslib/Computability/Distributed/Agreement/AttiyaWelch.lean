/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.AttiyaWelch.Communication
public import Cslib.Computability.Distributed.Agreement.AttiyaWelch.Latency

/-! # The Attiya–Welch graded consensus protocol AW′

AW′ (`Cslib.Distributed.AttiyaWelch.protocol`), a version of Algorithm 3 of
[Attiya and Welch, *Multi-valued connected consensus*][AttiyaWelch2023] (`R = 2`) adapted to the
graded consensus interface of [Civit et al., *Partial synchrony for free?*][CivitEtAl2024],
satisfies graded consensus (`Cslib.Distributed.GradedConsensus.spec`) with latency `9δ` for
`3t < n`, and a process sends `O(n)` messages and `O(n L)` bits for `L`-bit values in every run
(for `t > 0`). The protocol is defined in
`Cslib.Computability.Distributed.Agreement.AttiyaWelch.Protocol`, its safety, latency and
communication are proved in `...AttiyaWelch.Safety`, `...AttiyaWelch.Latency` and
`...AttiyaWelch.Communication`.

## Main statements

* `AttiyaWelch.satisfies`: for `3t < n`, AW′ satisfies graded consensus with latency `9δ`.
* `AttiyaWelch.requestQuiet`: AW′ is request-quiet.
* `AttiyaWelch.sendsWhileActive`: a process sends messages only from its proposal on and never
  after it has abandoned (`Protocol.SendsWhileActive`). This participation gate costs nothing in
  the specification: safety only constrains the messages correct processes do send, and the
  latency bound assumes that all correct processes have proposed.
* Communication, in every run (no validity needed): `AttiyaWelch.countP_send_le` (at most
  `⌊n / (t + 1)⌋ + 6` messages to each process), `AttiyaWelch.bitsSent_one_le` (at most
  `n (⌊n / (t + 1)⌋ + 6)` messages), `AttiyaWelch.bitsSent_le` (at most
  `n (⌊n / (t + 1)⌋ + 6) (L + 5)` bits for values of at most `L` bits, `AttiyaWelch.Msg.size`).

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

variable {P Value : Type} [DecidableEq P] [DecidableEq Value] [Fintype P] {t : ℕ}

/-- **AW′ is a graded consensus protocol** with latency `9δ`: for `3t < n`, every valid run
satisfies strong validity (`unanimity_decide`), external validity (from `proposal_validity` and the
validity of correct proposals), consistency, integrity, and the timed latency `9δ`
(`Timely.decides`); this justifies the claim of [CivitEtAl2024], appendix "Existing primitives",
that AW "terminates in 9 asynchronous rounds". -/
theorem satisfies (hn : 3 * t < Fintype.card P) (valid : Value → Prop) (δ : ℕ) :
    (protocol P Value t).Satisfies t δ (GradedConsensus.spec valid (9 * δ)) := by
  intro ρ hρ hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hU p hp w g τ h
    exact unanimity_decide hρ hn (fun q hq w τ h => hU q hq w τ (Run.history_reqAt.2 h)) hp
      (Run.history_indAt.1 h)
  · intro p hp w g τ h
    obtain ⟨q, hq, τ', h'⟩ := proposal_validity hρ hn hp (Run.history_indAt.1 h)
    exact hA.validProposal q hq w τ' (Run.history_reqAt.2 h')
  · intro p q hp hq v w g τ τ' h₁ h₂
    exact consistency hρ hn hp hq (Run.history_indAt.1 h₁) (Run.history_indAt.1 h₂)
  · intro p _
    exact atMostOnce ρ p (fun _ => rfl) (fun _ => rfl)
  · intro τ hprop hab p hp
    have H : Timely ρ δ (max τ ρ.gst) := by
      refine ⟨hρ, hn, le_max_right _ _, fun p hp => ?_, fun p hp τ' hτ' h => ?_⟩
      · obtain ⟨v, τ', hτ', h⟩ := hprop p hp
        exact ⟨v, τ', le_max_of_le_left hτ', Run.history_reqAt.1 h⟩
      · exact hab p hp ⟨τ', hτ', Run.history_reqAt.2 h⟩
    obtain ⟨v, g, τ', hτ', h⟩ := H.decides hp
    exact ⟨v, g, τ', hτ', Run.history_indAt.2 h⟩

end AttiyaWelch

end Cslib.Distributed
