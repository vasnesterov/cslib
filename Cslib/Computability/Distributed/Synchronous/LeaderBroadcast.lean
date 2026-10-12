/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.Byzantine

/-! # Leader broadcast

*Leader broadcast* with leader `ℓ` is the one-round synchronous algorithm in which `ℓ` sends its
proposal to every process, and each process decides the value it received from `ℓ`, if any (and
decides nothing otherwise).

In Crux ([Civit et al., *Partial synchrony for free?*][CivitEtAl2024], §5), Step 2 simulates a
synchronous Byzantine agreement algorithm `A^S`. The safety properties of Crux do not depend on
Step 2, and its synchronicity property uses only that the simulated execution satisfies Byzantine
agreement. Simulating one round of leader broadcast instead of `A^S` thus gives a Crux whose
synchronicity holds whenever the leader is correct: leader broadcast satisfies Byzantine agreement
after one round in every execution in which `ℓ` is correct, whatever the number of faulty
processes:
* *termination* and *agreement*: every correct process receives, and decides, the proposal of
  `ℓ`;
* *strong validity*: if all correct processes propose `v`, then so does `ℓ`;
* *external validity*: the proposal of the correct process `ℓ` is valid.

If `ℓ` is faulty, leader broadcast guarantees nothing: correct processes may decide different
values, invalid values, or nothing.

## Main definitions

* `LeaderBroadcast.algorithm Value ℓ`: leader broadcast with leader `ℓ`.

## Main statements

* `LeaderBroadcast.solves_of_correct`: every execution in which `ℓ` is correct and the proposals
  of correct processes are valid satisfies Byzantine agreement after `1` round.
* `LeaderBroadcast.perProcessBits`: if values have at most `L` bits, a process sends at most
  `n * L` bits in the first round (`Synchronous.Algorithm.PerProcessBits`).

## Implementation notes

The leader sends its proposal in every round, and a process records the message received from `ℓ`
in the last round. Only the first round matters: the algorithm is run for `R = 1` round.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Distributed.Synchronous.LeaderBroadcast

/-- The local state of a process in leader broadcast. -/
structure State (Value : Type) where
  /-- The proposal of the process (sent if the process is the leader). -/
  proposal : Value
  /-- The message received from the leader in the last round, if any: the decision. -/
  received : Option Value

variable {P : Type*} [DecidableEq P]

variable (Value : Type) in
/-- **Leader broadcast** with leader `ℓ`: in every round, `ℓ` sends its proposal to every process
(and the other processes send nothing), and at the end of the round every process records the
message it received from `ℓ`. The decision is the recorded message; after `1` round, it is the
proposal of `ℓ` received in round `1`, if any. -/
@[reducible] def algorithm (ℓ : P) : Algorithm P Value where
  State := State Value
  Msg := Value
  init _ v := ⟨v, none⟩
  send p s _ _ := if p = ℓ then some s.proposal else none
  next _ s _ m := { s with received := m ℓ }
  decision s := s.received

variable {Value : Type} {ℓ : P} {E : (algorithm Value ℓ).Execution} {p : P}

/-- After the first round, a process decides the message it received from `ℓ` in that round. -/
theorem decision_state_one :
    (algorithm Value ℓ).decision (E.state 1 p) = E.received (E.state 0) 1 p ℓ :=
  rfl

/-- If `ℓ` is correct, every process decides the proposal of `ℓ` after the first round. -/
theorem decision_state_one_of_notMem (hℓ : ℓ ∉ E.faulty) :
    (algorithm Value ℓ).decision (E.state 1 p) = some (E.proposal ℓ) := by
  rw [decision_state_one]
  simp [hℓ]

/-- **Leader broadcast solves Byzantine agreement if the leader is correct**: every execution of
leader broadcast in which `ℓ` is correct and the proposals of correct processes are valid
satisfies Byzantine agreement after `1` round (for any number of faulty processes): every correct
process decides the proposal of `ℓ`. -/
theorem solves_of_correct {valid : Value → Prop} (hℓ : ℓ ∉ E.faulty)
    (hvalid : ∀ p ∉ E.faulty, valid (E.proposal p)) : E.ByzantineAgreement valid 1 where
  termination _ _ := ⟨_, decision_state_one_of_notMem hℓ⟩
  agreement _ _ _ _ _ _ hv hw := by
    rw [decision_state_one_of_notMem hℓ, Option.some_inj] at hv hw
    rw [← hv, ← hw]
  strongValidity v hv _ _ _ hw := by
    rw [decision_state_one_of_notMem hℓ, Option.some_inj] at hw
    rw [← hw, hv ℓ hℓ]
  externalValidity _ _ _ hv := by
    rw [decision_state_one_of_notMem hℓ, Option.some_inj] at hv
    exact hv ▸ hvalid ℓ hℓ

/-- **Bits of leader broadcast.** If values have at most `L` bits (for the value sizes `size`),
then in every execution every process sends at most `n * L` bits in the first round: at most one
value to each process. -/
theorem perProcessBits [Fintype P] {size : Value → ℕ} {L : ℕ} (hL : ∀ v, size v ≤ L) {t : ℕ} :
    (algorithm Value ℓ).PerProcessBits t size 1 (Fintype.card P * L) := by
  simpa using Algorithm.perProcessBits_of_size_le (algorithm Value ℓ) hL t 1

end Cslib.Distributed.Synchronous.LeaderBroadcast
