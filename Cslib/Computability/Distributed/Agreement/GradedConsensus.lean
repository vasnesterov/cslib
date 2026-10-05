/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Spec

/-! # Graded consensus

In graded consensus, processes propose values and decide a value together with a binary *grade*.
Agreement is only guaranteed in the presence of a grade-`1` decision: if some correct process
decides `(v, 1)`, then every correct process decides `v` (with some grade). We follow the
variant of [Civit et al., *Partial synchrony for free?*][CivitEtAl2024], §5.2, Module 2
(`mod:graded-consensus`), which also allows processes to *abandon* the primitive (stop
participating in it) and does not assume that all correct processes propose.

**Interface.** Requests `propose v` and `abandon`; indication `decide v g`. Grades are
booleans: `g = true` is grade `1` and `g = false` is grade `0`.

**Assumptions** (on the environment, `Assumptions`): every correct process proposes at most
once, and correct processes propose only valid values (for a predicate `valid`).

**Properties** (`Properties`, for a latency `Δ`):
* *Strong validity*: if all correct processes that propose do so with the same value `v`, then
  every decision of a correct process is `(v, 1)`.
* *External validity*: correct processes decide only valid values.
* *Consistency*: if a correct process decides `(v, 1)`, then no correct process decides a value
  other than `v`.
* *Integrity*: no correct process decides more than once.
* *Latency* (timed termination): for every time `τ`, if all correct processes have proposed by
  `τ` and no correct process abandons by `max τ gst + Δ`, then all correct processes decide by
  `max τ gst + Δ`.

The paper only requires (eventual) *termination* — if all correct processes propose and none
abandons, all correct processes eventually decide — together with a "known worst-case latency"
measured in asynchronous rounds. The timed latency property above is the form in which this
latency is used ([Civit et al.][CivitEtAl2024], Crux, `theorem:block_synchronicity`, and the
latency analysis of Oper): it measures time from the *last* proposal (proposals may be spread
out, and may happen before GST), and it only requires that nobody abandons before the deadline,
since the primitive may legitimately be abandoned later. Termination is a consequence. The
deadline is inclusive: an `abandon` handled in the batch of time `max τ gst + Δ` may suppress a
decision in that batch.

The specification does not exclude decisions of processes that have not proposed (or have
abandoned); users must take such decisions into account.

## Main definitions

* `GradedConsensus.interface`: the interface of graded consensus.
* `GradedConsensus.Assumptions`, `GradedConsensus.Properties`, `GradedConsensus.spec`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Distributed.GradedConsensus

/-- The requests of graded consensus. -/
inductive Req (Value : Type) where
  /-- Propose value `v`. -/
  | propose (v : Value)
  /-- Abandon graded consensus, i.e. stop participating in it. -/
  | abandon
deriving DecidableEq

/-- The indications of graded consensus. -/
inductive Ind (Value : Type) where
  /-- Decide value `v` with grade `g`, where `true` is grade `1` and `false` is grade `0`. -/
  | decide (v : Value) (g : Bool)
deriving DecidableEq

/-- The interface of graded consensus on values `Value`. -/
abbrev interface (Value : Type) : Interface where
  Req := Req Value
  Ind := Ind Value

variable {P : Type*} {Value : Type}

/-- The environment assumptions of graded consensus ([CivitEtAl2024], Module 2, "Notes"). -/
structure Assumptions (valid : Value → Prop) (H : History P (interface Value)) : Prop where
  /-- Every correct process proposes at most once. -/
  proposeAtMostOnce : ∀ p, H.Correct p → H.AtMostOnce p (· matches .req (.propose _))
  /-- Correct processes propose only valid values. -/
  validProposal : ∀ p, H.Correct p → ∀ v τ, H.ReqAt p (.propose v) τ → valid v

/-- The guarantees of graded consensus with latency `Δ` ([CivitEtAl2024], Module 2, with
termination replaced by the timed `latency`). -/
structure Properties (valid : Value → Prop) (Δ : ℕ) (H : History P (interface Value)) :
    Prop where
  /-- *Strong validity*: if all correct processes that propose do so with the same value `v` and
  a correct process decides a pair `(v', g')`, then `v' = v` and `g' = 1`. -/
  strongValidity : ∀ v, (∀ p, H.Correct p → ∀ w τ, H.ReqAt p (.propose w) τ → w = v) →
    ∀ p, H.Correct p → ∀ w g τ, H.IndAt p (.decide w g) τ → w = v ∧ g = true
  /-- *External validity*: if a correct process decides a pair `(v', ·)`, then `valid v'`. -/
  externalValidity : ∀ p, H.Correct p → ∀ w g τ, H.IndAt p (.decide w g) τ → valid w
  /-- *Consistency*: if a correct process decides a pair `(v, 1)`, then no correct process
  decides a pair `(v', ·)` with `v' ≠ v`. -/
  consistency : ∀ p q, H.Correct p → H.Correct q → ∀ v w g τ τ',
    H.IndAt p (.decide v true) τ → H.IndAt q (.decide w g) τ' → w = v
  /-- *Integrity*: no correct process decides more than once. -/
  integrity : ∀ p, H.Correct p → H.AtMostOnce p (· matches .ind _)
  /-- *Latency* (timed termination): if every correct process has proposed by time `τ` and no
  correct process abandons by time `max τ gst + Δ`, then every correct process decides by time
  `max τ gst + Δ`. -/
  latency : ∀ τ, (∀ p, H.Correct p → ∃ v, H.ReqBy p (.propose v) τ) →
    (∀ p, H.Correct p → ¬ H.ReqBy p .abandon (max τ H.gst + Δ)) →
    ∀ p, H.Correct p → ∃ v g, H.IndBy p (.decide v g) (max τ H.gst + Δ)

/-- The specification of graded consensus for the validity predicate `valid`, with latency `Δ`:
if the environment satisfies the assumptions, then the guarantees hold. -/
def spec (valid : Value → Prop) (Δ : ℕ) : Spec P (interface Value) :=
  fun H => Assumptions valid H → Properties valid Δ H

end Cslib.Distributed.GradedConsensus
