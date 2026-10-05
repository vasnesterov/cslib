/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Existence
public import Cslib.Computability.Distributed.MessagePassing.InputProtocol
public import Cslib.Computability.Distributed.Synchronous.Algorithm
public import Mathlib.Data.Finset.Card

/-! # Byzantine agreement

In Byzantine agreement, each process proposes a value and all correct processes must decide a
common valid value, despite up to `t` Byzantine (arbitrarily behaving) processes. Following
[Civit et al., *Partial synchrony for free?*][CivitEtAl2024], §1, we require, for a predicate
`valid : Value → Prop` such that the proposals of correct processes are valid:

* *Agreement*: no two correct processes decide different values.
* *Termination*: all correct processes (eventually) decide.
* *Strong validity*: if all correct processes propose the same value `v`, then no correct process
  decides a value other than `v`.
* *External validity*: if a correct process decides a value `v`, then `valid v`.

## Synchronous Byzantine agreement

For a synchronous algorithm (`Synchronous.Algorithm`), termination is quantified by a latency
`R`: decisions are read from the processes' states after exactly `R` rounds, and every correct
process must have decided by then. This is how the paper uses a synchronous algorithm: it is
run for exactly `R` rounds, after which its decision (if any) is read
([Civit et al.][CivitEtAl2024], §5, Crux, Step 2). Since the decision is read only once,
*integrity* (no correct process decides more than once) holds by construction and is not
stated.

## Partially synchronous Byzantine agreement

For message-passing protocols in partial synchrony (`Cslib.Distributed.Protocol`), Byzantine
agreement is a specification (`ByzantineAgreement.spec`) on the interface with the request
`start` and the indication `decide v`. The proposal of a process is its *private input*: a
protocol for Byzantine agreement is an `InputProtocol` with inputs in `Value`, and for proposals
`prop : P → Value` process `p` runs with input `prop p` (`InputProtocol.toProtocol`); the paper's
request `propose v` of process `p` corresponds to `start` with `v = prop p`. That process `p`
cannot read the proposals of other processes is essential: for a family of protocols indexed by
all proposals, a protocol deciding a global function of the proposals without communication
would satisfy the specification (see `Cslib.Distributed.InputProtocol`).

The environment assumptions are that the proposals of correct processes are valid, and that every
correct process is started exactly once, no later than GST ([Civit et al.][CivitEtAl2024], §4:
"all correct processes start executing their local algorithm before GST"). The guarantees are
agreement, strong validity, external validity, *integrity* (no correct process decides more than
once), and termination with a latency `L`: every correct process decides by time `gst + L`.
The paper measures latency as `max (τ* - GST, 0)` (in units of `δ`), where `τ*` is the time by
which all correct processes have decided; a bound on it is a bound `L` as above.

## Main definitions

* `Synchronous.Algorithm.Execution.ByzantineAgreement`: the properties of Byzantine agreement
  for one execution of a synchronous algorithm, with decisions read after `R` rounds.
* `Synchronous.Algorithm.SolvesByzantineAgreement`: a synchronous algorithm is a `t`-resilient
  Byzantine agreement algorithm with latency `R`.
* `ByzantineAgreement.interface`, `ByzantineAgreement.Assumptions`,
  `ByzantineAgreement.Properties`, `ByzantineAgreement.spec`: Byzantine agreement for
  message-passing protocols in partial synchrony.
* `InputProtocol.SolvesByzantineAgreement`: a protocol with private inputs (the proposals) is a
  `t`-resilient partially synchronous Byzantine agreement protocol with latency `L`.

## Main statements

* `InputProtocol.SolvesByzantineAgreement.exists_run`: non-vacuity of
  `InputProtocol.SolvesByzantineAgreement` for `0 < δ`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Distributed

/-! ## Synchronous Byzantine agreement -/

namespace Synchronous.Algorithm

variable {P Value : Type*} [DecidableEq P] {A : Algorithm P Value}

/-- The properties of Byzantine agreement (for the validity predicate `valid`) in an execution
`E` of a synchronous algorithm, where the decision of a process is the one in its state after `R`
rounds. -/
structure Execution.ByzantineAgreement (E : A.Execution) (valid : Value → Prop) (R : ℕ) :
    Prop where
  /-- Every correct process has decided after `R` rounds. -/
  termination : ∀ p ∉ E.faulty, ∃ v, A.decision (E.state R p) = some v
  /-- No two correct processes decide different values. -/
  agreement : ∀ p ∉ E.faulty, ∀ q ∉ E.faulty, ∀ v w,
    A.decision (E.state R p) = some v → A.decision (E.state R q) = some w → v = w
  /-- If all correct processes propose `v`, then correct processes can only decide `v`. -/
  strongValidity : ∀ v, (∀ p ∉ E.faulty, E.proposal p = v) →
    ∀ p ∉ E.faulty, ∀ w, A.decision (E.state R p) = some w → w = v
  /-- Correct processes only decide valid values. -/
  externalValidity : ∀ p ∉ E.faulty, ∀ v, A.decision (E.state R p) = some v → valid v

variable (A) in
/-- `A` is a `t`-resilient synchronous Byzantine agreement algorithm with latency `R` for the
validity predicate `valid`: every execution with at most `t` faulty processes in which correct
processes propose valid values satisfies Byzantine agreement after `R` rounds. -/
def SolvesByzantineAgreement (t : ℕ) (valid : Value → Prop) (R : ℕ) : Prop :=
  ∀ E : A.Execution, E.faulty.card ≤ t → (∀ p ∉ E.faulty, valid (E.proposal p)) →
    E.ByzantineAgreement valid R

namespace Execution.ByzantineAgreement

variable {E : A.Execution} {valid : Value → Prop} {R : ℕ}

/-- If there is a correct process, then all correct processes decide the same valid value. -/
theorem exists_decision (h : E.ByzantineAgreement valid R) {p₀ : P} (hp₀ : p₀ ∉ E.faulty) :
    ∃ v, valid v ∧ ∀ p ∉ E.faulty, A.decision (E.state R p) = some v := by
  obtain ⟨v, hv⟩ := h.termination p₀ hp₀
  refine ⟨v, h.externalValidity p₀ hp₀ v hv, fun p hp => ?_⟩
  obtain ⟨w, hw⟩ := h.termination p hp
  rw [hw, h.agreement p hp p₀ hp₀ w v hw hv]

/-- If all correct processes propose `v`, then all correct processes decide `v`. -/
theorem decision_eq (h : E.ByzantineAgreement valid R) {v : Value}
    (hv : ∀ p ∉ E.faulty, E.proposal p = v) {p : P} (hp : p ∉ E.faulty) :
    A.decision (E.state R p) = some v := by
  obtain ⟨w, hw⟩ := h.termination p hp
  rw [hw, h.strongValidity v hv p hp w hw]

end Execution.ByzantineAgreement

end Synchronous.Algorithm

/-! ## Partially synchronous Byzantine agreement -/

namespace ByzantineAgreement

/-- The requests of Byzantine agreement for message-passing protocols. -/
inductive Req where
  /-- Start executing the protocol. The proposal of a process is its private input
  (`InputProtocol`). -/
  | start
deriving DecidableEq

/-- The indications of Byzantine agreement. -/
inductive Ind (Value : Type) where
  /-- Decide value `v`. -/
  | decide (v : Value)
deriving DecidableEq

/-- The interface of Byzantine agreement on values `Value`. -/
abbrev interface (Value : Type) : Interface where
  Req := Req
  Ind := Ind Value

variable {P : Type*} {Value : Type}

/-- The environment assumptions of Byzantine agreement, for the validity predicate `valid` and
the proposals `prop`: the proposals of correct processes are valid, and every correct process is
started exactly once, no later than GST. -/
structure Assumptions (valid : Value → Prop) (prop : P → Value)
    (H : History P (interface Value)) : Prop where
  /-- Correct processes propose valid values. -/
  validProposal : ∀ p, H.Correct p → valid (prop p)
  /-- Every correct process is started at most once. -/
  startAtMostOnce : ∀ p, H.Correct p → H.AtMostOnce p (· matches .req _)
  /-- Every correct process is started no later than GST. -/
  startByGst : ∀ p, H.Correct p → H.ReqBy p .start H.gst

/-- The guarantees of Byzantine agreement with latency `L`, for the validity predicate `valid`
and the proposals `prop` ([CivitEtAl2024], §1). -/
structure Properties (valid : Value → Prop) (prop : P → Value) (L : ℕ)
    (H : History P (interface Value)) : Prop where
  /-- *Agreement*: no two correct processes decide different values. -/
  agreement : ∀ p q, H.Correct p → H.Correct q → ∀ v w τ τ',
    H.IndAt p (.decide v) τ → H.IndAt q (.decide w) τ' → v = w
  /-- *Strong validity*: if all correct processes propose the same value `v`, then no correct
  process decides a value other than `v`. -/
  strongValidity : ∀ v, (∀ p, H.Correct p → prop p = v) →
    ∀ p, H.Correct p → ∀ w τ, H.IndAt p (.decide w) τ → w = v
  /-- *External validity*: if a correct process decides a value `v`, then `valid v`. -/
  externalValidity : ∀ p, H.Correct p → ∀ v τ, H.IndAt p (.decide v) τ → valid v
  /-- *Integrity*: no correct process decides more than once (over its whole trace, counting
  every `decide` event, including several in the same batch). -/
  integrity : ∀ p, H.Correct p → H.AtMostOnce p (· matches .ind _)
  /-- *Termination* with latency `L`: every correct process decides by time `gst + L`. -/
  termination : ∀ p, H.Correct p → ∃ v, H.IndBy p (.decide v) (H.gst + L)

/-- The specification of partially synchronous Byzantine agreement with latency `L`, for the
validity predicate `valid` and the proposals `prop`. -/
def spec (valid : Value → Prop) (prop : P → Value) (L : ℕ) : Spec P (interface Value) :=
  fun H => Assumptions valid prop H → Properties valid prop L H

end ByzantineAgreement

namespace InputProtocol

variable {P : Type*} {Value : Type}

/-- The protocol `A`, whose processes receive their proposals as private inputs, is a
`t`-resilient partially synchronous Byzantine agreement protocol for the validity predicate
`valid` (with post-GST message delay bound `δ`), with latency `L`: for all proposals `prop`, every
valid run of `A.toProtocol prop` (process `p` proposes `prop p`, at most `t` processes are faulty)
in which correct processes have valid proposals and are started exactly once, by GST, satisfies
Byzantine agreement, and all correct processes decide by `gst + L`.

The definition is meaningful only for `0 < δ` (see `Run.Valid`): for `δ = 0`, a message sent by a
correct process to a correct process at a time `τ ≥ gst` would have to be delivered in `(τ, τ]`,
so a protocol in which every input makes the process send a message to itself has no valid run
satisfying the assumptions (if some process is correct), and hence vacuously solves Byzantine
agreement. Theorems about Byzantine agreement protocols therefore assume `0 < δ`. For `0 < δ`,
the definition is not vacuous: `SolvesByzantineAgreement.exists_run` provides runs satisfying the
assumptions, and hence the guarantees.

Since process `p` only knows its own proposal, the definition is not trivial either: if there are
two valid values `a ≠ b` and two processes `p ≠ q`, no protocol in which correct processes send
no messages solves Byzantine agreement for `0 < δ`. Indeed, in the runs without faulty processes
in which all processes propose `a` (resp. `b`), `p` (resp. `q`) must decide `a` (resp. `b`) by
strong validity and termination; if `p` proposes `a` and `q` proposes `b`, their local views, and
hence their decisions, are the same as in these runs, contradicting agreement. -/
def SolvesByzantineAgreement (A : InputProtocol P (ByzantineAgreement.interface Value) Value)
    (t δ : ℕ) (valid : Value → Prop) (L : ℕ) : Prop :=
  ∀ prop, (A.toProtocol prop).Satisfies t δ (ByzantineAgreement.spec valid prop L)

/-- **Non-vacuity of Byzantine agreement.** Let `A` solve `t`-resilient Byzantine agreement with
`0 < δ`. For all proposals `prop`, every set `F` of at most `t` faulty processes such that the
proposals of correct processes are valid, and every GST, there is a valid run of
`A.toProtocol prop` with faulty processes `F` and GST `gst`, in which every process is started at
time `0` (and handles no other request), and whose history satisfies the guarantees of Byzantine
agreement. -/
theorem SolvesByzantineAgreement.exists_run [Finite P]
    {A : InputProtocol P (ByzantineAgreement.interface Value) Value} {t δ : ℕ}
    {valid : Value → Prop} {L : ℕ} (hA : A.SolvesByzantineAgreement t δ valid L) (hδ : 0 < δ)
    (prop : P → Value) {F : Finset P} (hF : F.card ≤ t) (hvalid : ∀ p ∉ F, valid (prop p))
    (gst : ℕ) :
    ∃ ρ : Run (A.toProtocol prop), ρ.Valid t δ ∧ ρ.faulty = F ∧ ρ.gst = gst ∧
      ρ.history.HasRequests (fun _ τ => if τ = 0 then [ByzantineAgreement.Req.start] else []) ∧
      ByzantineAgreement.Properties valid prop L ρ.history := by
  have henv : ∀ T, ((List.range T).flatMap fun τ =>
      if τ = 0 then [ByzantineAgreement.Req.start] else []).length ≤ 1 := by
    rintro (_ | T)
    · simp
    · simp [List.range_succ_eq_map, List.flatMap_map]
  obtain ⟨ρ, hρ, ⟨hfaulty, hgst, hreq, hAs⟩, hS⟩ := (hA prop).exists_run_of_env hδ hF
    (env := fun _ τ => if τ = 0 then [ByzantineAgreement.Req.start] else [])
    (Env := fun H => H.faulty = F ∧ H.gst = gst ∧
      H.HasRequests (fun _ τ => if τ = 0 then [ByzantineAgreement.Req.start] else []) ∧
      ByzantineAgreement.Assumptions valid prop H)
    fun H hF' hgst' hreq => ⟨hF', hgst', hreq,
      { validProposal := fun p hp => hvalid p (hF' ▸ hp)
        startAtMostOnce := fun p _ => hreq.atMostOnce (fun _ => rfl) fun T => by simpa using henv T
        startByGst := fun p _ => ⟨0, Nat.zero_le _, hreq.reqAt_iff.2 (by simp)⟩ }⟩
  exact ⟨ρ, hρ, hfaulty, hgst, hreq, hS hAs⟩

end InputProtocol

end Cslib.Distributed
