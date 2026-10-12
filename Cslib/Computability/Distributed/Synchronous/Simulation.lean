/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.Byzantine
public import Cslib.Computability.Distributed.MessagePassing.Bits
public import Cslib.Computability.Distributed.MessagePassing.Spec
public import Cslib.Computability.Distributed.MessagePassing.Reasoning
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Nat.Find

/-! # Simulating a synchronous algorithm in partial synchrony

A synchronous algorithm `A` (`Synchronous.Algorithm`) is run in the partially synchronous model
for exactly `R` rounds, each lasting exactly `Δsync` units of local time ([Civit et al.,
*Partial synchrony for free?*][CivitEtAl2024], §5, Crux Step 2, and appendix Algorithm
`algorithm:crypto_free_sim`). After GST, local clocks advance at rate `1`, so processes that start
the simulation within `Δshift` of each other, with `Δshift + δ < Δsync`, receive every message
of a round from a correct process before the round ends, and their simulated states are those of
a synchronous execution of `A` with the same faulty processes.

## The protocol

`Synchronous.Algorithm.simulation A size B R Δsync` has requests `propose v` and `abandon` and a
single indication carrying `A.decision` of the simulated state after `R` rounds (an
`Option Value`). A message of round `r` is tagged only with the parity `parity r` of `r` (one
bit). Each process keeps its simulated state, a two-slot buffer (`inbox b q` is the first message
tagged `b` received from `q` since slot `b` was last cleared), and the number `sent` of payload
bits it has sent. Process `p`:
* upon its first `propose v` (unless it has abandoned): starts round `1` in the simulated state
  `A.init p v`, i.e. sends its round-`1` messages within the budget (see below), tagged with
  `parity 1`, and sets timer `1` to fire `Δsync` later;
* upon a message `(b, m)` from `q`: stores `m` in slot `b` for `q`, unless that slot already
  holds a message (the first one wins); messages are buffered from the start, also before
  `propose`;
* upon timer `r` at the end of its current round `r`: computes its simulated state after `r`
  rounds by `A.next` from the messages in slot `parity r`, and clears that slot; if `r < R`,
  starts round `r + 1` (messages tagged with `parity (r + 1)`, timer `r + 1`); otherwise stops and
  indicates the decision of that state;
* upon `abandon`: stops (no further messages or indications).

*Bit budget* (paper line `check_sent_messages_crypto_free`): when starting a round, `p` considers
the receivers `q` in a fixed order and sends its message `m` to `q` (if any) only if
`sent + size m ≤ B`, and then adds `size m` to `sent`. Here `size m` is the size of the payload
`m` (without the parity tag), and `B` is a budget for the payload bits.

## Main definitions

* `Synchronous.Algorithm.simulation`: the protocol; `Synchronous.Simulation.sendRound`: the
  messages of a round, sent within the bit budget.
* `Synchronous.Simulation.spec` (`Synchronous.Simulation.Properties`): integrity, at most once,
  duration, termination, and *synchronous simulation* under `Synchronous.Simulation.SyncAssumptions`
  (the processes start after GST within `Δshift` of each other and do not abandon).
* `Synchronous.Simulation.simulatedExecution`: the synchronous execution simulated by a run.

## Main statements

* `Synchronous.Simulation.satisfies`: for `0 < R` and `Δshift + δ < Δsync`, if every correct
  process of `A` sends at most `B` bits in `R` rounds (`Synchronous.Algorithm.PerProcessBits`),
  the simulation satisfies its specification.
* `Synchronous.Simulation.bitsSent_payload_le`, `Synchronous.Simulation.bitsSent_le`: in every run
  (valid or not), a process sends at most `B` payload bits, and at most `2 * B` bits counting the
  parity tags if every payload has at least one bit (paper, proof of
  `lemma:cryptography_free_simulation_correct`, intermediate result 2).
* `Synchronous.Simulation.requestQuiet`: the simulation is request-quiet.
* `Synchronous.Simulation.sendsWhileActive`: a process sends messages only from its first
  `propose` on and never after an `abandon` (`Protocol.SendsWhileActive`); before it proposes, it
  only buffers the messages it receives. So a process sends nothing in a simulation it does not
  take part in.
* `Synchronous.Simulation.Properties.byzantineAgreement`: simulating a synchronous Byzantine
  agreement algorithm with latency `R` yields agreement on a valid value, with strong validity.

## Implementation notes

* *Parity tags suffice because slots are cleared.* Under `SyncAssumptions`, a correct `p`
  completes round `k` exactly at time `σ p + k * Δsync`. The round-`r` message of a correct `q`
  is sent at `σ q + (r - 1) * Δsync`, so (as `Δshift + δ < Δsync`) every copy of it reaches `p`
  strictly after the tick in which `p` completes round `r - 2` and strictly before the tick in
  which `p` completes round `r` (`SyncAssumptions.recv_window`). Slot `parity r` is cleared when
  `p` completes round `r - 2` and read when it completes round `r`; in between, the only messages
  tagged `parity r` that `p` receives from `q` are copies of `q`'s round-`r` message, so the slot
  holds exactly that message when round `r` ends (`SyncAssumptions.used_of_correct`). The
  message of a faulty `q` found in the slot becomes `q`'s round-`r` message to `p` in the
  simulated execution. The paper's `CryptoFreeSim` also tags messages with the round parity, but
  never clears its buffer, so that the transition of round `k` also consumes the stale messages of
  rounds `k - 2, k - 4, …`.
* The parity argument relies on the network delivering no copy of a message later than the delay
  bound (`Run.Valid.authentic`). If arbitrarily late duplicates were allowed, no bounded round tag
  would do: a late copy of a correct process's round-`(r - 2)` message `m`, delivered during round
  `r`, in which that process sends `m` or nothing, is indistinguishable from a round-`r` message
  `m`; full round numbers would be needed.
* The bound `Δshift + δ < Δsync` is strict (the paper uses `Δsync = Δshift + δ`): in the discrete
  model, a message delivered in the tick in which the round ends may be handled after the round's
  timer.
* The simulation property only assumes that each process does not abandon before the end of its
  own simulation. The paper's hypothesis (no correct process stops by `τ* + R * Δsync`, where `τ*`
  is the earliest start) is too weak for a process that starts up to `Δshift` later.
* The messages of faulty processes in the simulated execution are those consumed by the receivers
  (`Synchronous.Simulation.used`). This needs the synchronous model to allow arbitrary faulty
  messages per (round, receiver): a faulty process may base its round-`k` messages on
  round-`(k + 1)` messages of correct processes that are ahead.
* *The budget never binds under `SyncAssumptions`*: the messages sent by a correct process are
  those of the simulated execution, in which it sends at most `B` bits in `R` rounds (paper: the
  simulation with the check is equivalent to the one without it). The bound must hold for all
  executions of `A` with at most `t` faulty processes, whatever the proposals: the specification
  of the simulation does not assume valid proposals. The paper budgets `2𝓑` bits against the
  payload sizes, where `𝓑` bounds the bits a correct process sends in synchrony; we budget `B`,
  which is tight enough to bound the tagged messages by `2 * B`.
* `R = 0`: a request-quiet protocol cannot indicate while handling `propose`.
  The protocol always starts round `1`, so for `R = 0` it simulates one round; the specification
  is only claimed for `0 < R`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Distributed

/-! ### The simulation protocol -/

namespace Synchronous.Simulation

/-- The requests of the simulation module: start simulating with a proposal, or stop. -/
inductive Request (Value : Type) where
  /-- Start the simulation with proposal `v`. -/
  | propose (v : Value)
  /-- Stop the simulation. -/
  | abandon

/-- The interface of the simulation module: requests `propose v` and `abandon`; the single
indication carries the decision (if any) of the simulated algorithm after the last round. -/
abbrev interface (Value : Type) : Interface where
  Req := Request Value
  Ind := Option Value

/-! #### Specification -/

section Spec

variable {P Value : Type}

/-- The assumptions of the *synchronous simulation* property on a history `H`: from time
`τ₀ ≥ gst` on, every correct process `p` proposes exactly once, at time `σ p ∈ [τ₀, τ₀ + Δshift]`
and with value `prop p`, and does not abandon before the end of its simulation at
`σ p + R * Δsync`. -/
structure SyncAssumptions (H : History P (interface Value)) (R Δsync Δshift τ₀ : ℕ)
    (σ : P → ℕ) (prop : P → Value) : Prop where
  /-- The simulations start after GST. -/
  gst_le : H.gst ≤ τ₀
  /-- Correct processes start within `Δshift` of each other. -/
  start_mem : ∀ p ∉ H.faulty, τ₀ ≤ σ p ∧ σ p ≤ τ₀ + Δshift
  /-- Every correct process `p` proposes exactly once: `prop p` at time `σ p`. -/
  propose_iff : ∀ p ∉ H.faulty, ∀ τ v, .req (.propose v) ∈ H.trace p τ ↔ τ = σ p ∧ v = prop p
  /-- No correct process abandons before the end of its simulation. -/
  abandon_lt : ∀ p ∉ H.faulty, ∀ τ, .req .abandon ∈ H.trace p τ → σ p + R * Δsync < τ

variable [DecidableEq P]

/-- The properties of the simulation of the synchronous algorithm `A` for `R` rounds of `Δsync`
local time each (implemented by `Synchronous.Algorithm.simulation`), for simulations started
within `Δshift` of each other. -/
structure Properties (A : Algorithm P Value) (R Δsync Δshift : ℕ)
    (H : History P (interface Value)) : Prop where
  /-- *Integrity*: a correct process indicates only after it has proposed. -/
  integrity : ∀ p ∉ H.faulty, ∀ τ d, .ind d ∈ H.trace p τ →
    ∃ τ' ≤ τ, ∃ v, .req (.propose v) ∈ H.trace p τ'
  /-- *At most once*: a correct process indicates at most once (at a single time, with a single
  value). -/
  atMostOnce : ∀ p ∉ H.faulty, ∀ τ τ' d d', .ind d ∈ H.trace p τ → .ind d' ∈ H.trace p τ' →
    τ = τ' ∧ d = d'
  /-- *Duration*: a correct process that first proposes at time `σ ≥ gst` can indicate only at
  time `σ + R * Δsync`. -/
  duration : ∀ p ∉ H.faulty, ∀ σ v, H.gst ≤ σ → .req (.propose v) ∈ H.trace p σ →
    (∀ τ < σ, ∀ w, .req (.propose w) ∉ H.trace p τ) →
    ∀ τ d, .ind d ∈ H.trace p τ → τ = σ + R * Δsync
  /-- *Termination*: a correct process that proposes at time `σ` and does not abandon by
  `max σ gst + R * Δsync` indicates by then. -/
  termination : ∀ p ∉ H.faulty, ∀ σ v, .req (.propose v) ∈ H.trace p σ →
    (∀ τ ≤ max σ H.gst + R * Δsync, .req .abandon ∉ H.trace p τ) →
    ∃ τ ≤ max σ H.gst + R * Δsync, ∃ d, .ind d ∈ H.trace p τ
  /-- *Synchronous simulation* (paper `lemma:cryptography_free_simulation_correct`, with the
  hypotheses discussed in the implementation notes): if the simulations of correct processes start
  after GST within `Δshift` of each other and are not abandoned (`SyncAssumptions`), then there
  is a synchronous execution of `A` with the same faulty processes and the same proposals of
  correct processes such that every correct process `p` indicates exactly once, `R * Δsync`
  after its proposal, the decision of its state after `R` rounds in that execution. -/
  simulation : ∀ τ₀ σ prop, SyncAssumptions H R Δsync Δshift τ₀ σ prop →
    ∃ E : A.Execution, E.faulty = H.faulty ∧ (∀ p ∉ H.faulty, E.proposal p = prop p) ∧
      ∀ p ∉ H.faulty, ∀ τ d, .ind d ∈ H.trace p τ ↔
        τ = σ p + R * Δsync ∧ d = A.decision (E.state R p)

/-- The specification of the simulation module (see `Properties`). It has no environment
assumptions: the assumptions of the timed properties are part of their statements. -/
abbrev spec (A : Algorithm P Value) (R Δsync Δshift : ℕ) : Spec P (interface Value) :=
  fun H => Properties A R Δsync Δshift H

end Spec

/-- The parity of round `r`: the tag of the messages of round `r`, and the buffer slot that holds
them. -/
def parity (r : ℕ) : Fin 2 := ⟨r % 2, Nat.mod_lt _ (by decide)⟩

theorem parity_eq_parity_iff {r r' : ℕ} : parity r = parity r' ↔ r % 2 = r' % 2 := Fin.ext_iff

/-- The phase of a simulating process whose simulated states are in `St`. -/
inductive Phase (St : Type) where
  /-- Not yet proposed. -/
  | idle
  /-- Completed `r` rounds, reaching the simulated state `st`, and simulating round `r + 1`. -/
  | running (st : St) (r : ℕ)
  /-- Abandoned, or finished after the last round. -/
  | stopped

/-- `ph.Completed k`: the process has proposed and completed at least `k` rounds, or it has
stopped. -/
def Phase.Completed {St : Type} : Phase St → ℕ → Prop
  | .idle, _ => False
  | .running _ r, k => k ≤ r
  | .stopped, _ => True

instance {St : Type} (ph : Phase St) (k : ℕ) : Decidable (ph.Completed k) := by
  cases ph <;> unfold Phase.Completed <;> infer_instance

/-- The local state of a simulating process: its phase (with its simulated state), its
two-slot buffer of round messages (`inbox b q` is the first message tagged `b` received from `q`
since slot `b` was last cleared), and the number of payload bits it has sent. -/
structure State (P Msg St : Type) where
  /-- The phase. -/
  phase : Phase St
  /-- The buffer of round messages, with one slot per round parity. -/
  inbox : Fin 2 → P → Option Msg
  /-- The number of payload bits sent so far (the paper's `sent_bits`). -/
  sent : ℕ

/-- The buffer `inbox` with slot `b` cleared. -/
def clearSlot {P Msg : Type} (inbox : Fin 2 → P → Option Msg) (b : Fin 2) :
    Fin 2 → P → Option Msg :=
  fun b' q => if b' = b then none else inbox b' q

/-- `Enters k x s`: handling input `x` in state `s` completes round `k` (for `k = 0`: starts
the simulation). -/
def Enters {P Msg St Value : Type} :
    ℕ → Input P (Fin 2 × Msg) ℕ (Request Value) → State P Msg St → Prop
  | 0, x, s => s.phase = .idle ∧ ∃ v, x = .req (.propose v)
  | k + 1, x, s => (∃ st, s.phase = .running st k) ∧ x = .timeout (k + 1)

variable {P Value : Type} [Fintype P] (A : Algorithm P Value) (size : A.Msg → ℕ) (B R Δsync : ℕ)

/-- Sending the round-`r` message `m?` (if any) of a process to `q` within the budget `B`, when
`sent` payload bits have been sent before: the message `m` is sent, tagged with `parity r`, iff
`sent + size m ≤ B` (paper line `check_sent_messages_crypto_free`). Returns the payload bits
sent afterwards and the outputs. -/
def sendWithin (r : ℕ) (q : P) (m? : Option A.Msg) (sent : ℕ) :
    ℕ × List (Output P (Fin 2 × A.Msg) ℕ (Option Value)) :=
  match m? with
  | some m => if sent + size m ≤ B then (sent + size m, [.send q (parity r, m)]) else (sent, [])
  | none => (sent, [])

/-- The round-`r` messages of process `p` in simulated state `st`, sent within the budget `B`
when `sent` payload bits have been sent before: the receivers are considered in a fixed order
(`sendWithin`). Returns the payload bits sent afterwards and the `send` outputs. -/
noncomputable def sendRound (p : P) (st : A.State) (r sent : ℕ) :
    ℕ × List (Output P (Fin 2 × A.Msg) ℕ (Option Value)) :=
  foldSteps (fun q sent => sendWithin A size B r q (A.send p st r q) sent) Finset.univ.toList sent

/-- The outputs of process `p` starting round `r + 1` in simulated state `st` at local time
`now`, having sent `sent` payload bits before: its messages of round `r + 1` within the budget,
tagged with `parity (r + 1)` (`sendRound`), and a timer (tagged `r + 1`) for the end of the round,
`Δsync` later. -/
noncomputable def startRound (p : P) (now : ℕ) (st : A.State) (r sent : ℕ) :
    List (Output P (Fin 2 × A.Msg) ℕ (Option Value)) :=
  (sendRound A size B p st (r + 1) sent).2 ++ [.setTimer (r + 1) (now + Δsync)]

variable [DecidableEq P]

/-- The step function of the simulation protocol (see `Synchronous.Algorithm.simulation`). -/
noncomputable def step (p : P) (now : ℕ) :
    Input P (Fin 2 × A.Msg) ℕ (Request Value) → State P A.Msg A.State →
      State P A.Msg A.State × List (Output P (Fin 2 × A.Msg) ℕ (Option Value))
  | .req (.propose v), s =>
    match s.phase with
    | .idle => (⟨.running (A.init p v) 0, s.inbox, (sendRound A size B p (A.init p v) 1 s.sent).1⟩,
        startRound A size B Δsync p now (A.init p v) 0 s.sent)
    | _ => (s, [])
  | .req .abandon, s => (⟨.stopped, s.inbox, s.sent⟩, [])
  | .recv q (b, m), s =>
    if s.inbox b q = none then
      (⟨s.phase, fun b' q' => if b' = b ∧ q' = q then some m else s.inbox b' q', s.sent⟩, [])
    else (s, [])
  | .timeout k, s =>
    match s.phase with
    | .running st r =>
      if k = r + 1 then
        if k < R then
          (⟨.running (A.next p st k (s.inbox (parity k))) k, clearSlot s.inbox (parity k),
              (sendRound A size B p (A.next p st k (s.inbox (parity k))) (k + 1) s.sent).1⟩,
            startRound A size B Δsync p now (A.next p st k (s.inbox (parity k))) k s.sent)
        else (⟨.stopped, clearSlot s.inbox (parity k), s.sent⟩,
          [.ind (A.decision (A.next p st k (s.inbox (parity k))))])
      else (s, [])
    | _ => (s, [])

/-! #### Steps -/

variable {A size B R Δsync} {p : P} {now : ℕ}

/-! #### The bit budget -/

omit [Fintype P] [DecidableEq P] in
theorem mem_sendWithin {r : ℕ} {q : P} {m? : Option A.Msg} {sent : ℕ}
    {o : Output P (Fin 2 × A.Msg) ℕ (Option Value)} (h : o ∈ (sendWithin A size B r q m? sent).2) :
    ∃ m, m? = some m ∧ o = .send q (parity r, m) := by
  rcases m? with _ | m
  · simp [sendWithin] at h
  · simp only [sendWithin] at h
    split_ifs at h
    · exact ⟨m, rfl, List.mem_singleton.1 h⟩
    · simp at h

omit [Fintype P] [DecidableEq P] in
/-- `sendWithin` sends the message if it fits the budget. -/
theorem sendWithin_of_le {r : ℕ} {q : P} {m? : Option A.Msg} {sent : ℕ}
    (h : sent + (m?.map size).getD 0 ≤ B) :
    sendWithin A size B r q m? sent =
      (sent + (m?.map size).getD 0, m?.toList.map fun m => .send q (parity r, m)) := by
  rcases m? with _ | m
  · rfl
  · simp only [Option.map_some, Option.getD_some] at h
    simp [sendWithin, h]

omit [Fintype P] [DecidableEq P] in
theorem sendWithin_fst_le {r : ℕ} {q : P} {m? : Option A.Msg} {sent : ℕ} :
    (sendWithin A size B r q m? sent).1 ≤ sent + (m?.map size).getD 0 := by
  rcases m? with _ | m
  · exact Nat.le_add_right _ _
  · simp only [sendWithin, Option.map_some, Option.getD_some]
    split_ifs <;> simp

omit [Fintype P] [DecidableEq P] in
/-- `sendWithin` adds the payload bits it sends to the count of payload bits sent. -/
theorem sendWithin_fst_eq {r : ℕ} {q : P} {m? : Option A.Msg} {sent : ℕ} :
    (sendWithin A size B r q m? sent).1 =
      sent + ((sendWithin A size B r q m? sent).2.map (Output.bits fun m => size m.2)).sum := by
  rcases m? with _ | m
  · rfl
  · simp only [sendWithin]
    split_ifs <;> simp

omit [Fintype P] [DecidableEq P] in
/-- `sendWithin` keeps the payload bits sent within the budget. -/
theorem sendWithin_fst_le_budget {r : ℕ} {q : P} {m? : Option A.Msg} {sent : ℕ} (h : sent ≤ B) :
    (sendWithin A size B r q m? sent).1 ≤ B := by
  rcases m? with _ | m
  · exact h
  · simp only [sendWithin]
    split_ifs with h'
    · exact h'
    · exact h

omit [DecidableEq P] in
/-- The outputs of `sendRound` are round-`r` messages of the simulated state, tagged with
`parity r`. -/
theorem mem_sendRound {st : A.State} {r sent : ℕ} {o : Output P (Fin 2 × A.Msg) ℕ (Option Value)}
    (h : o ∈ (sendRound A size B p st r sent).2) :
    ∃ q m, A.send p st r q = some m ∧ o = .send q (parity r, m) :=
  foldSteps_rel (R := fun _ l _ => ∀ o ∈ l, ∃ q m, A.send p st r q = some m ∧
      o = (.send q (parity r, m) : Output P (Fin 2 × A.Msg) ℕ (Option Value))) (fun _ => by simp)
    (fun h₁ h₂ o ho => (List.mem_append.1 ho).elim (h₁ o) (h₂ o))
    (fun q _ sent o ho => by
      obtain ⟨m, hm, rfl⟩ := mem_sendWithin ho
      exact ⟨q, m, hm, rfl⟩) sent o h

omit [DecidableEq P] in
/-- `sendRound` adds the payload bits it sends to the count of payload bits sent. -/
theorem sendRound_fst_eq {st : A.State} {r sent : ℕ} :
    (sendRound A size B p st r sent).1 =
      sent + ((sendRound A size B p st r sent).2.map (Output.bits fun m => size m.2)).sum :=
  foldSteps_rel (R := fun s l s' =>
      s' = s + (l.map (Output.bits fun m : Fin 2 × A.Msg => size m.2)).sum)
    (fun _ => by simp) (fun h₁ h₂ => by simp only [h₂, h₁, List.map_append, List.sum_append]; omega)
    (fun _ _ _ => sendWithin_fst_eq) sent

omit [DecidableEq P] in
/-- `sendRound` keeps the payload bits sent within the budget. -/
theorem sendRound_fst_le_budget {st : A.State} {r sent : ℕ} (h : sent ≤ B) :
    (sendRound A size B p st r sent).1 ≤ B :=
  foldSteps_rel (R := fun s _ s' => s ≤ B → s' ≤ B) (fun _ => id) (fun h₁ h₂ => h₂ ∘ h₁)
    (fun _ _ _ => sendWithin_fst_le_budget) sent h

omit [DecidableEq P] in
/-- `sendRound` sends at most the bits of the round-`r` messages of the simulated state. -/
theorem sendRound_fst_le {st : A.State} {r sent : ℕ} :
    (sendRound A size B p st r sent).1 ≤ sent + A.roundBits size p st r := by
  rw [Algorithm.roundBits, ← Finset.sum_map_toList]
  unfold sendRound
  generalize (Finset.univ : Finset P).toList = l
  induction l generalizing sent with
  | nil => simp
  | cons q l ih =>
    simp only [foldSteps_cons, List.map_cons, List.sum_cons]
    have h₁ := sendWithin_fst_le (size := size) (B := B) (r := r) (q := q)
      (m? := A.send p st r q) (sent := sent) (Value := Value)
    have h₂ := ih (sent := (sendWithin A size B r q (A.send p st r q) sent).1)
    omega

omit [DecidableEq P] in
/-- **The budget does not bind** if the round-`r` messages fit in it: then `sendRound` sends all of
them. -/
theorem send_mem_sendRound_of_le {st : A.State} {r sent : ℕ} {q : P} {m : A.Msg}
    (h : sent + A.roundBits size p st r ≤ B) (hm : A.send p st r q = some m) :
    .send q (parity r, m) ∈ (sendRound A size B p st r sent).2 := by
  rw [Algorithm.roundBits, ← Finset.sum_map_toList] at h
  have hq : q ∈ (Finset.univ : Finset P).toList := Finset.mem_toList.2 (Finset.mem_univ q)
  unfold sendRound
  generalize (Finset.univ : Finset P).toList = l at h hq
  induction l generalizing sent with
  | nil => simp at hq
  | cons q' l ih =>
    simp only [List.map_cons, List.sum_cons] at h
    rw [foldSteps_cons, sendWithin_of_le (by omega), List.mem_append]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact .inl (by simp [hm])
    · exact .inr (ih (by omega) hq)

/-! #### Steps -/

omit [DecidableEq P] in
theorem send_mem_startRound {st : A.State} {r sent : ℕ} {q : P} {b : Fin 2} {m : A.Msg}
    (h : Output.send q (b, m) ∈ startRound A size B Δsync p now st r sent) :
    b = parity (r + 1) ∧ A.send p st (r + 1) q = some m := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨q', m', hm, h⟩ := mem_sendRound h
    simp only [Output.send.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, hm⟩
  · simp at h

omit [DecidableEq P] in
/-- If the messages of round `r + 1` fit in the budget, `startRound` sends all of them. -/
theorem send_mem_startRound_of_le {st : A.State} {r sent : ℕ} {q : P} {m : A.Msg}
    (h : sent + A.roundBits size p st (r + 1) ≤ B) (hm : A.send p st (r + 1) q = some m) :
    Output.send q (parity (r + 1), m) ∈ startRound A size B Δsync p now st r sent :=
  List.mem_append.2 (.inl (send_mem_sendRound_of_le h hm))

omit [DecidableEq P] in
theorem setTimer_mem_startRound_iff {st : A.State} {r sent j T : ℕ} :
    Output.setTimer j T ∈ startRound A size B Δsync p now st r sent ↔
      j = r + 1 ∧ T = now + Δsync := by
  rw [startRound, List.mem_append]
  constructor
  · rintro (h | h)
    · obtain ⟨q, m, -, h⟩ := mem_sendRound h
      cases h
    · simpa [eq_comm] using h
  · rintro ⟨rfl, rfl⟩
    exact .inr (List.mem_singleton_self _)

omit [DecidableEq P] in
theorem ind_notMem_startRound {st : A.State} {r sent : ℕ} {d : Option Value} :
    Output.ind d ∉ startRound A size B Δsync p now st r sent := by
  rw [startRound, List.mem_append]
  rintro (h | h)
  · obtain ⟨q, m, -, h⟩ := mem_sendRound h
    cases h
  · simp at h

omit [DecidableEq P] in
/-- The bits sent when starting a round are the payload bits added by `sendRound`. -/
theorem sum_bits_startRound {st : A.State} {r sent : ℕ} :
    sent + ((startRound A size B Δsync p now st r sent).map (Output.bits fun m => size m.2)).sum =
      (sendRound A size B p st (r + 1) sent).1 := by
  rw [startRound, List.map_append, List.sum_append, sendRound_fst_eq]
  simp

/-- Starting the simulation. -/
theorem step_propose_of_idle {v : Value} {s : State P A.Msg A.State} (h : s.phase = .idle) :
    step A size B R Δsync p now (.req (.propose v)) s =
      (⟨.running (A.init p v) 0, s.inbox, (sendRound A size B p (A.init p v) 1 s.sent).1⟩,
        startRound A size B Δsync p now (A.init p v) 0 s.sent) := by
  obtain ⟨phase, inbox, sent⟩ := s
  subst h
  rfl

/-- Completing round `k + 1`: the simulated state is updated with the messages of slot
`parity (k + 1)`, which is cleared. -/
theorem step_timeout_of_running {st : A.State} {k : ℕ} {s : State P A.Msg A.State}
    (h : s.phase = .running st k) :
    step A size B R Δsync p now (.timeout (k + 1)) s =
      if k + 1 < R then
        (⟨.running (A.next p st (k + 1) (s.inbox (parity (k + 1)))) (k + 1),
          clearSlot s.inbox (parity (k + 1)),
          (sendRound A size B p (A.next p st (k + 1) (s.inbox (parity (k + 1)))) (k + 1 + 1)
            s.sent).1⟩,
          startRound A size B Δsync p now (A.next p st (k + 1) (s.inbox (parity (k + 1)))) (k + 1)
            s.sent)
      else (⟨.stopped, clearSlot s.inbox (parity (k + 1)), s.sent⟩,
        [.ind (A.decision (A.next p st (k + 1) (s.inbox (parity (k + 1)))))]) := by
  obtain ⟨phase, inbox, sent⟩ := s
  subst h
  simp [step]

/-- A step that completes round `k` (see `Enters`): the process reaches a simulated state `st`
after `k` rounds and starts round `k + 1`, or stops and indicates the decision of `st` after the
last round. -/
theorem step_of_enters {k : ℕ} {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (h : Enters k x s) :
    ∃ st inbox, step A size B R Δsync p now x s =
      if k = 0 ∨ k < R then
        (⟨.running st k, inbox, (sendRound A size B p st (k + 1) s.sent).1⟩,
          startRound A size B Δsync p now st k s.sent)
      else (⟨.stopped, inbox, s.sent⟩, [.ind (A.decision st)]) := by
  cases k with
  | zero =>
    obtain ⟨hidle, v, rfl⟩ := h
    exact ⟨A.init p v, s.inbox, by simp only [step_propose_of_idle hidle, true_or, ↓reduceIte]⟩
  | succ k =>
    obtain ⟨⟨st, hst⟩, rfl⟩ := h
    refine ⟨A.next p st (k + 1) (s.inbox (parity (k + 1))), clearSlot s.inbox (parity (k + 1)),
      ?_⟩
    rw [step_timeout_of_running hst]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or]

/-- A step that starts the simulation or completes round `k < R` starts round `k + 1`. -/
theorem step_of_enters_of_lt {k : ℕ} {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (h : Enters k x s) (hk : k < R) :
    ∃ st inbox, step A size B R Δsync p now x s =
      (⟨.running st k, inbox, (sendRound A size B p st (k + 1) s.sent).1⟩,
        startRound A size B Δsync p now st k s.sent) := by
  obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R) (Δsync := Δsync)
    (p := p) (now := now) h
  exact ⟨st, inbox, by simp only [hstep, hk, or_true, ↓reduceIte]⟩

/-- A step that completes no round and is not `abandon` changes neither the phase nor the payload
bits sent, and emits no outputs. -/
theorem step_of_not_enters {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (h : ∀ k, ¬ Enters k x s) (hx : x ≠ .req .abandon) :
    (step A size B R Δsync p now x s).1.phase = s.phase ∧
      (step A size B R Δsync p now x s).1.sent = s.sent ∧
      (step A size B R Δsync p now x s).2 = [] := by
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (v | _) | ⟨q, b, m⟩ | k
  · cases phase with
    | idle => exact absurd ⟨rfl, v, rfl⟩ (h 0)
    | running st r => simp [step]
    | stopped => simp [step]
  · exact absurd rfl hx
  · simp only [step]
    split_ifs <;> simp
  · cases phase with
    | idle => simp [step]
    | running st r =>
      by_cases hk : k = r + 1
      · subst hk
        exact absurd ⟨⟨st, rfl⟩, rfl⟩ (h (r + 1))
      · simp [step, hk]
    | stopped => simp [step]

/-- `abandon` stops the process. -/
theorem step_abandon (s : State P A.Msg A.State) :
    step A size B R Δsync p now (.req .abandon) s = (⟨.stopped, s.inbox, s.sent⟩, []) := rfl

/-- A stopped process stays stopped. -/
theorem phase_step_of_stopped {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (h : s.phase = .stopped) :
    (step A size B R Δsync p now x s).1.phase = .stopped := by
  obtain ⟨phase, inbox, sent⟩ := s
  subst h
  rcases x with (v | _) | ⟨q, b, m⟩ | k
  · rfl
  · rfl
  · simp only [step]
    split_ifs <;> rfl
  · rfl

/-- Receipts do not change the phase. -/
theorem phase_step_recv (q : P) (b : Fin 2) (m : A.Msg) (s : State P A.Msg A.State) :
    (step A size B R Δsync p now (.recv q (b, m)) s).1.phase = s.phase := by
  simp only [step]
  split_ifs <;> rfl

/-- After receiving a message tagged `b` from `q`, slot `b` holds a message from `q`. -/
theorem inbox_step_recv_ne_none (q : P) (b : Fin 2) (m : A.Msg) (s : State P A.Msg A.State) :
    (step A size B R Δsync p now (.recv q (b, m)) s).1.inbox b q ≠ none := by
  simp only [step]
  split_ifs with h
  · simp
  · exact h

/-- `Mono s s'`: completed rounds stay completed from `s` to `s'`. -/
def Mono {Msg St : Type} (s s' : State P Msg St) : Prop :=
  ∀ k, s.phase.Completed k → s'.phase.Completed k

omit [Fintype P] [DecidableEq P] in
theorem Mono.refl {Msg St : Type} (s : State P Msg St) : Mono s s := fun _ h => h

omit [Fintype P] [DecidableEq P] in
theorem Mono.trans {Msg St : Type} {s₁ s₂ s₃ : State P Msg St} (h₁ : Mono s₁ s₂)
    (h₂ : Mono s₂ s₃) : Mono s₁ s₃ := fun k h => h₂ k (h₁ k h)

/-- Every step makes progress (`Mono`). -/
theorem mono_step (x : Input P (Fin 2 × A.Msg) ℕ (Request Value)) (s : State P A.Msg A.State) :
    Mono s (step A size B R Δsync p now x s).1 := by
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (v | _) | ⟨q, b, m⟩ | k
  · cases phase with
    | idle => exact fun _ h => h.elim
    | running st r => exact Mono.refl _
    | stopped => exact Mono.refl _
  · exact fun _ _ => trivial
  · intro k h
    rwa [phase_step_recv]
  · cases phase with
    | idle => exact Mono.refl _
    | running st r =>
      simp only [step]
      split_ifs with h₁ h₂
      · subst h₁
        exact fun k' (h : k' ≤ r) => (by simp [Phase.Completed]; omega)
      · exact fun _ _ => trivial
      · exact Mono.refl _
    | stopped => exact Mono.refl _

/-- A step that completes round `k` makes `Completed k` true. -/
theorem completed_step_of_enters {k : ℕ} {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (h : Enters k x s) :
    (step A size B R Δsync p now x s).1.phase.Completed k := by
  obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R) (Δsync := Δsync)
    (p := p) (now := now) h
  rw [hstep]
  split_ifs <;> simp [Phase.Completed]

omit [Fintype P] [DecidableEq P] in
/-- A step that completes round `k` is handled before round `k` is completed. -/
theorem not_completed_of_enters {k : ℕ} {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (h : Enters k x s) : ¬ s.phase.Completed k := by
  cases k with
  | zero =>
    obtain ⟨h, -⟩ := h
    simp [h, Phase.Completed]
  | succ k =>
    obtain ⟨⟨st, h⟩, -⟩ := h
    simp [h, Phase.Completed]

/-- A step that makes `Completed m` true, for `m ≤ R`, is an `abandon` or completes round
`m`. -/
theorem enters_of_completed {m : ℕ} {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} (hs : ¬ s.phase.Completed m)
    (h : (step A size B R Δsync p now x s).1.phase.Completed m) (hm : m ≤ R) :
    x = .req .abandon ∨ Enters m x s := by
  by_cases hab : x = .req .abandon
  · exact .inl hab
  refine .inr ?_
  by_cases hk : ∃ k, Enters k x s
  · obtain ⟨k, hk⟩ := hk
    obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R) (Δsync := Δsync)
      (p := p) (now := now) hk
    cases k with
    | zero =>
      rw [hstep] at h
      simp only [true_or, ↓reduceIte, Phase.Completed, Nat.le_zero] at h
      exact h ▸ hk
    | succ k =>
      obtain ⟨⟨st', hst'⟩, hx⟩ := hk
      rw [hst'] at hs
      simp only [Phase.Completed, not_le] at hs
      have hmk : m = k + 1 := by
        by_cases hc : k + 1 < R
        · rw [hstep] at h
          simp only [hc, or_true, ↓reduceIte, Phase.Completed] at h
          omega
        · omega
      subst hmk
      exact ⟨⟨st', hst'⟩, hx⟩
  · rw [(step_of_not_enters (fun k hk' => hk ⟨k, hk'⟩) hab).1] at h
    exact absurd h hs

/-- Only steps completing a round have outputs. -/
theorem exists_enters_of_mem_step {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} {o : Output P (Fin 2 × A.Msg) ℕ (Option Value)}
    (h : o ∈ (step A size B R Δsync p now x s).2) : ∃ k, Enters k x s := by
  by_contra hk
  push Not at hk
  by_cases hx : x = .req .abandon
  · subst hx
    simp [step_abandon] at h
  · simp [(step_of_not_enters hk hx).2] at h

/-- Timers are set when completing round `k` (with `k = 0` or `k < R`), for the end of round
`k + 1`, `Δsync` later. -/
theorem setTimer_mem_step {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} {j T : ℕ}
    (h : .setTimer j T ∈ (step A size B R Δsync p now x s).2) :
    ∃ k, Enters k x s ∧ (k = 0 ∨ k < R) ∧ j = k + 1 ∧ T = now + Δsync := by
  obtain ⟨k, hk⟩ := exists_enters_of_mem_step h
  obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R) (Δsync := Δsync)
    (p := p) (now := now) hk
  rw [hstep] at h
  split_ifs at h with hc
  · exact ⟨k, hk, hc, setTimer_mem_startRound_iff.1 h⟩
  · simp at h

/-- Messages are sent when completing round `k` (with `k = 0` or `k < R`): the messages of round
`k + 1` of the simulated state `st` after `k` rounds, tagged with `parity (k + 1)`. -/
theorem send_mem_step {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} {q : P} {b : Fin 2} {m : A.Msg}
    (h : .send q (b, m) ∈ (step A size B R Δsync p now x s).2) :
    ∃ k st, Enters k x s ∧ (k = 0 ∨ k < R) ∧ b = parity (k + 1) ∧
      A.send p st (k + 1) q = some m ∧
      (step A size B R Δsync p now x s).1.phase = .running st k := by
  obtain ⟨k, hk⟩ := exists_enters_of_mem_step h
  obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R) (Δsync := Δsync)
    (p := p) (now := now) hk
  rw [hstep] at h ⊢
  split_ifs at h ⊢ with hc
  · obtain ⟨rfl, hm⟩ := send_mem_startRound h
    exact ⟨k, st, hk, hc, rfl, hm, rfl⟩
  · simp at h

/-- The indication is emitted when completing the last round, with the decision of the simulated
state after it. -/
theorem ind_mem_step {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State} {d : Option Value}
    (h : .ind d ∈ (step A size B R Δsync p now x s).2) :
    ∃ k st, Enters (k + 1) x s ∧ s.phase = .running st k ∧ R ≤ k + 1 ∧
      d = A.decision (A.next p st (k + 1) (s.inbox (parity (k + 1)))) ∧
      (step A size B R Δsync p now x s).1.phase = .stopped := by
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (v | _) | ⟨q, b, m⟩ | k
  · cases phase <;> simp [step, ind_notMem_startRound] at h
  · simp [step] at h
  · simp only [step] at h
    split_ifs at h <;> simp at h
  · cases phase with
    | idle => simp [step] at h
    | running st r =>
      by_cases hk : k = r + 1
      · subst hk
        by_cases hR : r + 1 < R
        · simp [step, hR, ind_notMem_startRound] at h
        · simp only [step, hR, ↓reduceIte, List.mem_singleton, Output.ind.injEq] at h
          exact ⟨r, st, ⟨⟨st, rfl⟩, rfl⟩, rfl, by omega, h, by simp [step, hR]⟩
      · simp [step, hk] at h
    | stopped => simp [step] at h

theorem completed_zero_step_propose (v : Value) (s : State P A.Msg A.State) :
    (step A size B R Δsync p now (.req (.propose v)) s).1.phase.Completed 0 := by
  obtain ⟨phase, inbox, sent⟩ := s
  cases phase <;> simp [step, Phase.Completed]

theorem completed_succ_step_timeout {k : ℕ} {s : State P A.Msg A.State}
    (h : s.phase.Completed k) :
    (step A size B R Δsync p now (.timeout (k + 1)) s).1.phase.Completed (k + 1) := by
  obtain ⟨phase, inbox, sent⟩ := s
  cases phase with
  | idle => exact h.elim
  | running st r =>
    simp only [Phase.Completed] at h
    simp only [step]
    split_ifs with h₁ h₂
    · simp [Phase.Completed]
    · simp [Phase.Completed]
    · simp only [Phase.Completed]; omega
  | stopped => simp [step, Phase.Completed]

/-- A process runs in simulated state `st` after `r` rounds only if it did so before (and the
step keeps the payload bits sent), or it has just started (`r = 0`, `st` initial), or it has just
completed round `r` (`st` computed by `A.next` from the messages of slot `parity r`); in the last
two cases, the payload bits sent are updated by sending the messages of round `r + 1`. -/
theorem running_step {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)} {s : State P A.Msg A.State}
    {st : A.State} {r : ℕ} (h : (step A size B R Δsync p now x s).1.phase = .running st r) :
    (s.phase = .running st r ∧ (step A size B R Δsync p now x s).1.sent = s.sent) ∨
      (r = 0 ∧ s.phase = .idle ∧ ∃ v, x = .req (.propose v) ∧ st = A.init p v ∧
        (step A size B R Δsync p now x s).1.sent = (sendRound A size B p st 1 s.sent).1) ∨
      ∃ r' st', r = r' + 1 ∧ s.phase = .running st' r' ∧ x = .timeout (r' + 1) ∧
        st = A.next p st' (r' + 1) (s.inbox (parity (r' + 1))) ∧
        (step A size B R Δsync p now x s).1.sent = (sendRound A size B p st (r + 1) s.sent).1 := by
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (w | _) | ⟨q, b, m⟩ | k
  · cases phase with
    | idle =>
      simp only [step, Phase.running.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr (.inl ⟨rfl, rfl, w, rfl, rfl, rfl⟩)
    | running st' r' => exact .inl ⟨by simpa [step] using h, rfl⟩
    | stopped => simp [step] at h
  · simp [step] at h
  · refine .inl ⟨by rwa [phase_step_recv] at h, ?_⟩
    simp only [step]
    split_ifs <;> rfl
  · cases phase with
    | idle => simp [step] at h
    | running st' r' =>
      by_cases hk : k = r' + 1
      · subst hk
        by_cases hR : r' + 1 < R
        · simp only [step, hR, ↓reduceIte, Phase.running.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inr (.inr ⟨r', st', rfl, rfl, rfl, rfl, by simp [step, hR]⟩)
        · simp [step, hR] at h
      · simp only [step, hk, ↓reduceIte] at h
        exact .inl ⟨h, by simp [step, hk]⟩
    | stopped => simp [step] at h

/-- *Soundness of slots*, step form: while a process has completed round `k - 1` (if `k ≥ 2`)
but not round `k + 1`, a message `m` from `q` appears in slot `parity (k + 1)` only by a receipt
of `(parity (k + 1), m)` from `q` in that period (or the process abandons). -/
theorem inbox_step_of_waiting {k : ℕ} {q : P} {m : A.Msg}
    {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)} {s : State P A.Msg A.State}
    (h : (step A size B R Δsync p now x s).1.inbox (parity (k + 1)) q = some m)
    (hw : k ≤ 1 ∨ (step A size B R Δsync p now x s).1.phase.Completed (k - 1))
    (hn : ¬ (step A size B R Δsync p now x s).1.phase.Completed (k + 1)) :
    (s.inbox (parity (k + 1)) q = some m ∧ (k ≤ 1 ∨ s.phase.Completed (k - 1)) ∧
        ¬ s.phase.Completed (k + 1)) ∨
      (x = .recv q (parity (k + 1), m) ∧ (k ≤ 1 ∨ s.phase.Completed (k - 1))) ∨
      x = .req .abandon := by
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (v | _) | ⟨q', b, m'⟩ | j
  · cases phase with
    | idle =>
      simp only [step, Phase.Completed] at h hw hn
      exact .inl ⟨h, by omega, by simp [Phase.Completed]⟩
    | running st r => exact .inl ⟨by simpa [step] using h, by simpa [step] using hw,
        by simpa [step] using hn⟩
    | stopped => exact .inl ⟨by simpa [step] using h, by simpa [step] using hw,
        by simpa [step] using hn⟩
  · exact .inr (.inr rfl)
  · rw [phase_step_recv] at hw hn
    simp only [step] at h
    split_ifs at h with h₁
    · simp only at h
      split_ifs at h with h₂
      · obtain ⟨rfl, rfl⟩ := h₂
        simp only [Option.some.injEq] at h
        subst h
        exact .inr (.inl ⟨rfl, hw⟩)
      · exact .inl ⟨h, hw, hn⟩
    · exact .inl ⟨h, hw, hn⟩
  · cases phase with
    | idle => exact .inl ⟨by simpa [step] using h, by simpa [step] using hw,
        by simpa [step] using hn⟩
    | running st r =>
      by_cases hj : j = r + 1
      · subst hj
        by_cases hR : r + 1 < R
        · simp only [step, hR, ↓reduceIte, Phase.Completed, clearSlot] at h hw hn
          split_ifs at h with hb
          refine .inl ⟨h, ?_, by simp only [Phase.Completed]; omega⟩
          rw [parity_eq_parity_iff] at hb
          simp only [Phase.Completed]
          omega
        · simp [step, hR, Phase.Completed] at hn
      · exact .inl ⟨by simpa [step, hj] using h, by simpa [step, hj] using hw,
          by simpa [step, hj] using hn⟩
    | stopped => exact .inl ⟨by simpa [step] using h, by simpa [step] using hw,
        by simpa [step] using hn⟩

/-- *Completeness of slots*, step form: once a process has completed round `k - 1` (if `k ≥ 2`),
a message from `q` in slot `parity (k + 1)` stays there until the process completes round
`k + 1`. -/
theorem filled_step {k : ℕ} {q : P} {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg A.State}
    (h : (s.inbox (parity (k + 1)) q ≠ none ∧ (k ≤ 1 ∨ s.phase.Completed (k - 1))) ∨
      s.phase.Completed (k + 1)) :
    ((step A size B R Δsync p now x s).1.inbox (parity (k + 1)) q ≠ none ∧
        (k ≤ 1 ∨ (step A size B R Δsync p now x s).1.phase.Completed (k - 1))) ∨
      (step A size B R Δsync p now x s).1.phase.Completed (k + 1) := by
  rcases h with ⟨hne, hw⟩ | hc
  swap
  · exact .inr (mono_step x s _ hc)
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (v | _) | ⟨q', b, m'⟩ | j
  · cases phase with
    | idle =>
      simp only [Phase.Completed, or_false] at hw
      exact .inl ⟨by simpa [step] using hne, .inl hw⟩
    | running st r => exact .inl ⟨by simpa [step] using hne, by simpa [step] using hw⟩
    | stopped => exact .inr (by simp [step, Phase.Completed])
  · exact .inr (by simp [step, Phase.Completed])
  · refine .inl ⟨?_, by rwa [phase_step_recv]⟩
    simp only [step]
    split_ifs with h₁
    · simp only
      split_ifs
      · simp
      · exact hne
    · exact hne
  · cases phase with
    | idle => exact .inl ⟨by simpa [step] using hne, by simpa [step] using hw⟩
    | running st r =>
      by_cases hj : j = r + 1
      · subst hj
        by_cases hR : r + 1 < R
        · simp only [Phase.Completed] at hw
          by_cases hkr : k + 1 ≤ r + 1
          · exact .inr (by simp [step, hR, Phase.Completed]; omega)
          · refine .inl ⟨?_, .inr (by simp [step, hR, Phase.Completed]; omega)⟩
            have hb : parity (k + 1) ≠ parity (r + 1) := by
              rw [Ne, parity_eq_parity_iff]
              omega
            simpa [step, hR, clearSlot, hb] using hne
        · exact .inr (by simp [step, hR, Phase.Completed])
      · exact .inl ⟨by simpa [step, hj] using hne, by simpa [step, hj] using hw⟩
    | stopped => exact .inr (by simp [step, Phase.Completed])

end Synchronous.Simulation

namespace Synchronous.Algorithm

open Simulation

variable {P Value : Type} [Fintype P] [DecidableEq P]

/-- The simulation of the synchronous algorithm `A` for `R` rounds of `Δsync` local time
each, in which a process sends at most `B` payload bits, for the payload sizes `size` (the
paper's `CryptoFreeSim`). -/
noncomputable abbrev simulation (A : Algorithm P Value) (size : A.Msg → ℕ) (B R Δsync : ℕ) :
    Protocol P (Simulation.interface Value) where
  Msg := Fin 2 × A.Msg
  Timer := ℕ
  State := Simulation.State P A.Msg A.State
  init _ := ⟨.idle, fun _ _ => none, 0⟩
  step := Simulation.step A size B R Δsync

end Synchronous.Algorithm

/-! ### Runs of the simulation -/

namespace Synchronous.Simulation

open Algorithm

variable {P Value : Type} [Fintype P] [DecidableEq P] {A : Algorithm P Value}
  {size : A.Msg → ℕ} {B R Δsync t δ : ℕ} {ρ : Run (A.simulation size B R Δsync)} {p : P}
  {τ : ℕ}
  {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)} {s : State P A.Msg A.State}

/-- States of a simulating process progress over time (`Mono`). -/
theorem mono_state {τ τ' : ℕ} (h : τ ≤ τ') : Mono (ρ.state p τ) (ρ.state p τ') :=
  Run.rel_state (ρ := ρ) (p := p) (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s) h

/-- The state in which an input is handled at time `τ` is reached from the state at time `τ`. -/
theorem mono_handles_left (h : ρ.Handles p τ x s) : Mono (ρ.state p τ) s :=
  h.rel_left (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s)

/-- The state at time `τ + 1` is reached from the state after an input handled at time `τ`. -/
theorem mono_handles_right (h : ρ.Handles p τ x s) :
    Mono (step A size B R Δsync p (ρ.clock p τ) x s).1 (ρ.state p (τ + 1)) :=
  h.rel_right (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s)

/-- After a `propose`, the process has started (or stopped). -/
theorem completed_zero_of_propose {v : Value} (h : .req (.propose v) ∈ ρ.input p τ) :
    (ρ.state p (τ + 1)).phase.Completed 0 := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  exact hs.state_of_stable (Q := fun s : State P A.Msg A.State => s.phase.Completed 0)
    (fun _ x s h => mono_step x s 0 h) (completed_zero_step_propose (R := R) v s)
    (Nat.lt_succ_self τ)

/-- *First-time argument* for completed rounds: if `p` has completed round `m ≤ R` (or stopped),
then it abandoned or completed round `m` earlier. -/
theorem exists_enters_of_completed {m : ℕ} (hm : m ≤ R)
    (h : (ρ.state p τ).phase.Completed m) :
    ∃ τ' < τ, ∃ x s, ρ.Handles p τ' x s ∧ (x = .req .abandon ∨ Enters m x s) :=
  Run.exists_handles_of_state (ρ := ρ) (Q := fun s : State P A.Msg A.State => s.phase.Completed m)
    (G := fun _ x s => x = .req .abandon ∨ Enters m x s) (fun h => h)
    (fun _ _ s h => (em (s.phase.Completed m)).imp id fun hs => enters_of_completed hs h hm) h

/-- A process that starts the simulation or completes round `k < R` at time `τ` outputs its
messages of round `k + 1` and the timer for the end of that round at time `τ`. -/
theorem startRound_subset_output (hs : ρ.Handles p τ x s) {k : ℕ} (he : Enters k x s)
    (hk : k < R) :
    ∃ st inbox, (step A size B R Δsync p (ρ.clock p τ) x s).1 =
        ⟨.running st k, inbox, (sendRound A size B p st (k + 1) s.sent).1⟩ ∧
      startRound A size B Δsync p (ρ.clock p τ) st k s.sent ⊆ ρ.output p τ := by
  obtain ⟨st, inbox, hstep⟩ := step_of_enters_of_lt (size := size) (B := B) (R := R)
    (Δsync := Δsync) (p := p)
    (now := ρ.clock p τ) he hk
  refine ⟨st, inbox, by rw [hstep], fun o ho => hs.mem_output ?_⟩
  change o ∈ (step A size B R Δsync p (ρ.clock p τ) x s).2
  rwa [hstep]

/-- A process that completes the last round `k + 1 ≥ R` at time `τ` indicates the decision of its
simulated state after it at time `τ`. -/
theorem ind_mem_output_of_enters (hs : ρ.Handles p τ x s) {k : ℕ} (he : Enters (k + 1) x s)
    (hk : R ≤ k + 1) :
    ∃ st, s.phase = .running st k ∧
      .ind (A.decision (A.next p st (k + 1) (s.inbox (parity (k + 1))))) ∈ ρ.output p τ := by
  obtain ⟨⟨st, hst⟩, rfl⟩ := he
  refine ⟨st, hst, hs.mem_output ?_⟩
  change _ ∈ (step A size B R Δsync p (ρ.clock p τ) (.timeout (k + 1)) s).2
  rw [step_timeout_of_running hst]
  simp only [show ¬ k + 1 < R by omega, ↓reduceIte]
  exact List.mem_singleton_self _

/-- *Timeline* (only-if part): if a correct process `p` proposes for the first time at
`σ ≥ gst`, then it completes round `k` only at time `σ + k * Δsync`, and only for `k ≤ R`. -/
theorem enters_time (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hR : 0 < R) (hΔ : 0 < Δsync)
    {σ : ℕ} (hσ : ρ.gst ≤ σ) {v₀ : Value} (hprop : .req (.propose v₀) ∈ ρ.input p σ)
    (hfirst : ∀ τ < σ, ∀ v, .req (.propose v) ∉ ρ.input p τ) {k : ℕ} :
    ∀ {τ x s}, ρ.Handles p τ x s → Enters k x s → k ≤ R ∧ τ = σ + k * Δsync := by
  induction k with
  | zero =>
    rintro τ x s hs ⟨hidle, v, rfl⟩
    refine ⟨Nat.zero_le _, ?_⟩
    have hge : σ ≤ τ := by
      by_contra h
      exact hfirst τ (by omega) v hs.mem_input
    by_contra hne
    have hc := mono_handles_left hs 0
      (mono_state (show σ + 1 ≤ τ by omega) 0 (completed_zero_of_propose hprop))
    rw [hidle] at hc
    exact hc
  | succ k ih =>
    rintro τ x s hs ⟨⟨st, hst⟩, rfl⟩
    obtain ⟨τ', T, hT, hexp⟩ := (hρ.timer hp).1 hs.mem_input
    obtain ⟨x', s', hs', hT'⟩ := Run.mem_output_iff_handles.1 hT
    obtain ⟨k', hk', hk'R, hkk, rfl⟩ := setTimer_mem_step hT'
    obtain rfl : k = k' := by omega
    obtain ⟨-, rfl⟩ := ih hs' hk'
    have := hρ.eq_of_expires (hσ.trans (Nat.le_add_right _ _)) hΔ hexp
    refine ⟨by omega, ?_⟩
    rw [this, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- *Timeline* (existence part): if a correct process `p` proposes at `σ` and does not abandon by
`max σ gst + R * Δsync`, then it completes every round `k ≤ R` by `max σ gst + k * Δsync`. -/
theorem exists_enters (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hΔ : 0 < Δsync) {σ : ℕ}
    {v₀ : Value} (hprop : .req (.propose v₀) ∈ ρ.input p σ)
    (hab : ∀ τ ≤ max σ ρ.gst + R * Δsync, .req .abandon ∉ ρ.input p τ) {k : ℕ} (hk : k ≤ R) :
    ∃ τ ≤ max σ ρ.gst + k * Δsync, ∃ x s, ρ.Handles p τ x s ∧ Enters k x s := by
  have cross : ∀ m ≤ R, ∀ τ', (ρ.state p (τ' + 1)).phase.Completed m →
      τ' ≤ max σ ρ.gst + R * Δsync → ∃ τ ≤ τ', ∃ x s, ρ.Handles p τ x s ∧ Enters m x s := by
    intro m hm τ' hc hτ'
    obtain ⟨τ, hτ, x, s, hs, hx | hx⟩ := exists_enters_of_completed hm hc
    · subst hx
      exact absurd hs.mem_input (hab τ (by omega))
    · exact ⟨τ, by omega, x, s, hs, hx⟩
  induction k with
  | zero =>
    obtain ⟨τ, hτ, h⟩ := cross 0 (Nat.zero_le _) σ (completed_zero_of_propose hprop) (by omega)
    exact ⟨τ, by omega, h⟩
  | succ k ih =>
    obtain ⟨τk, hτk, x, s, hs, he⟩ := ih (by omega)
    obtain ⟨st, inbox, hpost, hsub⟩ := startRound_subset_output hs he (show k < R by omega)
    obtain ⟨τe, hτe₁, hτe₂, hto⟩ :=
      hρ.exists_timeout_mem_input hp hΔ (hsub (setTimer_mem_startRound_iff.2 ⟨rfl, rfl⟩))
    have hck : (ρ.state p τe).phase.Completed k :=
      mono_state (show τk + 1 ≤ τe by omega) k
        (mono_handles_right hs k (by rw [hpost]; exact le_refl k))
    have hc' : (ρ.state p (τe + 1)).phase.Completed (k + 1) :=
      Run.state_succ_of_mem (ρ := ρ) (G := fun s : State P A.Msg A.State => s.phase.Completed k)
        (Q := fun s : State P A.Msg A.State => s.phase.Completed (k + 1)) hto
        (fun y _ s h => mono_step y s k h)
        (fun y _ s h => mono_step y s (k + 1) h)
        (fun s h => completed_succ_step_timeout h) hck
    have hmul : (k + 1) * Δsync ≤ R * Δsync := Nat.mul_le_mul_right _ hk
    have hτe : τe ≤ max σ ρ.gst + (k + 1) * Δsync := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    obtain ⟨τ, hτ, h⟩ := cross (k + 1) hk τe hc' (by omega)
    exact ⟨τ, by omega, h⟩

/-! #### Consumed messages and simulated states -/

/-- Each round is completed at most once: the inputs completing round `r` are all handled in the
same state. -/
theorem eq_of_enters {τ' r : ℕ} {x' : Input P (Fin 2 × A.Msg) ℕ (Request Value)}
    {s' : State P A.Msg A.State} (hs : ρ.Handles p τ x s) (he : Enters r x s)
    (hs' : ρ.Handles p τ' x' s') (he' : Enters r x' s') : s = s' := by
  rcases hs.order (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s) hs' with
    ⟨-, -, rfl⟩ | hm | hm
  · rfl
  · exact absurd (hm r (completed_step_of_enters he)) (not_completed_of_enters he')
  · exact absurd (hm r (completed_step_of_enters he')) (not_completed_of_enters he)

variable (ρ) in
open Classical in
/-- The messages consumed by `p` when completing round `r`: the contents of slot `parity r` of its
buffer when it handles the timer of round `r` (`used_eq`), or no messages if it never completes
round `r`. They are the messages received by `p` in round `r` of the simulated execution. -/
noncomputable def used (p : P) (r : ℕ) : P → Option A.Msg :=
  if h : ∃ τ x s, ρ.Handles p τ x s ∧ Enters r x s then
    h.choose_spec.choose_spec.choose.inbox (parity r)
  else fun _ => none

/-- The messages consumed when completing round `r` are those of slot `parity r`. -/
theorem used_eq (hs : ρ.Handles p τ x s) {r : ℕ} (he : Enters r x s) :
    used ρ p r = s.inbox (parity r) := by
  unfold used
  split_ifs with h
  · obtain ⟨hs', he'⟩ := h.choose_spec.choose_spec.choose_spec
    rw [eq_of_enters hs' he' hs he]
  · exact absurd ⟨τ, x, s, hs, he⟩ h

/-- *First-time argument* for simulated states: a process runs in simulated state `st` after `c`
rounds only after a step that made it so. -/
theorem exists_handles_running {st : A.State} {c : ℕ} (hs : ρ.Handles p τ x s)
    (hst : s.phase = .running st c) :
    ∃ τ' ≤ τ, ∃ y s', ρ.Handles p τ' y s' ∧ ¬ s'.phase = .running st c ∧
      (step A size B R Δsync p (ρ.clock p τ') y s').1.phase = .running st c :=
  hs.exists_handles (Q := fun s : State P A.Msg A.State => s.phase = .running st c)
    (G := fun now y (s' : State P A.Msg A.State) => ¬ s'.phase = .running st c ∧
      (step A size B R Δsync p now y s').1.phase = .running st c)
    (fun h => by cases h) (fun _ _ _ h => (em _).imp id fun h' => ⟨h', h⟩) hst

/-- The simulated state of `p` after `c` rounds is computed by `A.localRun` from its proposal and
the messages it consumed, if all its proposals are `v₀`. -/
theorem running_eq_localRun {v₀ : Value}
    (hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = v₀) {c : ℕ} :
    ∀ {τ x s st}, ρ.Handles p τ x s → s.phase = .running st c →
      st = A.localRun p v₀ (used ρ p) c := by
  induction c with
  | zero =>
    intro τ x s st hs hst
    obtain ⟨τ', -, y, s', hs', hne, hpost⟩ := exists_handles_running hs hst
    rcases running_step hpost with ⟨h, -⟩ | ⟨-, -, v, rfl, rfl, -⟩ | ⟨r', -, h, -⟩
    · exact absurd h hne
    · rw [hprop τ' v hs'.mem_input, localRun_zero]
    · omega
  | succ c ih =>
    intro τ x s st hs hst
    obtain ⟨τ', -, y, s', hs', hne, hpost⟩ := exists_handles_running hs hst
    rcases running_step hpost with ⟨h, -⟩ | ⟨h, -⟩ | ⟨r', st', hr, hst', rfl, rfl, -⟩
    · exact absurd h hne
    · omega
    · obtain rfl : c = r' := by omega
      rw [localRun_succ, ← ih hs' hst', used_eq hs' (r := c + 1) ⟨⟨st', hst'⟩, rfl⟩]

/-- `running_eq_localRun` for the state right after handling an input. -/
theorem running_eq_localRun_step {v₀ : Value}
    (hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = v₀) {c : ℕ} {st : A.State}
    (hs : ρ.Handles p τ x s)
    (h : (step A size B R Δsync p (ρ.clock p τ) x s).1.phase = .running st c) :
    st = A.localRun p v₀ (used ρ p) c := by
  rcases running_step h with ⟨h, -⟩ | ⟨rfl, -, v, rfl, rfl, -⟩ | ⟨r', st', rfl, hst', rfl, rfl, -⟩
  · exact running_eq_localRun hprop hs h
  · rw [hprop τ v hs.mem_input, localRun_zero]
  · rw [localRun_succ, running_eq_localRun hprop hs hst',
      used_eq hs (r := r' + 1) ⟨⟨st', hst'⟩, rfl⟩]

/-! #### Payload bits sent -/

/-- A step leading to the idle phase starts from it and keeps the payload bits sent. -/
theorem idle_step {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)} {s : State P A.Msg A.State}
    {now : ℕ} (h : (step A size B R Δsync p now x s).1.phase = .idle) :
    s.phase = .idle ∧ (step A size B R Δsync p now x s).1.sent = s.sent := by
  obtain ⟨phase, inbox, sent⟩ := s
  rcases x with (v | _) | ⟨q, b, m⟩ | k
  · cases phase <;> simp_all [step]
  · simp [step] at h
  · simp only [step] at h ⊢
    split_ifs at h ⊢
    · exact ⟨h, rfl⟩
    · exact ⟨h, rfl⟩
  · cases phase with
    | running st r =>
      simp only [step] at h ⊢
      split_ifs at h ⊢
    | _ => simp_all [step]

/-- A process has sent no payload bits before it starts the simulation. -/
theorem sent_eq_zero_of_idle (hs : ρ.Handles p τ x s) (h : s.phase = .idle) : s.sent = 0 :=
  hs.of_forall_inputs (Q := fun s : State P A.Msg A.State => s.phase = .idle → s.sent = 0)
    (fun _ => rfl) (fun _ _ _ _ s hQ hidle => by
      obtain ⟨h₁, h₂⟩ := idle_step hidle
      rw [h₂, hQ h₁]) h

/-- The first step after which a process runs in simulated state `st` after `c` rounds, having
sent the payload bits it has sent when handling `x` at time `τ` in state `s`. -/
theorem exists_handles_running_sent {st : A.State} {c : ℕ} (hs : ρ.Handles p τ x s)
    (hst : s.phase = .running st c) :
    ∃ τ' ≤ τ, ∃ y s', ρ.Handles p τ' y s' ∧ ¬ (s'.phase = .running st c ∧ s'.sent = s.sent) ∧
      (step A size B R Δsync p (ρ.clock p τ') y s').1.phase = .running st c ∧
      (step A size B R Δsync p (ρ.clock p τ') y s').1.sent = s.sent := by
  obtain ⟨τ', hτ', y, s', hs', hne, h⟩ := hs.exists_handles
    (Q := fun s' : State P A.Msg A.State => s'.phase = .running st c ∧ s'.sent = s.sent)
    (G := fun now y (s' : State P A.Msg A.State) =>
      ¬ (s'.phase = .running st c ∧ s'.sent = s.sent) ∧
        ((step A size B R Δsync p now y s').1.phase = .running st c ∧
          (step A size B R Δsync p now y s').1.sent = s.sent))
    (fun h => by cases h.1) (fun _ _ _ h => (em _).imp id fun h' => ⟨h', h⟩) ⟨hst, rfl⟩
  exact ⟨τ', hτ', y, s', hs', hne, h⟩

/-- The payload bits sent by `p` while it simulates round `c + 1` are at most the bits of the
messages of rounds `1, …, c + 1` of its simulated states, if all its proposals are `v₀`. -/
theorem sent_le_of_running {v₀ : Value}
    (hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = v₀) {c : ℕ} :
    ∀ {τ x s st}, ρ.Handles p τ x s → s.phase = .running st c →
      s.sent ≤ ∑ r ∈ Finset.range (c + 1),
        A.roundBits size p (A.localRun p v₀ (used ρ p) r) (r + 1) := by
  induction c with
  | zero =>
    intro τ x s st hs hst
    obtain ⟨τ', -, y, s', hs', hne, hpost, hsent⟩ := exists_handles_running_sent hs hst
    rcases running_step hpost with ⟨h, h'⟩ | ⟨-, hidle, v, rfl, rfl, h'⟩ | ⟨r', -, h, -⟩
    · exact absurd ⟨h, h'.symm.trans hsent⟩ hne
    · rw [← hsent, h', sent_eq_zero_of_idle hs' hidle, hprop τ' v hs'.mem_input]
      simpa using sendRound_fst_le (A := A) (size := size) (B := B) (p := p)
        (st := A.init p v₀) (r := 1) (sent := 0)
    · omega
  | succ c ih =>
    intro τ x s st hs hst
    obtain ⟨τ', -, y, s', hs', hne, hpost, hsent⟩ := exists_handles_running_sent hs hst
    rcases running_step hpost with ⟨h, h'⟩ | ⟨h, -⟩ | ⟨r', st', hr, hst', rfl, -, h'⟩
    · exact absurd ⟨h, h'.symm.trans hsent⟩ hne
    · omega
    · obtain rfl : c = r' := by omega
      rw [← hsent, h', Finset.sum_range_succ,
        ← running_eq_localRun_step (fun τ w hw => hprop τ w hw) hs' hpost]
      have := ih hs' hst'
      have := sendRound_fst_le (A := A) (size := size) (B := B) (p := p) (st := st)
        (r := c + 1 + 1) (sent := s'.sent)
      omega

/-- When `p` starts the simulation or completes round `k`, it has sent at most the bits of the
messages of rounds `1, …, k` of its simulated states, if all its proposals are `v₀`. -/
theorem sent_le_of_enters {v₀ : Value}
    (hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = v₀) {k : ℕ} (hs : ρ.Handles p τ x s)
    (he : Enters k x s) :
    s.sent ≤ ∑ r ∈ Finset.range k, A.roundBits size p (A.localRun p v₀ (used ρ p) r) (r + 1) := by
  cases k with
  | zero => simp [sent_eq_zero_of_idle hs he.1]
  | succ k =>
    obtain ⟨⟨st, hst⟩, -⟩ := he
    exact sent_le_of_running hprop hs hst

omit [Fintype P] [DecidableEq P] in
/-- Every step adds the payload bits it sends to the count of payload bits sent. -/
theorem sent_step_eq [Fintype P] [DecidableEq P] {now : ℕ}
    (x : Input P (Fin 2 × A.Msg) ℕ (Request Value)) (s : State P A.Msg A.State) :
    (step A size B R Δsync p now x s).1.sent =
      s.sent + ((step A size B R Δsync p now x s).2.map (Output.bits fun m => size m.2)).sum := by
  by_cases hx : x = .req .abandon
  · subst hx
    simp [step_abandon]
  by_cases he : ∃ k, Enters k x s
  · obtain ⟨k, hk⟩ := he
    obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R)
      (Δsync := Δsync) (p := p) (now := now) hk
    rw [hstep]
    split_ifs
    · exact sum_bits_startRound.symm
    · simp
  · push Not at he
    obtain ⟨-, h₁, h₂⟩ := step_of_not_enters (size := size) (B := B) (R := R) (Δsync := Δsync)
      (p := p) (now := now) he hx
    simp [h₁, h₂]

omit [Fintype P] [DecidableEq P] in
/-- Every step keeps the payload bits sent within the budget. -/
theorem sent_step_le_budget [Fintype P] [DecidableEq P] {now : ℕ}
    {x : Input P (Fin 2 × A.Msg) ℕ (Request Value)} {s : State P A.Msg A.State} (h : s.sent ≤ B) :
    (step A size B R Δsync p now x s).1.sent ≤ B := by
  by_cases hx : x = .req .abandon
  · subst hx
    simpa [step_abandon] using h
  by_cases he : ∃ k, Enters k x s
  · obtain ⟨k, hk⟩ := he
    obtain ⟨st, inbox, hstep⟩ := step_of_enters (size := size) (B := B) (R := R)
      (Δsync := Δsync) (p := p) (now := now) hk
    rw [hstep]
    split_ifs
    · exact sendRound_fst_le_budget h
    · exact h
  · push Not at he
    rw [(step_of_not_enters (size := size) (B := B) (R := R) (Δsync := Δsync) (p := p)
      (now := now) he hx).2.1]
    exact h

variable (ρ) in
/-- **Payload budget**: in every run, a process sends at most `B` payload bits in the
simulation. -/
theorem bitsSent_payload_le (p : P) (a b : ℕ) :
    ρ.bitsSent (fun m => size m.2) p a b ≤ B := by
  have h₁ := Run.bitsSent_add_le (ρ := ρ) (size := fun m : Fin 2 × A.Msg => size m.2) (p := p)
    (f := fun s : State P A.Msg A.State => s.sent)
    (fun now x s => ((Nat.add_comm _ _).trans (sent_step_eq x s).symm).le) (Nat.zero_le b)
  have h₂ : (ρ.state p b).sent ≤ B :=
    Run.state_of_inputs (ρ := ρ) (p := p) (τ := b)
      (Q := fun s : State P A.Msg A.State => s.sent ≤ B) (Nat.zero_le B)
      fun _ _ _ _ _ h => sent_step_le_budget h
  have h₃ := Run.bitsSent_mono (ρ := ρ) (size := fun m : Fin 2 × A.Msg => size m.2) (p := p)
    (Nat.zero_le a) (le_refl b)
  exact le_trans h₃ (le_trans (Nat.le_add_right _ _) (le_trans h₁ h₂))

variable (ρ) in
/-- **Bits of a simulation** (paper, proof of `lemma:cryptography_free_simulation_correct`,
intermediate result 2): in every run, if every payload has at least one bit, a process sends at
most `2 * B` bits in the simulation, counting one parity bit per message. -/
theorem bitsSent_le (hsize : ∀ m, 0 < size m) (p : P) (a b : ℕ) :
    ρ.bitsSent (fun m => size m.2 + 1) p a b ≤ 2 * B :=
  calc ρ.bitsSent (fun m => size m.2 + 1) p a b
      ≤ ρ.bitsSent (fun m => 2 * size m.2) p a b :=
        Run.bitsSent_mono_size fun m => by have := hsize m.2; omega
    _ = 2 * ρ.bitsSent (fun m => size m.2) p a b := Run.bitsSent_mul_size 2
    _ ≤ 2 * B := Nat.mul_le_mul_left 2 (bitsSent_payload_le ρ p a b)

/-! #### Unconditional properties -/

/-- A process that is running when it handles an input at time `τ` has proposed by time `τ`. -/
theorem exists_propose_of_running {st : A.State} {r : ℕ} (hs : ρ.Handles p τ x s)
    (hst : s.phase = .running st r) : ∃ τ' ≤ τ, ∃ v, .req (.propose v) ∈ ρ.input p τ' := by
  obtain ⟨τ', hτ', y, hy, w, rfl⟩ := hs.exists_input
    (Q := fun s : State P A.Msg A.State => ∃ st r, s.phase = .running st r)
    (g := fun y : Input P (Fin 2 × A.Msg) ℕ (Request Value) => ∃ w, y = .req (.propose w))
    (fun ⟨_, _, h⟩ => by cases h)
    (fun _ _ _ ⟨st, r, h⟩ => by
      rcases running_step h with ⟨h, -⟩ | ⟨-, -, w, rfl, -⟩ | ⟨r', st', -, h, -⟩
      · exact .inl ⟨st, r, h⟩
      · exact .inr ⟨w, rfl⟩
      · exact .inl ⟨st', r', h⟩)
    ⟨st, r, hst⟩
  exact ⟨τ', hτ', w, hy⟩

/-- A process that has abandoned before time `τ` is stopped in every state in which it handles an
input at time `τ`. -/
theorem phase_eq_stopped_of_abandon {τ' : ℕ} (hτ' : τ' < τ) (hab : .req .abandon ∈ ρ.input p τ')
    (hs : ρ.Handles p τ x s) : s.phase = .stopped := by
  have hQ : ∀ now y (s : State P A.Msg A.State), s.phase = .stopped →
      (step A size B R Δsync p now y s).1.phase = .stopped := fun _ _ _ h => phase_step_of_stopped h
  obtain ⟨s', hs'⟩ := Run.exists_handles_of_mem_input hab
  exact hs.of_inputs (fun _ _ => hQ _ _)
    (hs'.state_of_stable (Q := fun s : State P A.Msg A.State => s.phase = .stopped) hQ rfl hτ')

/-- *Integrity*: a process indicates only after it has proposed. -/
theorem exists_propose_of_ind {d : Option Value} (h : .ind d ∈ ρ.output p τ) :
    ∃ τ' ≤ τ, ∃ v, .req (.propose v) ∈ ρ.input p τ' := by
  obtain ⟨x, s, hs, hd⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨k, st, -, hst, -⟩ := ind_mem_step hd
  exact exists_propose_of_running hs hst

/-- *At most once*: a process indicates at most once. -/
theorem ind_unique {τ' : ℕ} {d d' : Option Value} (h : .ind d ∈ ρ.output p τ)
    (h' : .ind d' ∈ ρ.output p τ') : τ = τ' ∧ d = d' := by
  obtain ⟨x, s, hs, hd⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨x', s', hs', hd'⟩ := Run.mem_output_iff_handles.1 h'
  obtain ⟨k, st, -, hst, -, rfl, hpost⟩ := ind_mem_step hd
  obtain ⟨k', st', -, hst', -, rfl, hpost'⟩ := ind_mem_step hd'
  rcases hs.order (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s) hs' with
    ⟨rfl, rfl, rfl⟩ | hm | hm
  · rw [hst] at hst'
    simp only [Phase.running.injEq] at hst'
    obtain ⟨rfl, rfl⟩ := hst'
    exact ⟨rfl, rfl⟩
  · have hm : Mono (step A size B R Δsync p (ρ.clock p τ) x s).1 s' := hm
    have := hm (k' + 1) (by rw [hpost]; trivial)
    rw [hst'] at this
    exact absurd this (by simp [Phase.Completed])
  · have hm : Mono (step A size B R Δsync p (ρ.clock p τ') x' s').1 s := hm
    have := hm (k + 1) (by rw [hpost']; trivial)
    rw [hst] at this
    exact absurd this (by simp [Phase.Completed])

/-- *Duration*: a correct process that first proposes at `σ ≥ gst` indicates only at
`σ + R * Δsync`. -/
theorem ind_time (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hR : 0 < R) (hΔ : 0 < Δsync)
    {σ : ℕ} (hσ : ρ.gst ≤ σ) {v₀ : Value} (hprop : .req (.propose v₀) ∈ ρ.input p σ)
    (hfirst : ∀ τ < σ, ∀ v, .req (.propose v) ∉ ρ.input p τ) {d : Option Value}
    (h : .ind d ∈ ρ.output p τ) : τ = σ + R * Δsync := by
  obtain ⟨x, s, hs, hd⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨k, st, he, -, hk, -⟩ := ind_mem_step hd
  obtain ⟨hk', rfl⟩ := enters_time hρ hp hR hΔ hσ hprop hfirst hs he
  rw [show k + 1 = R by omega]

/-- *Termination*: a correct process that proposes at `σ` and does not abandon by
`max σ gst + R * Δsync` indicates by then. -/
theorem exists_ind (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hR : 0 < R) (hΔ : 0 < Δsync)
    {σ : ℕ} {v₀ : Value} (hprop : .req (.propose v₀) ∈ ρ.input p σ)
    (hab : ∀ τ ≤ max σ ρ.gst + R * Δsync, .req .abandon ∉ ρ.input p τ) :
    ∃ τ ≤ max σ ρ.gst + R * Δsync, ∃ d, .ind d ∈ ρ.output p τ := by
  obtain ⟨τ, hτ, x, s, hs, he⟩ := exists_enters hρ hp hΔ hprop hab le_rfl
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  obtain ⟨st, -, h⟩ := ind_mem_output_of_enters hs he le_rfl
  exact ⟨τ, hτ, _, h⟩

/-! #### Synchronous simulation -/

section Correct

variable {Δshift τ₀ : ℕ} {σ : P → ℕ} {prop : P → Value}

variable (ρ) in
/-- The synchronous execution of `A` simulated by the run `ρ` (with proposals `prop p`): same
faulty processes and proposals, and the round-`r` message of a faulty `q` to `p` is the one `p`
consumed when completing round `r`. -/
noncomputable def simulatedExecution (prop : P → Value) : A.Execution where
  faulty := ρ.faulty
  proposal := prop
  adversary r q p := used ρ p r q

section

variable (h : SyncAssumptions ρ.history R Δsync Δshift τ₀ σ prop) (hp : p ∉ ρ.faulty)
include h hp

theorem SyncAssumptions.propose_mem_iff {τ : ℕ} {v : Value} :
    .req (.propose v) ∈ ρ.input p τ ↔ τ = σ p ∧ v = prop p :=
  Run.req_mem_trace.symm.trans (h.propose_iff p hp τ v)

theorem SyncAssumptions.abandon_notMem {τ : ℕ} (hτ : τ ≤ σ p + R * Δsync) :
    .req .abandon ∉ ρ.input p τ := fun h' => by
  have := h.abandon_lt p hp τ (Run.req_mem_trace.2 h')
  omega

theorem SyncAssumptions.gst_le_start : ρ.gst ≤ σ p :=
  h.gst_le.trans (h.start_mem p hp).1

/-- The simulated state of a correct process after `c` rounds is computed by `A.localRun` from its
proposal and the messages it consumed. -/
theorem SyncAssumptions.running_eq {c : ℕ} {st : A.State} (hs : ρ.Handles p τ x s)
    (hst : s.phase = .running st c) : st = A.localRun p (prop p) (used ρ p) c :=
  running_eq_localRun (fun _ _ hw => ((h.propose_mem_iff hp).1 hw).2) hs hst

variable (hρ : ρ.Valid t δ) (hR : 0 < R) (hΔ : Δshift + δ < Δsync)
include hρ hR hΔ

/-- A correct process completes round `k` only at time `σ p + k * Δsync`, and only for
`k ≤ R`. -/
theorem SyncAssumptions.enters_time (hs : ρ.Handles p τ x s) {k : ℕ} (he : Enters k x s) :
    k ≤ R ∧ τ = σ p + k * Δsync :=
  Simulation.enters_time hρ hp hR (by omega) (h.gst_le_start hp)
    ((h.propose_mem_iff hp).2 ⟨rfl, rfl⟩)
    (fun τ hτ v hv => by have := ((h.propose_mem_iff hp).1 hv).1; omega) hs he

/-- A correct process completes every round `k ≤ R` at time `σ p + k * Δsync`. -/
theorem SyncAssumptions.exists_enters {k : ℕ} (hk : k ≤ R) :
    ∃ x s, ρ.Handles p (σ p + k * Δsync) x s ∧ Enters k x s := by
  have hmax : max (σ p) ρ.gst = σ p := max_eq_left (h.gst_le_start hp)
  obtain ⟨τ, -, x, s, hs, he⟩ := Simulation.exists_enters hρ hp (by omega)
    ((h.propose_mem_iff hp).2 ⟨rfl, rfl⟩)
    (fun τ hτ => h.abandon_notMem hp (by rwa [hmax] at hτ)) hk
  obtain ⟨-, rfl⟩ := h.enters_time hp hρ hR hΔ hs he
  exact ⟨x, s, hs, he⟩

/-- A correct process has not completed round `k + 1 ≤ R` by time `σ p + (k + 1) * Δsync`. -/
theorem SyncAssumptions.not_completed {k : ℕ} (hk : k + 1 ≤ R)
    (hτ : τ ≤ σ p + (k + 1) * Δsync) : ¬ (ρ.state p τ).phase.Completed (k + 1) := by
  intro hc
  have hmul := Nat.mul_le_mul_right Δsync hk
  obtain ⟨τ', hτ', x, s, hs, hx | he⟩ := exists_enters_of_completed hk hc
  · subst hx
    exact h.abandon_notMem hp (by omega) hs.mem_input
  · have := (h.enters_time hp hρ hR hΔ hs he).2
    omega

/-- A correct process has completed round `k ≤ R` after time `σ p + k * Δsync`. -/
theorem SyncAssumptions.completed_of_lt {k : ℕ} (hk : k ≤ R) (hτ : σ p + k * Δsync < τ) :
    (ρ.state p τ).phase.Completed k := by
  obtain ⟨x, s, hs, he⟩ := h.exists_enters hp hρ hR hΔ hk
  exact mono_state (show σ p + k * Δsync + 1 ≤ τ by omega) k
    (mono_handles_right hs k (completed_step_of_enters he))

/-- An input handled by a correct process after it completed round `k + 1 ≤ R` is handled at or
after time `σ p + (k + 1) * Δsync`. -/
theorem SyncAssumptions.le_of_completed (hs : ρ.Handles p τ x s) {k : ℕ} (hk : k + 1 ≤ R)
    (hc : s.phase.Completed (k + 1)) : σ p + (k + 1) * Δsync ≤ τ := by
  by_contra hlt
  exact h.not_completed hp hρ hR hΔ hk (show τ + 1 ≤ σ p + (k + 1) * Δsync by omega)
    (mono_handles_right hs (k + 1) (mono_step x s (k + 1) hc))

/-- The messages sent by a correct process: in round `k + 1 ≤ R`, at time `σ p + k * Δsync`,
the messages of its simulated state after `k` rounds, tagged with `parity (k + 1)`. -/
theorem SyncAssumptions.send_of_output {q : P} {b : Fin 2} {m : A.Msg}
    (hsend : .send q (b, m) ∈ ρ.output p τ) :
    ∃ k < R, b = parity (k + 1) ∧ τ = σ p + k * Δsync ∧
      A.send p (A.localRun p (prop p) (used ρ p) k) (k + 1) q = some m := by
  obtain ⟨x, s, hs, ho⟩ := Run.mem_output_iff_handles.1 hsend
  obtain ⟨k, st, he, hk, rfl, hm, hpost⟩ := send_mem_step ho
  obtain ⟨-, rfl⟩ := h.enters_time hp hρ hR hΔ hs he
  obtain rfl := running_eq_localRun_step (fun τ w hw => ((h.propose_mem_iff hp).1 hw).2) hs hpost
  exact ⟨k, by omega, rfl, rfl, hm⟩

/-- A correct process sends the messages of round `k + 1 ≤ R` of its simulated state after
`k` rounds at time `σ p + k * Δsync`, if the messages of its simulated states in rounds
`1, …, k + 1` fit in the budget. -/
theorem SyncAssumptions.send_mem_output {q : P} {k : ℕ} {m : A.Msg} (hk : k < R)
    (hB : ∑ r ∈ Finset.range (k + 1),
      A.roundBits size p (A.localRun p (prop p) (used ρ p) r) (r + 1) ≤ B)
    (hm : A.send p (A.localRun p (prop p) (used ρ p) k) (k + 1) q = some m) :
    .send q (parity (k + 1), m) ∈ ρ.output p (σ p + k * Δsync) := by
  have hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = prop p :=
    fun _ _ hw => ((h.propose_mem_iff hp).1 hw).2
  obtain ⟨x, s, hs, he⟩ := h.exists_enters hp hρ hR hΔ hk.le
  obtain ⟨st, inbox, hpost, hsub⟩ := startRound_subset_output hs he hk
  obtain rfl := running_eq_localRun_step hprop hs (by rw [hpost])
  have hsent := sent_le_of_enters hprop hs he
  rw [Finset.sum_range_succ] at hB
  exact hsub (send_mem_startRound_of_le (by omega) hm)

/-- The indications of a correct process: exactly one, at time `σ p + R * Δsync`, carrying the
decision of its simulated state after `R` rounds. -/
theorem SyncAssumptions.ind_mem_output_iff {d : Option Value} :
    .ind d ∈ ρ.output p τ ↔
      τ = σ p + R * Δsync ∧ d = A.decision (A.localRun p (prop p) (used ρ p) R) := by
  constructor
  · intro hd
    obtain ⟨x, s, hs, ho⟩ := Run.mem_output_iff_handles.1 hd
    obtain ⟨k, st, he, hst, hk, rfl, -⟩ := ind_mem_step ho
    obtain ⟨hk', rfl⟩ := h.enters_time hp hρ hR hΔ hs he
    obtain rfl : k + 1 = R := by omega
    exact ⟨rfl, by rw [localRun_succ, ← h.running_eq hp hs hst, used_eq hs he]⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨x, s, hs, he⟩ := h.exists_enters hp hρ hR hΔ le_rfl
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    obtain ⟨st, hst, hind⟩ := ind_mem_output_of_enters hs he le_rfl
    rwa [localRun_succ, ← h.running_eq hp hs hst, used_eq hs he]

end

variable (h : SyncAssumptions ρ.history R Δsync Δshift τ₀ σ prop) (hρ : ρ.Valid t δ) (hR : 0 < R)
  (hΔ : Δshift + δ < Δsync)
include h hρ hR hΔ

/-- *Receipt window*: every copy of a message that a correct `p` receives from a correct `q` is
`q`'s message of some round `j + 1 ≤ R`, tagged with `parity (j + 1)` and received within `δ`
after its sending at `σ q + j * Δsync`; hence strictly after `p` completed round `j - 1` and
strictly before it completes round `j + 1`. -/
theorem SyncAssumptions.recv_window {q : P} (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty) {b : Fin 2}
    {m : A.Msg} (hrecv : .recv q (b, m) ∈ ρ.input p τ) :
    ∃ j < R, b = parity (j + 1) ∧ σ q + j * Δsync < τ ∧ τ ≤ σ q + j * Δsync + δ ∧
      A.send q (A.localRun q (prop q) (used ρ q) j) (j + 1) p = some m := by
  obtain ⟨τs, hτs, hsend, hdel⟩ := hρ.authentic hp hq hrecv
  obtain ⟨j, hj, hb, rfl, hm⟩ := h.send_of_output hq hρ hR hΔ hsend
  have hgst := h.gst_le_start hq
  rw [max_eq_left (by omega)] at hdel
  exact ⟨j, hj, hb, hτs, hdel, hm⟩

/-- The message consumed by a correct `p` from a correct `q` in round `k + 1 ≤ R` is `q`'s message
of round `k + 1` of its simulated state after `k` rounds (paper
`lemma:cryptography_free_simulation_correct`, fourth item): it reaches slot `parity (k + 1)`
after the slot was last cleared and before round `k + 1` ends (completeness), and every message
of `q` in the slot then is a copy of it (soundness), see `SyncAssumptions.recv_window`. -/
theorem SyncAssumptions.used_of_correct {q : P} (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    {k : ℕ} (hk : k < R)
    (hB : ∑ r ∈ Finset.range (k + 1),
      A.roundBits size q (A.localRun q (prop q) (used ρ q) r) (r + 1) ≤ B) :
    used ρ p (k + 1) q = A.send q (A.localRun q (prop q) (used ρ q) k) (k + 1) p := by
  obtain ⟨x, s, hs, he⟩ := h.exists_enters hp hρ hR hΔ (show k + 1 ≤ R by omega)
  rw [used_eq hs he]
  obtain ⟨⟨st, hst⟩, -⟩ := he
  have hσp := h.start_mem p hp
  have hσq := h.start_mem q hq
  have e₁ : (k + 1) * Δsync = k * Δsync + Δsync := by rw [Nat.add_mul, Nat.one_mul]
  have hmul : k * Δsync + Δsync ≤ R * Δsync := by
    rw [← e₁]; exact Nat.mul_le_mul_right _ hk
  -- soundness: a message of `q` in the slot is `q`'s round-`(k + 1)` message
  have sound : ∀ m, s.inbox (parity (k + 1)) q = some m →
      A.send q (A.localRun q (prop q) (used ρ q) k) (k + 1) p = some m := by
    intro m hm
    obtain ⟨τ', hτ', y, s', hs', hG⟩ := hs.exists_handles (ρ := ρ)
      (Q := fun s : State P A.Msg A.State => s.inbox (parity (k + 1)) q = some m ∧
        (k ≤ 1 ∨ s.phase.Completed (k - 1)) ∧ ¬ s.phase.Completed (k + 1))
      (G := fun _ (y : Input P (Fin 2 × A.Msg) ℕ (Request Value)) (s : State P A.Msg A.State) =>
        (y = .recv q (parity (k + 1), m) ∧
        (k ≤ 1 ∨ s.phase.Completed (k - 1))) ∨ y = .req .abandon)
      (fun h => by cases h.1) (fun _ _ _ h => inbox_step_of_waiting h.1 h.2.1 h.2.2)
      ⟨hm, by rw [hst]; simp only [Phase.Completed]; omega, by
        rw [hst]; simp [Phase.Completed]⟩
    rcases hG with ⟨rfl, hw⟩ | rfl
    · obtain ⟨j, -, hb, h₁, h₂, hmsg⟩ := h.recv_window hρ hR hΔ hp hq hs'.mem_input
      rw [parity_eq_parity_iff] at hb
      -- `q` sent `m` in round `j + 1`, at most one round later than `k + 1`
      have hj₁ : j < k + 2 := by
        refine Nat.lt_of_mul_lt_mul_right (a := Δsync) ?_
        rw [Nat.add_mul]
        omega
      -- ... and at most one round earlier
      have hj₂ : k ≤ 1 ∨ k < j + 2 := by
        rcases hw with hw | hw
        · exact .inl hw
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · exact .inl (by omega)
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        have hle := h.le_of_completed hp hρ hR hΔ hs' (k := k') (by omega)
          (by simpa using hw)
        refine .inr (by
          have := Nat.lt_of_mul_lt_mul_right (a := Δsync) (b := k' + 1) (c := j + 1) (by
            rw [show (j + 1) * Δsync = j * Δsync + Δsync by rw [Nat.add_mul, Nat.one_mul]]
            omega)
          omega)
      obtain rfl : j = k := by omega
      exact hmsg
    · exact absurd hs'.mem_input (h.abandon_notMem hp (by omega))
  -- completeness: `q`'s round-`(k + 1)` message reaches the slot before round `k + 1` ends
  have complete : ∀ m, A.send q (A.localRun q (prop q) (used ρ q) k) (k + 1) p = some m →
      s.inbox (parity (k + 1)) q ≠ none := by
    intro m hm
    obtain ⟨τ', hτ'₁, hτ'₂, hrecv⟩ := hρ.reliable hq hp (h.send_mem_output hq hρ hR hΔ hk hB hm)
    have hgst := h.gst_le_start hq
    rw [max_eq_left (by omega)] at hτ'₂
    obtain ⟨s', hs'⟩ := Run.exists_handles_of_mem_input hrecv
    have hw : k ≤ 1 ∨ s'.phase.Completed (k - 1) := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · exact .inl (by omega)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      refine .inr (mono_handles_left hs' _ (h.completed_of_lt hp hρ hR hΔ (by omega) ?_))
      rw [show k' + 2 - 1 = k' + 1 by omega, Nat.add_mul, Nat.one_mul]
      rw [Nat.add_mul] at hτ'₁
      omega
    let F := fun s : State P A.Msg A.State => (s.inbox (parity (k + 1)) q ≠ none ∧
      (k ≤ 1 ∨ s.phase.Completed (k - 1))) ∨ s.phase.Completed (k + 1)
    have hQ := hs'.state_of_stable (Q := F) (fun _ _ _ h => filled_step h)
      (.inl ⟨inbox_step_recv_ne_none (size := size) (B := B) (R := R) (Δsync := Δsync) (p := p)
        (now := ρ.clock p τ')
        _ _ _ _, by rwa [phase_step_recv]⟩)
      (show τ' < σ p + (k + 1) * Δsync by omega)
    rcases hs.of_inputs (Q := F) (fun _ _ _ h => filled_step h) hQ with ⟨hne, -⟩ | hc
    · exact hne
    · rw [hst] at hc
      simp only [Phase.Completed] at hc
      omega
  cases hS : A.send q (A.localRun q (prop q) (used ρ q) k) (k + 1) p with
  | none =>
    cases hf : s.inbox (parity (k + 1)) q with
    | none => rfl
    | some m => simpa [hS] using sound m hf
  | some m =>
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.1 (complete m hS)
    rw [hm', ← hS, sound m' hm']

/-- The simulated states of correct processes are the states of the simulated execution, if `A`
sends at most `B` bits per process in `R` rounds (so that the budget never binds). -/
theorem SyncAssumptions.localRun_eq_state (hB : A.PerProcessBits t size R B) (hp : p ∉ ρ.faulty)
    {k : ℕ} (hk : k ≤ R) :
    A.localRun p (prop p) (used ρ p) k = (simulatedExecution ρ prop).state k p := by
  induction k using Nat.strong_induction_on generalizing p with
  | _ k ih =>
  cases k with
  | zero => rfl
  | succ k =>
    rw [localRun_succ, Algorithm.Execution.state_succ, ih k (by omega) hp (by omega)]
    congr 1
    funext q
    by_cases hq : q ∈ (simulatedExecution ρ prop).faulty
    · rw [Algorithm.Execution.received_of_mem hq]
      rfl
    · rw [Algorithm.Execution.received_of_notMem hq, ← ih k (by omega) hq (by omega)]
      refine h.used_of_correct hρ hR hΔ hp hq (by omega) ?_
      calc ∑ r ∈ Finset.range (k + 1),
            A.roundBits size q (A.localRun q (prop q) (used ρ q) r) (r + 1)
          = ∑ r ∈ Finset.range (k + 1),
            A.roundBits size q ((simulatedExecution ρ prop).state r q) (r + 1) :=
            Finset.sum_congr rfl fun r hr => by
              rw [ih r (by simp at hr; omega) hq (by simp at hr; omega)]
        _ ≤ (simulatedExecution ρ prop).bitsSent size q R :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hk)
        _ ≤ B := hB _ hρ.card_faulty_le q hq

/-- **Synchronous simulation**: under `SyncAssumptions`, if `A` sends at most `B` bits per process
in `R` rounds, the correct processes indicate the decisions of their states after `R` rounds of
the simulated execution, exactly `R * Δsync` after their proposals. -/
theorem SyncAssumptions.simulation (hB : A.PerProcessBits t size R B) :
    ∃ E : A.Execution, E.faulty = ρ.faulty ∧ (∀ p ∉ ρ.faulty, E.proposal p = prop p) ∧
      ∀ p ∉ ρ.faulty, ∀ τ d, .ind d ∈ ρ.output p τ ↔
        τ = σ p + R * Δsync ∧ d = A.decision (E.state R p) := by
  refine ⟨simulatedExecution ρ prop, rfl, fun _ _ => rfl, fun p hp τ d => ?_⟩
  rw [h.ind_mem_output_iff hp hρ hR hΔ, h.localRun_eq_state hρ hR hΔ hB hp le_rfl]

end Correct

/-! #### The simulation satisfies its specification -/

/-- The simulation is request-quiet: it indicates only when a round ends (on a timer). -/
theorem requestQuiet : (A.simulation size B R Δsync).RequestQuiet := by
  rintro p now (v | _) ⟨phase, inbox, sent⟩ d
  · cases phase with
    | idle => exact ind_notMem_startRound
    | running w r => simp [Algorithm.simulation, step]
    | stopped => simp [Algorithm.simulation, step]
  · simp [Algorithm.simulation, step]

/-- The simulation sends messages only while it is active: a process sends only when it starts a
round, which it does only after its first `propose`, and `abandon` stops it for good. -/
theorem sendsWhileActive :
    (A.simulation size B R Δsync).SendsWhileActive (· matches .propose _) (· matches .abandon) := by
  intro ρ p τ q m h
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨k, hk⟩ := exists_enters_of_mem_step hx
  refine ⟨?_, fun τ' hτ' r hr hin => ?_⟩
  · cases k with
    | zero =>
      obtain ⟨-, v, rfl⟩ := hk
      exact ⟨τ, le_rfl, .propose v, rfl, hs.mem_input⟩
    | succ k =>
      obtain ⟨⟨st, hst⟩, -⟩ := hk
      obtain ⟨τ', hτ', v, hv⟩ := exists_propose_of_running hs hst
      exact ⟨τ', hτ', .propose v, rfl, hv⟩
  · obtain rfl : r = .abandon := by cases r <;> first | rfl | cases hr
    have hstop := phase_eq_stopped_of_abandon hτ' hin hs
    cases k with
    | zero => simp [Enters, hstop] at hk
    | succ k =>
      obtain ⟨⟨st, hst⟩, -⟩ := hk
      rw [hstop] at hst
      cases hst

/-- **The simulation satisfies its specification**: if `R > 0` rounds are simulated, each of
duration `Δsync > Δshift + δ`, and every correct process of `A` sends at most `B` bits in `R`
rounds in executions with at most `t` faulty processes (so that the budget never binds in a
synchronous simulation). -/
theorem satisfies {Δshift : ℕ} (hR : 0 < R) (hΔ : Δshift + δ < Δsync)
    (hB : A.PerProcessBits t size R B) :
    (A.simulation size B R Δsync).Satisfies t δ (spec A R Δsync Δshift) := by
  intro ρ hρ
  have hΔ' : 0 < Δsync := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _ τ d hd
    obtain ⟨τ', hτ', v, hv⟩ := exists_propose_of_ind (Run.ind_mem_trace.1 hd)
    exact ⟨τ', hτ', v, Run.req_mem_trace.2 hv⟩
  · intro p _ τ τ' d d' hd hd'
    exact ind_unique (Run.ind_mem_trace.1 hd) (Run.ind_mem_trace.1 hd')
  · intro p hp σ v hσ hv hfirst τ d hd
    exact ind_time hρ hp hR hΔ' hσ (Run.req_mem_trace.1 hv)
      (fun τ hτ w hw => hfirst τ hτ w (Run.req_mem_trace.2 hw)) (Run.ind_mem_trace.1 hd)
  · intro p hp σ v hv hab
    obtain ⟨τ, hτ, d, hd⟩ := exists_ind hρ hp hR hΔ' (Run.req_mem_trace.1 hv)
      (fun τ hτ h => hab τ hτ (Run.req_mem_trace.2 h))
    exact ⟨τ, hτ, d, Run.ind_mem_trace.2 hd⟩
  · intro τ₀ σ prop h
    obtain ⟨E, hE, hprop, hind⟩ := h.simulation hρ hR hΔ hB
    exact ⟨E, hE, hprop, fun p hp τ d => Run.ind_mem_trace.trans (hind p hp τ d)⟩

end Synchronous.Simulation

namespace Synchronous.Simulation.Properties

variable {P Value : Type} [DecidableEq P] {A : Algorithm P Value} {R Δsync Δshift : ℕ}
  {H : History P (interface Value)}

/-- **Simulation of a synchronous Byzantine agreement algorithm** (the form in which the proof of
Crux's *Synchronicity* uses the simulation, [Civit et al.][CivitEtAl2024], §5): if `A` solves
`t`-resilient synchronous Byzantine agreement with latency `R`, at most `t` processes are faulty,
the simulations satisfy `SyncAssumptions`, and the proposals of correct processes are valid, then
all correct processes indicate `some v`, `R * Δsync` after their proposals, for a common valid
value `v` that is the common proposal if there is one. (The existence of a correct process `p₀`
is needed for `valid v`.) -/
theorem byzantineAgreement (h : Properties A R Δsync Δshift H) {t : ℕ} {valid : Value → Prop}
    (hA : A.SolvesByzantineAgreement t valid R) (ht : H.faulty.card ≤ t) {τ₀ : ℕ} {σ : P → ℕ}
    {prop : P → Value} (hs : SyncAssumptions H R Δsync Δshift τ₀ σ prop)
    (hvalid : ∀ p ∉ H.faulty, valid (prop p)) {p₀ : P} (hp₀ : p₀ ∉ H.faulty) :
    ∃ v, valid v ∧ (∀ w, (∀ p ∉ H.faulty, prop p = w) → v = w) ∧
      ∀ p ∉ H.faulty, ∀ τ d, .ind d ∈ H.trace p τ ↔ τ = σ p + R * Δsync ∧ d = some v := by
  obtain ⟨E, hE, hprop, hind⟩ := h.simulation τ₀ σ prop hs
  rw [← hE] at ht hvalid hp₀ hind hprop ⊢
  have hBA := hA E ht fun p hp => (hprop p hp) ▸ hvalid p hp
  obtain ⟨v, hv, hdec⟩ := hBA.exists_decision hp₀
  refine ⟨v, hv, fun w hw => ?_, fun p hp τ d => by rw [hind p hp, hdec p hp]⟩
  have := hBA.decision_eq (v := w) (fun p hp => (hprop p hp).trans (hw p hp)) hp₀
  rw [hdec p₀ hp₀] at this
  exact Option.some_injective _ this

end Synchronous.Simulation.Properties

end Cslib.Distributed
