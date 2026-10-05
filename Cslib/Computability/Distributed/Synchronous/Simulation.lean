/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.Byzantine
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

`Synchronous.Algorithm.simulation A R Δsync` has requests `propose v` and `abandon` and a single
indication carrying `A.decision` of the simulated state after `R` rounds (an `Option Value`).
Process `p`:
* upon its first `propose v` (unless it has abandoned): starts round `1`, i.e. sends its round-`1`
  messages for the initial state `A.init p v`, tagged with `1`, and sets timer `1` to fire
  `Δsync` later;
* upon a message `(r, m)` from `q`: buffers `m` as the round-`r` message from `q`, unless a
  round-`r` message from `q` is already buffered (the first one wins) or round `r` is completed;
  messages are buffered from the start, also before `propose`;
* upon timer `r` at the end of its current round `r`: computes its state after `r` rounds by
  `A.next` from the buffered round-`r` messages; if `r < R`, starts round `r + 1` (messages tagged
  with `r + 1`, timer `r + 1`); otherwise stops and indicates the decision of that state;
* upon `abandon`: stops (no further messages or indications).
The simulated state is not stored: since the buffers of completed rounds are frozen, it is
recomputed from the buffers (`Synchronous.Algorithm.localRun`).

## Main definitions

* `Synchronous.Algorithm.simulation`: the protocol.
* `Synchronous.Simulation.spec` (`Synchronous.Simulation.Properties`): integrity, at most once,
  duration, termination, and *synchronous simulation* under `Synchronous.Simulation.SyncAssumptions`
  (the processes start after GST within `Δshift` of each other and do not abandon).
* `Synchronous.Simulation.simulatedExecution`: the synchronous execution simulated by a run.

## Main statements

* `Synchronous.Simulation.satisfies`: for `0 < R` and `Δshift + δ < Δsync`, the simulation
  satisfies its specification.
* `Synchronous.Simulation.requestQuiet`: the simulation is request-quiet.
* `Synchronous.Simulation.Properties.byzantineAgreement`: simulating a synchronous Byzantine
  agreement algorithm with latency `R` yields agreement on a valid value, with strong validity.

## Implementation notes

* Messages carry the full round number and are buffered per (round, sender), the first message
  winning. The paper's `CryptoFreeSim` tags messages only with the parity of the round and never
  clears its buffer, so that the transition of round `k` would also consume stale messages of
  rounds `k - 2, k - 4, …`.
* The bound `Δshift + δ < Δsync` is strict (the paper uses `Δsync = Δshift + δ`): in the discrete
  model, a message delivered in the tick in which the round ends may be handled after the round's
  timer.
* The simulation property only assumes that each process does not abandon before the end of its
  own simulation. The paper's hypothesis (no correct process stops by `τ* + R * Δsync`, where `τ*`
  is the earliest start) is too weak for a process that starts up to `Δshift` later.
* The messages of faulty processes in the simulated execution are taken from the receivers'
  buffers. This needs the synchronous model to allow arbitrary faulty messages per (round,
  receiver): a faulty process may base its round-`k` messages on round-`(k + 1)` messages of
  correct processes that are ahead.
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

/-- The phase of a simulating process. -/
inductive Phase (Value : Type) where
  /-- Not yet proposed. -/
  | idle
  /-- Proposed `v`, completed `r` rounds, and simulating round `r + 1`. -/
  | running (v : Value) (r : ℕ)
  /-- Abandoned, or finished after the last round. -/
  | stopped

/-- `ph.Completed k`: the process has proposed and completed at least `k` rounds, or it has
stopped. Messages of round `k` are no longer buffered once `ph.Completed k` holds. -/
def Phase.Completed {Value : Type} : Phase Value → ℕ → Prop
  | .idle, _ => False
  | .running _ r, k => k ≤ r
  | .stopped, _ => True

instance {Value : Type} (ph : Phase Value) (k : ℕ) : Decidable (ph.Completed k) := by
  cases ph <;> unfold Phase.Completed <;> infer_instance

/-- The local state of a simulating process: its phase, and its buffer of round messages:
`inbox r q` is the first message of round `r` received from `q`. -/
structure State (P Msg Value : Type) where
  /-- The phase. -/
  phase : Phase Value
  /-- The buffer of round messages. -/
  inbox : ℕ → P → Option Msg

/-- `Enters k x s`: handling input `x` in state `s` completes round `k` (for `k = 0`: starts
the simulation). -/
def Enters {P Msg Value : Type} :
    ℕ → Input P (ℕ × Msg) ℕ (Request Value) → State P Msg Value → Prop
  | 0, x, s => s.phase = .idle ∧ ∃ v, x = .req (.propose v)
  | k + 1, x, s => (∃ v, s.phase = .running v k) ∧ x = .timeout (k + 1)

variable {P Value : Type} [Fintype P] (A : Algorithm P Value) (R Δsync : ℕ)

/-- The outputs of process `p` starting round `r + 1` in simulated state `st` at local time
`now`: its messages of round `r + 1`, tagged with `r + 1`, and a timer (tagged `r + 1`) for the
end of the round, `Δsync` later. -/
noncomputable def startRound (p : P) (now : ℕ) (st : A.State) (r : ℕ) :
    List (Output P (ℕ × A.Msg) ℕ (Option Value)) :=
  (Finset.univ.toList.filterMap fun q =>
      (A.send p st (r + 1) q).map fun m => .send q (r + 1, m)) ++
    [.setTimer (r + 1) (now + Δsync)]

variable [DecidableEq P]

/-- The step function of the simulation protocol (see `Synchronous.Algorithm.simulation`). -/
noncomputable def step (p : P) (now : ℕ) :
    Input P (ℕ × A.Msg) ℕ (Request Value) → State P A.Msg Value →
      State P A.Msg Value × List (Output P (ℕ × A.Msg) ℕ (Option Value))
  | .req (.propose v), s =>
    match s.phase with
    | .idle => (⟨.running v 0, s.inbox⟩, startRound A Δsync p now (A.init p v) 0)
    | _ => (s, [])
  | .req .abandon, s => (⟨.stopped, s.inbox⟩, [])
  | .recv q (j, m), s =>
    if ¬ s.phase.Completed j ∧ s.inbox j q = none then
      (⟨s.phase, fun j' q' => if j' = j ∧ q' = q then some m else s.inbox j' q'⟩, [])
    else (s, [])
  | .timeout k, s =>
    match s.phase with
    | .running v r =>
      if k = r + 1 then
        if k < R then
          (⟨.running v k, s.inbox⟩, startRound A Δsync p now (A.localRun p v s.inbox k) k)
        else (⟨.stopped, s.inbox⟩, [.ind (A.decision (A.localRun p v s.inbox k))])
      else (s, [])
    | _ => (s, [])

/-! #### Steps -/

variable {A R Δsync} {p : P} {now : ℕ}

omit [DecidableEq P] in
theorem send_mem_startRound_iff {st : A.State} {r j : ℕ} {q : P} {m : A.Msg} :
    Output.send q (j, m) ∈ startRound A Δsync p now st r ↔
      j = r + 1 ∧ A.send p st (r + 1) q = some m := by
  simp only [startRound, List.mem_append, List.mem_filterMap, Finset.mem_toList,
    Finset.mem_univ, true_and, Option.map_eq_some_iff, List.mem_singleton, reduceCtorEq,
    or_false, Output.send.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨q', m', h, rfl, rfl, rfl⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨q, m, h, rfl, rfl, rfl⟩

omit [DecidableEq P] in
theorem setTimer_mem_startRound_iff {st : A.State} {r j T : ℕ} :
    Output.setTimer j T ∈ startRound A Δsync p now st r ↔ j = r + 1 ∧ T = now + Δsync := by
  simp [startRound, eq_comm]

omit [DecidableEq P] in
theorem ind_notMem_startRound {st : A.State} {r : ℕ} {d : Option Value} :
    Output.ind d ∉ startRound A Δsync p now st r := by
  simp [startRound]

/-- A step that completes round `k` (see `Enters`): the process starts round `k + 1`, or stops
and indicates its decision after the last round. -/
theorem step_of_enters {k : ℕ} {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} (h : Enters k x s) :
    ∃ v, (k = 0 → x = .req (.propose v)) ∧ (∀ j, k = j + 1 → s.phase = .running v j) ∧
      step A R Δsync p now x s =
        if k = 0 ∨ k < R then
          (⟨.running v k, s.inbox⟩, startRound A Δsync p now (A.localRun p v s.inbox k) k)
        else (⟨.stopped, s.inbox⟩, [.ind (A.decision (A.localRun p v s.inbox k))]) := by
  obtain ⟨phase, inbox⟩ := s
  cases k with
  | zero =>
    obtain ⟨rfl, v, rfl⟩ := h
    exact ⟨v, fun _ => rfl, by simp, by simp [step]⟩
  | succ k =>
    obtain ⟨⟨v, rfl⟩, rfl⟩ := h
    refine ⟨v, by simp, by simp, ?_⟩
    simp only [step, ite_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or]

/-- A step that starts the simulation or completes round `k < R` starts round `k + 1`. -/
theorem step_of_enters_of_lt {k : ℕ} {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} (h : Enters k x s) (hk : k < R) :
    ∃ v, step A R Δsync p now x s =
      (⟨.running v k, s.inbox⟩, startRound A Δsync p now (A.localRun p v s.inbox k) k) := by
  obtain ⟨v, -, -, hstep⟩ := step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := now) h
  refine ⟨v, ?_⟩
  rw [hstep]
  split_ifs
  · rfl
  · omega

/-- A step that completes the last round `R ≥ 1` stops and indicates the decision of the state
after `R` rounds. -/
theorem step_of_enters_last {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} (h : Enters R x s) (hR : 0 < R) :
    ∃ v r, s.phase = .running v r ∧ step A R Δsync p now x s =
      (⟨.stopped, s.inbox⟩, [.ind (A.decision (A.localRun p v s.inbox R))]) := by
  obtain ⟨v, -, hv, hstep⟩ := step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := now) h
  refine ⟨v, R - 1, hv _ (by omega), ?_⟩
  rw [hstep]
  split_ifs
  · omega
  · rfl

/-- A step that completes no round and is not `abandon` changes neither the phase nor emits
outputs. -/
theorem step_of_not_enters {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} (h : ∀ k, ¬ Enters k x s) (hx : x ≠ .req .abandon) :
    (step A R Δsync p now x s).1.phase = s.phase ∧ (step A R Δsync p now x s).2 = [] := by
  obtain ⟨phase, inbox⟩ := s
  rcases x with (v | _) | ⟨q, j, m⟩ | k
  · cases phase with
    | idle => exact absurd ⟨rfl, v, rfl⟩ (h 0)
    | running w r => simp [step]
    | stopped => simp [step]
  · exact absurd rfl hx
  · simp only [step]
    split_ifs <;> simp
  · cases phase with
    | idle => simp [step]
    | running w r =>
      by_cases hk : k = r + 1
      · subst hk
        exact absurd ⟨⟨w, rfl⟩, rfl⟩ (h (r + 1))
      · simp [step, hk]
    | stopped => simp [step]

/-- `abandon` stops the process. -/
theorem step_abandon (s : State P A.Msg Value) :
    step A R Δsync p now (.req .abandon) s = (⟨.stopped, s.inbox⟩, []) := rfl

/-- `Mono s s'`: the progress from `s` to `s'` of a simulating process: completed rounds stay
completed, the buffers of completed rounds are frozen, and buffered messages are kept. -/
structure Mono {Msg : Type} (s s' : State P Msg Value) : Prop where
  /-- Completed rounds stay completed. -/
  completed : ∀ k, s.phase.Completed k → s'.phase.Completed k
  /-- The buffers of completed rounds are frozen. -/
  frozen : ∀ j, s.phase.Completed j → s'.inbox j = s.inbox j
  /-- Buffered messages are kept. -/
  inbox_some : ∀ j q m, s.inbox j q = some m → s'.inbox j q = some m

omit [Fintype P] [DecidableEq P] in
theorem Mono.refl {Msg : Type} (s : State P Msg Value) : Mono s s :=
  ⟨fun _ h => h, fun _ _ => rfl, fun _ _ _ h => h⟩

omit [Fintype P] [DecidableEq P] in
theorem Mono.trans {Msg : Type} {s₁ s₂ s₃ : State P Msg Value} (h₁ : Mono s₁ s₂)
    (h₂ : Mono s₂ s₃) : Mono s₁ s₃ :=
  ⟨fun k h => h₂.completed k (h₁.completed k h),
    fun j h => (h₂.frozen j (h₁.completed j h)).trans (h₁.frozen j h),
    fun j q m h => h₂.inbox_some j q m (h₁.inbox_some j q m h)⟩

/-- Every step makes progress (`Mono`). -/
theorem mono_step (x : Input P (ℕ × A.Msg) ℕ (Request Value)) (s : State P A.Msg Value) :
    Mono s (step A R Δsync p now x s).1 := by
  obtain ⟨phase, inbox⟩ := s
  rcases x with (v | _) | ⟨q, j, m⟩ | k
  · cases phase with
    | idle => exact ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ _ _ h => h⟩
    | running w r => exact Mono.refl _
    | stopped => exact Mono.refl _
  · exact ⟨fun _ _ => trivial, fun _ _ => rfl, fun _ _ _ h => h⟩
  · simp only [step]
    split_ifs with h
    · refine ⟨fun _ h => h, fun j' hj' => ?_, fun j' q' m' h' => ?_⟩
      · funext q'
        have : j' ≠ j := by rintro rfl; exact h.1 hj'
        simp [this]
      · simp only
        split_ifs with h''
        · obtain ⟨rfl, rfl⟩ := h''
          simp [h.2] at h'
        · exact h'
    · exact Mono.refl _
  · cases phase with
    | idle => exact Mono.refl _
    | running w r =>
      simp only [step]
      split_ifs with h₁ h₂
      · subst h₁
        exact ⟨fun k' (h : k' ≤ r) => (by simp [Phase.Completed]; omega), fun _ _ => rfl,
          fun _ _ _ h => h⟩
      · exact ⟨fun _ _ => trivial, fun _ _ => rfl, fun _ _ _ h => h⟩
      · exact Mono.refl _
    | stopped => exact Mono.refl _

/-- A step that makes `Completed m` true, for `m ≤ R`, is an `abandon` or completes round
`m`. -/
theorem enters_of_completed {m : ℕ} {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} (hs : ¬ s.phase.Completed m)
    (h : (step A R Δsync p now x s).1.phase.Completed m) (hm : m ≤ R) :
    x = .req .abandon ∨ Enters m x s := by
  by_cases hab : x = .req .abandon
  · exact .inl hab
  refine .inr ?_
  by_cases hk : ∃ k, Enters k x s
  · obtain ⟨k, hk⟩ := hk
    obtain ⟨v, -, hv, hstep⟩ := step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := now) hk
    cases k with
    | zero =>
      rw [hstep] at h
      simp only [true_or, ↓reduceIte, Phase.Completed, Nat.le_zero] at h
      exact h ▸ hk
    | succ k =>
      rw [hv k rfl] at hs
      simp only [Phase.Completed, not_le] at hs
      have hmk : m = k + 1 := by
        by_cases hc : k + 1 < R
        · rw [hstep] at h
          simp only [hc, or_true, ↓reduceIte, Phase.Completed] at h
          omega
        · omega
      exact hmk ▸ hk
  · rw [(step_of_not_enters (fun k hk' => hk ⟨k, hk'⟩) hab).1] at h
    exact absurd h hs

/-- Only steps completing a round have outputs. -/
theorem exists_enters_of_mem_step {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} {o : Output P (ℕ × A.Msg) ℕ (Option Value)}
    (h : o ∈ (step A R Δsync p now x s).2) : ∃ k, Enters k x s := by
  by_contra hk
  push Not at hk
  by_cases hx : x = .req .abandon
  · subst hx
    simp [step_abandon] at h
  · simp [(step_of_not_enters hk hx).2] at h

/-- Timers are set when completing round `k` (with `k = 0` or `k < R`), for the end of round
`k + 1`, `Δsync` later. -/
theorem setTimer_mem_step {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} {j T : ℕ} (h : .setTimer j T ∈ (step A R Δsync p now x s).2) :
    ∃ k, Enters k x s ∧ (k = 0 ∨ k < R) ∧ j = k + 1 ∧ T = now + Δsync := by
  obtain ⟨k, hk⟩ := exists_enters_of_mem_step h
  obtain ⟨v, -, -, hstep⟩ := step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := now) hk
  rw [hstep] at h
  split_ifs at h with hc
  · exact ⟨k, hk, hc, setTimer_mem_startRound_iff.1 h⟩
  · simp at h

/-- Messages are sent when completing round `k` (with `k = 0` or `k < R`): the messages of round
`k + 1` of the state after `k` rounds. -/
theorem send_mem_step {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} {q : P} {j : ℕ} {m : A.Msg}
    (h : .send q (j, m) ∈ (step A R Δsync p now x s).2) :
    ∃ k v, Enters k x s ∧ (k = 0 ∨ k < R) ∧ j = k + 1 ∧
      A.send p (A.localRun p v s.inbox k) (k + 1) q = some m ∧
      (step A R Δsync p now x s).1 = ⟨.running v k, s.inbox⟩ := by
  obtain ⟨k, hk⟩ := exists_enters_of_mem_step h
  obtain ⟨v, -, -, hstep⟩ := step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := now) hk
  rw [hstep] at h ⊢
  split_ifs at h ⊢ with hc
  · obtain ⟨rfl, hm⟩ := send_mem_startRound_iff.1 h
    exact ⟨k, v, hk, hc, rfl, hm, rfl⟩
  · simp at h

/-- The indication is emitted when completing the last round. -/
theorem ind_mem_step {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} {d : Option Value}
    (h : .ind d ∈ (step A R Δsync p now x s).2) :
    ∃ k v, Enters (k + 1) x s ∧ s.phase = .running v k ∧ R ≤ k + 1 ∧
      d = A.decision (A.localRun p v s.inbox (k + 1)) ∧
      (step A R Δsync p now x s).1 = ⟨.stopped, s.inbox⟩ := by
  obtain ⟨k, hk⟩ := exists_enters_of_mem_step h
  obtain ⟨v, -, hv, hstep⟩ := step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := now) hk
  rw [hstep] at h ⊢
  split_ifs at h ⊢ with hc
  · exact absurd h ind_notMem_startRound
  · cases k with
    | zero => simp at hc
    | succ k =>
      simp only [List.mem_singleton, Output.ind.injEq] at h
      exact ⟨k, v, hk, hv k rfl, by omega, h, rfl⟩

theorem completed_zero_step_propose (v : Value) (s : State P A.Msg Value) :
    (step A R Δsync p now (.req (.propose v)) s).1.phase.Completed 0 := by
  obtain ⟨phase, inbox⟩ := s
  cases phase <;> simp [step, Phase.Completed]

theorem completed_succ_step_timeout {k : ℕ} {s : State P A.Msg Value}
    (h : s.phase.Completed k) :
    (step A R Δsync p now (.timeout (k + 1)) s).1.phase.Completed (k + 1) := by
  obtain ⟨phase, inbox⟩ := s
  cases phase with
  | idle => exact h.elim
  | running v r =>
    simp only [Phase.Completed] at h
    simp only [step]
    split_ifs with h₁ h₂
    · simp [Phase.Completed]
    · simp [Phase.Completed]
    · simp only [Phase.Completed]; omega
  | stopped => simp [step, Phase.Completed]

/-- A process runs with proposal `v` only after it ran with `v` before or handled `propose v`. -/
theorem running_step {x : Input P (ℕ × A.Msg) ℕ (Request Value)} {s : State P A.Msg Value}
    {v : Value} {r : ℕ} (h : (step A R Δsync p now x s).1.phase = .running v r) :
    (∃ r', s.phase = .running v r') ∨ x = .req (.propose v) := by
  obtain ⟨phase, inbox⟩ := s
  rcases x with (w | _) | ⟨q, j, m⟩ | k
  · cases phase with
    | idle =>
      simp only [step, Phase.running.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact .inr rfl
    | running w' r' => exact .inl ⟨r, by simpa [step] using h⟩
    | stopped => simp [step] at h
  · simp [step] at h
  · simp only [step] at h
    split_ifs at h <;> exact .inl ⟨r, h⟩
  · cases phase with
    | idle => simp [step] at h
    | running w r' =>
      by_cases hk : k = r' + 1
      · subst hk
        by_cases hR : r' + 1 < R
        · simp only [step, hR, ↓reduceIte, Phase.running.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact .inl ⟨r', rfl⟩
        · simp [step, hR] at h
      · simp only [step, hk, ↓reduceIte, Phase.running.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact .inl ⟨r', rfl⟩
    | stopped => simp [step] at h

/-- The proposal recorded in the phase can only come from a `propose` request. -/
theorem value_step {v₀ : Value} {x : Input P (ℕ × A.Msg) ℕ (Request Value)}
    {s : State P A.Msg Value} (hx : ∀ w, x = .req (.propose w) → w = v₀)
    (hs : ∀ v r, s.phase = .running v r → v = v₀) :
    ∀ v r, (step A R Δsync p now x s).1.phase = .running v r → v = v₀ := fun v _ h =>
  (running_step h).elim (fun ⟨r', h'⟩ => hs v r' h') (hx v)

/-- Buffered messages come from receipts. -/
theorem inbox_step {x : Input P (ℕ × A.Msg) ℕ (Request Value)} {s : State P A.Msg Value}
    {j : ℕ} {q : P} {m : A.Msg} (h : (step A R Δsync p now x s).1.inbox j q = some m) :
    s.inbox j q = some m ∨ x = .recv q (j, m) := by
  obtain ⟨phase, inbox⟩ := s
  rcases x with (w | _) | ⟨q', j', m'⟩ | k
  · cases phase <;> simp_all [step]
  · simp_all [step]
  · simp only [step] at h
    split_ifs at h with h₁
    · simp only at h
      split_ifs at h with h₂
      · obtain ⟨rfl, rfl⟩ := h₂
        simp only [Option.some.injEq] at h
        subst h
        exact .inr rfl
      · exact .inl h
    · exact .inl h
  · cases phase with
    | idle => simp_all [step]
    | running w r =>
      simp only [step] at h
      split_ifs at h <;> exact .inl h
    | stopped => simp_all [step]

/-- Receiving a message of a round that is not completed buffers a message from its sender. -/
theorem step_recv (q : P) (j : ℕ) (m : A.Msg) (s : State P A.Msg Value) :
    (step A R Δsync p now (.recv q (j, m)) s).1.inbox j q ≠ none ∨
      (step A R Δsync p now (.recv q (j, m)) s).1.phase.Completed j := by
  simp only [step]
  split_ifs with h
  · simp
  · by_cases hc : s.phase.Completed j
    · exact .inr hc
    · exact .inl fun h' => h ⟨hc, h'⟩

end Synchronous.Simulation

namespace Synchronous.Algorithm

open Simulation

variable {P Value : Type} [Fintype P] [DecidableEq P]

/-- The simulation of the synchronous algorithm `A` for `R` rounds of `Δsync` local time
each. -/
noncomputable abbrev simulation (A : Algorithm P Value) (R Δsync : ℕ) :
    Protocol P (Simulation.interface Value) where
  Msg := ℕ × A.Msg
  Timer := ℕ
  State := Simulation.State P A.Msg Value
  init _ := ⟨.idle, fun _ _ => none⟩
  step := Simulation.step A R Δsync

end Synchronous.Algorithm

/-! ### Runs of the simulation -/

namespace Synchronous.Simulation

open Algorithm

variable {P Value : Type} [Fintype P] [DecidableEq P] {A : Algorithm P Value}
  {R Δsync t δ : ℕ} {ρ : Run (A.simulation R Δsync)} {p : P} {τ : ℕ}
  {x : Input P (ℕ × A.Msg) ℕ (Request Value)} {s : State P A.Msg Value}

/-- States of a simulating process progress over time (`Mono`). -/
theorem mono_state {τ τ' : ℕ} (h : τ ≤ τ') : Mono (ρ.state p τ) (ρ.state p τ') :=
  Run.rel_state (ρ := ρ) (p := p) (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s) h

/-- The state in which an input is handled at time `τ` is reached from the state at time `τ`. -/
theorem mono_handles_left (h : ρ.Handles p τ x s) : Mono (ρ.state p τ) s :=
  h.rel_left (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s)

/-- The state at time `τ + 1` is reached from the state after an input handled at time `τ`. -/
theorem mono_handles_right (h : ρ.Handles p τ x s) :
    Mono (step A R Δsync p (ρ.clock p τ) x s).1 (ρ.state p (τ + 1)) :=
  h.rel_right (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s)

/-- After a `propose`, the process has started (or stopped). -/
theorem completed_zero_of_propose {v : Value} (h : .req (.propose v) ∈ ρ.input p τ) :
    (ρ.state p (τ + 1)).phase.Completed 0 := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  exact hs.state_of_stable (Q := fun s : State P A.Msg Value => s.phase.Completed 0)
    (fun _ x s h => (mono_step x s).completed 0 h) (completed_zero_step_propose (R := R) v s)
    (Nat.lt_succ_self τ)

/-- *First-time argument* for completed rounds: if `p` has completed round `m ≤ R` (or stopped),
then it abandoned or completed round `m` earlier. -/
theorem exists_enters_of_completed {m : ℕ} (hm : m ≤ R)
    (h : (ρ.state p τ).phase.Completed m) :
    ∃ τ' < τ, ∃ x s, ρ.Handles p τ' x s ∧ (x = .req .abandon ∨ Enters m x s) :=
  Run.exists_handles_of_state (ρ := ρ) (Q := fun s : State P A.Msg Value => s.phase.Completed m)
    (G := fun _ x s => x = .req .abandon ∨ Enters m x s) (fun h => h)
    (fun _ _ s h => (em (s.phase.Completed m)).imp id fun hs => enters_of_completed hs h hm) h

/-- A process that starts the simulation or completes round `k < R` at time `τ` outputs its
messages of round `k + 1` and the timer for the end of that round at time `τ`. -/
theorem startRound_subset_output (hs : ρ.Handles p τ x s) {k : ℕ} (he : Enters k x s)
    (hk : k < R) :
    ∃ v, (step A R Δsync p (ρ.clock p τ) x s).1 = ⟨.running v k, s.inbox⟩ ∧
      startRound A Δsync p (ρ.clock p τ) (A.localRun p v s.inbox k) k ⊆ ρ.output p τ := by
  obtain ⟨v, hstep⟩ := step_of_enters_of_lt (R := R) (Δsync := Δsync) (p := p)
    (now := ρ.clock p τ) he hk
  refine ⟨v, by rw [hstep], fun o ho => hs.mem_output ?_⟩
  change o ∈ (step A R Δsync p (ρ.clock p τ) x s).2
  rwa [hstep]

/-- A process that completes the last round `R ≥ 1` at time `τ` indicates the decision of its
state after `R` rounds at time `τ`. -/
theorem ind_mem_output_of_enters (hs : ρ.Handles p τ x s) (he : Enters R x s) (hR : 0 < R) :
    ∃ v r, s.phase = .running v r ∧
      .ind (A.decision (A.localRun p v s.inbox R)) ∈ ρ.output p τ := by
  obtain ⟨v, r, hv, hstep⟩ := step_of_enters_last (Δsync := Δsync) (p := p)
    (now := ρ.clock p τ) he hR
  refine ⟨v, r, hv, hs.mem_output ?_⟩
  change _ ∈ (step A R Δsync p (ρ.clock p τ) x s).2
  rw [hstep]
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
    have hc := (mono_handles_left hs).completed 0
      ((mono_state (show σ + 1 ≤ τ by omega)).completed 0 (completed_zero_of_propose hprop))
    rw [hidle] at hc
    exact hc
  | succ k ih =>
    rintro τ x s hs ⟨⟨v, hv⟩, rfl⟩
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
    obtain ⟨v, hpost, hsub⟩ := startRound_subset_output hs he (show k < R by omega)
    obtain ⟨τe, hτe₁, hτe₂, hto⟩ :=
      hρ.exists_timeout_mem_input hp hΔ (hsub (setTimer_mem_startRound_iff.2 ⟨rfl, rfl⟩))
    have hck : (ρ.state p τe).phase.Completed k :=
      (mono_state (show τk + 1 ≤ τe by omega)).completed k
        ((mono_handles_right hs).completed k (by rw [hpost]; exact le_refl k))
    have hc' : (ρ.state p (τe + 1)).phase.Completed (k + 1) :=
      Run.state_succ_of_mem (ρ := ρ) (G := fun s : State P A.Msg Value => s.phase.Completed k)
        (Q := fun s : State P A.Msg Value => s.phase.Completed (k + 1)) hto
        (fun y _ s h => (mono_step y s).completed k h)
        (fun y _ s h => (mono_step y s).completed (k + 1) h)
        (fun s h => completed_succ_step_timeout h) hck
    have hmul : (k + 1) * Δsync ≤ R * Δsync := Nat.mul_le_mul_right _ hk
    have hτe : τe ≤ max σ ρ.gst + (k + 1) * Δsync := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    obtain ⟨τ, hτ, h⟩ := cross (k + 1) hk τe hc' (by omega)
    exact ⟨τ, by omega, h⟩

omit [Fintype P] [DecidableEq P] in
/-- Buffered messages are kept. -/
theorem Mono.inbox_ne_none {Msg : Type} {s s' : State P Msg Value} (h : Mono s s') {j : ℕ}
    {q : P} (hs : s.inbox j q ≠ none) : s'.inbox j q ≠ none := by
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hs
  rw [h.inbox_some j q m hm]
  simp

/-- The proposal recorded in the phase of `p` is one of its proposals. -/
theorem value_of_handles {v₀ : Value}
    (hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = v₀) (hs : ρ.Handles p τ x s) :
    ∀ v r, s.phase = .running v r → v = v₀ :=
  hs.of_forall_inputs (Q := fun s : State P A.Msg Value => ∀ v r, s.phase = .running v r → v = v₀)
    (fun _ _ h => by cases h)
    (fun τ' _ y hy s hs => value_step (fun w hw => hprop τ' w (hw ▸ hy)) hs)

theorem value_of_handles_step {v₀ : Value}
    (hprop : ∀ τ v, .req (.propose v) ∈ ρ.input p τ → v = v₀) (hs : ρ.Handles p τ x s) :
    ∀ v r, (step A R Δsync p (ρ.clock p τ) x s).1.phase = .running v r → v = v₀ :=
  value_step (fun w hw => hprop τ w (hw ▸ hs.mem_input)) (value_of_handles hprop hs)

/-- Buffered messages were received earlier. -/
theorem exists_recv_of_inbox {j : ℕ} {q : P} {m : A.Msg}
    (h : (ρ.state p τ).inbox j q = some m) : ∃ τ' < τ, .recv q (j, m) ∈ ρ.input p τ' := by
  obtain ⟨τ', hτ', y, s, hs, rfl⟩ := Run.exists_handles_of_state (ρ := ρ)
    (Q := fun s : State P A.Msg Value => s.inbox j q = some m)
    (G := fun _ y _ => y = .recv q (j, m)) (fun h => by cases h) (fun _ _ _ h => inbox_step h) h
  exact ⟨τ', hτ', hs.mem_input⟩

/-- A message of a round that is not completed at the end of the time of its receipt has been
buffered. -/
theorem inbox_ne_none_of_recv {j : ℕ} {q : P} {m : A.Msg} (h : .recv q (j, m) ∈ ρ.input p τ)
    (hc : ¬ (ρ.state p (τ + 1)).phase.Completed j) : (ρ.state p (τ + 1)).inbox j q ≠ none := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  have := hs.state_of_stable
    (Q := fun s : State P A.Msg Value => s.inbox j q ≠ none ∨ s.phase.Completed j)
    (fun _ y s h => h.imp (mono_step y s).inbox_ne_none ((mono_step y s).completed j))
    (step_recv (R := R) (Δsync := Δsync) (p := p) (now := ρ.clock p τ) q j m s)
    (Nat.lt_succ_self τ)
  exact this.resolve_right hc

/-! #### Unconditional properties -/

/-- *Integrity*: a process indicates only after it has proposed. -/
theorem exists_propose_of_ind {d : Option Value} (h : .ind d ∈ ρ.output p τ) :
    ∃ τ' ≤ τ, ∃ v, .req (.propose v) ∈ ρ.input p τ' := by
  obtain ⟨x, s, hs, hd⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨k, v, -, hv, -⟩ := ind_mem_step hd
  obtain ⟨τ', hτ', y, hy, w, rfl⟩ := hs.exists_input
    (Q := fun s : State P A.Msg Value => ∃ v r, s.phase = .running v r)
    (g := fun y : Input P (ℕ × A.Msg) ℕ (Request Value) => ∃ w, y = .req (.propose w))
    (fun ⟨_, _, h⟩ => by cases h)
    (fun _ _ _ ⟨v, r, h⟩ => (running_step h).imp (fun ⟨r', h'⟩ => ⟨v, r', h'⟩) fun h => ⟨v, h⟩)
    ⟨v, k, hv⟩
  exact ⟨τ', hτ', w, hy⟩

/-- *At most once*: a process indicates at most once. -/
theorem ind_unique {τ' : ℕ} {d d' : Option Value} (h : .ind d ∈ ρ.output p τ)
    (h' : .ind d' ∈ ρ.output p τ') : τ = τ' ∧ d = d' := by
  obtain ⟨x, s, hs, hd⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨x', s', hs', hd'⟩ := Run.mem_output_iff_handles.1 h'
  obtain ⟨k, v, -, hv, -, rfl, hpost⟩ := ind_mem_step hd
  obtain ⟨k', v', -, hv', -, rfl, hpost'⟩ := ind_mem_step hd'
  rcases hs.order (Rel := Mono) Mono.refl Mono.trans (fun _ x s => mono_step x s) hs' with
    ⟨rfl, rfl, rfl⟩ | hm | hm
  · rw [hv] at hv'
    simp only [Phase.running.injEq] at hv'
    obtain ⟨rfl, rfl⟩ := hv'
    exact ⟨rfl, rfl⟩
  · have hm : Mono (step A R Δsync p (ρ.clock p τ) x s).1 s' := hm
    rw [hpost] at hm
    have := hm.completed (k' + 1) trivial
    rw [hv'] at this
    exact absurd this (by simp [Phase.Completed])
  · have hm : Mono (step A R Δsync p (ρ.clock p τ') x' s').1 s := hm
    rw [hpost'] at hm
    have := hm.completed (k + 1) trivial
    rw [hv] at this
    exact absurd this (by simp [Phase.Completed])

/-- *Duration*: a correct process that first proposes at `σ ≥ gst` indicates only at
`σ + R * Δsync`. -/
theorem ind_time (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hR : 0 < R) (hΔ : 0 < Δsync)
    {σ : ℕ} (hσ : ρ.gst ≤ σ) {v₀ : Value} (hprop : .req (.propose v₀) ∈ ρ.input p σ)
    (hfirst : ∀ τ < σ, ∀ v, .req (.propose v) ∉ ρ.input p τ) {d : Option Value}
    (h : .ind d ∈ ρ.output p τ) : τ = σ + R * Δsync := by
  obtain ⟨x, s, hs, hd⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨k, v, he, -, hk, -⟩ := ind_mem_step hd
  obtain ⟨hk', rfl⟩ := enters_time hρ hp hR hΔ hσ hprop hfirst hs he
  rw [show k + 1 = R by omega]

/-- *Termination*: a correct process that proposes at `σ` and does not abandon by
`max σ gst + R * Δsync` indicates by then. -/
theorem exists_ind (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hR : 0 < R) (hΔ : 0 < Δsync)
    {σ : ℕ} {v₀ : Value} (hprop : .req (.propose v₀) ∈ ρ.input p σ)
    (hab : ∀ τ ≤ max σ ρ.gst + R * Δsync, .req .abandon ∉ ρ.input p τ) :
    ∃ τ ≤ max σ ρ.gst + R * Δsync, ∃ d, .ind d ∈ ρ.output p τ := by
  obtain ⟨τ, hτ, x, s, hs, he⟩ := exists_enters hρ hp hΔ hprop hab le_rfl
  obtain ⟨v, -, -, h⟩ := ind_mem_output_of_enters hs he hR
  exact ⟨τ, hτ, _, h⟩

/-! #### Synchronous simulation -/

section Correct

variable {Δshift τ₀ : ℕ} {σ : P → ℕ} {prop : P → Value}

variable (ρ) in
/-- The messages buffered by `p` at the end of its simulation, at time `σ p + R * Δsync + 1`. -/
noncomputable def finalInbox (σ : P → ℕ) (p : P) : ℕ → P → Option A.Msg :=
  (ρ.state p (σ p + R * Δsync + 1)).inbox

variable (ρ) in
/-- The synchronous execution of `A` simulated by the run `ρ` (with simulations started at
times `σ p` with proposals `prop p`): same faulty processes and proposals, and the round-`r`
message of a faulty `q` to `p` is the one `p` buffered. -/
noncomputable def simulatedExecution (σ : P → ℕ) (prop : P → Value) : A.Execution where
  faulty := ρ.faulty
  proposal := prop
  adversary r q p := finalInbox ρ σ p r q

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

/-- When a correct process completes round `k`, its buffers of rounds `≤ k` are final. -/
theorem SyncAssumptions.finalInbox_eq (hs : ρ.Handles p τ x s) {k : ℕ} (he : Enters k x s)
    {j : ℕ} (hj : j ≤ k) : finalInbox ρ σ p j = s.inbox j := by
  obtain ⟨hk, rfl⟩ := h.enters_time hp hρ hR hΔ hs he
  obtain ⟨v, -, -, hstep⟩ :=
    step_of_enters (R := R) (Δsync := Δsync) (p := p) (now := ρ.clock p (σ p + k * Δsync)) he
  have hm := (mono_handles_right hs).trans
    (mono_state (p := p) (show σ p + k * Δsync + 1 ≤ σ p + R * Δsync + 1 by
      have := Nat.mul_le_mul_right Δsync hk; omega))
  have hc : (step A R Δsync p (ρ.clock p (σ p + k * Δsync)) x s).1.phase.Completed j ∧
      (step A R Δsync p (ρ.clock p (σ p + k * Δsync)) x s).1.inbox = s.inbox := by
    rw [hstep]
    split_ifs
    · exact ⟨hj, rfl⟩
    · exact ⟨trivial, rfl⟩
  rw [finalInbox, hm.frozen j hc.1, hc.2]

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

/-- The messages sent by a correct process: in round `k + 1 ≤ R`, at time `σ p + k * Δsync`,
the messages of its simulated state after `k` rounds. -/
theorem SyncAssumptions.send_of_output {q : P} {j : ℕ} {m : A.Msg}
    (hsend : .send q (j, m) ∈ ρ.output p τ) :
    ∃ k < R, j = k + 1 ∧ τ = σ p + k * Δsync ∧
      A.send p (A.localRun p (prop p) (finalInbox ρ σ p) k) (k + 1) q = some m := by
  obtain ⟨x, s, hs, ho⟩ := Run.mem_output_iff_handles.1 hsend
  obtain ⟨k, v, he, hk, rfl, hm, hpost⟩ := send_mem_step ho
  obtain ⟨-, rfl⟩ := h.enters_time hp hρ hR hΔ hs he
  have hv : v = prop p := value_of_handles_step
    (fun τ w hw => ((h.propose_mem_iff hp).1 hw).2) hs v k (by rw [hpost])
  subst hv
  refine ⟨k, by omega, rfl, rfl, ?_⟩
  rwa [A.localRun_congr fun j hj => h.finalInbox_eq hp hρ hR hΔ hs he hj]

/-- A correct process sends the messages of round `k + 1 ≤ R` of its simulated state after
`k` rounds at time `σ p + k * Δsync`. -/
theorem SyncAssumptions.send_mem_output {q : P} {k : ℕ} {m : A.Msg} (hk : k < R)
    (hm : A.send p (A.localRun p (prop p) (finalInbox ρ σ p) k) (k + 1) q = some m) :
    .send q (k + 1, m) ∈ ρ.output p (σ p + k * Δsync) := by
  obtain ⟨x, s, hs, he⟩ := h.exists_enters hp hρ hR hΔ hk.le
  obtain ⟨v, hpost, hsub⟩ := startRound_subset_output hs he hk
  obtain rfl : v = prop p := value_of_handles_step
    (fun τ w hw => ((h.propose_mem_iff hp).1 hw).2) hs v k (by rw [hpost])
  refine hsub (send_mem_startRound_iff.2 ⟨rfl, ?_⟩)
  rwa [← A.localRun_congr fun j hj => h.finalInbox_eq hp hρ hR hΔ hs he hj]

/-- The indications of a correct process: exactly one, at time `σ p + R * Δsync`, carrying the
decision of its simulated state after `R` rounds. -/
theorem SyncAssumptions.ind_mem_output_iff {d : Option Value} :
    .ind d ∈ ρ.output p τ ↔
      τ = σ p + R * Δsync ∧ d = A.decision (A.localRun p (prop p) (finalInbox ρ σ p) R) := by
  have hval := fun τ w hw => ((h.propose_mem_iff (τ := τ) (v := w) hp).1 hw).2
  constructor
  · intro hd
    obtain ⟨x, s, hs, ho⟩ := Run.mem_output_iff_handles.1 hd
    obtain ⟨k, v, he, hv, hk, rfl, -⟩ := ind_mem_step ho
    obtain ⟨hk', rfl⟩ := h.enters_time hp hρ hR hΔ hs he
    obtain rfl : k + 1 = R := by omega
    obtain rfl := value_of_handles hval hs v k hv
    exact ⟨rfl, by rw [A.localRun_congr fun j hj => h.finalInbox_eq hp hρ hR hΔ hs he hj]⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨x, s, hs, he⟩ := h.exists_enters hp hρ hR hΔ le_rfl
    obtain ⟨v, r, hv, hind⟩ := ind_mem_output_of_enters hs he hR
    obtain rfl := value_of_handles hval hs v r hv
    rwa [A.localRun_congr fun j hj => h.finalInbox_eq hp hρ hR hΔ hs he hj]

end

variable (h : SyncAssumptions ρ.history R Δsync Δshift τ₀ σ prop) (hρ : ρ.Valid t δ) (hR : 0 < R)
  (hΔ : Δshift + δ < Δsync)
include h hρ hR hΔ

/-- The buffered round-`(k + 1)` message of a correct `p` from a correct `q` is the message of
round `k + 1` of `q`'s simulated state after `k` rounds (paper
`lemma:simulation_correct`, items (i) and (ii)): the message is delivered before the end of the
receiver's round `k + 1`, and every buffered round-`(k + 1)` message from `q` is the one `q`
sent. -/
theorem SyncAssumptions.finalInbox_of_correct {q : P} (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    {k : ℕ} (hk : k < R) :
    finalInbox ρ σ p (k + 1) q =
      A.send q (A.localRun q (prop q) (finalInbox ρ σ q) k) (k + 1) p := by
  have key : ∀ m, finalInbox ρ σ p (k + 1) q = some m →
      A.send q (A.localRun q (prop q) (finalInbox ρ σ q) k) (k + 1) p = some m := by
    intro m hm
    obtain ⟨τ', -, hrecv⟩ := exists_recv_of_inbox hm
    obtain ⟨τs, -, hsend⟩ := hρ.authentic hp hq hrecv
    obtain ⟨k', -, hkk, -, hm'⟩ := h.send_of_output hq hρ hR hΔ hsend
    obtain rfl : k = k' := by omega
    exact hm'
  cases hS : A.send q (A.localRun q (prop q) (finalInbox ρ σ q) k) (k + 1) p with
  | none =>
    cases hf : finalInbox ρ σ p (k + 1) q with
    | none => rfl
    | some m => simpa [hS] using key m hf
  | some m =>
    obtain ⟨τ', hτ'₁, hτ'₂, hrecv⟩ := hρ.reliable hq hp (h.send_mem_output hq hρ hR hΔ hk hS)
    have hgst := h.gst_le_start hq
    have hσ := h.start_mem p hp
    have hσ' := h.start_mem q hq
    have hmul : k * Δsync + Δsync ≤ R * Δsync := by
      have := Nat.mul_le_mul_right Δsync (show k + 1 ≤ R from hk)
      rwa [Nat.add_mul, Nat.one_mul] at this
    have hτ : τ' + 1 ≤ σ p + (k + 1) * Δsync := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hne := inbox_ne_none_of_recv hrecv (h.not_completed hp hρ hR hΔ hk hτ)
    have hne' : finalInbox ρ σ p (k + 1) q ≠ none :=
      (mono_state (p := p) (show τ' + 1 ≤ σ p + R * Δsync + 1 by
        rw [Nat.add_mul, Nat.one_mul] at hτ; omega)).inbox_ne_none hne
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.1 hne'
    rw [hm', ← hS, key m' hm']

/-- The simulated states of correct processes are the states of the simulated execution. -/
theorem SyncAssumptions.localRun_eq_state (hp : p ∉ ρ.faulty) {k : ℕ} (hk : k ≤ R) :
    A.localRun p (prop p) (finalInbox ρ σ p) k = (simulatedExecution ρ σ prop).state k p := by
  refine Algorithm.Execution.eq_state (s := fun k p => A.localRun p (prop p) (finalInbox ρ σ p) k)
    (fun _ _ => rfl) (fun r hr p hp => ?_) hk hp
  rw [localRun_succ]
  congr 1
  funext q
  by_cases hq : q ∈ (simulatedExecution ρ σ prop).faulty
  · rw [Algorithm.Execution.received_of_mem hq]
    rfl
  · rw [Algorithm.Execution.received_of_notMem hq]
    exact h.finalInbox_of_correct hρ hR hΔ hp hq hr

/-- **Synchronous simulation**: under `SyncAssumptions`, the correct processes
indicate the decisions of their states after `R` rounds of the simulated execution, exactly
`R * Δsync` after their proposals. -/
theorem SyncAssumptions.simulation :
    ∃ E : A.Execution, E.faulty = ρ.faulty ∧ (∀ p ∉ ρ.faulty, E.proposal p = prop p) ∧
      ∀ p ∉ ρ.faulty, ∀ τ d, .ind d ∈ ρ.output p τ ↔
        τ = σ p + R * Δsync ∧ d = A.decision (E.state R p) := by
  refine ⟨simulatedExecution ρ σ prop, rfl, fun _ _ => rfl, fun p hp τ d => ?_⟩
  rw [h.ind_mem_output_iff hp hρ hR hΔ, h.localRun_eq_state hρ hR hΔ hp le_rfl]

end Correct

/-! #### The simulation satisfies its specification -/

/-- The simulation is request-quiet: it indicates only when a round ends (on a timer). -/
theorem requestQuiet : (A.simulation R Δsync).RequestQuiet := by
  rintro p now (v | _) ⟨phase, inbox⟩ d
  · cases phase with
    | idle => exact ind_notMem_startRound
    | running w r => simp [Algorithm.simulation, step]
    | stopped => simp [Algorithm.simulation, step]
  · simp [Algorithm.simulation, step]

/-- **The simulation satisfies its specification**: if `R > 0` rounds are simulated, each of
duration `Δsync > Δshift + δ`. -/
theorem satisfies {Δshift : ℕ} (hR : 0 < R) (hΔ : Δshift + δ < Δsync) :
    (A.simulation R Δsync).Satisfies t δ (spec A R Δsync Δshift) := by
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
    obtain ⟨E, hE, hprop, hind⟩ := h.simulation hρ hR hΔ
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
