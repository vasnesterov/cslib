/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.ENat.Lattice
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Canonical asynchronous rounds in the asynchronous Byzantine message-passing model

This file models the *canonical-round algorithms* (in the style of Ben-Or's randomized consensus
algorithm: wait for `n - f` round-`r` messages, then start round `r + 1`) of Attiya, Flam and
Welch, *Why Canonical-Round Algorithms Fail for Optimal Byzantine Resilience* (Section 2),
running in the standard asynchronous message-passing model with Byzantine failures
(Section 2.1 there):

* `n` processes `Fin n`, at most `f` of them Byzantine (static faulty set chosen by the adversary).
* Reliable FIFO point-to-point links: process `p` receives the messages of `q` in the order in
  which `q` sent them.
* Every correct process wakes up exactly once (an adversary event), draws a random number and sends
  its round-1 message to all processes. Messages that arrive before wake-up are saved.
* Once a correct process has received round-`r` messages from `n - f` distinct senders, where `r`
  is the round of the last message it sent, it draws a fresh random number and sends its
  round-`r+1` message to all processes. This rule is applied repeatedly ("cascade"), since
  round-`r+1` messages may already have arrived.
* The *history* of a process is its input followed by the sequence of received messages and random
  numbers (`Log`). A canonical-round algorithm is given by
  - `msg p v h`: the content of the message sent by `p` (input `v`) when its history is `h`
    (`h` ends with the random number just drawn; the round label is added by the model), and
  - `dec p v h`: the decision function, applied to *every* history the process goes through; the
    decision of a process is the first `some` (decisions are irrevocable).
  In the paper the message content is the full history together with the random number; allowing
  an arbitrary function of the history is more general, so impossibility results proved in this
  model are stronger.
* Randomness: a *tape* `ρ : Fin n → ℕ → R`; `ρ p r` is the random number drawn by `p` when it
  starts its round `r` (i.e. sends its round-`r` message). For deterministic algorithms take
  `R = Unit`. The distribution of the tape is an arbitrary probability measure.
* The adversary is *full information* and *adaptive*: its next event is a function of the time
  and of the current configuration (all histories, i.e. all random numbers drawn so far, all
  messages sent so far), but not of future random numbers. Byzantine processes send arbitrary
  messages (with arbitrary round labels) at arbitrary times (`Event.byz`).

States are computed from the adversary's choices and the tape (`exec`); configurations store the
histories of the processes, the messages sent by Byzantine processes and, per link, how many
messages have been delivered; the messages sent by a correct process are *derived* from its
history (`outbox`), which makes FIFO delivery and the indistinguishability arguments simple.

Admissible executions (Section 2.1): every correct process eventually wakes up, and every link into
a correct process is served infinitely often (hence every message sent to a correct process is
eventually received, by FIFO). Agreement/validity-type properties ("safety") are required at every
finite prefix of every admissible execution (`Safe`).

## Main definitions

* `CanonAlg`: a canonical-round algorithm (message and decision functions of the history).
* `Config`, `Event`, `Adversary`, `Tape`: configurations, adversary events, full-information
  adversaries and random tapes.
* `CanonAlg.exec`: the execution of an algorithm under an adversary and a tape.
* `CanonAlg.Fair`, `CanonAlg.Admissible`: admissible executions and adversaries.
* `CanonAlg.rounds`, `CanonAlg.expRounds`: the (expected) canonical round complexity.
* `CanonAlg.Safe`: a specification holds at every prefix of every admissible execution.
* `ccView`, `CanonAlg.CommClosed`: communication-closed algorithms (late messages are discarded).

## Related models in CSLib

* `Cslib.Byzantine.PartialSync` is a partially synchronous model (global stabilization time,
  bounded delays after it) with state machines taking synchronous steps on a complete network.
* `Cslib.Byzantine.LockStep` is a model of synchronous lock-step rounds over a fixed graph.

The model here is different from both: it is *event-based* and fully asynchronous (adversarial
wake-ups and per-link FIFO deliveries, no timing assumptions at all), and it is specialised to
canonical-round algorithms, whose round structure is fixed by the model rather than by the clock.

## References

* [M. Ben-Or, *Another advantage of free choice: completely asynchronous agreement
  protocols*][BenOr1983]
* [H. Attiya, I. Flam, J. Welch, *Why Canonical-Round Algorithms Fail for Optimal Byzantine
  Resilience*][AttiyaFlamWelch2026]
-/

@[expose] public section

namespace Cslib.Byzantine.CanonicalRounds

open MeasureTheory

/-- An entry of the history of a process: a received message (sender, round label, content) or a
random number drawn when starting a new round. -/
inductive Entry (n : ℕ) (R M : Type*) where
  /-- The message with round label `r` and content `m`, received from `q`. -/
  | recv (q : Fin n) (r : ℕ) (m : M)
  /-- The random number `x`, drawn when starting a new round. -/
  | draw (x : R)

/-- A history (oldest entry first). The input is kept separately. -/
abbrev Log (n : ℕ) (R M : Type*) := List (Entry n R M)

variable {n : ℕ} {V R M O : Type*}

namespace Entry

/-- Is this entry a random draw (= the start of a new round)? -/
def isDraw : Entry n R M → Bool
  | recv .. => false
  | draw _ => true

end Entry

/-- The current round of a process with history `l`: the number of messages it has sent, i.e.
the number of random draws (`0` = not yet awake). -/
def rnd (l : Log n R M) : ℕ := l.countP Entry.isDraw

open Classical in
/-- The set of processes from which a round-`r` message is in the history. -/
noncomputable def senders (r : ℕ) (l : Log n R M) : Finset (Fin n) :=
  Finset.univ.filter fun q => ∃ m, Entry.recv q r m ∈ l

/-- The canonical-round rule: the process is awake and has received round-`r` messages from at
least `n - f` distinct processes, where `r` is its current round. -/
def Quorum (f : ℕ) (l : Log n R M) : Prop :=
  1 ≤ rnd l ∧ n - f ≤ (senders (rnd l) l).card

open Classical in
/-- Apply the canonical-round rule repeatedly (at most `k` times): each time, draw the next random
number (from the process' row `ρp` of the tape), which starts the next round. -/
noncomputable def advance (f : ℕ) (ρp : ℕ → R) : ℕ → Log n R M → Log n R M
  | 0, l => l
  | k + 1, l => if Quorum f l then advance f ρp k (l ++ [Entry.draw (ρp (rnd l + 1))]) else l

/-- The cascade after an event. With `n > f` every advance consumes a fresh round label among
the received messages, so `l.length + 1` iterations always suffice. -/
noncomputable def adv (f : ℕ) (ρp : ℕ → R) (l : Log n R M) : Log n R M :=
  advance f ρp (l.length + 1) l

/-- A canonical-round algorithm. -/
structure CanonAlg (n : ℕ) (V R M O : Type*) where
  /-- Content of the message sent by `p` with input `v` and history `h` (the round label is
  `rnd h`, added by the model). -/
  msg : Fin n → V → Log n R M → M
  /-- Decision function, applied to every history. -/
  dec : Fin n → V → Log n R M → Option O

namespace CanonAlg

variable (alg : CanonAlg n V R M O)

/-- The messages (round label, content) sent so far to every process by a correct process `q`
with input `v` and history `l`: one per draw, computed from the history ending with that draw. -/
def outbox (q : Fin n) (v : V) (l : Log n R M) : List (ℕ × M) :=
  ((l.inits).filter fun h => (h.getLast?.map Entry.isDraw) = some true).map
    fun h => (rnd h, alg.msg q v h)

/-- The decision of `p` (input `v`) after history `l`: the first decision along the history. -/
def decision (p : Fin n) (v : V) (l : Log n R M) : Option O :=
  l.inits.findSome? (alg.dec p v)

/-- `p` decides in or before its round `r`: some history prefix of round `≤ r` yields a decision. -/
def DecidesBy (p : Fin n) (v : V) (r : ℕ) (l : Log n R M) : Prop :=
  ∃ h ∈ l.inits, rnd h ≤ r ∧ (alg.dec p v h).isSome

end CanonAlg

/-- A global configuration. -/
structure Config (n : ℕ) (R M : Type*) where
  /-- Histories (only meaningful for correct processes). -/
  log : Fin n → Log n R M
  /-- `byzOut q p`: messages sent so far by the Byzantine process `q` to `p`. -/
  byzOut : Fin n → Fin n → List (ℕ × M)
  /-- `dlvd p q`: number of messages from `q` received so far by `p`. -/
  dlvd : Fin n → Fin n → ℕ

/-- The initial configuration. -/
def Config.init : Config n R M := ⟨fun _ => [], fun _ _ => [], fun _ _ => 0⟩

/-- Events chosen by the adversary. -/
inductive Event (n : ℕ) (M : Type*) where
  /-- Spontaneous wake-up of `p`. -/
  | wake (p : Fin n)
  /-- `p` receives the oldest in-transit message from `q` (no-op if there is none). -/
  | deliver (p q : Fin n)
  /-- Byzantine `q` sends the message `(r, m)` (round label `r`) to `p`. -/
  | byz (q p : Fin n) (r : ℕ) (m : M)
  /-- No-op. -/
  | skip

/-- An adversary: a static faulty set and a full-information scheduling strategy. -/
structure Adversary (n : ℕ) (R M : Type*) where
  /-- The (static) set of Byzantine processes. -/
  F : Finset (Fin n)
  /-- The event scheduled at time `k` in configuration `c`. -/
  ev : ℕ → Config n R M → Event n M

/-- A random tape: `ρ p r` is the random number drawn by `p` when starting round `r`. -/
abbrev Tape (n : ℕ) (R : Type*) := Fin n → ℕ → R

namespace CanonAlg

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n))
  (ρ : Tape n R)

/-- Messages sent so far by `q` to `p` in configuration `c`. -/
def sent (c : Config n R M) (q p : Fin n) : List (ℕ × M) :=
  if q ∈ F then c.byzOut q p else alg.outbox q (I q) (c.log q)

/-- One step of the system. -/
noncomputable def step (c : Config n R M) : Event n M → Config n R M
  | .wake p =>
    if p ∉ F ∧ rnd (c.log p) = 0 then
      { c with log := Function.update c.log p (adv f (ρ p) (c.log p ++ [.draw (ρ p 1)])) }
    else c
  | .deliver p q =>
    if p ∈ F then c else
    match (alg.sent I F c q p)[c.dlvd p q]? with
    | some w =>
      { c with
        log := Function.update c.log p (adv f (ρ p) (c.log p ++ [.recv q w.1 w.2]))
        dlvd := Function.update c.dlvd p (Function.update (c.dlvd p) q (c.dlvd p q + 1)) }
    | none => c
  | .byz q p r m =>
    if q ∈ F then
      { c with
        byzOut := Function.update c.byzOut q
          (Function.update (c.byzOut q) p (c.byzOut q p ++ [(r, m)])) }
    else c
  | .skip => c

/-- The execution of `alg` under adversary `A`, inputs `I` and tape `ρ`: configuration at
time `k`. -/
noncomputable def exec (A : Adversary n R M) : ℕ → Config n R M
  | 0 => Config.init
  | k + 1 => alg.step f I A.F ρ (exec A k) (A.ev k (exec A k))

/-- Fairness (admissibility) of the execution under tape `ρ`: every correct process wakes up and
every link into a correct process is served infinitely often. -/
def Fair (A : Adversary n R M) : Prop :=
  (∀ p ∉ A.F, ∃ k, 1 ≤ rnd ((alg.exec f I ρ A k).log p)) ∧
  ∀ p ∉ A.F, ∀ q, ∀ k, ∃ k' ≥ k, A.ev k' (alg.exec f I ρ A k') = .deliver p q

/-- An admissible adversary: at most `f` faults, fair for every tape. -/
def Admissible (A : Adversary n R M) : Prop :=
  A.F.card ≤ f ∧ ∀ ρ, alg.Fair f I ρ A

/-- All correct processes decide in or before their round `r`. -/
def AllDecideBy (A : Adversary n R M) (r : ℕ) : Prop :=
  ∀ p ∉ A.F, ∃ k, alg.DecidesBy p (I p) r ((alg.exec f I ρ A k).log p)

/-- The (canonical) round complexity of the execution: the smallest `r` such that every correct
process decides in or before its round `r` (`⊤` if there is none). -/
noncomputable def rounds (A : Adversary n R M) : ℕ∞ :=
  ⨅ (r : ℕ) (_ : alg.AllDecideBy f I ρ A r), (r : ℕ∞)

/-- All correct processes eventually decide. -/
def AllDecide (A : Adversary n R M) : Prop :=
  ∀ p ∉ A.F, ∃ k, (alg.decision p (I p) ((alg.exec f I ρ A k).log p)).isSome

/-- Expected round complexity under adversary `A` and inputs `I`, when the tape has
distribution `μ`. -/
noncomputable def expRounds [MeasurableSpace R] (μ : MeasureTheory.Measure (Tape n R))
    (A : Adversary n R M) : ENNReal :=
  ∫⁻ ρ, ((alg.rounds f I ρ A : ℕ∞) : ENNReal) ∂μ

end CanonAlg

/-- A problem specification: a property of the inputs, the faulty set, and the decisions so far
(`none` = not decided yet) of all processes. -/
abbrev Spec (n : ℕ) (V O : Type*) := (Fin n → V) → Finset (Fin n) → (Fin n → Option O) → Prop

namespace CanonAlg

variable (alg : CanonAlg n V R M O) (f : ℕ)

/-- Safety: the specification holds at every finite prefix of every admissible execution, for
every input assignment and every tape. -/
def Safe (S : Spec n V O) : Prop :=
  ∀ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A → ∀ ρ k,
    S I A.F fun p => alg.decision p (I p) ((alg.exec f I ρ A k).log p)

end CanonAlg

/-! ### Communication-closed algorithms (Section 3.2) -/

/-- One step of the communication-closed view: keep draws, keep a received round-`r` message iff
it did not arrive in a round later than `r`. -/
def ccStep (acc : Log n R M) : Entry n R M → Log n R M
  | .draw x => acc ++ [.draw x]
  | .recv q r m => if rnd acc ≤ r then acc ++ [.recv q r m] else acc

/-- The communication-closed view of a history: late messages are discarded. -/
def ccView (l : Log n R M) : Log n R M := l.foldl ccStep []

/-- A communication-closed canonical-round algorithm: messages and decisions only depend on the
communication-closed view of the history (round-`r` messages arriving after round `r` are
discarded). -/
def CanonAlg.CommClosed (alg : CanonAlg n V R M O) : Prop :=
  ∀ p v l l', ccView l = ccView l' → alg.msg p v l = alg.msg p v l' ∧ alg.dec p v l = alg.dec p v l'

end Cslib.Byzantine.CanonicalRounds
