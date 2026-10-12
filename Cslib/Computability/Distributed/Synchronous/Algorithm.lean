/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Synchronous round-based algorithms with Byzantine faults

In the synchronous model, computation unfolds in lock-step rounds `1, 2, …`: in each round,
every process sends (possibly different) messages to (some of) the processes, receives all
messages sent to it in this round, and updates its state deterministically
(see e.g. [Civit et al., *Partial synchrony for free?*][CivitEtAl2024], §1 and §4).

## The model

* An `Algorithm P Value` consists of local states and messages, an initial state for each
  process and proposal `Value`, the message `send p s r q` that `p` (in state `s`) sends to `q` in
  round `r` (`none` for no message), the transition `next p s r m` of `p` at the end of round `r`
  given the messages `m q` received from each `q`, and the decision `decision s` read off a state.
* An `Algorithm.Execution` fixes a set of faulty processes, the proposals, and an adversary that
  chooses, for every round `r`, faulty sender `q` and receiver `p`, the message
  `adversary r q p : Option Msg` that `p` receives from `q` in round `r`. Correct processes follow
  the algorithm; faulty processes are Byzantine: their messages are chosen by the adversary, and
  their states (also computed by `next` in `Execution.state`) are irrelevant.

Since the algorithm is deterministic, quantifying over all adversary functions covers all
(adaptive, full-information) adversary strategies for a fixed faulty set. Adaptive corruption is
subsumed by taking `faulty` to be the set of processes that are ever corrupted: the adversary can
make such a process behave correctly until its corruption.

The model covers deterministic algorithms without cryptography, the main setting of
[Civit et al.][CivitEtAl2024]: the messages of faulty processes are arbitrary, so the adversary is
not restricted to messages it can compute (it could, e.g., produce any signature). Algorithms whose
correctness relies on unforgeable signatures (simulated by the paper's `CryptoSim`) are not
covered.

The local states and messages live in `Type`, as do those of message-passing protocols
(`Cslib.Distributed.Protocol`), in which synchronous algorithms are simulated.

## Bits sent

`A.roundBits size p s r` is the number of bits that `p` in state `s` sends in round `r`, for the
message sizes `size`; `E.bitsSent size p R` is the number of bits `p` sends in the rounds
`1, …, R` of `E`; and `A.PerProcessBits t size R B` states that every correct process sends at
most `B` bits in these rounds, in every execution with at most `t` faulty processes (a bound on the
per-process bit complexity `pbit` of [Civit et al.][CivitEtAl2024], §3).
`Algorithm.perProcessBits_of_size_le`: messages of at most `L` bits give `B = R * n * L`.

## Round numbering

Rounds are numbered from `1`. `E.state r p` is the state of `p` *after `r` rounds*, i.e. at the
end of round `r` (equivalently, at the start of round `r + 1`); `E.state 0 p` is the initial
state. In round `r + 1`, a correct `q` sends `A.send q (E.state r q) (r + 1) p` to each `p`, and
then `E.state (r + 1) p = A.next p (E.state r p) (r + 1) m`, where `m q` is the message
received from `q` (see `Execution.received` and `Execution.state_succ`). The functions `send`
and `next` are never called with round number `0`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Distributed.Synchronous

/-- A deterministic round-based synchronous algorithm for processes `P` proposing and deciding
values in `Value`. Rounds are numbered from `1`. -/
structure Algorithm (P : Type*) (Value : Type*) where
  /-- The local states of processes. -/
  State : Type
  /-- The messages exchanged by processes. -/
  Msg : Type
  /-- `init p v` is the initial state of process `p` proposing `v`. -/
  init : P → Value → State
  /-- `send p s r q` is the message that process `p`, in state `s` at the start of round `r`,
  sends to process `q` in round `r`; `none` means that no message is sent. -/
  send : P → State → (round : ℕ) → P → Option Msg
  /-- `next p s r m` is the state of process `p` at the end of round `r`, where `s` is its state
  at the start of round `r` and `m q` is the message received from `q` in round `r` (`none` if
  no message was received). -/
  next : P → State → (round : ℕ) → (P → Option Msg) → State
  /-- The value decided in a state, if any. -/
  decision : State → Option Value

namespace Algorithm

variable {P Value : Type*}

/-- An execution of a synchronous algorithm `A` with Byzantine faults, determined by the set of
faulty processes, the proposals, and the messages sent by faulty processes. -/
structure Execution (A : Algorithm P Value) where
  /-- The set of faulty (Byzantine) processes; the others are correct. -/
  faulty : Finset P
  /-- The proposal of each process (that of a faulty process is irrelevant). -/
  proposal : P → Value
  /-- `adversary r q p` is the message that process `p` receives from process `q` in round `r`
  if `q` is faulty (it is ignored if `q` is correct or `r = 0`). -/
  adversary : (round : ℕ) → P → P → Option A.Msg

namespace Execution

variable [DecidableEq P] {A : Algorithm P Value} (E : A.Execution)

/-- `E.received s r p q` is the message that process `p` receives from process `q` in round `r`
when `s` gives the processes' states at the start of round `r`: a correct `q` follows `A.send`,
while the message of a faulty `q` is chosen by the adversary. -/
def received (s : P → A.State) (r : ℕ) (p : P) : P → Option A.Msg :=
  fun q => if q ∈ E.faulty then E.adversary r q p else A.send q (s q) r p

/-- `E.state r p` is the state of process `p` after `r` rounds (at the end of round `r`);
`E.state 0 p` is its initial state. Only the states of correct processes are meaningful. -/
def state : ℕ → P → A.State
  | 0, p => A.init p (E.proposal p)
  | r + 1, p => A.next p (state r p) (r + 1) (E.received (state r) (r + 1) p)

variable {E} {s s' : P → A.State} {r : ℕ} {p q : P}

@[simp]
theorem received_of_notMem (hq : q ∉ E.faulty) : E.received s r p q = A.send q (s q) r p := by
  simp [received, hq]

@[simp]
theorem received_of_mem (hq : q ∈ E.faulty) : E.received s r p q = E.adversary r q p := by
  simp [received, hq]

/-- Messages received in a round depend only on the states of correct processes. -/
theorem received_congr (h : ∀ q ∉ E.faulty, s q = s' q) :
    E.received s r p = E.received s' r p := by
  funext q
  by_cases hq : q ∈ E.faulty <;> simp [hq, h]

variable (E) (r p)

@[simp]
theorem state_zero : E.state 0 p = A.init p (E.proposal p) := rfl

theorem state_succ :
    E.state (r + 1) p = A.next p (E.state r p) (r + 1) (E.received (E.state r) (r + 1) p) :=
  rfl

variable {E r p}

/-- The states of correct processes during the first `R` rounds are determined by the algorithm,
the faulty set, the proposals and the adversary: any family of states `s` that starts from the
initial states and follows `A.next` on the messages prescribed by `E` (for correct processes,
during the first `R` rounds) agrees with `E.state` on correct processes after `r ≤ R` rounds. The
states of faulty processes in `s` are arbitrary. -/
theorem eq_state {s : ℕ → P → A.State} {R : ℕ}
    (h₀ : ∀ p ∉ E.faulty, s 0 p = A.init p (E.proposal p))
    (hs : ∀ r < R, ∀ p ∉ E.faulty,
      s (r + 1) p = A.next p (s r p) (r + 1) (E.received (s r) (r + 1) p))
    (hr : r ≤ R) (hp : p ∉ E.faulty) : s r p = E.state r p := by
  induction r generalizing p with
  | zero => exact h₀ p hp
  | succ r ih =>
    rw [hs r (by omega) p hp, state_succ, ih (by omega) hp,
      received_congr fun q hq => ih (by omega) hq]

end Execution

/-! ### Local runs -/

variable (A : Algorithm P Value)

/-- `A.localRun p v rcv r` is the state of process `p` after `r` rounds when it proposes `v` and
receives the message `rcv r' q` from each process `q` in each round `r' ≤ r`. -/
def localRun (p : P) (v : Value) (rcv : ℕ → P → Option A.Msg) : ℕ → A.State
  | 0 => A.init p v
  | r + 1 => A.next p (localRun p v rcv r) (r + 1) (rcv (r + 1))

variable {A}

@[simp]
theorem localRun_zero (p : P) (v : Value) (rcv : ℕ → P → Option A.Msg) :
    A.localRun p v rcv 0 = A.init p v := rfl

theorem localRun_succ (p : P) (v : Value) (rcv : ℕ → P → Option A.Msg) (r : ℕ) :
    A.localRun p v rcv (r + 1) = A.next p (A.localRun p v rcv r) (r + 1) (rcv (r + 1)) := rfl

/-- The state after `r` rounds depends only on the messages received in rounds `≤ r`. -/
theorem localRun_congr {p : P} {v : Value} {rcv rcv' : ℕ → P → Option A.Msg} {r : ℕ}
    (h : ∀ j ≤ r, rcv j = rcv' j) : A.localRun p v rcv r = A.localRun p v rcv' r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [localRun_succ, localRun_succ, ih fun j hj => h j (by omega), h _ le_rfl]

/-! ### Bits sent -/

section Bits

variable [Fintype P] (size : A.Msg → ℕ)

variable (A) in
/-- The bits that process `p` in state `s` sends in round `r`, for the message sizes `size`: the
sum of the sizes of its round-`r` messages to all processes. -/
def roundBits (p : P) (s : A.State) (r : ℕ) : ℕ :=
  ∑ q, ((A.send p s r q).map size).getD 0

variable [DecidableEq P]

/-- `E.bitsSent size p R` is the number of bits that process `p` sends in the rounds `1, …, R` of
the execution `E`, for the message sizes `size` (the bit complexity of `p` in the first `R` rounds
of `E`). -/
def Execution.bitsSent (E : A.Execution) (p : P) (R : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, A.roundBits size p (E.state r p) (r + 1)

omit size in
variable (A) in
/-- `A.PerProcessBits t size R B`: in every execution of `A` with at most `t` faulty processes,
every correct process sends at most `B` bits in the rounds `1, …, R`, for the message sizes
`size`. For an algorithm run for `R` rounds, the least such `B` is its per-process bit complexity
`pbit` ([Civit et al.][CivitEtAl2024], §3: the maximum, over all executions and processes, of the
number of bits sent by a correct process). Proposals are not restricted (to valid ones). -/
def PerProcessBits (t : ℕ) (size : A.Msg → ℕ) (R B : ℕ) : Prop :=
  ∀ E : A.Execution, E.faulty.card ≤ t → ∀ p ∉ E.faulty, E.bitsSent size p R ≤ B

variable {size}

theorem PerProcessBits.mono {t R B B' : ℕ} (h : A.PerProcessBits t size R B) (hB : B ≤ B') :
    A.PerProcessBits t size R B' :=
  fun E hE p hp => (h E hE p hp).trans hB

omit [DecidableEq P] in
/-- A process sends at most one message to each process per round, so it sends at most `n * L`
bits per round if messages have at most `L` bits. -/
theorem roundBits_le {L : ℕ} (h : ∀ m, size m ≤ L) (p : P) (s : A.State) (r : ℕ) :
    A.roundBits size p s r ≤ Fintype.card P * L := by
  refine (Finset.sum_le_card_nsmul _ _ L fun q _ => ?_).trans_eq (by simp)
  cases A.send p s r q <;> simp [h]

variable (A) in
/-- **Bits of messages of bounded size**: if messages have at most `L` bits, every process sends
at most `R * n * L` bits in `R` rounds. -/
theorem perProcessBits_of_size_le {L : ℕ} (h : ∀ m, size m ≤ L) (t R : ℕ) :
    A.PerProcessBits t size R (R * Fintype.card P * L) := by
  intro E _ p _
  refine (Finset.sum_le_card_nsmul _ _ _ fun r _ => roundBits_le h p _ _).trans_eq ?_
  simp [Nat.mul_assoc]

end Bits

end Algorithm

end Cslib.Distributed.Synchronous
