/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.Byzantine
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The Dolev–Reischuk lower bound

If there are two valid values, every deterministic synchronous Byzantine agreement algorithm for
`n` processes tolerating `t` faults makes some correct process send `Ω(t² / n)` messages in some
execution with at most `t` faulty processes (D. Dolev and R. Reischuk, *Bounds on information
exchange for Byzantine agreement*, J. ACM 32(1), 1985). In particular, if `n ≤ 3 * (t + 1)`, the
per-process message (and bit) complexity of such an algorithm is `Ω(n)`.

**Argument (execution surgery).** Let `F` be a set of `b ≤ t` processes and `w`, `y` two valid
values. In the execution `E = DolevReischuk.execution A F w y`, the processes of `F` are faulty:
each of them sends the messages of a process that proposes `w` and hears from no other process
(`Algorithm.isolatedRun`), but only to processes outside `F`; the processes outside `F` are correct
and propose `y`, so they decide `y` by strong validity. Let `p ∈ F` be a process whose decision in
its isolated run is not `y`, and let `S = E.senders p R` be the set of correct processes that send
a message to `p` in the rounds `1, …, R` of `E`. If `b + |S| ≤ t + 1`, consider the execution
`E' = DolevReischuk.isolate E p R`, in which `p` is correct and the (at most `t`) processes of
`S ∪ (F \ {p})` are faulty and send the messages they send in `E`, except that they send nothing
to `p`. Then `p` hears from no other process in `E'`, so it follows its isolated run, while the
correct processes outside `F ∪ S` (there is one as `t + 2 ≤ n`) have the same states as in `E`
(`DolevReischuk.state_isolate`) and decide `y`; this contradicts agreement or termination in `E'`.
Hence `p` receives messages from at least `t - b + 2` correct processes
(`DolevReischuk.le_card_senders`).

If `2 * b ≤ n + 1`, the set `F` and the value `y` can be chosen such that the isolated decisions
of all processes of `F` differ from `y` (`DolevReischuk.exists_execution`). Then the `n - b`
correct processes of `E` send at least `b * (t - b + 2)` messages, and one of them sends at least
`⌈b * (t - b + 2) / (n - b)⌉` messages. For `b = t / 2 + 1`, this gives
`(t + 1) * (t + 3) ≤ 4 * n * B` for every bound `B` on the per-process bit complexity.

## Implementation notes

* A process may send messages to itself, and a correct process receives them in every execution.
  The isolated run of `p` is thus the run in which `p` receives only its own messages, not the run
  with an empty inbox (`Algorithm.localRun` with no messages).
* The isolated decision of `p ∈ F` depends on `p`, while `y` is the same for all of `F`; so `y`
  cannot simply be chosen different from the isolated decision of one process of `F`. Instead,
  for two distinct valid values `a` and `c`, either at least `b` processes do not decide `a` in
  their isolated run with proposal `a` (and we take `y = a`), or at least `n - b + 1 ≥ b`
  processes do (and we take `y = c`); `F` is a set of `b` such processes. This is where
  `2 * b ≤ n + 1` is needed.
* Messages are counted as bits of unit size: `E.bitsSent (fun _ => 1) p R` is the number of
  messages sent by `p` in the rounds `1, …, R` of `E`.
* The hypotheses on `n` are `t + 2 ≤ n` and `2 * b ≤ n + 1` rather than `3 * t < n`; for
  `b = t / 2 + 1`, `t + 2 ≤ n` suffices.

## Main definitions

* `Synchronous.Algorithm.isolatedRun`: the run of a process that hears from no other process.
* `Synchronous.Algorithm.Execution.senders`: the correct processes that send a message to a
  process in the first `R` rounds of an execution.
* `Synchronous.DolevReischuk.execution`, `Synchronous.DolevReischuk.isolate`: the executions `E`
  and `E'` of the argument.

## Main statements

* `Synchronous.Algorithm.SolvesByzantineAgreement.exists_mul_le_bitsSent`,
  `Synchronous.Algorithm.SolvesByzantineAgreement.exists_ceilDiv_le_bitsSent`: in some execution
  with at most `t` faulty processes, a correct process sends at least
  `⌈b * (t - b + 2) / (n - b)⌉` messages.
* `Synchronous.Algorithm.SolvesByzantineAgreement.mul_le_of_perProcessBits`,
  `Synchronous.Algorithm.SolvesByzantineAgreement.mul_le_four_mul_of_perProcessBits`: bounds on
  the per-process bit complexity, `b * (t - b + 2) ≤ (n - b) * B` and
  `(t + 1) * (t + 3) ≤ 4 * n * B`.
* `Synchronous.Algorithm.SolvesByzantineAgreement.card_add_six_le_of_perProcessBits`: if
  `n ≤ 3 * (t + 1)`, then `n + 6 ≤ 36 * B`.
-/

@[expose] public section

namespace Cslib.Distributed.Synchronous

open Finset

namespace Algorithm

variable {P Value : Type*} [DecidableEq P] {A : Algorithm P Value}

/-! ### Isolated runs, senders and messages -/

variable (A) in
/-- `A.isolatedRun p v r` is the state of process `p` after `r` rounds when it proposes `v` and
receives no message from other processes. It does receive its own messages to itself, as a
correct process does in every execution. -/
def isolatedRun (p : P) (v : Value) : ℕ → A.State
  | 0 => A.init p v
  | r + 1 => A.next p (isolatedRun p v r) (r + 1)
      fun q => if q = p then A.send p (isolatedRun p v r) (r + 1) p else none

@[simp]
theorem isolatedRun_zero (p : P) (v : Value) : A.isolatedRun p v 0 = A.init p v := rfl

theorem isolatedRun_succ (p : P) (v : Value) (r : ℕ) :
    A.isolatedRun p v (r + 1) = A.next p (A.isolatedRun p v r) (r + 1)
      (fun q => if q = p then A.send p (A.isolatedRun p v r) (r + 1) p else none) := rfl

namespace Execution

variable [Fintype P] {E : A.Execution}

variable (E) in
/-- `E.senders p R` is the set of correct processes that send a message to `p` in one of the
rounds `1, …, R` of `E`. -/
def senders (p : P) (R : ℕ) : Finset P :=
  {q ∈ E.faultyᶜ | ∃ r < R, (A.send q (E.state r q) (r + 1) p).isSome}

theorem mem_senders {p q : P} {R : ℕ} :
    q ∈ E.senders p R ↔ q ∉ E.faulty ∧ ∃ r < R, (A.send q (E.state r q) (r + 1) p).isSome := by
  simp [senders]

/-- The bits sent by a process are monotone in the message sizes. -/
theorem bitsSent_mono {size size' : A.Msg → ℕ} (h : ∀ m, size m ≤ size' m) (p : P) (R : ℕ) :
    E.bitsSent size p R ≤ E.bitsSent size' p R := by
  unfold bitsSent roundBits
  gcongr with r _ q
  cases A.send p _ _ q <;> simp [h]

/-- **Counting messages by receivers.** The correct processes send at least as many messages in
the rounds `1, …, R` as there are pairs of a correct process and a process to which it sends a
message in these rounds. -/
theorem sum_card_senders_le (R : ℕ) :
    ∑ p, #(E.senders p R) ≤ ∑ q ∈ E.faultyᶜ, E.bitsSent (fun _ => 1) q R := by
  simp only [senders, card_filter]
  rw [sum_comm]
  refine sum_le_sum fun q _ => ?_
  unfold bitsSent roundBits
  rw [sum_comm]
  refine sum_le_sum fun p _ => ?_
  split_ifs with h
  · obtain ⟨r, hr, hs⟩ := h
    refine le_trans ?_ (single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 hr))
    cases h' : A.send q (E.state r q) (r + 1) p <;> simp_all
  · exact Nat.zero_le _

end Execution

end Algorithm

/-! ### The executions of the argument -/

namespace DolevReischuk

open Algorithm Execution

variable {P Value : Type*} [DecidableEq P] {A : Algorithm P Value}

variable (A) in
/-- The execution `E` of the Dolev–Reischuk argument, for a set `F` of processes and values `w`
and `y`: the processes of `F` are faulty, and each `q ∈ F` sends the messages of a process that
proposes `w` and receives no message from other processes (`Algorithm.isolatedRun`), but only to
the processes outside `F`; the processes outside `F` are correct and propose `y`. -/
@[simps]
def execution (F : Finset P) (w y : Value) : A.Execution where
  faulty := F
  proposal q := if q ∈ F then w else y
  adversary r q p := if p ∈ F then none else A.send q (A.isolatedRun q w (r - 1)) r p

/-- The execution `E'` of the Dolev–Reischuk argument, obtained from an execution `E` by making
`p` correct and making faulty the correct processes that send a message to `p` in the rounds
`1, …, R` of `E` (`Execution.senders`): every faulty process sends the messages that are received
from it in `E` (`Execution.received`), except that it sends no message to `p`. -/
@[simps]
def isolate [Fintype P] (E : A.Execution) (p : P) (R : ℕ) : A.Execution where
  faulty := E.senders p R ∪ E.faulty.erase p
  proposal := E.proposal
  adversary r q p' := if p' = p then none else E.received (E.state (r - 1)) r p' q

variable [Fintype P] {F : Finset P} {w y : Value} {p : P} {R : ℕ}

/-- In the first `R` rounds of `E' = isolate E p R`, where `E = execution A F w y` and `p ∈ F`,
the process `p` follows its isolated run with proposal `w`, and the correct processes of `E'`
other than `p` have the same states as in `E`. -/
theorem state_isolate (hp : p ∈ F) {r : ℕ} (hr : r ≤ R) :
    (isolate (execution A F w y) p R).state r p = A.isolatedRun p w r ∧
      ∀ q ∉ F, q ∉ (execution A F w y).senders p R →
        (isolate (execution A F w y) p R).state r q = (execution A F w y).state r q := by
  set E := execution A F w y
  set E' := isolate E p R
  have hpE' : p ∉ E'.faulty := by simp [E', E, mem_senders, hp]
  let s : ℕ → P → A.State := fun r q => if q = p then A.isolatedRun p w r else E.state r q
  have key : ∀ q ∉ E'.faulty, s r q = E'.state r q := by
    refine fun q hq => eq_state (fun q hq => ?_) (fun r hr q hq => ?_) hr hq
    · by_cases hqp : q = p
      · subst hqp; simp [s, E', E, hp]
      · simp [s, hqp, E', E]
    by_cases hqp : q = p
    · subst hqp
      simp only [s, ↓reduceIte, isolatedRun_succ]
      congr 1
      funext q'
      by_cases hq' : q' ∈ E'.faulty
      · have : q' ≠ q := fun h => hpE' (h ▸ hq')
        simp [received_of_mem hq', this, E']
      · rw [received_of_notMem hq']
        by_cases hq'p : q' = q
        · subst hq'p; simp
        · have hq'F : q' ∉ F := fun h => hq' (by simp [E', E, h, hq'p])
          have hq'S : q' ∉ E.senders q R := by
            intro h; exact hq' (by simp [E', h])
          simp only [mem_senders, not_and, not_exists, not_and] at hq'S
          have := hq'S (by simpa [E] using hq'F) r hr
          simp_all
    · have hqF : q ∉ F := fun h => hq (by simp [E', E, h, hqp])
      simp only [s, hqp, ↓reduceIte, state_succ]
      congr 1
      funext q'
      by_cases hq' : q' ∈ E'.faulty
      · simp [received_of_mem hq', hqp, E']
      · rw [received_of_notMem hq']
        by_cases hq'p : q' = p
        · subst hq'p
          simp [E, hp, hqF]
        · have hq'F : q' ∉ F := fun h => hq' (by simp [E', E, h, hq'p])
          simp [hq'p, E, hq'F]
  refine ⟨by simpa [s] using (key p hpE').symm, fun q hqF hqS => ?_⟩
  have hqp : q ≠ p := fun h => hqF (h ▸ hp)
  simpa [s, hqp] using (key q (by simp [E', E, hqF, hqS])).symm

variable {t : ℕ} {valid : Value → Prop}

/-- **Every process of `F` with an isolated decision other than `y` receives messages from at
least `t - #F + 2` correct processes** in `E = execution A F w y` (for `#F ≤ t` and `t + 2 ≤ n`):
otherwise, in `E' = isolate E p R` (with at most `t` faulty processes), `p` follows its isolated
run and a correct process outside `F` follows its run in `E` and decides `y`, contradicting
agreement or termination. -/
theorem le_card_senders (hA : A.SolvesByzantineAgreement t valid R)
    (hn : t + 2 ≤ Fintype.card P) (hF : #F ≤ t) (hw : valid w) (hy : valid y) (hp : p ∈ F)
    (hpy : A.decision (A.isolatedRun p w R) ≠ some y) :
    t + 2 ≤ #F + #((execution A F w y).senders p R) := by
  by_contra! h
  set E := execution A F w y
  set E' := isolate E p R
  have hvalid : ∀ q, valid (E.proposal q) := fun q => by
    simp only [E, execution_proposal]; split_ifs <;> assumption
  have hE := hA E hF fun q _ => hvalid q
  have hE' := hA E' (by
    calc #E'.faulty ≤ #(E.senders p R) + #(F.erase p) := card_union_le _ _
      _ ≤ t := by
        have := card_pos.2 ⟨p, hp⟩
        rw [card_erase_of_mem hp]
        omega) fun q _ => hvalid q
  obtain ⟨q₀, hq₀F, hq₀S⟩ : ∃ q ∉ F, q ∉ E.senders p R := by
    by_contra! h'
    have := card_le_card (show (univ : Finset P) ⊆ F ∪ E.senders p R from fun q _ => by
      by_cases hq : q ∈ F
      · exact mem_union_left _ hq
      · exact mem_union_right _ (h' q hq))
    have := card_union_le F (E.senders p R)
    rw [card_univ] at *
    omega
  have hpE' : p ∉ E'.faulty := by simp [E', E, mem_senders, hp]
  have hq₀E' : q₀ ∉ E'.faulty := by simp [E', E, hq₀F, hq₀S]
  obtain ⟨hpR, hq₀R⟩ := state_isolate (y := y) hp le_rfl
  have hdec : A.decision (E.state R q₀) = some y :=
    hE.decision_eq (fun q hq => by simp_all [E]) (by simpa [E] using hq₀F)
  obtain ⟨v, hv⟩ := hE'.termination p hpE'
  have hvy := hE'.agreement p hpE' q₀ hq₀E' v y hv (by rw [hq₀R q₀ hq₀F hq₀S]; exact hdec)
  rw [hpR, hvy] at hv
  exact hpy hv

/-- **Choice of `F` and `y`.** If there are two distinct valid values, `t + 2 ≤ n`, `b ≤ t` and
`2 * b ≤ n + 1`, then there is an execution with exactly `b` faulty processes, in which correct
processes propose valid values and every faulty process receives messages from at least
`t - b + 2` correct processes in the rounds `1, …, R`. -/
theorem exists_execution (hA : A.SolvesByzantineAgreement t valid R) {a c : Value}
    (ha : valid a) (hc : valid c) (hac : a ≠ c) (hn : t + 2 ≤ Fintype.card P) {b : ℕ}
    (hbt : b ≤ t) (hbn : 2 * b ≤ Fintype.card P + 1) :
    ∃ E : A.Execution, #E.faulty = b ∧ (∀ q, valid (E.proposal q)) ∧
      ∀ p ∈ E.faulty, t - b + 2 ≤ #(E.senders p R) := by
  classical
  set G : Finset P := {p | A.decision (A.isolatedRun p a R) = some a}
  have key : ∀ (y : Value), valid y → ∀ D : Finset P, b ≤ #D →
      (∀ p ∈ D, A.decision (A.isolatedRun p a R) ≠ some y) →
      ∃ E : A.Execution, #E.faulty = b ∧ (∀ q, valid (E.proposal q)) ∧
        ∀ p ∈ E.faulty, t - b + 2 ≤ #(E.senders p R) := by
    intro y hy D hD hDy
    obtain ⟨F, hFD, hF⟩ := exists_subset_card_eq hD
    refine ⟨execution A F a y, hF, fun q => ?_, fun p hp => ?_⟩
    · simp only [execution_proposal]; split_ifs <;> assumption
    · rw [execution_faulty] at hp
      have := le_card_senders hA hn (hF ▸ hbt) ha hy hp (hDy p (hFD hp))
      omega
  by_cases h : b ≤ #Gᶜ
  · exact key a ha Gᶜ h fun p hp => by simpa [G] using hp
  · refine key c hc G (by rw [card_compl] at h; omega) fun p hp => ?_
    simp only [G, mem_filter, mem_univ, true_and] at hp
    rw [hp]
    exact fun h' => hac (Option.some_injective _ h')

end DolevReischuk

/-! ### The lower bound -/

namespace Algorithm.SolvesByzantineAgreement

open DolevReischuk Execution

variable {P Value : Type*} [DecidableEq P] [Fintype P] {A : Algorithm P Value} {t : ℕ}
  {valid : Value → Prop} {R : ℕ}

/-- **The Dolev–Reischuk lower bound.** If `A` solves `t`-resilient synchronous Byzantine
agreement with latency `R`, there are two distinct valid values, `t + 2 ≤ n`, `b ≤ t` and
`2 * b ≤ n + 1`, then in some execution with at most `t` faulty processes (and valid proposals),
some correct process sends at least `⌈b * (t - b + 2) / (n - b)⌉` messages in the rounds
`1, …, R`, i.e. `m` messages with `b * (t - b + 2) ≤ (n - b) * m`. -/
theorem exists_mul_le_bitsSent (hA : A.SolvesByzantineAgreement t valid R)
    (hvalid : ∃ a c, valid a ∧ valid c ∧ a ≠ c) (hn : t + 2 ≤ Fintype.card P) {b : ℕ}
    (hbt : b ≤ t) (hbn : 2 * b ≤ Fintype.card P + 1) :
    ∃ E : A.Execution, #E.faulty ≤ t ∧ (∀ q, valid (E.proposal q)) ∧ ∃ p ∉ E.faulty,
      b * (t - b + 2) ≤ (Fintype.card P - b) * E.bitsSent (fun _ => 1) p R := by
  obtain ⟨a, c, ha, hc, hac⟩ := hvalid
  obtain ⟨E, hEb, hEvalid, hE⟩ := exists_execution hA ha hc hac hn hbt hbn
  have hsum : b * (t - b + 2) ≤ ∑ q ∈ E.faultyᶜ, E.bitsSent (fun _ => 1) q R := by
    calc b * (t - b + 2) ≤ ∑ p ∈ E.faulty, #(E.senders p R) := by
          simpa [hEb] using card_nsmul_le_sum E.faulty _ _ hE
      _ ≤ ∑ p, #(E.senders p R) := sum_le_sum_of_subset (subset_univ _)
      _ ≤ _ := sum_card_senders_le R
  have hcard : #E.faultyᶜ = Fintype.card P - b := by rw [card_compl, hEb]
  have hne : E.faultyᶜ.Nonempty := by
    rw [← card_pos, hcard]; omega
  obtain ⟨p, hp, hle⟩ := exists_le_of_sum_le hne (f := fun _ => b * (t - b + 2))
    (g := fun q => (Fintype.card P - b) * E.bitsSent (fun _ => 1) q R) (by
      rw [sum_const, hcard, smul_eq_mul, ← mul_sum]
      exact Nat.mul_le_mul_left _ hsum)
  exact ⟨E, hEb ▸ hbt, hEvalid, p, mem_compl.1 hp, hle⟩

/-- **The Dolev–Reischuk lower bound** (`exists_mul_le_bitsSent`), stated with a ceiling
division: some correct process sends at least `⌈b * (t - b + 2) / (n - b)⌉` messages. -/
theorem exists_ceilDiv_le_bitsSent (hA : A.SolvesByzantineAgreement t valid R)
    (hvalid : ∃ a c, valid a ∧ valid c ∧ a ≠ c) (hn : t + 2 ≤ Fintype.card P) {b : ℕ}
    (hbt : b ≤ t) (hbn : 2 * b ≤ Fintype.card P + 1) :
    ∃ E : A.Execution, #E.faulty ≤ t ∧ (∀ q, valid (E.proposal q)) ∧ ∃ p ∉ E.faulty,
      b * (t - b + 2) ⌈/⌉ (Fintype.card P - b) ≤ E.bitsSent (fun _ => 1) p R := by
  obtain ⟨E, hE, hEvalid, p, hp, hle⟩ := exists_mul_le_bitsSent hA hvalid hn hbt hbn
  exact ⟨E, hE, hEvalid, p, hp, (ceilDiv_le_iff_le_mul (by omega)).2 hle⟩

/-- **Per-process bit complexity.** If every correct process sends at most `B` bits in the rounds
`1, …, R` (`PerProcessBits`), for message sizes `size` that are positive, then
`b * (t - b + 2) ≤ (n - b) * B` (under the assumptions of `exists_mul_le_bitsSent`). -/
theorem mul_le_of_perProcessBits (hA : A.SolvesByzantineAgreement t valid R)
    (hvalid : ∃ a c, valid a ∧ valid c ∧ a ≠ c) (hn : t + 2 ≤ Fintype.card P)
    {size : A.Msg → ℕ} (hsize : ∀ m, 0 < size m) {B : ℕ} (hB : A.PerProcessBits t size R B)
    {b : ℕ} (hbt : b ≤ t) (hbn : 2 * b ≤ Fintype.card P + 1) :
    b * (t - b + 2) ≤ (Fintype.card P - b) * B := by
  obtain ⟨E, hE, -, p, hp, hle⟩ := exists_mul_le_bitsSent hA hvalid hn hbt hbn
  exact hle.trans <| Nat.mul_le_mul_left _ <| (bitsSent_mono hsize p R).trans (hB E hE p hp)

/-- **Per-process bit complexity, `Ω(t² / n)`.** If `1 ≤ t`, `t + 2 ≤ n` and there are two
distinct valid values, then every bound `B` on the bits sent by a correct process in the rounds
`1, …, R` (for positive message sizes) satisfies `(t + 1) * (t + 3) ≤ 4 * n * B`. This is
`mul_le_of_perProcessBits` for `b = t / 2 + 1`. -/
theorem mul_le_four_mul_of_perProcessBits (hA : A.SolvesByzantineAgreement t valid R)
    (hvalid : ∃ a c, valid a ∧ valid c ∧ a ≠ c) (ht : 1 ≤ t) (hn : t + 2 ≤ Fintype.card P)
    {size : A.Msg → ℕ} (hsize : ∀ m, 0 < size m) {B : ℕ} (hB : A.PerProcessBits t size R B) :
    (t + 1) * (t + 3) ≤ 4 * Fintype.card P * B := by
  have h := (mul_le_of_perProcessBits hA hvalid hn hsize hB (b := t / 2 + 1) (by omega)
    (by omega)).trans (Nat.mul_le_mul_right B (Nat.sub_le (Fintype.card P) (t / 2 + 1)))
  suffices (t + 1) * (t + 3) ≤ 4 * ((t / 2 + 1) * (t - (t / 2 + 1) + 2)) by
    rw [Nat.mul_assoc]
    exact this.trans (Nat.mul_le_mul_left 4 h)
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' t
  · rw [show 2 * k / 2 + 1 = k + 1 by omega, show 2 * k - (k + 1) + 2 = k + 1 by omega]
    nlinarith
  · rw [show (2 * k + 1) / 2 + 1 = k + 1 by omega,
      show 2 * k + 1 - (k + 1) + 2 = k + 2 by omega]
    nlinarith

/-- **Per-process bit complexity, `Ω(n)` for `n ≤ 3 * (t + 1)`.** If `1 ≤ t`,
`t + 2 ≤ n ≤ 3 * (t + 1)` and there are two distinct valid values, then every bound `B` on the
bits sent by a correct process in the rounds `1, …, R` (for positive message sizes) satisfies
`n + 6 ≤ 36 * B`. -/
theorem card_add_six_le_of_perProcessBits (hA : A.SolvesByzantineAgreement t valid R)
    (hvalid : ∃ a c, valid a ∧ valid c ∧ a ≠ c) (ht : 1 ≤ t) (hn : t + 2 ≤ Fintype.card P)
    (hn' : Fintype.card P ≤ 3 * (t + 1)) {size : A.Msg → ℕ} (hsize : ∀ m, 0 < size m) {B : ℕ}
    (hB : A.PerProcessBits t size R B) :
    Fintype.card P + 6 ≤ 36 * B := by
  have h := mul_le_four_mul_of_perProcessBits hA hvalid ht hn hsize hB
  have hpos : 0 < Fintype.card P := by omega
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Fintype.card P * (Fintype.card P + 6) ≤ (3 * t + 3) * (3 * t + 9) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = 9 * ((t + 1) * (t + 3)) := by ring
    _ ≤ 9 * (4 * Fintype.card P * B) := Nat.mul_le_mul_left _ h
    _ = Fintype.card P * (36 * B) := by ring

end Algorithm.SolvesByzantineAgreement

end Cslib.Distributed.Synchronous
