/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.Byzantine
public import Cslib.Computability.Distributed.Quorum

/-! # The phase-king algorithm

We prove that synchronous Byzantine agreement (`Synchronous.Algorithm.SolvesByzantineAgreement`)
is solvable whenever `3 * t < n`, for any type of values and any validity predicate, with a
multi-valued variant of the *phase-king* algorithm of
[Berman, Garay and Perry, *Towards optimal distributed consensus*][BermanGarayPerry1989].

**Algorithm.** There are `t + 1` phases `k = 0, …, t` of three rounds each (`3 * (t + 1)`
rounds in total). The king of phase `k` is `king k`, for an injective `king : Fin (t + 1) ↪ P`.
Every process holds a current value, initially its proposal, and decides its current value after
the last phase. In phase `k`:
1. every process broadcasts its value; a process that received some value `v` from at least
   `n - t` processes *proposes* `v`;
2. every process broadcasts its proposal (if any); a process that received the proposal `w` from
   at least `t + 1` processes adopts `w`, and is *strong* if it received `w` from at least
   `n - t` processes;
3. every process broadcasts its value; a process that is not strong adopts the value received
   from the king of the phase, **if this value is valid**.

**Correctness.** Let `F` be the set of at most `t` faulty processes.
* The proposals in a phase are equal: two quorums of `n - t` processes share a correct process
  (`proposal_eq`).
* The values of correct processes are always valid (`valid_value`): a proposed value was sent by
  a correct process, an adopted proposal was proposed by a correct process, and the value of the
  king is adopted only if it is valid.
* Unanimity persists: if all correct processes have the value `v` at the beginning of a phase,
  they all propose `v`, are strong with value `v`, and keep `v` (`value_of_forall`).
* After a phase with a correct king, all correct processes have the king's value
  (`value_eq_king`): a strong process adopted a value proposed by more than `t` correct processes,
  which the king adopted as well.
Since `king` is injective, one of the `t + 1` kings is correct, which gives agreement; strong
validity follows from the persistence of unanimity, and external validity from the validity
invariant.

## Implementation notes

* Compared with the usual (binary) presentation, values are arbitrary, and the king's value is
  only adopted if it is valid, which guarantees external validity against a faulty king.
* A process broadcasts in every round (its proposal in the second round of a phase, its value in
  the other rounds); the absence of a proposal is sent as no message. When several values reach a
  threshold, an arbitrary one is chosen (`supported`); the thresholds are such that the choice
  never matters.
* The king of phase `k` is `king k` for `k ≤ t`; for later rounds (which are irrelevant for the
  decision) the phase index is reduced modulo `t + 1`.

## Main definitions

* `PhaseKing.algorithm t king valid`: the phase-king algorithm.
* `PhaseKing.kings P t h`: an injective assignment of kings to the `t + 1` phases, for
  `t + 1 ≤ n`.

## Main statements

* `PhaseKing.solvesByzantineAgreement`: the phase-king algorithm is a `t`-resilient synchronous
  Byzantine agreement algorithm with latency `3 * (t + 1)` if `3 * t < n`.
* `PhaseKing.exists_solvesByzantineAgreement`: hence, if `3 * t < n`, there is such an algorithm.

## References

* [P. Berman, J. A. Garay, K. J. Perry, *Towards optimal distributed consensus*,
  FOCS 1989][BermanGarayPerry1989]
-/

@[expose] public section

namespace Cslib.Distributed.Synchronous.PhaseKing

open Finset

/-! ### Counting received messages -/

section Count

variable {P α : Type*} [Fintype P] [DecidableEq α] {m m' : P → Option α}
  {F : Finset P} {k l t : ℕ} {v w : α}

/-- `count m v` is the number of processes `q` with `m q = some v`. -/
def count (m : P → Option α) (v : α) : ℕ := #{q | m q = some v}

/-- `supported k m` is some value `v` with `k ≤ count m v`, if there is one. -/
noncomputable def supported (k : ℕ) (m : P → Option α) : Option α :=
  open scoped Classical in
  if h : ∃ v, k ≤ count m v then some h.choose else none

/-- A supported value reaches the threshold. -/
theorem le_count_of_supported_eq_some (h : supported k m = some v) : k ≤ count m v := by
  unfold supported at h
  split_ifs at h with hex
  cases h
  exact hex.choose_spec

/-- The only value that reaches the threshold is supported. -/
theorem supported_eq_some (hv : k ≤ count m v) (huniq : ∀ w, k ≤ count m w → w = v) :
    supported k m = some v := by
  have hex : ∃ v, k ≤ count m v := ⟨v, hv⟩
  simp [supported, hex, huniq _ hex.choose_spec]

/-- Two values received from sets of processes of total size more than `n` are equal. -/
theorem eq_of_lt_count_add_count (h : Fintype.card P < count m v + count m w) : v = w := by
  classical
  have := Quorum.card_add_card_sub_le_card_inter ({q | m q = some v} : Finset P)
    ({q | m q = some w} : Finset P)
  obtain ⟨q, hq⟩ :
      (({q | m q = some v} : Finset P) ∩ ({q | m q = some w} : Finset P)).Nonempty := by
    rw [← card_pos]
    unfold count at h
    omega
  simp only [mem_inter, mem_filter, mem_univ, true_and] at hq
  exact Option.some.inj (hq.1.symm.trans hq.2)

/-- If `v` was received from `l` processes, and `k + l > n` with `k ≤ l`, then `v` is the only
value received from `k` processes. -/
theorem supported_eq_some_of_lt (hv : l ≤ count m v) (hk : k ≤ l)
    (hkl : Fintype.card P < k + l) : supported k m = some v :=
  supported_eq_some (hk.trans hv) fun w hw =>
    eq_of_lt_count_add_count (m := m) (v := w) (by omega)

/-- If more than `t` processes sent `v`, then a correct process did. -/
theorem exists_notMem_of_lt_count (hF : #F ≤ t) (h : t < count m v) :
    ∃ q ∉ F, m q = some v := by
  obtain ⟨q, hq, hqF⟩ := Quorum.exists_notMem_of_lt_card hF h
  exact ⟨q, hqF, (mem_filter.1 hq).2⟩

/-- If correct processes send the same messages to two receivers, and each receiver received a
value from `n - t` processes, then these values are equal. -/
theorem eq_of_quorums (hF : #F ≤ t) (hn : 3 * t < Fintype.card P) (hm : ∀ q ∉ F, m q = m' q)
    (hv : Fintype.card P - t ≤ count m v) (hw : Fintype.card P - t ≤ count m' w) : v = w := by
  obtain ⟨q, hq, hq', hqF⟩ := Quorum.exists_notMem_inter_of_quorums hF hn hv hw
  simp only [mem_filter, mem_univ, true_and] at hq hq'
  exact Option.some.inj (hq.symm.trans ((hm q hqF).trans hq'))

/-- If correct processes send the same messages to two receivers, and the first one received `v`
from `n - t` processes, then the second one received `v` from more than `t` processes. -/
theorem lt_count_of_quorum (hF : #F ≤ t) (hn : 3 * t < Fintype.card P)
    (hm : ∀ q ∉ F, m q = m' q) (hv : Fintype.card P - t ≤ count m v) : t < count m' v := by
  classical
  refine (Quorum.lt_card_sdiff_of_quorum hF hn hv).trans_le (card_le_card fun q hq => ?_)
  simp only [mem_sdiff, mem_filter, mem_univ, true_and] at hq ⊢
  exact (hm q hq.2).symm.trans hq.1

/-- If all correct processes sent `v`, then `v` was received from `n - t` processes. -/
theorem card_sub_le_count (hF : #F ≤ t) (h : ∀ q ∉ F, m q = some v) :
    Fintype.card P - t ≤ count m v := by
  classical
  exact Quorum.card_sub_le_card_of_compl_subset hF fun q hq => by simp [h q (mem_compl.1 hq)]

end Count

/-! ### The algorithm -/

/-- The local state of a process in the phase-king algorithm. -/
structure State (Value : Type) where
  /-- The current value, initially the proposal; it is decided after the last phase. -/
  value : Value
  /-- The proposal of the current phase (sent in its second round), if any. -/
  proposal : Option Value
  /-- Whether the process is strong in the current phase: in its second round, it received the
  same proposal from at least `n - t` processes. -/
  strong : Bool

variable {P : Type*} [Fintype P] {Value : Type} [DecidableEq Value]

/-- The multi-valued **phase-king algorithm** ([BermanGarayPerry1989]) for at most `t` faulty
processes, with king `king k` in phase `k` and validity predicate `valid`. Phase `k` consists of
the rounds `3k + 1`, `3k + 2`, `3k + 3`:
1. every process broadcasts its value, and proposes a value received from `n - t` processes;
2. every process broadcasts its proposal (if any), adopts a value proposed by `t + 1` processes,
   and is strong if it was proposed by `n - t` processes;
3. every process broadcasts its value; a process that is not strong adopts the king's value if
   it is valid.

The decision is the current value. -/
@[reducible] noncomputable def algorithm (t : ℕ) (king : Fin (t + 1) ↪ P)
    (valid : Value → Prop) [DecidablePred valid] : Algorithm P Value where
  State := State Value
  Msg := Value
  init _ v := ⟨v, none, false⟩
  send _ s r _ := if (r - 1) % 3 = 1 then s.proposal else some s.value
  next _ s r m :=
    if (r - 1) % 3 = 0 then { s with proposal := supported (Fintype.card P - t) m }
    else if (r - 1) % 3 = 1 then
      { s with
        value := (supported (t + 1) m).getD s.value
        strong := (supported (Fintype.card P - t) m).isSome }
    else if s.strong then s
    else
      match m (king (Fin.ofNat (t + 1) ((r - 1) / 3))) with
      | some v => if valid v then { s with value := v } else s
      | none => s
  decision s := some s.value

section Execution

variable [DecidableEq P] {t : ℕ} {king : Fin (t + 1) ↪ P} {valid : Value → Prop}
  [DecidablePred valid] {E : (algorithm t king valid).Execution} {k : ℕ} {p q : P} {v w : Value}

/-! ### Rounds of a phase

Phase `k` consists of the rounds `3k + 1`, `3k + 2`, `3k + 3`, i.e. it leads from the states
`E.state (3 * k)` to the states `E.state (3 * k + 3)`. -/

/-- In the first round of a phase, a correct process sends its value. -/
theorem received_round1 (hq : q ∉ E.faulty) :
    E.received (E.state (3 * k)) (3 * k + 1) p q = some (E.state (3 * k) q).value := by
  simp [hq]

/-- In the second round of a phase, a correct process sends its proposal (if any). -/
theorem received_round2 (hq : q ∉ E.faulty) :
    E.received (E.state (3 * k + 1)) (3 * k + 2) p q = (E.state (3 * k + 1) q).proposal := by
  simp [hq]

/-- In the third round of a phase, a correct process sends its value. -/
theorem received_round3 (hq : q ∉ E.faulty) :
    E.received (E.state (3 * k + 2)) (3 * k + 3) p q = some (E.state (3 * k + 2) q).value := by
  simp [hq]

/-- The first round of a phase does not change the value. -/
theorem value_round1 : (E.state (3 * k + 1) p).value = (E.state (3 * k) p).value := by
  rw [Algorithm.Execution.state_succ]
  simp

/-- In the first round of a phase, a process proposes a value received from `n - t` processes,
if any. -/
theorem proposal_round1 : (E.state (3 * k + 1) p).proposal =
    supported (Fintype.card P - t) (E.received (E.state (3 * k)) (3 * k + 1) p) := by
  rw [Algorithm.Execution.state_succ]
  simp

/-- In the second round of a phase, a process adopts a value proposed by `t + 1` processes, if
any. -/
theorem value_round2 : (E.state (3 * k + 2) p).value =
    (supported (t + 1) (E.received (E.state (3 * k + 1)) (3 * k + 2) p)).getD
      (E.state (3 * k + 1) p).value := by
  rw [Algorithm.Execution.state_succ]
  simp

/-- In the second round of a phase, a process becomes strong iff some value was proposed by
`n - t` processes. -/
theorem strong_round2 : (E.state (3 * k + 2) p).strong =
    (supported (Fintype.card P - t) (E.received (E.state (3 * k + 1)) (3 * k + 2) p)).isSome := by
  rw [Algorithm.Execution.state_succ]
  simp

/-- A strong process keeps its value in the third round of a phase. -/
theorem value_round3_of_strong (h : (E.state (3 * k + 2) p).strong) :
    (E.state (3 * k + 3) p).value = (E.state (3 * k + 2) p).value := by
  rw [Algorithm.Execution.state_succ]
  simp [h]

/-- In the third round of a phase `k ≤ t`, a process that is not strong adopts the valid value
received from the king `king k`. -/
theorem value_round3_of_not_strong (h : (E.state (3 * k + 2) p).strong = false)
    (hk : k < t + 1)
    (hm : E.received (E.state (3 * k + 2)) (3 * k + 3) p (king ⟨k, hk⟩) = some v)
    (hv : valid v) : (E.state (3 * k + 3) p).value = v := by
  have hidx : Fin.ofNat (t + 1) ((3 * k + 2) / 3) = ⟨k, hk⟩ := by
    ext
    rw [Fin.val_ofNat, show (3 * k + 2) / 3 = k by omega, Nat.mod_eq_of_lt hk]
  rw [show 3 * k + 3 = 3 * k + 2 + 1 from rfl] at hm ⊢
  rw [Algorithm.Execution.state_succ]
  simp only [algorithm, Nat.add_sub_cancel]
  rw [hidx, hm]
  simp [h, hv]

/-- In the third round of a phase, a process keeps its value or adopts a valid one. -/
theorem value_round3 : (E.state (3 * k + 3) p).value = (E.state (3 * k + 2) p).value ∨
    valid (E.state (3 * k + 3) p).value := by
  rw [Algorithm.Execution.state_succ]
  simp only [algorithm, Nat.add_sub_cancel]
  split_ifs
  · omega
  · omega
  · exact Or.inl rfl
  split
  · split_ifs with hv
    exacts [Or.inr hv, Or.inl rfl]
  · exact Or.inl rfl

/-! ### Correctness -/

/-- All proposals in a phase are equal: any two quorums share a correct process, which sent the
same value to both proposers. -/
theorem proposal_eq (hF : #E.faulty ≤ t) (hn : 3 * t < Fintype.card P)
    (hpv : (E.state (3 * k + 1) p).proposal = some v)
    (hqw : (E.state (3 * k + 1) q).proposal = some w) : v = w := by
  rw [proposal_round1] at hpv hqw
  exact eq_of_quorums hF hn (fun r hr => by rw [received_round1 hr, received_round1 hr])
    (le_count_of_supported_eq_some hpv) (le_count_of_supported_eq_some hqw)

/-- A proposed value is the value of a correct process at the beginning of the phase. -/
theorem exists_value_of_proposal (hF : #E.faulty ≤ t) (hn : 3 * t < Fintype.card P)
    (h : (E.state (3 * k + 1) p).proposal = some v) :
    ∃ q ∉ E.faulty, (E.state (3 * k) q).value = v := by
  rw [proposal_round1] at h
  obtain ⟨q, hq, hqv⟩ := exists_notMem_of_lt_count hF
    ((by omega : t < Fintype.card P - t).trans_le (le_count_of_supported_eq_some h))
  rw [received_round1 hq] at hqv
  exact ⟨q, hq, Option.some.inj hqv⟩

/-- If the values of correct processes are valid at the beginning of a phase, then they are valid
after its second round. -/
theorem valid_value_round2 (hF : #E.faulty ≤ t) (hn : 3 * t < Fintype.card P)
    (h : ∀ q ∉ E.faulty, valid (E.state (3 * k) q).value) (hp : p ∉ E.faulty) :
    valid (E.state (3 * k + 2) p).value := by
  rw [value_round2]
  cases hs : supported (t + 1) (E.received (E.state (3 * k + 1)) (3 * k + 2) p) with
  | none => rw [Option.getD_none, value_round1]; exact h p hp
  | some w =>
    rw [Option.getD_some]
    obtain ⟨q, hq, hqw⟩ := exists_notMem_of_lt_count hF (le_count_of_supported_eq_some hs)
    rw [received_round2 hq] at hqw
    obtain ⟨q', hq', rfl⟩ := exists_value_of_proposal hF hn hqw
    exact h q' hq'

/-- **Validity invariant**: the values of correct processes at the beginning of each phase are
valid. -/
theorem valid_value (hF : #E.faulty ≤ t) (hn : 3 * t < Fintype.card P)
    (hvalid : ∀ p ∉ E.faulty, valid (E.proposal p)) (k : ℕ) (hp : p ∉ E.faulty) :
    valid (E.state (3 * k) p).value := by
  induction k generalizing p with
  | zero => simpa using hvalid p hp
  | succ k ih =>
    rw [Nat.mul_add_one]
    rcases value_round3 (E := E) (k := k) (p := p) with h | h
    · rw [h]
      exact valid_value_round2 hF hn (fun q hq => ih hq) hp
    · exact h

/-- **Persistence of unanimity**: if all correct processes have the value `v` at the beginning of
a phase, then all processes (in particular, all correct ones) have the value `v` at its end. -/
theorem value_of_forall (hF : #E.faulty ≤ t) (hn : 3 * t < Fintype.card P)
    (h : ∀ q ∉ E.faulty, (E.state (3 * k) q).value = v) (p : P) :
    (E.state (3 * k + 3) p).value = v := by
  have h1 : ∀ q, (E.state (3 * k + 1) q).proposal = some v := fun q => by
    rw [proposal_round1]
    exact supported_eq_some_of_lt
      (card_sub_le_count hF fun r hr => by rw [received_round1 hr, h r hr]) le_rfl (by omega)
  have hcount : Fintype.card P - t ≤ count (E.received (E.state (3 * k + 1)) (3 * k + 2) p) v :=
    card_sub_le_count hF fun r hr => by rw [received_round2 hr, h1 r]
  have hs : (E.state (3 * k + 2) p).strong := by
    rw [strong_round2, supported_eq_some_of_lt hcount le_rfl (by omega)]
    rfl
  rw [value_round3_of_strong hs, value_round2,
    supported_eq_some_of_lt hcount (by omega) (by omega)]
  rfl

/-- **A correct king unifies the values**: after a phase with a correct king, all processes (in
particular, all correct ones) have the value of the king after the second round of the phase. -/
theorem value_eq_king (hF : #E.faulty ≤ t) (hn : 3 * t < Fintype.card P)
    (hvalid : ∀ p ∉ E.faulty, valid (E.proposal p)) (hk : k < t + 1)
    (hking : king ⟨k, hk⟩ ∉ E.faulty) (p : P) :
    (E.state (3 * k + 3) p).value = (E.state (3 * k + 2) (king ⟨k, hk⟩)).value := by
  cases hs : (E.state (3 * k + 2) p).strong with
  | false =>
    exact value_round3_of_not_strong hs hk (received_round3 hking)
      (valid_value_round2 hF hn (fun q hq => valid_value hF hn hvalid k hq) hking)
  | true =>
    rw [value_round3_of_strong hs]
    rw [strong_round2, Option.isSome_iff_exists] at hs
    obtain ⟨w, hw⟩ := hs
    have hcount := le_count_of_supported_eq_some hw
    -- a correct process proposed `w`
    obtain ⟨q, hq, hqw⟩ := exists_notMem_of_lt_count hF
      ((by omega : t < Fintype.card P - t).trans_le hcount)
    rw [received_round2 hq] at hqw
    -- `p` and the king adopted `w`
    have hpw : (E.state (3 * k + 2) p).value = w := by
      rw [value_round2, supported_eq_some_of_lt hcount (by omega) (by omega)]
      rfl
    have hkw : (E.state (3 * k + 2) (king ⟨k, hk⟩)).value = w := by
      rw [value_round2, supported_eq_some (lt_count_of_quorum hF hn
        (fun r hr => by rw [received_round2 hr, received_round2 hr]) hcount) fun w' hw' => ?_]
      · rfl
      obtain ⟨q', hq', hq'w'⟩ := exists_notMem_of_lt_count hF hw'
      rw [received_round2 hq'] at hq'w'
      exact proposal_eq hF hn hq'w' hqw
    rw [hpw, hkw]

end Execution

/-! ### Main statements -/

variable {t : ℕ}

variable (P t) in
/-- Kings for the `t + 1` phases: the first `t + 1` processes in the enumeration
`Fintype.equivFin P`. -/
noncomputable def kings (h : t + 1 ≤ Fintype.card P) : Fin (t + 1) ↪ P :=
  (Fin.castLEEmb h).trans (Fintype.equivFin P).symm.toEmbedding

variable [DecidableEq P]

/-- **The phase-king algorithm solves Byzantine agreement.** If `3 * t < n`, then for every
injective assignment `king` of kings to the `t + 1` phases, the phase-king algorithm is a
`t`-resilient synchronous Byzantine agreement algorithm for the validity predicate `valid`, with
latency `3 * (t + 1)`. -/
theorem solvesByzantineAgreement {valid : Value → Prop} [DecidablePred valid]
    (hn : 3 * t < Fintype.card P) (king : Fin (t + 1) ↪ P) :
    (algorithm t king valid).SolvesByzantineAgreement t valid (3 * (t + 1)) := by
  intro E hF hvalid
  -- unanimity persists until the end
  have persist : ∀ k v, (∀ p ∉ E.faulty, (E.state (3 * k) p).value = v) →
      ∀ j, ∀ p ∉ E.faulty, (E.state (3 * (k + j)) p).value = v := by
    intro k v h j
    induction j with
    | zero => exact h
    | succ j ih =>
      intro p hp
      rw [← Nat.add_assoc, Nat.mul_add_one]
      exact value_of_forall hF hn ih p
  -- some king is correct
  obtain ⟨i, hi⟩ : ∃ i, king i ∉ E.faulty := by
    obtain ⟨q, hq, hqF⟩ := Quorum.exists_notMem_of_lt_card hF (S := univ.map king) (by simp)
    obtain ⟨i, -, rfl⟩ := mem_map.1 hq
    exact ⟨i, hqF⟩
  -- after its phase, all correct processes have the same value
  have hagree : ∀ p ∉ E.faulty,
      (E.state (3 * (t + 1)) p).value = (E.state (3 * i + 2) (king i)).value := by
    have := persist (i + 1) _
      (fun p hp => by rw [Nat.mul_add_one]; exact value_eq_king hF hn hvalid i.isLt hi p) (t - i)
    rwa [show i.val + 1 + (t - i) = t + 1 by omega] at this
  refine ⟨fun p _ => ⟨_, rfl⟩, fun p hp q hq v w hv hw => ?_, fun v hv p hp w hw => ?_,
    fun p hp v hv => ?_⟩
  · rw [← Option.some.inj hv, ← Option.some.inj hw, hagree p hp, hagree q hq]
  · have := persist 0 v (fun p hp => by simpa using hv p hp) (t + 1) p hp
    rw [Nat.zero_add] at this
    rw [← Option.some.inj hw, this]
  · rw [← Option.some.inj hv]
    exact valid_value hF hn hvalid (t + 1) hp

omit [DecidableEq Value] in
/-- **Synchronous Byzantine agreement is solvable if `3 * t < n`**, for every type of values and
every validity predicate, with latency `3 * (t + 1)`: by the phase-king algorithm. -/
theorem exists_solvesByzantineAgreement (hn : 3 * t < Fintype.card P) (valid : Value → Prop) :
    ∃ A : Algorithm P Value, A.SolvesByzantineAgreement t valid (3 * (t + 1)) := by
  classical
  exact ⟨algorithm t (kings P t (by omega)) valid, solvesByzantineAgreement hn _⟩

end Cslib.Distributed.Synchronous.PhaseKing
