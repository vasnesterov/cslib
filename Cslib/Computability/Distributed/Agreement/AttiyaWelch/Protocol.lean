/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.GradedConsensus
public import Cslib.Computability.Distributed.MessagePassing.Reasoning
public import Cslib.Computability.Distributed.Quorum

/-! # The Attiya–Welch graded consensus protocol AW′: protocol and invariants

We implement graded consensus (`Cslib.Distributed.GradedConsensus.spec`) for `3t < n` with the
protocol AW′: Algorithm 3 of
[Attiya and Welch, *Multi-valued connected consensus*][AttiyaWelch2023] (`R = 2`), adapted to the
graded consensus interface of [Civit et al., *Partial synchrony for free?*][CivitEtAl2024]
(requests `propose v` and `abandon`, indication `decide v g`). The paper uses AW as a black box
(appendix, "Existing primitives": AW tolerates `t < n / 3` Byzantine processes and "terminates in
9 asynchronous rounds") and gives neither its pseudocode nor a proof. This file defines AW′ and
proves its basic invariants; its safety is proved in
`Cslib.Computability.Distributed.Agreement.AttiyaWelch.Safety`, its latency in
`Cslib.Computability.Distributed.Agreement.AttiyaWelch.Latency`, its communication in
`Cslib.Computability.Distributed.Agreement.AttiyaWelch.Communication`, and the specification in
`Cslib.Computability.Distributed.Agreement.AttiyaWelch`.

**Protocol.** Messages are `INIT x` (a proposal) and `ECHO_k a` for the phases `k = 1, …, 5`,
where `a : Option Value` and `none` is AW's centre value `⊥`. A process records every `ECHO`
message it receives and the first `INIT` message of each sender (`State.rcv m` is the set of
recorded senders of `m`; all counts are of distinct senders).
* `propose v`: unless it has already proposed or abandoned, the process sends `INIT v` to all,
  together with the `ECHO`s of the guards that have already fired (see the participation gate
  below).
* `abandon`: the process stops sending and deciding (it keeps recording messages).
* After every receipt (unless abandoned) the guards are evaluated (`Cand`, `Dec`); the `ECHO`s of
  the guards that fire are sent if the process has proposed:
  - A1: `ECHO_1 a` once for every *amplified* `a` (`Amp`): more than `t` `INIT x` for `a = x`;
    for `a = ⊥`, evidence `Evid` that the proposals diverge (for every `x`, more than `t`
    processes sent an `INIT` with a value other than `x`), more than `t` `ECHO_1 ⊥`, or more
    than `t` `ECHO_1 b` and more than `t` `ECHO_1 c` for two different values `b ≠ c`;
  - A2: one `ECHO_2 a` for an *approved* `a` (`n - t` `ECHO_1 a`);
  - A3: one `ECHO_3 a` for `a` with `n - t` `ECHO_2 a`, or `ECHO_3 ⊥` if `AC` (two values or `⊥`
    approved);
  - A4: one `ECHO_4 ⊥` if `n - t` processes sent `ECHO_3` and `AC` (two values or `⊥` approved),
    or `ECHO_4 a` for `a` with `n - t` `ECHO_3 a`;
  - A5: one `ECHO_5 a` for `a` with `n - t` `ECHO_4 a`, or `ECHO_5 ⊥` if `n - t` processes sent
    `ECHO_4` and `AC`;
  - AD: once the process has received its own `INIT x`, it decides `(v, 1)` on `n - t`
    `ECHO_5 v` (D2); `(v, 0)` if `n - t` processes sent `ECHO_5`, `AC`, some `ECHO_5 v` and more
    than `t` `ECHO_4 v` were received (D1); or `(x, 0)` on `n - t` `ECHO_5 ⊥` (D0).

## Implementation notes

* Compared with AW's Algorithm 3, a process does not echo its input directly: inputs are sent in
  separate `INIT` messages, and divergence of the inputs (`Evid`) is detected by counting distinct
  senders, so that a single faulty process sending messages with many values cannot make correct
  processes echo `⊥` when all correct inputs are equal. Thresholds are inclusive and every guard
  is re-evaluated after every receipt, with once-only flags (`sent`, `dec`). AW's outputs
  `(v, 2)`, `(v, 1)` and `(⊥, 0)` become the decisions `(v, 1)`, `(v, 0)` and `(x, 0)`, where `x`
  is the process's proposal. A process may abandon, and need not propose.
* *Bounded communication.* Only the first `INIT` of each sender is recorded (as in the
  validation broadcast of [CivitEtAl2024], "only one INIT message is processed per process"), so
  at most `⌊n / (t + 1)⌋` values have more than `t` recorded `INIT`s (`eq_of_mem_rcv_init`).
  AW's Algorithm 3 also echoes every value that more than `t` processes echoed; then a correct
  process may have to echo every correct proposal (one correct echo of it and the echoes of the
  `t` faulty processes suffice), i.e. `Θ(n)` values and `Θ(n²)` messages. AW′
  instead echoes a value only on `INIT`s and echoes `⊥` when two different values were each
  echoed by more than `t` processes. This keeps the latency analysis intact: the only use of
  echo amplification there is the totality of `AC`, and `AC` at a correct process implies that
  every correct process receives more than `t` `ECHO_1 ⊥`, or more than `t` `ECHO_1` for two
  different values, hence echoes `⊥`, so that `⊥` is approved everywhere. Accordingly, the
  approved-branch of A3 is taken on `AC` rather than on two approved values. Safety is
  unaffected: `⊥` is never echoed by a correct process when all correct proposals are equal.
  So a process broadcasts at most `⌊n / (t + 1)⌋ + 6` messages
  (`Cslib.Computability.Distributed.Agreement.AttiyaWelch.Communication`).
* The branches of a guard are merged, and when several values (or decisions) are enabled, an
  arbitrary one is chosen (`Classical.choose`); the proofs never depend on the choice.
* Guard A1 is evaluated only for the value of the received message and for `⊥` (no other value
  can become amplified by the receipt); the other guards are evaluated after every receipt.
* Decisions are gated on the receipt of the process's own `INIT`, which arrives strictly after
  its proposal; D0 decides the value `x` of that `INIT`, i.e. the process's proposal. Hence a
  process decides only after proposing, and AW′ is request-quiet.
* *Participation gate.* A process sends messages only from its proposal on and never after it
  has abandoned (`sendsWhileActive`), so that it does not communicate in instances it does not
  take part in (this bounds the communication of a process that records the messages of many
  instances but proposes to few). Before proposing, a process records messages and its guards
  fire as usual (`State.sent`), but it sends nothing. When it proposes, it sends its `INIT`
  together with the `ECHO`s of all guards that have fired so far, i.e. the messages its recorded
  state requires (catch-up). The gate is harmless for the specification: the safety arguments
  only constrain the messages that correct processes do send (a sent `ECHO_k a` has its guard
  enabled, `cand_of_sendAll`, and at most one `ECHO_k` is sent for `k ≠ 1`,
  `sendAll_echo_unique`), and the latency assumes that every correct process has proposed, after
  which it sends whatever its guards require.

## Main definitions

* `AttiyaWelch.protocol P Value t`: the protocol AW′.
* `AttiyaWelch.SendAll ρ q m τ`: process `q` sent `m` to all processes at time `τ`.

## Main statements

* `AttiyaWelch.requestQuiet`: AW′ is request-quiet.
* `AttiyaWelch.sendsWhileActive`: a process sends messages only from its proposal on and never
  after it has abandoned.
* Invariants: at most one `INIT` recorded from each sender (`eq_of_mem_rcv_init`) and sent by
  each process (`sendAll_init_unique`); at most one `ECHO_k` per phase `k ≠ 1` (`card_sent_le`,
  `sendAll_echo_unique`);
  *quiescence*, i.e. enabled guards have fired (`sent_nonempty_of_cand`, `mem_sent_of_amp`,
  `dec_isSome_of_dec`), and once the process has proposed, their `ECHO`s were sent
  (`exists_sendAll_of_mem_sent`); *branch soundness*, i.e. a guard fires and a message or decision
  is sent only with its guard enabled (`cand_of_mem_sent`, `cand_of_sendAll`, `dec_of_ind`).
* In valid runs: messages recorded from correct processes were sent (`exists_sendAll_of_mem_rcv`),
  and messages sent by correct processes are recorded `δ` after GST (`mem_rcv_of_sendAll`).

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
* [H. Attiya, J. L. Welch, *Multi-Valued Connected Consensus: A New Perspective on Crusader
  Agreement and Adopt-Commit*, OPODIS 2023][AttiyaWelch2023]
-/

@[expose] public section

namespace Cslib.Distributed

/-! ### The protocol -/

namespace AttiyaWelch

open GradedConsensus Finset

/-- The five echo phases of AW′ (`ECHO_1`, …, `ECHO_5`). -/
inductive Phase where
  /-- `ECHO_1` (AW's `echo`). -/
  | one
  /-- `ECHO_2`. -/
  | two
  /-- `ECHO_3`. -/
  | three
  /-- `ECHO_4`. -/
  | four
  /-- `ECHO_5`. -/
  | five
deriving DecidableEq

/-- The list of all phases. -/
def Phase.all : List Phase := [.one, .two, .three, .four, .five]

@[simp]
theorem Phase.mem_all (k : Phase) : k ∈ Phase.all := by
  cases k <;> simp [Phase.all]

/-- The messages of AW′: `INIT x` carries a proposal, `ECHO_k a` an echoed value, where
`a = none` is AW's "centre" value `⊥`. -/
inductive Msg (Value : Type) where
  /-- `INIT x`. -/
  | init (x : Value)
  /-- `ECHO_k a`. -/
  | echo (k : Phase) (a : Option Value)
deriving DecidableEq

/-- The value carried by a message. -/
def Msg.val {Value : Type} : Msg Value → Option Value
  | .init x => some x
  | .echo _ a => a

/-- The local state of an AW′ process. -/
structure State (P Value : Type) where
  /-- The process has accepted a proposal (and sent its `INIT`). -/
  proposed : Bool
  /-- The process has abandoned. -/
  ab : Bool
  /-- `rcv m`: the processes from which message `m` was received and recorded (every `ECHO`, and
  the first `INIT` of each sender). -/
  rcv : Msg Value → Finset P
  /-- `sent k`: the values `a` with which the guard of phase `k` has fired. The process sends
  `ECHO_k a` when the guard fires, or when it proposes if the guard fired earlier. -/
  sent : Phase → Finset (Option Value)
  /-- The decision, once taken. -/
  dec : Option (Value × Bool)

variable {P Value : Type}

/-! #### Guards

The enabling conditions of AW′'s guards depend only on the received messages
`R : Msg Value → Finset P`, and they are monotone in `R`. -/

section Guards

variable [Fintype P]

variable (t : ℕ) (R : Msg Value → Finset P)

/-- `ECHO_k a` was received from a quorum (`n - t` processes). For `k = one` this means that `a`
is *approved*. -/
def Quo (k : Phase) (a : Option Value) : Prop := Fintype.card P - t ≤ #(R (.echo k a))

/-- Evidence for `⊥`: for every value `x`, more than `t` processes sent an `INIT` with a value
other than `x` (the ∀-form of the paper's `|total_init| - |init(most_frequent)| ≥ t + 1`). -/
def Evid : Prop := ∀ x : Value, ∃ S : Finset P, t < #S ∧ ∀ q ∈ S, ∃ y, y ≠ x ∧ q ∈ R (.init y)

/-- Amplification condition `Amp a` of guard A1: for `a = x`, more than `t` processes sent
`INIT x`; for `a = ⊥`, evidence `Evid` that the proposals diverge, more than `t` processes sent
`ECHO_1 ⊥`, or two different values were each sent in `ECHO_1` by more than `t` processes. -/
def Amp : Option Value → Prop
  | some x => t < #(R (.init x))
  | none => Evid t R ∨ t < #(R (.echo .one none)) ∨
      ∃ a b, a ≠ b ∧ t < #(R (.echo .one a)) ∧ t < #(R (.echo .one b))

/-- Two different values are approved (`|approved| > 1`). -/
def Appr2 : Prop := ∃ a b, a ≠ b ∧ Quo t R .one a ∧ Quo t R .one b

/-- `AC`: two values are approved, or `⊥` is. -/
def AC : Prop := Appr2 t R ∨ Quo t R .one none

/-- `Tot k`: some `ECHO_k` message was received from each of `n - t` processes. -/
def Tot (k : Phase) : Prop :=
  ∃ S : Finset P, Fintype.card P - t ≤ #S ∧ ∀ q ∈ S, ∃ a, q ∈ R (.echo k a)

/-- `Cand k a`: the guard of phase `k` is enabled with value `a`, i.e. `ECHO_k a` may be sent
(guards A1–A5, with the branches of each guard merged). -/
def Cand : Phase → Option Value → Prop
  | .one, a => Amp t R a
  | .two, a => Quo t R .one a
  | .three, a => Quo t R .two a ∨ (a = none ∧ AC t R)
  | .four, a => (a = none ∧ Tot t R .three ∧ AC t R) ∨ Quo t R .three a
  | .five, a => Quo t R .four a ∨ (a = none ∧ Tot t R .four ∧ AC t R)

/-- `SelfInit`: process `p` has received its own `INIT`. -/
def SelfInit (p : P) : Prop := ∃ x, p ∈ R (.init x)

/-- The decision branches: `(v, 1)` via D2, `(v, 0)` via D1 or D0. -/
def DecBranch (p : P) (v : Value) : Bool → Prop
  | true => Quo t R .five (some v)
  | false => (Tot t R .five ∧ AC t R ∧ (R (.echo .five (some v))).Nonempty ∧
      t < #(R (.echo .four (some v)))) ∨ (Quo t R .five none ∧ p ∈ R (.init v))

/-- `Dec p v g`: the decision guard AD of process `p` is enabled with decision `(v, g)`. -/
def Dec (p : P) (v : Value) (g : Bool) : Prop := SelfInit R p ∧ DecBranch t R p v g

end Guards

/-! #### Monotonicity of the guards -/

section Monotone

variable [Fintype P] {R R' : Msg Value → Finset P} {k : Phase} {a : Option Value} {p : P}
  {v : Value} {g : Bool} {t : ℕ}

theorem Quo.mono (h : R ≤ R') : Quo t R k a → Quo t R' k a :=
  fun hq => hq.trans (card_le_card (h _))

omit [Fintype P] in
theorem Evid.mono (h : R ≤ R') : Evid t R → Evid t R' := by
  intro he x
  obtain ⟨S, hS, hS'⟩ := he x
  exact ⟨S, hS, fun q hq => (hS' q hq).imp fun y hy => ⟨hy.1, h _ hy.2⟩⟩

omit [Fintype P] in
theorem Amp.mono (h : R ≤ R') : Amp t R a → Amp t R' a := by
  have hc : ∀ {m}, t < #(R m) → t < #(R' m) := fun hc => hc.trans_le (card_le_card (h _))
  cases a with
  | none =>
    exact Or.imp (Evid.mono h) (Or.imp hc fun ⟨a, b, hab, ha, hb⟩ => ⟨a, b, hab, hc ha, hc hb⟩)
  | some x => exact hc

theorem Appr2.mono (h : R ≤ R') : Appr2 t R → Appr2 t R' :=
  fun ⟨a, b, hab, ha, hb⟩ => ⟨a, b, hab, ha.mono h, hb.mono h⟩

theorem AC.mono (h : R ≤ R') : AC t R → AC t R' :=
  Or.imp (Appr2.mono h) (Quo.mono h)

theorem Tot.mono (h : R ≤ R') : Tot t R k → Tot t R' k :=
  fun ⟨S, hS, hS'⟩ => ⟨S, hS, fun q hq => (hS' q hq).imp fun _ ha => h _ ha⟩

theorem Cand.mono (h : R ≤ R') : Cand t R k a → Cand t R' k a := by
  cases k with
  | one => exact Amp.mono h
  | two => exact Quo.mono h
  | three => exact Or.imp (Quo.mono h) (And.imp_right (AC.mono h))
  | four =>
    exact Or.imp (And.imp_right (And.imp (Tot.mono h) (AC.mono h))) (Quo.mono h)
  | five => exact Or.imp (Quo.mono h) (And.imp_right (And.imp (Tot.mono h) (AC.mono h)))

omit [Fintype P] in
theorem SelfInit.mono (h : R ≤ R') : SelfInit R p → SelfInit R' p :=
  fun ⟨x, hx⟩ => ⟨x, h _ hx⟩

theorem Dec.mono (h : R ≤ R') : Dec t R p v g → Dec t R' p v g := by
  rintro ⟨hs, hd⟩
  refine ⟨hs.mono h, ?_⟩
  cases g with
  | true => exact Quo.mono h hd
  | false =>
    simp only [DecBranch] at hd ⊢
    rcases hd with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂⟩
    · exact .inl ⟨h₁.mono h, h₂.mono h, h₃.mono (h _), h₄.trans_le (card_le_card (h _))⟩
    · exact .inr ⟨h₁.mono h, h _ h₂⟩

/-- With more than `t` processes, no guard is enabled before any message is received. -/
theorem not_quo_empty (ht : t < Fintype.card P) :
    ¬ Quo t (fun _ : Msg Value => (∅ : Finset P)) k a := by
  simp [Quo]; omega

end Monotone

variable [DecidableEq P] [DecidableEq Value]

open scoped Classical in
/-- Record the receipt of message `m` from `q`: every `ECHO` message, and the first `INIT` message
of each sender (an `INIT` from a sender whose `INIT` has already been recorded is ignored). -/
noncomputable def record (q : P) (m : Msg Value) (R : Msg Value → Finset P) :
    Msg Value → Finset P :=
  if (∃ x, m = .init x) ∧ ∃ y, q ∈ R (.init y) then R else Function.update R m (insert q (R m))

section Record

variable {q r : P} {m m' : Msg Value} {R : Msg Value → Finset P} {k : Phase} {a : Option Value}
  {x : Value}

theorem record_echo :
    record q (.echo k a) R = Function.update R (.echo k a) (insert q (R (.echo k a))) := by
  simp [record]

theorem mem_record_echo :
    r ∈ record q (.echo k a) R m' ↔ r ∈ R m' ∨ (r = q ∧ m' = .echo k a) := by
  rw [record_echo]
  by_cases h : m' = .echo k a
  · subst h; simp [or_comm]
  · simp [h]

/-- A recorded sender was recorded before, or is the sender of the message being recorded. -/
theorem mem_record_imp (h : r ∈ record q m R m') : r ∈ R m' ∨ (r = q ∧ m' = m) := by
  unfold record at h
  split_ifs at h
  · exact .inl h
  · by_cases hm : m' = m
    · subst hm; simpa [or_comm] using h
    · simpa [hm] using h

/-- After an `INIT` from `q` is recorded, some `INIT` from `q` is recorded. -/
theorem exists_mem_record_init : ∃ y, q ∈ record q (.init x) R (.init y) := by
  unfold record
  split_ifs with h
  · exact h.2
  · exact ⟨x, by simp⟩

theorem le_record (q : P) (m : Msg Value) (R : Msg Value → Finset P) : R ≤ record q m R := by
  intro m' r h
  unfold record
  split_ifs
  · exact h
  · by_cases hm : m' = m
    · subst hm; simp [h]
    · simpa [hm] using h

theorem record_of_ne (h : m' ≠ m) : record q m R m' = R m' := by
  unfold record
  split_ifs
  · rfl
  · exact Function.update_of_ne h _ _

/-- Recording preserves the invariant that at most one `INIT` is recorded from each sender. -/
theorem record_init_unique (hR : ∀ r x y, r ∈ R (.init x) → r ∈ R (.init y) → x = y)
    {r : P} {x y : Value} (hx : r ∈ record q m R (.init x)) (hy : r ∈ record q m R (.init y)) :
    x = y := by
  unfold record at hx hy
  split_ifs at hx hy with h
  · exact hR r x y hx hy
  · simp only [not_and, not_exists] at h
    by_cases hm : ∃ z, m = .init z
    · obtain ⟨z, rfl⟩ := hm
      have hfresh := h ⟨z, rfl⟩
      have key : ∀ {w}, r ∈ Function.update R (.init z) (insert q (R (.init z))) (.init w) →
          (r = q ∧ w = z) ∨ r ∈ R (.init w) := by
        intro w hw
        by_cases hwz : w = z
        · subst hwz
          rcases Finset.mem_insert.1 (by simpa using hw) with rfl | hw'
          · exact .inl ⟨rfl, rfl⟩
          · exact .inr hw'
        · exact .inr (by simpa [hwz] using hw)
      rcases key hx with ⟨rfl, rfl⟩ | hx' <;> rcases key hy with ⟨hr, rfl⟩ | hy'
      · rfl
      · exact absurd hy' (hfresh _)
      · subst hr; exact absurd hx' (hfresh _)
      · exact hR r x y hx' hy'
    · push Not at hm
      rw [Function.update_of_ne (hm x).symm] at hx
      rw [Function.update_of_ne (hm y).symm] at hy
      exact hR r x y hx hy

end Record

variable [Fintype P]

section Step

variable (t : ℕ)

open scoped Classical in
/-- The values sent in phase `k` by the guard pass that follows the receipt of message `m`,
given the received messages `R` (including `m`) and the values sent so far. Guard A1 is
evaluated for the value of `m` and for `⊥` only (no other value can become amplified by `m`);
the guards of phases `2`–`5` are evaluated globally and fire once, with an arbitrary enabled
value. -/
noncomputable def newVals (R : Msg Value → Finset P) (sent : Phase → Finset (Option Value))
    (m : Msg Value) (k : Phase) : Finset (Option Value) :=
  if k = .one then ({m.val, none} : Finset (Option Value)).filter fun a =>
      a ∉ sent .one ∧ Cand t R .one a
  else if h : sent k = ∅ ∧ ∃ a, Cand t R k a then {h.2.choose} else ∅

open scoped Classical in
/-- The decision taken by the guard pass of process `p` (guard AD), if any. -/
noncomputable def newDec (p : P) (R : Msg Value → Finset P) (dec : Option (Value × Bool)) :
    Option (Value × Bool) :=
  if h : dec = none ∧ ∃ d : Value × Bool, Dec t R p d.1 d.2 then some h.2.choose else none

/-- The `ECHO` messages sent by a guard pass. -/
noncomputable def echoOuts (nv : Phase → Finset (Option Value)) :
    List (Output P (Msg Value) Empty (Ind Value)) :=
  Phase.all.flatMap fun k => (nv k).toList.flatMap fun a => Output.broadcast (.echo k a)

/-- The step function of AW′ for process `p`.
* `propose v`: if the process has neither proposed nor abandoned, accept the proposal, send
  `INIT v` to all, and send the `ECHO`s of the guards that have already fired (catch-up). The
  decision guard is not evaluated (request-quietness).
* `abandon`: stop sending and deciding.
* receipt of `m` from `q`: record it; unless abandoned, run the guard pass, and send its `ECHO`s
  if the process has proposed. -/
noncomputable def step (p : P) :
    Input P (Msg Value) Empty (Req Value) → State P Value →
      State P Value × List (Output P (Msg Value) Empty (Ind Value))
  | .req (.propose v), s =>
    if s.proposed || s.ab then (s, [])
    else ({ s with proposed := true }, Output.broadcast (.init v) ++ echoOuts s.sent)
  | .req .abandon, s => ({ s with ab := true }, [])
  | .recv q m, s =>
    if s.ab then ({ s with rcv := record q m s.rcv }, []) else
      ({ s with
          rcv := record q m s.rcv
          sent := fun k => s.sent k ∪ newVals t (record q m s.rcv) s.sent m k
          dec := s.dec.or (newDec t p (record q m s.rcv) s.dec) },
        (if s.proposed then echoOuts (newVals t (record q m s.rcv) s.sent m) else []) ++
          (newDec t p (record q m s.rcv) s.dec).toList.map fun d => .ind (.decide d.1 d.2))
  | .timeout k, _ => k.elim

end Step

variable (P Value) in
/-- **AW′**, the Attiya–Welch graded consensus protocol (Attiya–Welch, *Multi-valued connected
consensus*, Algorithm 3 with `R = 2`, adapted to graded consensus), for at most `t` faulty
processes. -/
@[reducible] noncomputable def protocol (t : ℕ) : Protocol P (interface Value) where
  Msg := Msg Value
  Timer := Empty
  State := State P Value
  init _ := { proposed := false, ab := false, rcv := fun _ => ∅, sent := fun _ => ∅, dec := none }
  step p _ := step t p

/-! ### Local lemmas: guards and steps -/

section Local

variable {t : ℕ} {R R' : Msg Value → Finset P} {k : Phase} {a : Option Value} {p : P}
  {v : Value} {g : Bool}

/-! #### The guard pass -/

variable {sent : Phase → Finset (Option Value)} {m : Msg Value}

omit [DecidableEq P] in
theorem mem_newVals_one :
    a ∈ newVals t R sent m .one ↔ (a = m.val ∨ a = none) ∧ a ∉ sent .one ∧ Cand t R .one a := by
  simp [newVals]

omit [DecidableEq P] in
theorem mem_newVals_of_ne (hk : k ≠ .one) (h : a ∈ newVals t R sent m k) :
    sent k = ∅ ∧ Cand t R k a := by
  simp only [newVals, hk, ite_false] at h
  split_ifs at h with hs
  · rw [mem_singleton] at h
    subst h
    exact ⟨hs.1, hs.2.choose_spec⟩
  · simp at h

omit [DecidableEq P] in
/-- A value sent by the guard pass satisfies the guard and was not sent before. -/
theorem cand_of_mem_newVals (h : a ∈ newVals t R sent m k) : Cand t R k a ∧ a ∉ sent k := by
  by_cases hk : k = .one
  · subst hk
    exact ⟨(mem_newVals_one.1 h).2.2, (mem_newVals_one.1 h).2.1⟩
  · obtain ⟨hs, hc⟩ := mem_newVals_of_ne hk h
    exact ⟨hc, by simp [hs]⟩

omit [DecidableEq P] in
theorem card_newVals_le (hk : k ≠ .one) : #(newVals t R sent m k) ≤ 1 := by
  simp only [newVals, hk, ite_false]
  split_ifs <;> simp

omit [DecidableEq P] in
theorem newVals_nonempty (hk : k ≠ .one) (hs : sent k = ∅) (h : Cand t R k a) :
    (newVals t R sent m k).Nonempty := by
  simp only [newVals, hk, ite_false]
  split_ifs with h'
  · simp
  · exact absurd ⟨hs, a, h⟩ h'

variable {dec : Option (Value × Bool)} {d : Value × Bool}

omit [DecidableEq P] [DecidableEq Value] in
theorem newDec_eq_some (h : newDec t p R dec = some d) : dec = none ∧ Dec t R p d.1 d.2 := by
  unfold newDec at h
  split_ifs at h with hd
  · cases h
    exact ⟨hd.1, hd.2.choose_spec⟩

omit [DecidableEq P] [DecidableEq Value] in
theorem newDec_isSome (hdec : dec = none) (h : Dec t R p v g) : (newDec t p R dec).isSome := by
  unfold newDec
  split_ifs with h'
  · rfl
  · exact absurd ⟨hdec, (v, g), h⟩ h'

/-! #### Steps -/

variable {x : Input P (Msg Value) Empty (Req Value)} {s : State P Value}

omit [DecidableEq P] [DecidableEq Value] in
theorem send_mem_echoOuts {nv : Phase → Finset (Option Value)} {r : P} {m' : Msg Value} :
    .send r m' ∈ (echoOuts nv : List (Output P (Msg Value) Empty (Ind Value))) ↔
      ∃ k a, a ∈ nv k ∧ m' = .echo k a := by
  simp [echoOuts, @eq_comm _ m']

omit [DecidableEq P] [DecidableEq Value] in
theorem ind_notMem_echoOuts {nv : Phase → Finset (Option Value)} {i : Ind Value} :
    .ind i ∉ (echoOuts nv : List (Output P (Msg Value) Empty (Ind Value))) := by
  simp [echoOuts]

omit [DecidableEq P] [DecidableEq Value] in
theorem filterMap_ind?_echoOuts {nv : Phase → Finset (Option Value)} :
    (echoOuts nv : List (Output P (Msg Value) Empty (Ind Value))).filterMap Output.ind? = [] := by
  simp [echoOuts, List.filterMap_flatMap, Output.broadcast, Output.ind?, Function.comp_def]

theorem rcv_step_recv {q : P} : (step t p (.recv q m) s).1.rcv = record q m s.rcv := by
  by_cases hab : s.ab <;> simp [step, hab]

theorem rcv_step_of_forall_ne (hx : ∀ q m, x ≠ .recv q m) : (step t p x s).1.rcv = s.rcv := by
  cases x with
  | req r' => cases r' <;> simp [step]; split_ifs <;> simp
  | recv q m' => exact absurd rfl (hx q m')
  | timeout k => exact k.elim

theorem rcv_le_step : s.rcv ≤ (step t p x s).1.rcv := by
  cases x with
  | recv q m' => rw [rcv_step_recv]; exact le_record q m' s.rcv
  | req r' => rw [rcv_step_of_forall_ne (by simp)]
  | timeout k => exact k.elim

/-- A step records a new sender of `m` only upon receiving `m` from it. -/
theorem mem_rcv_step_imp {r : P} (h : r ∈ (step t p x s).1.rcv m) :
    r ∈ s.rcv m ∨ x = .recv r m := by
  cases x with
  | recv q m' =>
    rw [rcv_step_recv] at h
    rcases mem_record_imp h with h | ⟨rfl, rfl⟩
    · exact .inl h
    · exact .inr rfl
  | req r' => rw [rcv_step_of_forall_ne (by simp)] at h; exact .inl h
  | timeout k => exact k.elim

/-- `ECHO` messages are always recorded. -/
theorem mem_rcv_step_echo {r : P} {k : Phase} :
    r ∈ (step t p x s).1.rcv (.echo k a) ↔ r ∈ s.rcv (.echo k a) ∨ x = .recv r (.echo k a) := by
  refine ⟨mem_rcv_step_imp, ?_⟩
  rintro (h | rfl)
  · exact rcv_le_step _ h
  · rw [rcv_step_recv, mem_record_echo]
    exact .inr ⟨rfl, rfl⟩

/-- After the receipt of an `INIT` from `r`, some `INIT` from `r` is recorded. -/
theorem exists_mem_rcv_step_init {r : P} {y : Value} :
    ∃ z, r ∈ (step t p (.recv r (.init y)) s).1.rcv (.init z) := by
  rw [rcv_step_recv]
  exact exists_mem_record_init

theorem ab_step : (step t p x s).1.ab = true ↔ s.ab = true ∨ x = .req .abandon := by
  cases x with
  | req r' => cases r' <;> simp [step]; split_ifs <;> simp
  | recv q m' => by_cases hab : s.ab <;> simp [step, hab]
  | timeout k => exact k.elim

theorem proposed_step :
    (step t p x s).1.proposed = true ↔
      s.proposed = true ∨ ∃ v, x = .req (.propose v) ∧ s.ab = false := by
  cases x with
  | req r' =>
    cases r' with
    | propose v => cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab]
    | abandon => simp [step]
  | recv q m' => by_cases hab : s.ab <;> simp [step, hab]
  | timeout k => exact k.elim

theorem mem_sent_step :
    a ∈ (step t p x s).1.sent k ↔
      a ∈ s.sent k ∨ ∃ q m, x = .recv q m ∧ s.ab = false ∧
        a ∈ newVals t (record q m s.rcv) s.sent m k := by
  cases x with
  | req r' => cases r' <;> simp [step]; split_ifs <;> simp
  | recv q m' => by_cases hab : s.ab <;> simp [step, hab]
  | timeout k => exact k.elim

theorem sent_le_step : s.sent ≤ (step t p x s).1.sent :=
  fun _ _ h => mem_sent_step.2 (.inl h)

theorem dec_isSome_step :
    (step t p x s).1.dec.isSome ↔
      s.dec.isSome ∨ ∃ q m, x = .recv q m ∧ s.ab = false ∧
        (newDec t p (record q m s.rcv) s.dec).isSome := by
  cases x with
  | req r' => cases r' <;> simp [step]; split_ifs <;> simp
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · cases h : s.dec <;> simp [step, hab, h]
  | timeout k => exact k.elim

/-- The sends of a step: `INIT v` and the catch-up `ECHO`s of the guards that have already fired
when the proposal `v` is accepted, and the `ECHO`s of the guard pass after a receipt, once the
process has proposed. -/
theorem send_mem_step {r : P} {m' : Msg Value} :
    .send r m' ∈ (step t p x s).2 ↔
      (∃ v, x = .req (.propose v) ∧ s.proposed = false ∧ s.ab = false ∧
        (m' = .init v ∨ ∃ k a, a ∈ s.sent k ∧ m' = .echo k a)) ∨
        ∃ q m k a, x = .recv q m ∧ s.ab = false ∧ s.proposed = true ∧
          a ∈ newVals t (record q m s.rcv) s.sent m k ∧ m' = .echo k a := by
  cases x with
  | req r' =>
    cases r' with
    | propose v =>
      cases hp : s.proposed <;> cases hab : s.ab <;>
        simp [step, hp, hab, @eq_comm _ m', send_mem_echoOuts]
    | abandon => simp [step]
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · cases hp : s.proposed <;> simp [step, hab, hp, send_mem_echoOuts]
  | timeout k => exact k.elim

/-- Once a process has proposed and the guard of phase `k` has fired with `a`, this stays so. -/
theorem proposed_mem_sent_step (h : s.proposed = true ∧ a ∈ s.sent k) :
    (step t p x s).1.proposed = true ∧ a ∈ (step t p x s).1.sent k :=
  ⟨proposed_step.2 (.inl h.1), sent_le_step k h.2⟩

/-- After a step that sends `ECHO_k a`, the process has proposed and the guard of phase `k` has
fired with `a`. -/
theorem mem_sent_of_send_mem_step {r : P} (h : .send r (.echo k a) ∈ (step t p x s).2) :
    (step t p x s).1.proposed = true ∧ a ∈ (step t p x s).1.sent k := by
  rcases send_mem_step.1 h with ⟨v, rfl, -, hab, h | ⟨k', a', ha, h⟩⟩ |
    ⟨q, m, k', a', rfl, hab, hp, ha, h⟩
  · cases h
  · obtain ⟨rfl, rfl⟩ := Msg.echo.inj h
    exact ⟨proposed_step.2 (.inr ⟨v, rfl, hab⟩), sent_le_step k ha⟩
  · obtain ⟨rfl, rfl⟩ := Msg.echo.inj h
    exact ⟨proposed_step.2 (.inl hp), mem_sent_step.2 (.inr ⟨q, m, rfl, hab, ha⟩)⟩

/-- A step that sends `INIT v` accepts the proposal `v`, in a state in which the process has
neither proposed nor abandoned. -/
theorem propose_of_send_init_mem_step {r : P} (h : .send r (.init v) ∈ (step t p x s).2) :
    x = .req (.propose v) ∧ s.proposed = false ∧ s.ab = false := by
  rcases send_mem_step.1 h with ⟨w, rfl, hp, hab, hw | ⟨_, _, -, hw⟩⟩ |
    ⟨_, _, _, _, -, -, -, -, hw⟩
  · cases hw
    exact ⟨rfl, hp, hab⟩
  · cases hw
  · cases hw

/-- A step that sends `ECHO_k a`, `k ≠ 1`, is handled in a state in which the process has not
proposed or the guard of phase `k` has not fired. -/
theorem proposed_eq_false_or_sent_eq_empty {r : P} (hk : k ≠ .one)
    (h : .send r (.echo k a) ∈ (step t p x s).2) : s.proposed = false ∨ s.sent k = ∅ := by
  rcases send_mem_step.1 h with ⟨v, -, hp, -⟩ | ⟨q, m, k', a', -, -, -, ha, h⟩
  · exact .inl hp
  · obtain ⟨rfl, rfl⟩ := Msg.echo.inj h
    exact .inr (mem_newVals_of_ne hk ha).1

theorem ind_mem_step :
    .ind (.decide v g) ∈ (step t p x s).2 ↔
      ∃ q m, x = .recv q m ∧ s.ab = false ∧
        newDec t p (record q m s.rcv) s.dec = some (v, g) := by
  cases x with
  | req r' =>
    cases r' with
    | propose v =>
      cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab, ind_notMem_echoOuts]
    | abandon => simp [step]
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · cases hp : s.proposed <;> simp [step, hab, hp, ind_notMem_echoOuts, eq_comm]
  | timeout k => exact k.elim

/-- A step emits at most one indication. -/
theorem length_filterMap_ind?_step_le :
    ((step t p x s).2.filterMap Output.ind?).length ≤ 1 := by
  cases x with
  | req r' =>
    cases r' with
    | propose v =>
      cases hp : s.proposed <;> cases hab : s.ab <;>
        simp [step, hp, hab, filterMap_ind?_echoOuts, Output.broadcast, Output.ind?,
          Function.comp_def]
    | abandon => simp [step]
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · cases h : newDec t p (record q m' s.rcv) s.dec <;> cases hp : s.proposed <;>
        simp [step, hab, h, hp, filterMap_ind?_echoOuts, Output.ind?]
  | timeout k => exact k.elim

end Local

/-- AW′ is request-quiet: `propose` and `abandon` emit no indication (`propose` does not evaluate
the decision guard; decisions are gated on the receipt of the process's own `INIT`, which arrives
strictly later). -/
theorem requestQuiet (t : ℕ) : (protocol P Value t).RequestQuiet := by
  intro p now r s i
  cases r with
  | propose v =>
    cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab, ind_notMem_echoOuts]
  | abandon => simp [step]

/-! ### Invariants of local states -/

section Invariants

variable {t : ℕ} {p : P} {s : (protocol P Value t).State} {k : Phase} {a : Option Value}

@[simp]
theorem init_eq : (protocol P Value t).init p =
    { proposed := false, ab := false, rcv := fun _ => ∅, sent := fun _ => ∅, dec := none } :=
  rfl

theorem protocol_step {now : ℕ} {x : (protocol P Value t).In} :
    (protocol P Value t).step p now x s = step t p x s := rfl

theorem ab_eq_false_of_step {x : Input P (Msg Value) Empty (Req Value)}
    (h : (step t p x s).1.ab = false) : s.ab = false := by
  cases hs : s.ab
  · rfl
  · rw [(ab_step (t := t) (p := p) (x := x)).2 (.inl hs)] at h
    cases h

/-- *Single messages* (state form): at most one value is sent in each phase `k ≠ 1`. -/
theorem card_sent_le (hs : (protocol P Value t).Reachable p s) (hk : k ≠ .one) :
    #(s.sent k) ≤ 1 := by
  induction hs with
  | init => simp
  | @step s now x hs ih =>
    rw [protocol_step, Finset.card_le_one]
    intro a ha b hb
    rcases mem_sent_step.1 ha with ha | ⟨q, m, hx, -, ha⟩ <;>
      rcases mem_sent_step.1 hb with hb | ⟨q', m', hx', -, hb⟩
    · exact Finset.card_le_one.1 ih a ha b hb
    · exact absurd ha (by simp [(mem_newVals_of_ne hk hb).1])
    · exact absurd hb (by simp [(mem_newVals_of_ne hk ha).1])
    · obtain ⟨rfl, rfl⟩ := Input.recv.inj (hx.symm.trans hx')
      exact Finset.card_le_one.1 (card_newVals_le hk) a ha b hb

/-- *First `INIT` wins*: at most one `INIT` is recorded from each sender. -/
theorem eq_of_mem_rcv_init (hs : (protocol P Value t).Reachable p s) {q : P} {x y : Value}
    (hx : q ∈ s.rcv (.init x)) (hy : q ∈ s.rcv (.init y)) : x = y := by
  induction hs generalizing q x y with
  | init => simp at hx
  | @step s now x' hs ih =>
    rw [protocol_step] at hx hy
    cases x' with
    | recv r m =>
      rw [rcv_step_recv] at hx hy
      exact record_init_unique (fun _ _ _ => ih) hx hy
    | req r =>
      rw [rcv_step_of_forall_ne (by simp)] at hx hy
      exact ih hx hy
    | timeout k => exact k.elim

/-- *Branch soundness* (state form): a guard fires only when it is enabled; by monotonicity, it
stays enabled. -/
theorem cand_of_mem_sent (hs : (protocol P Value t).Reachable p s) (h : a ∈ s.sent k) :
    Cand t s.rcv k a := by
  induction hs with
  | init => simp at h
  | @step s now x hs ih =>
    rw [protocol_step] at h ⊢
    rcases mem_sent_step.1 h with h | ⟨q, m, rfl, -, h⟩
    · exact (ih h).mono rcv_le_step
    · rw [rcv_step_recv]
      exact (cand_of_mem_newVals h).1

omit [DecidableEq P] [DecidableEq Value] in
/-- With more than `t` processes, the guards of phases `2`–`5` are disabled initially. -/
theorem not_cand_empty (ht : t < Fintype.card P) (hk : k ≠ .one) :
    ¬ Cand t (fun _ : Msg Value => (∅ : Finset P)) k a := by
  have hq := fun k a => not_quo_empty (Value := Value) (k := k) (a := a) ht
  have htot : ∀ k, ¬ Tot t (fun _ : Msg Value => (∅ : Finset P)) k := by
    rintro k ⟨S, hS, hS'⟩
    obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun q hq => by simpa using hS' q hq
    simp at hS; omega
  cases k with
  | one => exact absurd rfl hk
  | two => exact hq .one a
  | three => rintro (h | ⟨-, ⟨_, _, -, h, -⟩ | h⟩) <;> exact hq _ _ h
  | four => rintro (⟨-, h, -⟩ | h); exacts [htot _ h, hq _ _ h]
  | five => rintro (h | ⟨-, h, -⟩); exacts [hq _ _ h, htot _ h]

/-- *Quiescence* for phases `2`–`5`: in a process that has not abandoned, an enabled
guard has fired. -/
theorem sent_nonempty_of_cand (ht : t < Fintype.card P) (hs : (protocol P Value t).Reachable p s)
    (hk : k ≠ .one) (hab : s.ab = false) (h : Cand t s.rcv k a) : (s.sent k).Nonempty := by
  induction hs with
  | init => exact absurd h (not_cand_empty ht hk)
  | @step s now x hs ih =>
    rw [protocol_step] at hab h ⊢
    cases x with
    | recv q m =>
      have hab' := ab_eq_false_of_step hab
      rw [rcv_step_recv] at h
      by_cases hsk : (s.sent k).Nonempty
      · exact hsk.mono (sent_le_step k)
      · obtain ⟨b, hb⟩ := newVals_nonempty (sent := s.sent) (m := m) hk
          (Finset.not_nonempty_iff_eq_empty.1 hsk) h
        exact ⟨b, mem_sent_step.2 (.inr ⟨q, m, rfl, hab', hb⟩)⟩
    | req r =>
      rw [rcv_step_of_forall_ne (by simp)] at h
      exact (ih (ab_eq_false_of_step hab) h).mono (sent_le_step k)
    | timeout k => exact k.elim

/-- *Quiescence* for guard A1: in a process that has not abandoned, every amplified
value has been echoed. -/
theorem mem_sent_of_amp [Nonempty Value] (hs : (protocol P Value t).Reachable p s)
    (hab : s.ab = false) (h : Amp t s.rcv a) : a ∈ s.sent .one := by
  induction hs generalizing a with
  | init =>
    exfalso
    cases a with
    | some x => simp [Amp] at h
    | none =>
      rcases h with h | h | ⟨_, _, -, h, -⟩
      · obtain ⟨S, hS, hS'⟩ := h (Classical.arbitrary Value)
        obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun q hq => by
          simpa using hS' q hq
        simp at hS
      all_goals simp at h
  | @step s now x hs ih =>
    rw [protocol_step] at hab h ⊢
    cases x with
    | recv q m =>
      have hab' := ab_eq_false_of_step hab
      rw [rcv_step_recv] at h
      by_cases ha : a = m.val ∨ a = none
      · by_cases ha' : a ∈ s.sent .one
        · exact sent_le_step _ ha'
        · exact mem_sent_step.2 (.inr ⟨q, m, rfl, hab', mem_newVals_one.2 ⟨ha, ha', h⟩⟩)
      · push Not at ha
        obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 ha.2
        have h₁ : Msg.init x ≠ m := by rintro rfl; exact ha.1 rfl
        simp only [Amp, record_of_ne h₁] at h
        exact sent_le_step _ (ih hab' h)
    | req r =>
      rw [rcv_step_of_forall_ne (by simp)] at h
      exact sent_le_step _ (ih (ab_eq_false_of_step hab) h)
    | timeout k => exact k.elim

/-- *Quiescence* for the decision guard AD: a process that has not abandoned and whose
decision guard is enabled has decided. -/
theorem dec_isSome_of_dec (hs : (protocol P Value t).Reachable p s) (hab : s.ab = false)
    {v : Value} {g : Bool} (h : Dec t s.rcv p v g) : s.dec.isSome := by
  induction hs with
  | init => exact absurd h.1 (by simp [SelfInit])
  | @step s now x hs ih =>
    rw [protocol_step] at hab h ⊢
    cases x with
    | recv q m =>
      have hab' := ab_eq_false_of_step hab
      rw [rcv_step_recv] at h
      refine dec_isSome_step.2 ?_
      cases hd : s.dec with
      | some d => exact .inl rfl
      | none => exact .inr ⟨q, m, rfl, hab', newDec_isSome rfl h⟩
    | req r =>
      rw [rcv_step_of_forall_ne (by simp)] at h
      exact dec_isSome_step.2 (.inl (ih (ab_eq_false_of_step hab) h))
    | timeout k => exact k.elim

end Invariants

/-! ### Runs: what processes recorded and sent -/

section Runs

variable {t : ℕ} {ρ : Run (protocol P Value t)} {p q r : P} {τ τ' : ℕ} {m : Msg Value}
  {k : Phase} {a b : Option Value} {v : Value} {g : Bool}

variable (ρ) in
/-- `SendAll ρ q m τ`: process `q` sent `m` to all processes at time `τ` ("send-all"). -/
def SendAll (q : P) (m : Msg Value) (τ : ℕ) : Prop := ∀ r, .send r m ∈ ρ.output q τ

variable (t) in
/-- `rcv m` soundly records senders of `m`: a sender is recorded only upon the receipt of `m`
from it (for `INIT` messages, only the first `INIT` of each sender is recorded). -/
theorem recordsSound_rcv (p : P) : (protocol P Value t).RecordsSound p id fun s m => s.rcv m where
  init _ := by simp
  step := mem_rcv_step_imp

variable (t) in
/-- `rcv (ECHO_k a)` records exactly the senders of `ECHO_k a`. -/
theorem records_rcv_echo (p : P) :
    (protocol P Value t).Records p (fun e : Phase × Option Value => Msg.echo e.1 e.2)
      fun s e => s.rcv (.echo e.1 e.2) where
  init _ := by simp
  mem_step_iff := mem_rcv_step_echo

theorem rcv_mono (h : τ ≤ τ') : (ρ.state p τ).rcv ≤ (ρ.state p τ').rcv :=
  Run.monotone_state (f := fun s : (protocol P Value t).State => s.rcv)
    (fun _ _ _ => rcv_le_step) h

theorem sent_mono (h : τ ≤ τ') : (ρ.state p τ).sent ≤ (ρ.state p τ').sent :=
  Run.monotone_state (f := fun s : (protocol P Value t).State => s.sent)
    (fun _ _ _ => sent_le_step) h

/-- A process has abandoned iff it handled an `abandon` request earlier. -/
theorem ab_state : (ρ.state p τ).ab = true ↔ ∃ τ' < τ, .req .abandon ∈ ρ.input p τ' := by
  rw [Run.state_iff_exists_input (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.ab = true) (g := fun x => x = .req .abandon)
    (by simp) (fun _ _ _ => ab_step)]
  simp

/-- All sends of AW′ are send-alls. -/
theorem sendAll_of_send (h : .send r m ∈ ρ.output q τ) : SendAll ρ q m τ :=
  fun _ => Run.mem_output_of_forall_step (fun _ _ _ h => send_mem_step.2 (send_mem_step.1 h)) h

/-- A process sends `INIT v` only when it accepts the proposal `v`. -/
theorem propose_of_sendAll_init (h : SendAll ρ q (.init v) τ) :
    .req (.propose v) ∈ ρ.input q τ := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 (h q)
  rcases send_mem_step.1 hx with ⟨w, rfl, -, -, hw | ⟨_, _, -, hw⟩⟩ | ⟨_, _, _, _, -, -, -, -, h'⟩
  · cases hw
    exact hs.mem_input
  · cases hw
  · cases h'

/-- A process sends at most one `INIT` value. -/
theorem sendAll_init_unique {w : Value} (h₁ : SendAll ρ q (.init v) τ)
    (h₂ : SendAll ρ q (.init w) τ') : v = w := by
  obtain ⟨x₁, s₁, hs₁, hx₁⟩ := Run.mem_output_iff_handles.1 (h₁ q)
  obtain ⟨x₂, s₂, hs₂, hx₂⟩ := Run.mem_output_iff_handles.1 (h₂ q)
  obtain ⟨rfl, hp₁, hab₁⟩ := propose_of_send_init_mem_step hx₁
  obtain ⟨rfl, hp₂, hab₂⟩ := propose_of_send_init_mem_step hx₂
  rcases hs₁.order (Rel := fun s s' : (protocol P Value t).State =>
      s.proposed = true → s'.proposed = true) (fun _ => id) (fun h h' hs => h' (h hs))
      (fun _ _ _ h => proposed_step.2 (.inl h)) hs₂ with ⟨-, h, -⟩ | h | h
  · cases h; rfl
  · simpa [hp₂] using h (proposed_step.2 (.inr ⟨v, rfl, hab₁⟩))
  · simpa [hp₁] using h (proposed_step.2 (.inr ⟨w, rfl, hab₂⟩))

/-- When a process sends `ECHO_k a`, it has proposed and the guard of phase `k` has fired with
`a`. -/
theorem mem_sent_of_sendAll (h : SendAll ρ q (.echo k a) τ) :
    (ρ.state q (τ + 1)).proposed = true ∧ a ∈ (ρ.state q (τ + 1)).sent k := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 (h q)
  exact hs.state_of_stable (Q := fun s : (protocol P Value t).State =>
    s.proposed = true ∧ a ∈ s.sent k) (fun _ _ _ => proposed_mem_sent_step)
    (mem_sent_of_send_mem_step hx) (Nat.lt_succ_self τ)

/-- *Branch soundness*: when a process sends `ECHO_k a`, the guard of phase `k` is
enabled with value `a`; by monotonicity, it still is after that time. -/
theorem cand_of_sendAll (h : SendAll ρ q (.echo k a) τ) :
    Cand t (ρ.state q (τ + 1)).rcv k a :=
  cand_of_mem_sent (ρ.reachable_state q (τ + 1)) (mem_sent_of_sendAll h).2

/-- *Single messages*: a process sends at most one `ECHO_k` message for `k ≠ 1` (same value,
same time). -/
theorem sendAll_echo_unique (hk : k ≠ .one) (h₁ : SendAll ρ q (.echo k a) τ)
    (h₂ : SendAll ρ q (.echo k b) τ') : a = b ∧ τ = τ' := by
  have key : ∀ {a b τ τ'}, SendAll ρ q (.echo k a) τ → SendAll ρ q (.echo k b) τ' →
      ¬ τ < τ' := by
    intro a b τ τ' h₁ h₂ hlt
    obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 (h₂ q)
    let Q := fun s : (protocol P Value t).State => s.proposed = true ∧ a ∈ s.sent k
    obtain ⟨hp, ha⟩ : Q s := hs.of_inputs (fun _ _ _ => proposed_mem_sent_step)
      (Run.state_of_stable (Q := Q) (fun _ _ _ => proposed_mem_sent_step)
        (mem_sent_of_sendAll h₁) hlt)
    rcases proposed_eq_false_or_sent_eq_empty hk hx with h | h
    · simp [hp] at h
    · simp [h] at ha
  obtain rfl : τ = τ' := by
    rcases lt_trichotomy τ τ' with h | h | h
    exacts [absurd h (key h₁ h₂), h, absurd h (key h₂ h₁)]
  exact ⟨Finset.card_le_one.1 (card_sent_le (ρ.reachable_state q (τ + 1)) hk) a
    (mem_sent_of_sendAll h₁).2 b (mem_sent_of_sendAll h₂).2, rfl⟩

/-- Once a process has proposed, it has sent `ECHO_k a` for every value `a` with which the guard
of phase `k` has fired. -/
theorem exists_sendAll_of_mem_sent (hp : (ρ.state q τ).proposed = true)
    (h : a ∈ (ρ.state q τ).sent k) : ∃ τ' < τ, SendAll ρ q (.echo k a) τ' := by
  have hQ : ∀ now x (s : (protocol P Value t).State),
      ((protocol P Value t).step q now x s).1.proposed = true ∧
        a ∈ ((protocol P Value t).step q now x s).1.sent k →
      (s.proposed = true ∧ a ∈ s.sent k) ∨
        ∃ o ∈ ((protocol P Value t).step q now x s).2, o = .send q (.echo k a) := by
    rintro now x s ⟨hp, ha⟩
    rcases mem_sent_step.1 ha with ha' | ⟨r, m, rfl, hab, ha'⟩
    · cases hp' : s.proposed
      · obtain ⟨v, rfl, hab⟩ := (proposed_step.1 hp).resolve_left (by simp [hp'])
        exact .inr ⟨_, send_mem_step.2 (.inl ⟨v, rfl, hp', hab, .inr ⟨k, a, ha', rfl⟩⟩), rfl⟩
      · exact .inl ⟨rfl, ha'⟩
    · have hp' : s.proposed = true := by
        rcases proposed_step.1 hp with hp | ⟨v, hv, -⟩
        · exact hp
        · cases hv
      exact .inr ⟨_, send_mem_step.2 (.inr ⟨r, m, k, a, rfl, hab, hp', ha', rfl⟩), rfl⟩
  obtain ⟨τ', hτ', o, ho, rfl⟩ := Run.exists_output_of_state (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.proposed = true ∧ a ∈ s.sent k) (by simp) hQ
    ⟨hp, h⟩
  exact ⟨τ', hτ', sendAll_of_send ho⟩

/-- *Branch soundness* for decisions: when a process decides `(v, g)`, its decision guard is
enabled with `(v, g)`; by monotonicity, it still is after that time. -/
theorem dec_of_ind (h : .ind (.decide v g) ∈ ρ.output q τ) :
    Dec t (ρ.state q (τ + 1)).rcv q v g := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨r, m, rfl, -, hd⟩ := ind_mem_step.1 hx
  refine (newDec_eq_some hd).2.mono ?_
  have := hs.step_le (f := fun s : (protocol P Value t).State => s.rcv) (fun _ _ _ => rcv_le_step)
  rwa [protocol_step, rcv_step_recv] at this

/-- A process that has decided emitted a decision earlier. -/
theorem exists_ind_of_dec (h : (ρ.state q τ).dec.isSome) :
    ∃ τ' < τ, ∃ v g, .ind (.decide v g) ∈ ρ.output q τ' := by
  have hQ : ∀ now x (s : (protocol P Value t).State),
      ((protocol P Value t).step q now x s).1.dec.isSome →
      s.dec.isSome ∨ ∃ o ∈ ((protocol P Value t).step q now x s).2,
        ∃ v g, o = .ind (.decide v g) := by
    intro now x s h
    rcases dec_isSome_step.1 h with h | ⟨r, m, rfl, hab, hd⟩
    · exact .inl h
    · obtain ⟨⟨v, g⟩, hd'⟩ := Option.isSome_iff_exists.1 hd
      exact .inr ⟨_, ind_mem_step.2 ⟨r, m, rfl, hab, hd'⟩, v, g, rfl⟩
  obtain ⟨τ', hτ', o, ho, v, g, rfl⟩ := Run.exists_output_of_state (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.dec.isSome) (by simp) hQ h
  exact ⟨τ', hτ', v, g, ho⟩

/-- A process that has accepted a proposal sent its `INIT` earlier. -/
theorem exists_sendAll_init_of_proposed (h : (ρ.state q τ).proposed = true) :
    ∃ τ' < τ, ∃ v, SendAll ρ q (.init v) τ' := by
  have hQ : ∀ now x (s : (protocol P Value t).State),
      ((protocol P Value t).step q now x s).1.proposed = true →
      s.proposed = true ∨ ∃ o ∈ ((protocol P Value t).step q now x s).2,
        ∃ v, o = .send q (.init v) := by
    intro now x s h
    rcases proposed_step.1 h with h | ⟨v, rfl, hab⟩
    · exact .inl h
    · cases hp : s.proposed
      · exact .inr ⟨_, send_mem_step.2 (.inl ⟨v, rfl, hp, hab, .inl rfl⟩), v, rfl⟩
      · exact .inl rfl
  obtain ⟨τ', hτ', o, ho, v, rfl⟩ := Run.exists_output_of_state (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.proposed = true) (by simp) hQ h
  exact ⟨τ', hτ', v, sendAll_of_send ho⟩

/-- A process that handles `propose v` and has not abandoned afterwards has accepted a
proposal. -/
theorem proposed_of_propose (h : .req (.propose v) ∈ ρ.input q τ)
    (hab : (ρ.state q (τ + 1)).ab = false) : (ρ.state q (τ + 1)).proposed = true := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  have hab' : s.ab = false := Bool.eq_false_iff.2 fun hs' => by
    simpa [hab] using hs.state_of_stable (Q := fun s : (protocol P Value t).State => s.ab = true)
      (fun _ _ _ h => ab_step.2 (.inl h)) (ab_step.2 (.inl hs')) (Nat.lt_succ_self τ)
  exact hs.state_of_stable (Q := fun s : (protocol P Value t).State => s.proposed = true)
    (fun _ _ _ h => proposed_step.2 (.inl h)) (proposed_step.2 (.inr ⟨v, rfl, hab'⟩))
    (Nat.lt_succ_self τ)

variable (t) in
/-- **AW′ sends only while active**: a process sends messages only from its proposal on (its
`INIT`, its catch-up `ECHO`s, and later `ECHO`s), and never after it has abandoned. -/
theorem sendsWhileActive :
    (protocol P Value t).SendsWhileActive (· matches .propose _) (· matches .abandon) := by
  intro ρ p τ q m h
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  refine ⟨?_, fun τ' hτ' r hr hin => ?_⟩
  · rcases send_mem_step.1 hx with ⟨v, rfl, -⟩ | ⟨-, -, -, -, -, -, hp, -⟩
    · exact ⟨τ, le_rfl, .propose v, rfl, hs.mem_input⟩
    · obtain ⟨τ', hτ', y, hy, v, rfl⟩ := hs.exists_input
        (Q := fun s : (protocol P Value t).State => s.proposed = true)
        (g := fun y : (protocol P Value t).In => ∃ v, y = .req (.propose v)) (by simp)
        (fun _ _ _ h => (proposed_step.1 h).imp_right fun ⟨v, hv, _⟩ => ⟨v, hv⟩) hp
      exact ⟨τ', hτ', .propose v, rfl, hy⟩
  · obtain rfl : r = .abandon := by cases r <;> first | rfl | cases hr
    have hab := hs.of_inputs (Q := fun s : (protocol P Value t).State => s.ab = true)
      (fun _ _ _ h => ab_step.2 (.inl h)) (ab_state.2 ⟨τ', hτ', hin⟩)
    rcases send_mem_step.1 hx with ⟨-, -, -, h', -⟩ | ⟨-, -, -, -, -, h', -⟩ <;> simp [hab] at h'

/-! #### Valid runs -/

variable {δ : ℕ}

/-- A message recorded by a correct process from a correct process was sent by it
at least two ticks earlier (recorded before `τ`, received strictly after being sent). -/
theorem exists_sendAll_of_mem_rcv (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    (h : q ∈ (ρ.state p τ).rcv m) : ∃ τ', τ' + 1 < τ ∧ SendAll ρ q m τ' :=
  let ⟨τ', hτ', h'⟩ := hρ.exists_send_of_mem_get (recordsSound_rcv t p) hp hq h
  ⟨τ', hτ', sendAll_of_send h'⟩

/-- *Delivery*: a message sent by a correct process to all by time `T ≥ gst` is recorded by every
correct process after time `T + δ`. For `INIT` messages: the `INIT` recorded from a correct
process is its only `INIT` (`sendAll_init_unique`). -/
theorem mem_rcv_of_sendAll (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    {T : ℕ} (h : SendAll ρ q m τ) (hτ : τ ≤ T) (hT : ρ.gst ≤ T) :
    q ∈ (ρ.state p (T + δ + 1)).rcv m := by
  cases m with
  | echo k a =>
    have := hρ.mem_get_of_send (records_rcv_echo t p) (m := (k, a)) hq hp (h p) hτ
    rwa [max_eq_left hT] at this
  | init x =>
    obtain ⟨y, hy⟩ : ∃ y, q ∈ (ρ.state p (T + δ + 1)).rcv (.init y) := by
      have := hρ.state_of_send hq hp (h p) hτ
        (Q := fun s : (protocol P Value t).State => ∃ y, q ∈ s.rcv (.init y))
        (fun _ _ _ ⟨y, hy⟩ => ⟨y, rcv_le_step _ hy⟩) fun _ _ => exists_mem_rcv_step_init
      rwa [max_eq_left hT] at this
    obtain ⟨τ', -, hs⟩ := exists_sendAll_of_mem_rcv hρ hp hq hy
    rwa [sendAll_init_unique hs h] at hy

/-- More than `t` recorded senders include a correct one, which sent the message earlier. -/
theorem exists_correct_of_lt_card (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : t < #((ρ.state p τ).rcv m)) : ∃ q ∉ ρ.faulty, ∃ τ', τ' + 1 < τ ∧ SendAll ρ q m τ' := by
  obtain ⟨q, hq, hqF⟩ := Quorum.exists_notMem_of_lt_card hρ.card_faulty_le h
  exact ⟨q, hqF, exists_sendAll_of_mem_rcv hρ hp hqF hq⟩

/-- Two quorums of recorded senders (at correct processes) share a correct sender. -/
theorem exists_correct_of_quorums (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    {p' : P} {τ' : ℕ} {m' : Msg Value} (hp : p ∉ ρ.faulty) (hp' : p' ∉ ρ.faulty)
    (h : Fintype.card P - t ≤ #((ρ.state p τ).rcv m))
    (h' : Fintype.card P - t ≤ #((ρ.state p' τ').rcv m')) :
    ∃ r ∉ ρ.faulty, (∃ τ₁, SendAll ρ r m τ₁) ∧ ∃ τ₂, SendAll ρ r m' τ₂ := by
  obtain ⟨r, hr, hr', hrF⟩ := Quorum.exists_notMem_inter_of_quorums hρ.card_faulty_le hn h h'
  obtain ⟨τ₁, -, h₁⟩ := exists_sendAll_of_mem_rcv hρ hp hrF hr
  obtain ⟨τ₂, -, h₂⟩ := exists_sendAll_of_mem_rcv hρ hp' hrF hr'
  exact ⟨r, hrF, ⟨τ₁, h₁⟩, τ₂, h₂⟩

end Runs

end AttiyaWelch

end Cslib.Distributed
