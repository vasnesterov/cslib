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
`Cslib.Computability.Distributed.Agreement.AttiyaWelch.Latency`, and the specification in
`Cslib.Computability.Distributed.Agreement.AttiyaWelch`.

**Protocol.** Messages are `INIT x` (a proposal) and `ECHO_k a` for the phases `k = 1, …, 5`,
where `a : Option Value` and `none` is AW's centre value `⊥`. A process records every message it
receives (`State.rcv m` is the set of senders of `m`; all counts are of distinct senders).
* `propose v`: unless it has already proposed or abandoned, the process sends `INIT v` to all.
* `abandon`: the process stops sending and deciding (it keeps recording messages).
* After every receipt (unless abandoned) the guards are evaluated (`Cand`, `Dec`):
  - A1: `ECHO_1 a` once for every *amplified* `a` (`Amp`): more than `t` `INIT x` or `ECHO_1 x`
    for `a = x`; for `a = ⊥`, more than `t` `ECHO_1 ⊥`, or evidence `Evid` that the proposals
    diverge (for every `x`, more than `t` processes sent an `INIT` with a value other than `x`);
  - A2: one `ECHO_2 a` for an *approved* `a` (`n - t` `ECHO_1 a`);
  - A3: one `ECHO_3 a` for `a` with `n - t` `ECHO_2 a`, or `ECHO_3 ⊥` if two values are approved;
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
* `INIT` messages are recorded per (sender, value), like `ECHO` messages; since `Evid` counts
  distinct senders, a faulty process sending several `INIT`s gains nothing.
* The branches of a guard are merged, and when several values (or decisions) are enabled, an
  arbitrary one is chosen (`Classical.choose`); the proofs never depend on the choice.
* Guard A1 is evaluated only for the value of the received message and for `⊥` (no other value
  can become amplified by the receipt); the other guards are evaluated after every receipt.
* Decisions are gated on the receipt of the process's own `INIT`, which arrives strictly after
  its proposal; D0 decides the value `x` of that `INIT`, i.e. the process's proposal. Hence a
  process decides only after proposing, and AW′ is request-quiet.

## Main definitions

* `AttiyaWelch.protocol P Value t`: the protocol AW′.
* `AttiyaWelch.SendAll ρ q m τ`: process `q` sent `m` to all processes at time `τ`.

## Main statements

* `AttiyaWelch.requestQuiet`: AW′ is request-quiet.
* Invariants: at most one `ECHO_k` per phase `k ≠ 1` (`card_sent_le`, `sendAll_echo_unique`);
  *quiescence*, i.e. enabled guards have fired (`sent_nonempty_of_cand`, `mem_sent_of_amp`,
  `dec_isSome_of_dec`); *branch soundness*, i.e. a message or decision is sent only with its
  guard enabled (`cand_of_sendAll`, `dec_of_ind`).
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
  /-- `rcv m`: the processes from which message `m` was received. -/
  rcv : Msg Value → Finset P
  /-- `sent k`: the values `a` such that `ECHO_k a` was sent. -/
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

/-- Amplification condition `Amp a` of guard A1. -/
def Amp : Option Value → Prop
  | some x => t < #(R (.init x)) ∨ t < #(R (.echo .one (some x)))
  | none => Evid t R ∨ t < #(R (.echo .one none))

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
  | .three, a => Quo t R .two a ∨ (a = none ∧ Appr2 t R)
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
  cases a with
  | none =>
    exact Or.imp (Evid.mono h) fun hc => hc.trans_le (card_le_card (h _))
  | some x =>
    exact Or.imp (fun hc => hc.trans_le (card_le_card (h _)))
      fun hc => hc.trans_le (card_le_card (h _))

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
  | three => exact Or.imp (Quo.mono h) (And.imp_right (Appr2.mono h))
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

/-- Record the receipt of message `m` from `q`. -/
def record (q : P) (m : Msg Value) (R : Msg Value → Finset P) : Msg Value → Finset P :=
  Function.update R m (insert q (R m))

@[simp]
theorem mem_record {q r : P} {m m' : Msg Value} {R : Msg Value → Finset P} :
    r ∈ record q m R m' ↔ r ∈ R m' ∨ (r = q ∧ m' = m) := by
  unfold record
  by_cases h : m' = m
  · subst h; simp [or_comm]
  · simp [h]

theorem le_record (q : P) (m : Msg Value) (R : Msg Value → Finset P) : R ≤ record q m R :=
  fun _ _ h => mem_record.2 (.inl h)

theorem record_of_ne {q : P} {m m' : Msg Value} {R : Msg Value → Finset P} (h : m' ≠ m) :
    record q m R m' = R m' :=
  Function.update_of_ne h _ _

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
* `propose v`: if the process has neither proposed nor abandoned, accept the proposal and send
  `INIT v` to all. No guard is evaluated (request-quietness).
* `abandon`: stop sending and deciding.
* receipt of `m` from `q`: record it; unless abandoned, run the guard pass. -/
noncomputable def step (p : P) :
    Input P (Msg Value) Empty (Req Value) → State P Value →
      State P Value × List (Output P (Msg Value) Empty (Ind Value))
  | .req (.propose v), s =>
    if s.proposed || s.ab then (s, [])
    else ({ s with proposed := true }, Output.broadcast (.init v))
  | .req .abandon, s => ({ s with ab := true }, [])
  | .recv q m, s =>
    if s.ab then ({ s with rcv := record q m s.rcv }, []) else
      ({ s with
          rcv := record q m s.rcv
          sent := fun k => s.sent k ∪ newVals t (record q m s.rcv) s.sent m k
          dec := s.dec.or (newDec t p (record q m s.rcv) s.dec) },
        echoOuts (newVals t (record q m s.rcv) s.sent m) ++
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

theorem rcv_step_recv {q : P} : (step t p (.recv q m) s).1.rcv = record q m s.rcv := by
  by_cases hab : s.ab <;> simp [step, hab]

theorem mem_rcv_step {r : P} :
    r ∈ (step t p x s).1.rcv m ↔ r ∈ s.rcv m ∨ x = .recv r m := by
  cases x with
  | req r' => cases r' <;> simp [step]; split_ifs <;> simp
  | recv q m' =>
    rw [rcv_step_recv, mem_record]
    simp only [Input.recv.injEq]
    exact or_congr_right ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩
  | timeout k => exact k.elim

theorem rcv_le_step : s.rcv ≤ (step t p x s).1.rcv :=
  fun _ _ h => mem_rcv_step.2 (.inl h)

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

theorem send_mem_step {r : P} {m' : Msg Value} :
    .send r m' ∈ (step t p x s).2 ↔
      (∃ v, x = .req (.propose v) ∧ s.proposed = false ∧ s.ab = false ∧ m' = .init v) ∨
        ∃ q m k a, x = .recv q m ∧ s.ab = false ∧
          a ∈ newVals t (record q m s.rcv) s.sent m k ∧ m' = .echo k a := by
  cases x with
  | req r' =>
    cases r' with
    | propose v =>
      cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab, @eq_comm _ m']
    | abandon => simp [step]
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · simp [step, hab, send_mem_echoOuts]
  | timeout k => exact k.elim

theorem ind_mem_step :
    .ind (.decide v g) ∈ (step t p x s).2 ↔
      ∃ q m, x = .recv q m ∧ s.ab = false ∧
        newDec t p (record q m s.rcv) s.dec = some (v, g) := by
  cases x with
  | req r' =>
    cases r' with
    | propose v => cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab]
    | abandon => simp [step]
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · simp [step, hab, ind_notMem_echoOuts, eq_comm]
  | timeout k => exact k.elim

/-- A step emits at most one indication. -/
theorem length_filterMap_ind?_step_le :
    ((step t p x s).2.filterMap Output.ind?).length ≤ 1 := by
  cases x with
  | req r' =>
    cases r' with
    | propose v =>
      cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab, Output.broadcast,
        Output.ind?, Function.comp_def]
    | abandon => simp [step]
  | recv q m' =>
    by_cases hab : s.ab
    · simp [step, hab]
    · cases h : newDec t p (record q m' s.rcv) s.dec <;>
        simp [step, hab, h, echoOuts, List.filterMap_flatMap, Output.broadcast, Output.ind?,
          Function.comp_def]
  | timeout k => exact k.elim

end Local

/-- AW′ is request-quiet: `propose` and `abandon` emit no indication (decisions are
gated on the receipt of the process's own `INIT`, which arrives strictly later). -/
theorem requestQuiet (t : ℕ) : (protocol P Value t).RequestQuiet := by
  intro p now r s i
  cases r with
  | propose v => cases hp : s.proposed <;> cases hab : s.ab <;> simp [step, hp, hab]
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

theorem rcv_step_of_forall_ne {x : Input P (Msg Value) Empty (Req Value)}
    (hx : ∀ q m, x ≠ .recv q m) : (step t p x s).1.rcv = s.rcv := by
  ext m r
  simp [mem_rcv_step, hx]

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
  | three => rintro (h | ⟨-, _, _, -, h, -⟩) <;> exact hq _ _ h
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
      rcases h with h | h
      · obtain ⟨S, hS, hS'⟩ := h (Classical.arbitrary Value)
        obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun q hq => by
          simpa using hS' q hq
        simp at hS
      · simp at h
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
        have h₂ : Msg.echo .one (some x) ≠ m := by rintro rfl; exact ha.1 rfl
        simp only [Amp, record_of_ne h₁, record_of_ne h₂] at h
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
/-- `rcv m` records exactly the senders of `m`. -/
theorem records_rcv (p : P) : (protocol P Value t).Records p id fun s m => s.rcv m where
  init _ := by simp
  mem_step_iff := mem_rcv_step

/-- The senders recorded by `p` at time `τ` are those of the messages it received earlier. -/
theorem mem_rcv_state : q ∈ (ρ.state p τ).rcv m ↔ ∃ τ' < τ, .recv q m ∈ ρ.input p τ' :=
  Run.mem_get_state_iff (records_rcv t p)

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
  rcases send_mem_step.1 hx with ⟨w, rfl, -, -, hw⟩ | ⟨_, _, _, _, -, -, -, h'⟩
  · cases hw
    exact hs.mem_input
  · cases h'

/-- The step in which an `ECHO` is sent: the receipt of a message, by a process that has not
abandoned, after which the guard of the phase fires. -/
theorem exists_handles_of_sendAll_echo (h : SendAll ρ q (.echo k a) τ) :
    ∃ r m s, ρ.Handles q τ (.recv r m) s ∧ s.ab = false ∧
      a ∈ newVals t (record r m s.rcv) s.sent m k := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 (h q)
  rcases send_mem_step.1 hx with ⟨_, -, -, -, h'⟩ | ⟨r, m, k', a', rfl, hab, ha, h'⟩
  · cases h'
  · cases h'
    exact ⟨r, m, s, hs, hab, ha⟩

/-- *Branch soundness*: when a process sends `ECHO_k a`, the guard of phase `k` is
enabled with value `a`; by monotonicity, it still is after that time. -/
theorem cand_of_sendAll (h : SendAll ρ q (.echo k a) τ) :
    Cand t (ρ.state q (τ + 1)).rcv k a := by
  obtain ⟨r, m, s, hs, -, ha⟩ := exists_handles_of_sendAll_echo h
  refine (cand_of_mem_newVals ha).1.mono ?_
  have := hs.step_le (f := fun s : (protocol P Value t).State => s.rcv) (fun _ _ _ => rcv_le_step)
  rwa [protocol_step, rcv_step_recv] at this

theorem mem_sent_of_sendAll (h : SendAll ρ q (.echo k a) τ) : a ∈ (ρ.state q (τ + 1)).sent k := by
  obtain ⟨r, m, s, hs, hab, ha⟩ := exists_handles_of_sendAll_echo h
  exact hs.step_le (f := fun s : (protocol P Value t).State => s.sent) (fun _ _ _ => sent_le_step)
    k (mem_sent_step.2 (.inr ⟨r, m, rfl, hab, ha⟩))

theorem sent_eq_empty_of_sendAll (hk : k ≠ .one) (h : SendAll ρ q (.echo k a) τ) :
    (ρ.state q τ).sent k = ∅ := by
  obtain ⟨r, m, s, hs, -, ha⟩ := exists_handles_of_sendAll_echo h
  have := hs.le (f := fun s : (protocol P Value t).State => s.sent) (fun _ _ _ => sent_le_step) k
  exact Finset.subset_empty.1 ((mem_newVals_of_ne hk ha).1 ▸ this)

/-- *Single messages*: a process sends at most one `ECHO_k` message for `k ≠ 1` (same value,
same time). -/
theorem sendAll_echo_unique (hk : k ≠ .one) (h₁ : SendAll ρ q (.echo k a) τ)
    (h₂ : SendAll ρ q (.echo k b) τ') : a = b ∧ τ = τ' := by
  have key : ∀ {a b τ τ'}, SendAll ρ q (.echo k a) τ → SendAll ρ q (.echo k b) τ' →
      ¬ τ < τ' := by
    intro a b τ τ' h₁ h₂ hlt
    have := sent_mono (ρ := ρ) (p := q) (show τ + 1 ≤ τ' by omega) k (mem_sent_of_sendAll h₁)
    simp [sent_eq_empty_of_sendAll hk h₂] at this
  obtain rfl : τ = τ' := by
    rcases lt_trichotomy τ τ' with h | h | h
    exacts [absurd h (key h₁ h₂), h, absurd h (key h₂ h₁)]
  exact ⟨Finset.card_le_one.1 (card_sent_le (ρ.reachable_state q (τ + 1)) hk) a
    (mem_sent_of_sendAll h₁) b (mem_sent_of_sendAll h₂), rfl⟩

/-- Values recorded as sent were sent earlier. -/
theorem exists_sendAll_of_mem_sent (h : a ∈ (ρ.state q τ).sent k) :
    ∃ τ' < τ, SendAll ρ q (.echo k a) τ' := by
  have hQ : ∀ now x (s : (protocol P Value t).State),
      a ∈ ((protocol P Value t).step q now x s).1.sent k →
      a ∈ s.sent k ∨ ∃ o ∈ ((protocol P Value t).step q now x s).2, o = .send q (.echo k a) := by
    intro now x s h
    rcases mem_sent_step.1 h with h | ⟨r, m, rfl, hab, ha⟩
    · exact .inl h
    · exact .inr ⟨_, send_mem_step.2 (.inr ⟨r, m, k, a, rfl, hab, ha, rfl⟩), rfl⟩
  obtain ⟨τ', hτ', o, ho, rfl⟩ := Run.exists_output_of_state (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => a ∈ s.sent k) (by simp) hQ h
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
      · exact .inr ⟨_, send_mem_step.2 (.inl ⟨v, rfl, hp, hab, rfl⟩), v, rfl⟩
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

/-! #### Valid runs -/

variable {δ : ℕ}

/-- A message recorded by a correct process from a correct process was sent by it
at least two ticks earlier (recorded before `τ`, received strictly after being sent). -/
theorem exists_sendAll_of_mem_rcv (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    (h : q ∈ (ρ.state p τ).rcv m) : ∃ τ', τ' + 1 < τ ∧ SendAll ρ q m τ' :=
  let ⟨τ', hτ', h'⟩ := hρ.exists_send_of_mem_get (records_rcv t p).sound hp hq h
  ⟨τ', hτ', sendAll_of_send h'⟩

/-- *Delivery*: a message sent by a correct process to all by time `T ≥ gst` is recorded by every
correct process after time `T + δ`. -/
theorem mem_rcv_of_sendAll (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    {T : ℕ} (h : SendAll ρ q m τ) (hτ : τ ≤ T) (hT : ρ.gst ≤ T) :
    q ∈ (ρ.state p (T + δ + 1)).rcv m := by
  have := hρ.mem_get_of_send (records_rcv t p) hq hp (h p) hτ
  rwa [max_eq_left hT] at this

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
