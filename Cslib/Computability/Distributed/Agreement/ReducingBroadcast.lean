/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Bits
public import Cslib.Computability.Distributed.MessagePassing.Reasoning
public import Cslib.Computability.Distributed.Quorum

/-! # Reducing broadcast: a one-round value reduction

A *reducing broadcast* reduces the number of different values held by correct processes: every
process broadcasts a value and delivers either a value or `⊥`, such that few different values are
delivered by correct processes in total. It was introduced by
[Mostéfaoui and Raynal][MostefaouiRaynal2017], and [Civit et al.][CivitEtAl2024] (appendix
"Existing primitives") use it to bound the number of `ECHO` messages of their validation broadcast.

**Interface.** Requests `broadcast v` and `abandon` (stop participating); indication `deliver a`
with `a : Option Value`, where `none` is the paper's `⊥_rd`.

**Assumption** (`Assumptions`): every correct process broadcasts at most once.

**Properties** (`Properties`, for resilience `t` and a latency `Δ`):
* *Validity*: if all correct processes that broadcast do so with the same value `v`, then every
  delivery of a correct process is `some v`.
* *Safety*: if a correct process delivers `some x`, then at least `n - 3t` correct processes have
  broadcast `x` (strictly earlier); if `3t < n`, at least one.
* *Integrity*: a correct process delivers at most once (`integrity`), and only at a time strictly
  after a time at which it broadcast (`afterBroadcast`).
* *Latency* (timed termination): for every time `τ`, if all correct processes have broadcast by `τ`
  and no correct process abandons by `max τ gst + Δ`, then every correct process delivers by
  `max τ gst + Δ`.

*Reduction* is a consequence of safety (`Properties.card_le`): if `3t < n`, the values other than
`⊥` delivered by correct processes are at most `n / (n - 3t)`, since each of them is broadcast by
`n - 3t` correct processes and every correct process broadcasts at most one value.

## Differences from the paper's module

* The paper's *validity* only excludes `⊥` when all correct broadcasts carry the same value `v`;
  ours also says that `v` is delivered. The paper's *safety* asks for one correct broadcaster of a
  delivered value; ours asks for `n - 3t` of them, and the paper's *reduction* (`O(1)` values in
  total, including `⊥`) is replaced by the bound `n / (n - 3t)` of `Properties.card_le`.
* The paper's *termination* is replaced by the timed *latency* (a consequence), and *integrity*
  is added: users of the primitive need both (as for graded consensus,
  `Cslib.Distributed.GradedConsensus`).

## The one-round protocol

`protocol` is a one-round implementation for `3t < n`. On `broadcast v`, a process sends
`INIT v` to all (once, and not after it has abandoned). It records the first `INIT` of each sender.
Once it has received its own `INIT` and `INIT`s from `n - t` distinct senders (and unless it has
abandoned or already delivered), it delivers `some x` for a value `x` with at least `n - 2t` of the
recorded `INIT`s if there is one, and `⊥` otherwise (`result`). It satisfies the specification
with latency `δ` (`satisfies`), and a process broadcasts one message of `1 + L` bits for
`L`-bit values (`bitsSent_le`).

Compared with the two-round reducing broadcast of [Mostéfaoui and Raynal][MostefaouiRaynal2017],
whose reduction is `O(1)` for every `t < n / 3`, this one-round variant only guarantees that at
most `n / (n - 3t)` values other than `⊥` are delivered, which is `O(1)` only if `n - 3t = Ω(n)`.
Downstream, however, values are typically adopted only with `t + 1` supporters (e.g. a value is
echoed on `t + 1` `INIT`s), which bounds them by `n / (t + 1)`; both bounds together leave at most
three values for every `t < n / 3` (`Quorum.min_div_le_three`,
`Quorum.card_le_three_of_pairwiseDisjoint`).

## Implementation notes

* Delivery is gated on the receipt of the process's own `INIT`, which arrives strictly after its
  `broadcast` in valid runs. Hence a correct process delivers only after broadcasting (strictly
  later), and request handlers emit no indication (`requestQuiet`). The guard does not
  test the `broadcast` flag itself: the own `INIT` already implies it for correct processes, and
  the guard then depends only on the received messages, so that an enabled guard has fired
  (`done_of_ready`).
* If `n ≤ 4t`, two values may each have `n - 2t` recorded `INIT`s (e.g. `n = 4`, `t = 1`); then
  either may be delivered (`Classical.choose`). The proofs never depend on the choice: validity and
  safety only use that the delivered value has `n - 2t` recorded `INIT`s.
* A process records messages also before it broadcasts and after it abandons; it sends only
  between its `broadcast` and its `abandon` (`sendsWhileActive`).

## Main definitions

* `interface`, `Assumptions`, `Properties`, `spec`.
* `protocol P Value t`: the one-round protocol; `Msg.size`: message sizes.

## Main statements

* `Properties.card_le`: reduction, at most `n / (n - 3t)` values other than `⊥` are
  delivered by correct processes.
* `satisfies`: for `3t < n`, the protocol satisfies `spec t δ`.
* `requestQuiet`, `sendsWhileActive`.
* `bitsSent_one_le`, `bitsSent_le`: in every run, a process sends at most `n`
  messages and `n (L + 1)` bits for values of at most `L` bits.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
* [A. Mostéfaoui, M. Raynal, *Signature-Free Asynchronous Byzantine Systems: From Multivalued to
  Binary Consensus with t < n/3, O(n²) Messages, and Constant Time*, Acta Informatica 54(5),
  2017][MostefaouiRaynal2017]
-/

@[expose] public section

namespace Cslib.Distributed.ReducingBroadcast

open Finset

/-! ### Specification -/

/-- The requests of reducing broadcast. -/
inductive Req (Value : Type) where
  /-- Broadcast value `v`. -/
  | broadcast (v : Value)
  /-- Abandon reducing broadcast, i.e. stop participating in it. -/
  | abandon
deriving DecidableEq

/-- The indications of reducing broadcast. -/
inductive Ind (Value : Type) where
  /-- Deliver `a`, a value or `⊥_rd` (`none`). -/
  | deliver (a : Option Value)
deriving DecidableEq

/-- The interface of reducing broadcast on values `Value`. -/
abbrev interface (Value : Type) : Interface where
  Req := Req Value
  Ind := Ind Value

section Spec

variable {P : Type*} {Value : Type}

/-- The environment assumption of reducing broadcast ([CivitEtAl2024], appendix "Existing
primitives"). -/
structure Assumptions (H : History P (interface Value)) : Prop where
  /-- Every correct process broadcasts at most once. -/
  broadcastAtMostOnce : ∀ p, H.Correct p → H.AtMostOnce p (· matches .req (.broadcast _))

/-- The guarantees of reducing broadcast for resilience `t` with latency `Δ` (see the module
docstring for the differences from [CivitEtAl2024]). -/
structure Properties [Fintype P] (t Δ : ℕ) (H : History P (interface Value)) : Prop where
  /-- *Validity*: if all correct processes that broadcast do so with the same value `v`, then every
  correct process that delivers delivers `v` (in particular, not `⊥_rd`). -/
  validity : ∀ v, (∀ p, H.Correct p → ∀ w τ, H.ReqAt p (.broadcast w) τ → w = v) →
    ∀ p, H.Correct p → ∀ a τ, H.IndAt p (.deliver a) τ → a = some v
  /-- *Safety*: if a correct process delivers a value `x` (not `⊥_rd`) at time `τ`, then at least
  `n - 3t` correct processes broadcast `x` before `τ`. -/
  safety : ∀ p, H.Correct p → ∀ x τ, H.IndAt p (.deliver (some x)) τ →
    ∃ S : Finset P, Fintype.card P - 3 * t ≤ #S ∧
      ∀ q ∈ S, H.Correct q ∧ ∃ τ' < τ, H.ReqAt q (.broadcast x) τ'
  /-- *Integrity* (at most once): no correct process delivers more than once. -/
  integrity : ∀ p, H.Correct p → H.AtMostOnce p (· matches .ind _)
  /-- *Integrity* (after broadcasting): a correct process delivers only at a time strictly after a
  time at which it broadcast. -/
  afterBroadcast : ∀ p, H.Correct p → ∀ a τ, H.IndAt p (.deliver a) τ →
    ∃ τ' < τ, ∃ v, H.ReqAt p (.broadcast v) τ'
  /-- *Latency* (timed termination): if every correct process has broadcast by time `τ` and no
  correct process abandons by time `max τ gst + Δ`, then every correct process delivers by time
  `max τ gst + Δ`. -/
  latency : ∀ τ, (∀ p, H.Correct p → ∃ v, H.ReqBy p (.broadcast v) τ) →
    (∀ p, H.Correct p → ¬ H.ReqBy p .abandon (max τ H.gst + Δ)) →
    ∀ p, H.Correct p → ∃ a, H.IndBy p (.deliver a) (max τ H.gst + Δ)

/-- The specification of reducing broadcast for resilience `t` with latency `Δ`: if the
environment satisfies the assumption, then the guarantees hold. -/
def spec [Fintype P] (t Δ : ℕ) : Spec P (interface Value) :=
  fun H => Assumptions H → Properties t Δ H

/-- **Reduction**: if `3t < n`, at most `n / (n - 3t)` different values other than `⊥_rd` are
delivered by correct processes. Each of them is broadcast by `n - 3t` correct processes (safety),
and every correct process broadcasts at most once (`Quorum.card_le_div_sub_of_pairwiseDisjoint`). -/
theorem Properties.card_le [Fintype P] {t Δ : ℕ} {H : History P (interface Value)}
    (h : Properties t Δ H) (hA : Assumptions H) (hn : 3 * t < Fintype.card P)
    {X : Finset Value} (hX : ∀ x ∈ X, ∃ p τ, H.Correct p ∧ H.IndAt p (.deliver (some x)) τ) :
    #X ≤ Fintype.card P / (Fintype.card P - 3 * t) := by
  classical
  -- the correct broadcasters of each value
  let B : Value → Finset P := fun x =>
    univ.filter fun q => H.Correct q ∧ ∃ τ, H.ReqAt q (.broadcast x) τ
  refine Quorum.card_le_div_sub_of_pairwiseDisjoint (S := B) hn ?_ fun x hx => ?_
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun q hx hy => hxy ?_
    obtain ⟨hq, τ₁, h₁⟩ := (mem_filter.1 hx).2
    obtain ⟨-, τ₂, h₂⟩ := (mem_filter.1 hy).2
    simpa using ((hA.broadcastAtMostOnce q hq).eq_of_mem h₁ h₂ rfl rfl).2
  · obtain ⟨p, τ, hp, hd⟩ := hX x hx
    obtain ⟨S, hS, hS'⟩ := h.safety p hp x τ hd
    refine hS.trans (card_le_card fun q hq => ?_)
    obtain ⟨hq, τ', -, h'⟩ := hS' q hq
    exact mem_filter.2 ⟨mem_univ q, hq, τ', h'⟩

end Spec

/-! ### The one-round protocol -/

/-- The messages of the one-round reducing broadcast: `INIT v` carries a broadcast value. -/
inductive Msg (Value : Type) where
  /-- `INIT v`. -/
  | init (v : Value)
deriving DecidableEq

variable {P Value : Type}

/-- The size in bits of a message, given the sizes `valueSize` of the encodings of the values: one
bit for the message type, followed by the encoding of the value. -/
def Msg.size (valueSize : Value → ℕ) : Msg Value → ℕ
  | .init v => 1 + valueSize v

/-- A message has at most `L + 1` bits if every value has at most `L` bits. -/
theorem Msg.size_le {valueSize : Value → ℕ} {L : ℕ} (hL : ∀ v, valueSize v ≤ L)
    (m : Msg Value) : m.size valueSize ≤ L + 1 := by
  cases m with
  | init v => have := hL v; simp only [Msg.size]; omega

/-- The local state of a process. -/
structure State (P Value : Type) where
  /-- The process has abandoned. -/
  ab : Bool
  /-- The process has accepted a `broadcast` request (and sent its `INIT`). -/
  bcast : Bool
  /-- `initFrom q`: the value of the first `INIT` received from `q`, if any. -/
  initFrom : P → Option Value
  /-- The process has delivered. -/
  done : Bool

/-! #### Guards

The delivery guard and the delivered value depend only on the recorded `INIT`s
`R : P → Option Value`. -/

section Guards

variable [Fintype P]

/-- The processes from which an `INIT` has been recorded. -/
def senders (R : P → Option Value) : Finset P := univ.filter fun q => (R q).isSome

/-- The processes whose recorded `INIT` carries `x`. -/
def initSet [DecidableEq Value] (R : P → Option Value) (x : Value) : Finset P :=
  univ.filter fun q => R q = some x

/-- The delivery guard of process `p`: its own `INIT` and `INIT`s from `n - t` distinct senders
have been recorded. -/
def Ready (t : ℕ) (R : P → Option Value) (p : P) : Prop :=
  (R p).isSome ∧ Fintype.card P - t ≤ #(senders R)

open scoped Classical in
/-- The delivered value: a value with at least `n - 2t` recorded `INIT`s if there is one (chosen
arbitrarily if there are several), and `⊥` (`none`) otherwise. -/
noncomputable def result [DecidableEq Value] (t : ℕ) (R : P → Option Value) : Option Value :=
  if h : ∃ x, Fintype.card P - 2 * t ≤ #(initSet R x) then some h.choose else none

variable {R : P → Option Value} {t : ℕ}

@[simp]
theorem mem_senders {q : P} : q ∈ senders R ↔ (R q).isSome := by
  simp [senders]

@[simp]
theorem mem_initSet [DecidableEq Value] {q : P} {x : Value} : q ∈ initSet R x ↔ R q = some x := by
  simp [initSet]

/-- A delivered value has `n - 2t` recorded `INIT`s. -/
theorem le_card_initSet_of_result_eq_some [DecidableEq Value] {x : Value}
    (h : result t R = some x) : Fintype.card P - 2 * t ≤ #(initSet R x) := by
  unfold result at h
  split_ifs at h with hx
  cases h
  exact hx.choose_spec

/-- If a value `x` has `n - 2t` recorded `INIT`s and no other value does, `x` is delivered. -/
theorem result_eq_some [DecidableEq Value] {x : Value}
    (hx : Fintype.card P - 2 * t ≤ #(initSet R x))
    (huniq : ∀ y, Fintype.card P - 2 * t ≤ #(initSet R y) → y = x) : result t R = some x := by
  unfold result
  split_ifs with h
  · exact congrArg some (huniq _ h.choose_spec)
  · exact absurd ⟨x, hx⟩ h

end Guards

section Record

variable [DecidableEq P]

/-- Record an `INIT x` received from `q`, unless an `INIT` from `q` has already been recorded (only
the first `INIT` of each sender is recorded). -/
def record (q : P) (x : Value) (R : P → Option Value) : P → Option Value :=
  fun r => if r = q ∧ (R r).isNone then some x else R r

variable {q r : P} {x y : Value} {R : P → Option Value}

theorem record_eq_some_iff :
    record q x R r = some y ↔ R r = some y ∨ (r = q ∧ R r = none ∧ y = x) := by
  unfold record
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    rw [Option.isNone_iff_eq_none] at h
    simp [h, eq_comm]
  · simp only [not_and, Option.isNone_iff_eq_none] at h
    constructor
    · exact .inl
    · rintro (h' | ⟨rfl, h', -⟩)
      · exact h'
      · exact absurd h' (h rfl)

/-- Recorded `INIT`s are never forgotten or changed. -/
theorem record_of_eq_some (h : R r = some y) : record q x R r = some y :=
  record_eq_some_iff.2 (.inl h)

theorem isSome_record_self : (record q x R q).isSome := by
  unfold record
  split_ifs with h
  · rfl
  · simp only [true_and, Option.isNone_iff_eq_none] at h
    exact Option.isSome_iff_ne_none.2 h

end Record

/-! #### Steps -/

section Step

variable [Fintype P] [DecidableEq P] [DecidableEq Value] (t : ℕ)

open scoped Classical in
/-- The step function of process `p`.
* `broadcast v`: unless the process has already broadcast or has abandoned, accept `v` and send
  `INIT v` to all. No guard is evaluated (request-quietness).
* `abandon`: stop sending and delivering.
* receipt of `INIT x` from `q`: record it (first `INIT` of each sender); if the process has not
  abandoned and not delivered, and the delivery guard `Ready` holds, deliver `result`. -/
noncomputable def step (p : P) :
    Input P (Msg Value) Empty (Req Value) → State P Value →
      State P Value × List (Output P (Msg Value) Empty (Ind Value))
  | .req (.broadcast v), s =>
    if s.bcast || s.ab then (s, [])
    else ({ s with bcast := true }, Output.broadcast (.init v))
  | .req .abandon, s => ({ s with ab := true }, [])
  | .recv q (.init x), s =>
    if s.ab = false ∧ s.done = false ∧ Ready t (record q x s.initFrom) p then
      ({ s with initFrom := record q x s.initFrom, done := true },
        [.ind (.deliver (result t (record q x s.initFrom)))])
    else ({ s with initFrom := record q x s.initFrom }, [])
  | .timeout k, _ => k.elim

end Step

variable (P Value) in
/-- **The one-round reducing broadcast** for at most `t` faulty processes: broadcast `INIT v`,
and deliver once the own `INIT` and `n - t` `INIT`s have been received, a value with `n - 2t` of
them or `⊥`. -/
@[reducible] noncomputable def protocol [Fintype P] [DecidableEq P] [DecidableEq Value] (t : ℕ) :
    Protocol P (interface Value) where
  Msg := Msg Value
  Timer := Empty
  State := State P Value
  init _ := { ab := false, bcast := false, initFrom := fun _ => none, done := false }
  step p _ := step t p

variable [Fintype P] [DecidableEq P] [DecidableEq Value]

/-! ### Local lemmas -/

section Local

variable {t : ℕ} {p q r : P} {x : Input P (Msg Value) Empty (Req Value)} {s : State P Value}
  {v y : Value}

theorem initFrom_step_recv :
    (step t p (.recv q (.init y)) s).1.initFrom = record q y s.initFrom := by
  simp only [step]
  split_ifs <;> rfl

theorem initFrom_step_of_forall_ne (hx : ∀ q y, x ≠ .recv q (.init y)) :
    (step t p x s).1.initFrom = s.initFrom := by
  rcases x with (v | _) | ⟨q, ⟨y⟩⟩ | k
  · simp only [step]; split_ifs <;> rfl
  · rfl
  · exact absurd rfl (hx q y)
  · exact k.elim

/-- A step records a new `INIT y` from `r` only upon receiving it from `r`. -/
theorem initFrom_step_eq_some (h : (step t p x s).1.initFrom r = some y) :
    s.initFrom r = some y ∨ x = .recv r (.init y) := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · rw [initFrom_step_of_forall_ne (by simp)] at h; exact .inl h
  · rw [initFrom_step_of_forall_ne (by simp)] at h; exact .inl h
  · rw [initFrom_step_recv, record_eq_some_iff] at h
    rcases h with h | ⟨rfl, -, rfl⟩
    · exact .inl h
    · exact .inr rfl
  · exact k.elim

/-- Recorded `INIT`s are never forgotten or changed. -/
theorem initFrom_step_of_eq_some (h : s.initFrom r = some y) :
    (step t p x s).1.initFrom r = some y := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · rwa [initFrom_step_of_forall_ne (by simp)]
  · rwa [initFrom_step_of_forall_ne (by simp)]
  · rw [initFrom_step_recv]; exact record_of_eq_some h
  · exact k.elim

theorem isSome_initFrom_step (h : (s.initFrom r).isSome) :
    ((step t p x s).1.initFrom r).isSome := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
  rw [initFrom_step_of_eq_some hy]
  rfl

theorem isSome_initFrom_step_recv : ((step t p (.recv r (.init y)) s).1.initFrom r).isSome := by
  rw [initFrom_step_recv]
  exact isSome_record_self

theorem ab_step : (step t p x s).1.ab = true ↔ s.ab = true ∨ x = .req .abandon := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · simp only [step]; split_ifs <;> simp
  · simp [step]
  · simp only [step]; split_ifs <;> simp
  · exact k.elim

theorem bcast_step :
    (step t p x s).1.bcast = true ↔
      s.bcast = true ∨ ∃ v, x = .req (.broadcast v) ∧ s.ab = false := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · cases hb : s.bcast <;> cases hab : s.ab <;> simp [step, hb, hab]
  · simp [step]
  · simp only [step]; split_ifs <;> simp
  · exact k.elim

theorem done_step_of_done (h : s.done = true) : (step t p x s).1.done = true := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · simp only [step]; split_ifs <;> exact h
  · exact h
  · simp only [step]; split_ifs <;> first | rfl | exact h
  · exact k.elim

/-- The sends of a step: `INIT v` to all when `broadcast v` is accepted. -/
theorem send_mem_step {m : Msg Value} :
    .send r m ∈ (step t p x s).2 ↔
      ∃ v, x = .req (.broadcast v) ∧ s.bcast = false ∧ s.ab = false ∧ m = .init v := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · cases hb : s.bcast <;> cases hab : s.ab <;> simp [step, hb, hab, eq_comm]
  · simp [step]
  · simp only [step]; split_ifs <;> simp
  · exact k.elim

/-- The indications of a step: `deliver (result t R)` upon a receipt of `INIT` that enables the
guard, where `R` records the received `INIT`. -/
theorem ind_mem_step {i : Ind Value} :
    .ind i ∈ (step t p x s).2 ↔
      ∃ q z, x = .recv q (.init z) ∧ s.ab = false ∧ s.done = false ∧
        Ready t (record q z s.initFrom) p ∧ i = .deliver (result t (record q z s.initFrom)) := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · simp only [step]; split_ifs <;> simp [Output.broadcast]
  · simp [step]
  · simp only [step]
    split_ifs with h
    · simp [h]
    · simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      rintro q' z' hx hab hd hr -
      obtain ⟨rfl, rfl⟩ : q = q' ∧ z = z' := by simpa using hx
      exact h ⟨hab, hd, hr⟩
  · exact k.elim

/-- A step that emits an indication emits exactly one, and sets the `done` flag. -/
theorem countP_ind_step (h : 0 < (step t p x s).2.countP fun o => o.ind?.isSome) :
    s.done = false ∧ (step t p x s).1.done = true ∧
      (step t p x s).2.countP (fun o => o.ind?.isSome) ≤ 1 := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · simp only [step] at h
    split_ifs at h <;> simp [Output.broadcast, List.countP_map, Output.ind?] at h
  · simp [step] at h
  · simp only [step] at h ⊢
    split_ifs at h ⊢ with hg
    · exact ⟨hg.2.1, rfl, by simp [Output.ind?]⟩
    · simp at h
  · exact k.elim

end Local

/-- The one-round reducing broadcast is request-quiet: `broadcast` and `abandon` emit no
indication. -/
theorem requestQuiet (t : ℕ) : (protocol P Value t).RequestQuiet := by
  intro p now r s i h
  obtain ⟨q, z, hx, -⟩ := ind_mem_step.1 h
  cases hx

/-! ### Invariants -/

section Invariants

variable {t : ℕ} {p : P} {s : (protocol P Value t).State}

theorem protocol_step {now : ℕ} {x : (protocol P Value t).In} :
    (protocol P Value t).step p now x s = step t p x s := rfl

/-- *Quiescence*: in a process that has not abandoned, an enabled delivery guard has fired. -/
theorem done_of_ready (hs : (protocol P Value t).Reachable p s) (hab : s.ab = false)
    (h : Ready t s.initFrom p) : s.done = true := by
  induction hs with
  | init => simp [Ready] at h
  | @step s now x hs ih =>
    rw [protocol_step] at hab h ⊢
    rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
    · simp only [step] at hab h ⊢
      split_ifs at hab h ⊢ <;> exact ih hab h
    · simp [step] at hab
    · simp only [step] at hab h ⊢
      split_ifs at hab h ⊢ with hg
      · rfl
      · cases hd : s.done
        · exact absurd ⟨hab, hd, h⟩ hg
        · rfl
    · exact k.elim

end Invariants

/-! ### Runs -/

section Runs

variable {t : ℕ} {ρ : Run (protocol P Value t)} {p q r : P} {τ : ℕ} {v y : Value}

/-- A process has abandoned iff it handled an `abandon` request earlier. -/
theorem ab_state : (ρ.state p τ).ab = true ↔ ∃ τ' < τ, .req .abandon ∈ ρ.input p τ' := by
  rw [Run.state_iff_exists_input (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.ab = true) (g := fun x => x = .req .abandon)
    (by simp) (fun _ _ _ => ab_step)]
  simp

/-- A process sends only `INIT v`, when it handles `broadcast v`. -/
theorem req_of_send {m : Msg Value} (h : .send r m ∈ ρ.output p τ) :
    ∃ v, m = .init v ∧ .req (.broadcast v) ∈ ρ.input p τ := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨v, rfl, -, -, rfl⟩ := send_mem_step.1 hx
  exact ⟨v, rfl, hs.mem_input⟩

/-- A process that has accepted a `broadcast` sent an `INIT` to every process earlier. -/
theorem exists_send_of_bcast (h : (ρ.state p τ).bcast = true) (r : P) :
    ∃ τ' < τ, ∃ v, .send r (.init v) ∈ ρ.output p τ' := by
  have hQ : ∀ now x (s : (protocol P Value t).State),
      ((protocol P Value t).step p now x s).1.bcast = true →
      s.bcast = true ∨ ∃ o ∈ ((protocol P Value t).step p now x s).2,
        ∃ v, o = .send r (.init v) := by
    intro now x s h
    rcases bcast_step.1 h with h | ⟨v, rfl, hab⟩
    · exact .inl h
    · cases hb : s.bcast
      · exact .inr ⟨_, send_mem_step.2 ⟨v, rfl, hb, hab, rfl⟩, v, rfl⟩
      · exact .inl rfl
  obtain ⟨τ', hτ', o, ho, v, rfl⟩ := Run.exists_output_of_state (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.bcast = true) (by simp) hQ h
  exact ⟨τ', hτ', v, ho⟩

/-- A process that has delivered emitted a `deliver` indication earlier. -/
theorem exists_ind_of_done (h : (ρ.state p τ).done = true) :
    ∃ τ' < τ, ∃ a, .ind (.deliver a) ∈ ρ.output p τ' := by
  have hQ : ∀ now x (s : (protocol P Value t).State),
      ((protocol P Value t).step p now x s).1.done = true →
      s.done = true ∨ ∃ o ∈ ((protocol P Value t).step p now x s).2,
        ∃ a, o = .ind (.deliver a) := by
    intro now x s h
    cases hd : s.done
    · rw [protocol_step] at h ⊢
      rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
      · simp only [step] at h; split_ifs at h <;> simp [hd] at h
      · simp [step, hd] at h
      · simp only [step] at h ⊢
        split_ifs at h ⊢ with hg
        · exact .inr ⟨_, List.mem_singleton_self _, _, rfl⟩
        · simp [hd] at h
      · exact k.elim
    · exact .inl rfl
  obtain ⟨τ', hτ', o, ho, a, rfl⟩ := Run.exists_output_of_state (ρ := ρ)
    (Q := fun s : (protocol P Value t).State => s.done = true) (by simp) hQ h
  exact ⟨τ', hτ', a, ho⟩

variable (t) in
/-- `initSet` soundly records the senders of `INIT x`: a sender is recorded only upon the receipt
of `INIT x` from it (only the first `INIT` of each sender is recorded). -/
theorem recordsSound_initSet (p : P) :
    (protocol P Value t).RecordsSound p Msg.init fun s x => initSet s.initFrom x where
  init _ := by simp [initSet]
  step h := by
    rw [mem_initSet] at h
    exact (initFrom_step_eq_some h).imp_left mem_initSet.2

/-- *Integrity* (at most once): a process delivers at most once (in every run). -/
theorem atMostOnce (ρ : Run (protocol P Value t)) (p : P) :
    ρ.history.AtMostOnce p (· matches .ind _) :=
  Run.atMostOnce_of_flag_output (c := fun o => o.ind?.isSome) (fun _ => rfl)
    (fun o => by rcases o with ⟨_, _⟩ | i | ⟨_, _⟩ <;> rfl)
    (fun s : (protocol P Value t).State => s.done = true) (by simp)
    (fun _ _ _ => done_step_of_done) fun _ _ _ h => by
      rw [protocol_step] at h ⊢
      obtain ⟨h₁, h₂, h₃⟩ := countP_ind_step h
      exact ⟨by simp [h₁], h₂, h₃⟩

variable (t) in
/-- **The one-round reducing broadcast sends only while active**: a process sends its `INIT` only
when it handles a `broadcast` request, and never after it has abandoned. -/
theorem sendsWhileActive :
    (protocol P Value t).SendsWhileActive (· matches .broadcast _) (· matches .abandon) := by
  intro ρ p τ q m h
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨v, rfl, -, hab, -⟩ := send_mem_step.1 hx
  refine ⟨⟨τ, le_rfl, .broadcast v, rfl, hs.mem_input⟩, fun τ' hτ' r hr hin => ?_⟩
  obtain rfl : r = .abandon := by cases r <;> first | rfl | cases hr
  have := hs.of_inputs (Q := fun s : (protocol P Value t).State => s.ab = true)
    (fun _ _ _ h => ab_step.2 (.inl h)) (ab_state.2 ⟨τ', hτ', hin⟩)
  simp [hab] at this

/-! #### Valid runs -/

variable {δ : ℕ}

/-- In a valid run, a correct process `q` whose `INIT y` is recorded by a correct process after
handling an input at time `τ` broadcast `y` before `τ`. -/
theorem exists_req_of_mem_initSet (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    {x : (protocol P Value t).In} {s : (protocol P Value t).State} (hs : ρ.Handles p τ x s)
    (h : (step t p x s).1.initFrom q = some y) :
    ∃ τ' < τ, .req (.broadcast y) ∈ ρ.input q τ' := by
  obtain ⟨τ', hτ', h'⟩ := hρ.exists_send_of_mem_get_step (recordsSound_initSet t p) hp hs hq
    (m := y) (mem_initSet.2 h)
  obtain ⟨w, hw, h''⟩ := req_of_send h'
  cases hw
  exact ⟨τ', hτ', h''⟩

/-- The receipt that produces a delivery at time `τ`, with its guard. -/
theorem exists_handles_of_ind {a : Option Value} (h : .ind (.deliver a) ∈ ρ.output p τ) :
    ∃ x s, ρ.Handles p τ x s ∧ Ready t (step t p x s).1.initFrom p ∧
      a = result t (step t p x s).1.initFrom := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨q, z, rfl, -, -, hr, ha⟩ := ind_mem_step.1 hx
  cases ha
  exact ⟨_, s, hs, by rwa [initFrom_step_recv], by rw [initFrom_step_recv]⟩

/-- **Safety**: if a correct process delivers `some x` at time `τ`, then at least `n - 3t` correct
processes broadcast `x` before `τ`: the `n - 2t` recorded `INIT x` include at most `t` from faulty
processes. -/
theorem safety (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : .ind (.deliver (some y)) ∈ ρ.output p τ) :
    ∃ S : Finset P, Fintype.card P - 3 * t ≤ #S ∧
      ∀ q ∈ S, q ∉ ρ.faulty ∧ ∃ τ' < τ, .req (.broadcast y) ∈ ρ.input q τ' := by
  obtain ⟨x, s, hs, -, ha⟩ := exists_handles_of_ind h
  have hc := le_card_initSet_of_result_eq_some ha.symm
  refine ⟨initSet (step t p x s).1.initFrom y \ ρ.faulty, ?_, fun q hq => ?_⟩
  · have := Quorum.card_sub_le_card_sdiff hρ.card_faulty_le (initSet (step t p x s).1.initFrom y)
    omega
  · obtain ⟨hq, hqF⟩ := mem_sdiff.1 hq
    exact ⟨hqF, exists_req_of_mem_initSet hρ hp hqF hs (mem_initSet.1 hq)⟩

/-- **Validity**: if `3t < n` and all correct processes that broadcast do so with `v`, every
delivery of a correct process is `some v`. The `n - t` recorded senders include `n - 2t` correct
ones, which all sent `INIT v`, and a value with `n - 2t` recorded `INIT`s has a correct sender. -/
theorem validity (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hU : ∀ q ∉ ρ.faulty, ∀ w τ, .req (.broadcast w) ∈ ρ.input q τ → w = v) (hp : p ∉ ρ.faulty)
    {a : Option Value} (h : .ind (.deliver a) ∈ ρ.output p τ) : a = some v := by
  obtain ⟨x, s, hs, hr, rfl⟩ := exists_handles_of_ind h
  set R := (step t p x s).1.initFrom
  -- every correct recorded value is `v`
  have hcorrect : ∀ q ∉ ρ.faulty, ∀ w, R q = some w → w = v := fun q hq w hw =>
    let ⟨τ', _, h'⟩ := exists_req_of_mem_initSet hρ hp hq hs hw
    hU q hq w τ' h'
  refine result_eq_some ?_ fun w hw => ?_
  · have h₁ := Quorum.card_sub_le_card_sdiff hρ.card_faulty_le (senders R)
    have h₂ : senders R \ ρ.faulty ⊆ initSet R v := fun q hq => by
      obtain ⟨hq, hqF⟩ := mem_sdiff.1 hq
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (mem_senders.1 hq)
      rw [mem_initSet, hw, hcorrect q hqF w hw]
    have h₃ := card_le_card h₂
    have h₄ := hr.2
    omega
  · obtain ⟨q, hq, hqF⟩ := Quorum.exists_notMem_of_lt_card hρ.card_faulty_le
      (S := initSet R w) (by omega)
    exact hcorrect q hqF w (mem_initSet.1 hq)

/-- *Integrity* (after broadcasting): a correct process delivers only at a time strictly after a
time at which it broadcast, since it delivers only after receiving its own `INIT`. -/
theorem afterBroadcast (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty) {a : Option Value}
    (h : .ind (.deliver a) ∈ ρ.output p τ) :
    ∃ τ' < τ, ∃ v, .req (.broadcast v) ∈ ρ.input p τ' := by
  obtain ⟨x, s, hs, hr, -⟩ := exists_handles_of_ind h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hr.1
  obtain ⟨τ', hτ', h'⟩ := exists_req_of_mem_initSet hρ hp hp hs hv
  exact ⟨τ', hτ', v, h'⟩

/-- **Latency** `δ`: if every correct process has broadcast by time `τ` and no correct process
abandons by time `max τ gst + δ`, then every correct process delivers by `max τ gst + δ`, since
the `INIT`s of the correct processes (at least `n - t`, including its own) have arrived by then
(`done_of_ready`). -/
theorem latency (hρ : ρ.Valid t δ) {τ : ℕ}
    (hb : ∀ q ∉ ρ.faulty, ∃ v, ∃ τ' ≤ τ, .req (.broadcast v) ∈ ρ.input q τ')
    (hab : ∀ q ∉ ρ.faulty, ∀ τ' ≤ max τ ρ.gst + δ, .req .abandon ∉ ρ.input q τ')
    (hp : p ∉ ρ.faulty) :
    ∃ τ' ≤ max τ ρ.gst + δ, ∃ a, .ind (.deliver a) ∈ ρ.output p τ' := by
  -- every correct process sent its `INIT` to `p` by time `τ`
  have hsent : ∀ q ∉ ρ.faulty, ∃ τ' ≤ τ, ∃ w, .send p (.init w) ∈ ρ.output q τ' := by
    intro q hq
    obtain ⟨v, τ₁, hτ₁, h₁⟩ := hb q hq
    obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h₁
    have hab' : s.ab = false := by
      cases hs' : s.ab
      · rfl
      · obtain ⟨τ₂, hτ₂, y, hy, rfl⟩ := hs.exists_input
          (Q := fun s : (protocol P Value t).State => s.ab = true)
          (g := fun y => y = .req .abandon) (by simp) (fun _ _ _ => ab_step.1) hs'
        exact absurd hy (hab q hq τ₂ (by omega))
    have hbcast : (ρ.state q (τ₁ + 1)).bcast = true :=
      hs.state_of_stable (Q := fun s : (protocol P Value t).State => s.bcast = true)
        (fun _ _ _ h => bcast_step.2 (.inl h)) (bcast_step.2 (.inr ⟨v, rfl, hab'⟩))
        (Nat.lt_succ_self τ₁)
    obtain ⟨τ₂, hτ₂, w, h₂⟩ := exists_send_of_bcast hbcast p
    exact ⟨τ₂, by omega, w, h₂⟩
  -- they have all been recorded by `p` after `max τ gst + δ`
  have hrec : ∀ q ∉ ρ.faulty, ((ρ.state p (max τ ρ.gst + δ + 1)).initFrom q).isSome := by
    intro q hq
    obtain ⟨τ', hτ', w, h⟩ := hsent q hq
    exact hρ.state_of_send hq hp h hτ'
      (Q := fun s : (protocol P Value t).State => (s.initFrom q).isSome)
      (fun _ _ _ => isSome_initFrom_step) fun _ _ => isSome_initFrom_step_recv
  have hready : Ready t (ρ.state p (max τ ρ.gst + δ + 1)).initFrom p :=
    ⟨hrec p hp, (Quorum.card_sub_le_card_compl hρ.card_faulty_le).trans
      (card_le_card fun q hq => mem_senders.2 (hrec q (mem_compl.1 hq)))⟩
  have habp : (ρ.state p (max τ ρ.gst + δ + 1)).ab = false := by
    cases h : (ρ.state p (max τ ρ.gst + δ + 1)).ab
    · rfl
    · obtain ⟨τ', hτ', h'⟩ := ab_state.1 h
      exact absurd h' (hab p hp τ' (by omega))
  obtain ⟨τ', hτ', a, h⟩ :=
    exists_ind_of_done (done_of_ready (ρ.reachable_state p _) habp hready)
  exact ⟨τ', by omega, a, h⟩

end Runs

/-- **The one-round reducing broadcast satisfies the specification** with latency `δ`, for
`3t < n`: validity (`validity`), safety (`safety`), integrity (`atMostOnce`, `afterBroadcast`) and
latency (`latency`). -/
theorem satisfies {t : ℕ} (hn : 3 * t < Fintype.card P) (δ : ℕ) :
    (protocol P Value t).Satisfies t δ (spec t δ) := by
  intro ρ hρ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hU p hp a τ h
    exact validity hρ hn (fun q hq w τ' h' => hU q hq w τ' (Run.history_reqAt.2 h')) hp
      (Run.history_indAt.1 h)
  · intro p hp x τ h
    obtain ⟨S, hS, hS'⟩ := safety hρ hp (Run.history_indAt.1 h)
    refine ⟨S, hS, fun q hq => ?_⟩
    obtain ⟨hqF, τ', hτ', h'⟩ := hS' q hq
    exact ⟨hqF, τ', hτ', Run.history_reqAt.2 h'⟩
  · intro p _
    exact atMostOnce ρ p
  · intro p hp a τ h
    obtain ⟨τ', hτ', v, h'⟩ := afterBroadcast hρ hp (Run.history_indAt.1 h)
    exact ⟨τ', hτ', v, Run.history_reqAt.2 h'⟩
  · intro τ hb hab p hp
    obtain ⟨τ', hτ', a, h⟩ := latency hρ
      (fun q hq => let ⟨v, τ', hτ', h⟩ := hb q hq; ⟨v, τ', hτ', Run.history_reqAt.1 h⟩)
      (fun q hq τ' hτ' h => hab q hq ⟨τ', hτ', Run.history_reqAt.2 h⟩) hp
    exact ⟨a, τ', hτ', Run.history_indAt.2 h⟩

/-! ### Communication -/

section Communication

variable {t : ℕ}

/-- A step sends at most as many messages as it raises the potential "`n` once the process has
broadcast": only the accepted `broadcast` sends, `INIT` to every process. -/
theorem sum_bits_one_step_add_le (p : P) (x : Input P (Msg Value) Empty (Req Value))
    (s : State P Value) :
    ((step t p x s).2.map (Output.bits fun _ => 1)).sum +
        (if s.bcast then Fintype.card P else 0) ≤
      if (step t p x s).1.bcast then Fintype.card P else 0 := by
  rcases x with (v | _) | ⟨q, ⟨z⟩⟩ | k
  · cases hb : s.bcast <;> cases hab : s.ab <;> simp [step, hb, hab, sum_map_bits_broadcast]
  · exact (Nat.zero_add _).le
  · simp only [step]; split_ifs <;> simp
  · exact k.elim

/-- **Messages**: in every run, in every window of time, a process sends at most `n` messages
(one `INIT` to each process). This is a property of the local state machine; it does not depend
on the validity of the run. -/
theorem bitsSent_one_le (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) :
    ρ.bitsSent (fun _ => 1) p a b ≤ Fintype.card P := by
  rcases le_total a b with hab | hab
  · have := Run.bitsSent_add_le (ρ := ρ) (p := p) (size := fun _ => 1)
      (f := fun s : (protocol P Value t).State => if s.bcast then Fintype.card P else 0)
      (fun _ x s => sum_bits_one_step_add_le p x s) hab
    split_ifs at this <;> omega
  · rw [Run.bitsSent_of_le hab]
    exact Nat.zero_le _

/-- **Bits**: in every run, in every window of time, a process sends at most `n (L + 1)` bits if
every value is encoded with at most `L` bits (`Msg.size`). -/
theorem bitsSent_le (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) {valueSize : Value → ℕ}
    {L : ℕ} (hL : ∀ v, valueSize v ≤ L) :
    ρ.bitsSent (Msg.size valueSize) p a b ≤ Fintype.card P * (L + 1) :=
  (Run.bitsSent_le_mul (Msg.size_le hL)).trans (Nat.mul_le_mul_right _ (bitsSent_one_le ρ p a b))

end Communication

end Cslib.Distributed.ReducingBroadcast
