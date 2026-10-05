/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Protocol
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find

/-! # Runs of message-passing protocols in partial synchrony

We model the partially synchronous Byzantine message-passing system with discrete real time `ℕ`
and a per-tick semantics. A run fixes the set of faulty processes, the global stabilisation time
`gst`, the local clocks, and, for every process `p` and time `τ`, an ordered list `input p τ`
of inputs that `p` handles at time `τ` (in zero time, one after another). Everything else
(local states, outputs, traces) is determined by the protocol. Validity of a run constrains
the inputs of correct processes (network and timers) and the clocks; requests from the
environment are unconstrained, and faulty processes are arbitrary.

## Main definitions

* `Run A`: a run of protocol `A`, with derived `Run.state`, `Run.steps`, `Run.output`,
  `Run.trace`.
* `Run.Valid t δ`: at most `t` faulty processes; clocks are monotone and advance at rate `1`
  after GST; the network between correct processes is authenticated, reliable, and delivers
  a message sent at time `τ` within `(τ, max τ gst + δ]`; timers expire exactly when the local
  clock first reaches their deadline.

## Main statements

* `Run.mem_output_iff`: outputs at time `τ` are produced by individual steps of the batch.
* `Run.filterMap_req?_trace`, `Run.filterMap_ind?_trace`: the requests and indications of the
  trace are those of the inputs and outputs.
* `Run.state_congr`, `Run.output_congr`: states and outputs depend only on earlier inputs.
* `Run.reachable_state`, `Run.rel_state`, `Run.monotone_state`: invariants, relations and
  monotone quantities of states.
* `Run.Valid.clock_add`, `Run.Valid.timeout_mem_input`, `Run.Valid.le_of_expires`,
  `Run.Valid.eq_of_expires`, `Run.Valid.exists_timeout_mem_input`: clocks and timers after GST.

## Corner cases of the model

See the docstring of `Run.Valid`: for `δ = 0` there are no messages between correct processes
after GST; timers cannot be cancelled and fire once per setting. Valid runs exist for every
protocol, every environment and every `δ > 0` (`Protocol.exists_valid_run`, in
`Cslib.Computability.Distributed.MessagePassing.Existence`), so `Protocol.Satisfies` is not
vacuous.
-/

@[expose] public section

namespace Cslib.Distributed

variable {P : Type*} {I : Interface}

/-- A run of protocol `A`: the faulty processes, the global stabilisation time, the local
clocks (`clock p τ` is the reading of `p`'s clock at real time `τ`), and the inputs (`input p τ`
is the ordered list of inputs handled by `p` at real time `τ`). -/
structure Run (A : Protocol P I) where
  /-- The (Byzantine) faulty processes. -/
  faulty : Finset P
  /-- The global stabilisation time. -/
  gst : ℕ
  /-- The local clocks. -/
  clock : P → ℕ → ℕ
  /-- The inputs handled by each process at each time, in processing order. -/
  input : P → ℕ → List A.In

namespace Run

variable {A : Protocol P I} (ρ : Run A)

/-- The local state of `p` at time `τ`, before handling the inputs of time `τ`. -/
def state (p : P) : ℕ → A.State
  | 0 => A.init p
  | τ + 1 => (A.batch p (ρ.clock p τ) (ρ.input p τ) (state p τ)).1

/-- The steps taken by `p` at time `τ`: each input handled at time `τ` together with the
outputs produced while handling it. -/
def steps (p : P) (τ : ℕ) : List (A.In × List A.Out) :=
  (A.batch p (ρ.clock p τ) (ρ.input p τ) (ρ.state p τ)).2

/-- The outputs of `p` at time `τ`, in order. -/
def output (p : P) (τ : ℕ) : List A.Out :=
  (ρ.steps p τ).flatMap Prod.snd

/-- The trace of `p` at time `τ`: the requests handled and indications emitted by `p` at time
`τ`, in processing order. -/
def trace (p : P) (τ : ℕ) : List (Event I) :=
  (ρ.steps p τ).flatMap stepEvents

/-- `ρ.Expires p τ' T τ`: a timer set by `p` at time `τ'` with deadline `T` (in local time)
expires at time `τ`, i.e. `τ` is the first time after `τ'` at which `p`'s clock reads at
least `T`. -/
def Expires (p : P) (τ' T τ : ℕ) : Prop :=
  τ' < τ ∧ T ≤ ρ.clock p τ ∧ ∀ τ'', τ' < τ'' → τ'' < τ → ρ.clock p τ'' < T

/-- Validity of a run for resilience `t` and post-GST message delay bound `δ`.

Validity constrains neither the requests of the environment nor the faulty processes. Corner
cases:
* `δ = 0`: `reliable` cannot hold for a message sent between correct processes at a time
  `τ ≥ gst` (it would have to be delivered strictly after `τ` and by `max τ gst + 0 = τ`), so in
  valid runs correct processes send no messages to each other after GST, and liveness
  properties may hold vacuously. Statements about liveness should assume `0 < δ`.
* Timers cannot be cancelled: every `setTimer k T` of a correct process makes `timeout k` occur
  at the first tick after the setting at which the local clock reads at least `T` (at the next
  tick if the deadline has already been reached). A tag that is set again fires once for each
  setting (`timer` only constrains membership, so two settings expiring at the same tick may
  produce a single `timeout k`, and a batch may contain `timeout k` several times). Protocols
  that reuse timer tags must therefore tolerate stale timeouts.

Valid runs exist for every protocol, every set of at most `t` faulty processes, every GST, every
`δ > 0` and every schedule of requests (`Protocol.exists_valid_run`). -/
structure Valid (t δ : ℕ) : Prop where
  /-- At most `t` processes are faulty. -/
  card_faulty_le : ρ.faulty.card ≤ t
  /-- Local clocks are monotone. -/
  clock_mono (p : P) : Monotone (ρ.clock p)
  /-- After GST, local clocks advance by exactly one unit per tick. -/
  clock_succ {p : P} {τ : ℕ} : ρ.gst ≤ τ → ρ.clock p (τ + 1) = ρ.clock p τ + 1
  /-- Authenticity: a message from a correct process was sent by it, strictly earlier. -/
  authentic {p q : P} {m : A.Msg} {τ : ℕ} : p ∉ ρ.faulty → q ∉ ρ.faulty →
    .recv q m ∈ ρ.input p τ → ∃ τ' < τ, .send p m ∈ ρ.output q τ'
  /-- Reliability and timeliness: a message sent at `τ` between correct processes is delivered
  strictly after `τ` and no later than `max τ gst + δ`. -/
  reliable {p q : P} {m : A.Msg} {τ : ℕ} : p ∉ ρ.faulty → q ∉ ρ.faulty →
    .send q m ∈ ρ.output p τ → ∃ τ', τ < τ' ∧ τ' ≤ max τ ρ.gst + δ ∧ .recv p m ∈ ρ.input q τ'
  /-- Timers of correct processes expire exactly when their deadline is first reached. -/
  timer {p : P} {k : A.Timer} {τ : ℕ} : p ∉ ρ.faulty →
    (.timeout k ∈ ρ.input p τ ↔ ∃ τ' T, .setTimer k T ∈ ρ.output p τ' ∧ ρ.Expires p τ' T τ)

/-! ### Basic API -/

variable {ρ}

@[simp]
theorem state_zero (p : P) : ρ.state p 0 = A.init p := rfl

theorem state_succ (p : P) (τ : ℕ) :
    ρ.state p (τ + 1) = (A.batch p (ρ.clock p τ) (ρ.input p τ) (ρ.state p τ)).1 := rfl

@[simp]
theorem map_fst_steps (p : P) (τ : ℕ) : (ρ.steps p τ).map Prod.fst = ρ.input p τ :=
  Protocol.map_fst_batch ..

/-- An output of `p` at time `τ` is produced by handling some input `x` of the batch of time
`τ`, in the state reached after handling the inputs preceding `x`. -/
theorem mem_output_iff {p : P} {τ : ℕ} {o : A.Out} :
    o ∈ ρ.output p τ ↔ ∃ xs x ys, ρ.input p τ = xs ++ x :: ys ∧
      o ∈ (A.step p (ρ.clock p τ) x (A.batch p (ρ.clock p τ) xs (ρ.state p τ)).1).2 :=
  Protocol.mem_flatMap_batch_iff

theorem req_mem_trace {p : P} {τ : ℕ} {r : I.Req} :
    Event.req r ∈ ρ.trace p τ ↔ Input.req r ∈ ρ.input p τ := by
  rw [← map_fst_steps, trace]
  simp only [List.mem_flatMap, stepEvents, List.mem_append, Option.mem_toList,
    Option.map_eq_some_iff, Input.req?_eq_some_iff, List.mem_filterMap, Output.ind?_eq_some_iff,
    List.mem_map]
  constructor
  · rintro ⟨e, he, ⟨r', h', h⟩ | ⟨o, -, i, -, h⟩⟩
    · cases h; exact ⟨e, he, h'⟩
    · cases h
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, .inl ⟨r, h, rfl⟩⟩

theorem ind_mem_trace {p : P} {τ : ℕ} {i : I.Ind} :
    Event.ind i ∈ ρ.trace p τ ↔ Output.ind i ∈ ρ.output p τ := by
  simp only [trace, output, List.mem_flatMap, stepEvents, List.mem_append, Option.mem_toList,
    Option.map_eq_some_iff, List.mem_filterMap, Output.ind?_eq_some_iff]
  constructor
  · rintro ⟨e, he, ⟨r, -, h⟩ | ⟨o, ho, i', rfl, h⟩⟩
    · cases h
    · cases h; exact ⟨e, he, ho⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, .inr ⟨_, h, i, rfl, rfl⟩⟩

variable (ρ) in
/-- The requests in the trace of a run are the requests among its inputs, in order. -/
theorem filterMap_req?_trace (p : P) (τ : ℕ) :
    (ρ.trace p τ).filterMap Event.req? = (ρ.input p τ).filterMap Input.req? := by
  rw [← map_fst_steps, trace]
  induction ρ.steps p τ with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨x, os⟩ := e
    have hinds : (os.filterMap fun o => o.ind?.map Event.ind).filterMap Event.req? = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro e he
      obtain ⟨o, -, ho⟩ := List.mem_filterMap.1 he
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 ho
      rfl
    simp only [List.flatMap_cons, List.filterMap_append, stepEvents, hinds, List.append_nil, ih,
      List.map_cons]
    cases x <;> rfl

variable (ρ) in
/-- The indications in the trace of a run are the indications among its outputs, in order. -/
theorem filterMap_ind?_trace (p : P) (τ : ℕ) :
    (ρ.trace p τ).filterMap Event.ind? = (ρ.output p τ).filterMap Output.ind? := by
  rw [trace, output]
  induction ρ.steps p τ with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨x, os⟩ := e
    have hos : (os.filterMap fun o => o.ind?.map Event.ind).filterMap Event.ind? =
        os.filterMap Output.ind? := by
      rw [List.filterMap_filterMap]
      congr 1
      funext o
      cases o.ind? <;> rfl
    have hreq : ((x.req?.map Event.req).toList : List (Event I)).filterMap Event.ind? = [] := by
      cases x.req? <;> rfl
    simp only [List.flatMap_cons, List.filterMap_append, stepEvents, hos, hreq, ih,
      List.nil_append]

section congr

variable {ρ' : Run A} {p : P} {n : ℕ}

/-- The state of a process at time `n` depends only on its clock readings and inputs before
`n`. -/
theorem state_congr (hc : ∀ τ < n, ρ.clock p τ = ρ'.clock p τ)
    (hi : ∀ τ < n, ρ.input p τ = ρ'.input p τ) : ρ.state p n = ρ'.state p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [state_succ, state_succ, hc n (by omega), hi n (by omega),
      ih (fun τ h => hc τ (by omega)) (fun τ h => hi τ (by omega))]

/-- The steps of a process at time `n` depend only on its clock readings and inputs up to
`n`. -/
theorem steps_congr (hc : ∀ τ ≤ n, ρ.clock p τ = ρ'.clock p τ)
    (hi : ∀ τ ≤ n, ρ.input p τ = ρ'.input p τ) : ρ.steps p n = ρ'.steps p n := by
  rw [steps, steps, hc n le_rfl, hi n le_rfl,
    state_congr (fun τ h => hc τ h.le) (fun τ h => hi τ h.le)]

/-- The outputs of a process at time `n` depend only on its clock readings and inputs up to
`n`. -/
theorem output_congr (hc : ∀ τ ≤ n, ρ.clock p τ = ρ'.clock p τ)
    (hi : ∀ τ ≤ n, ρ.input p τ = ρ'.input p τ) : ρ.output p n = ρ'.output p n := by
  rw [output, output, steps_congr hc hi]

end congr

/-- Local states of a run are reachable. -/
theorem reachable_state (p : P) (τ : ℕ) : A.Reachable p (ρ.state p τ) := by
  induction τ with
  | zero => exact .init
  | succ τ ih => exact ih.batch _ _

/-- A reflexive and transitive relation that relates every local state of `p` to its successors
relates the states of `p` at earlier and later times. -/
theorem rel_state {p : P} {Rel : A.State → A.State → Prop} (refl : ∀ s, Rel s s)
    (trans : ∀ {s₁ s₂ s₃}, Rel s₁ s₂ → Rel s₂ s₃ → Rel s₁ s₃)
    (hstep : ∀ now x s, Rel s (A.step p now x s).1) {τ τ' : ℕ} (h : τ ≤ τ') :
    Rel (ρ.state p τ) (ρ.state p τ') := by
  induction τ', h using Nat.le_induction with
  | base => exact refl _
  | succ τ' _ ih =>
    rw [state_succ]
    exact trans ih (Protocol.rel_batch refl trans hstep _ _ _)

/-- A quantity of local states that does not decrease along steps does not decrease over
time. -/
theorem monotone_state {α : Type*} [Preorder α] {f : A.State → α} {p : P}
    (hf : ∀ now x s, f s ≤ f (A.step p now x s).1) : Monotone fun τ => f (ρ.state p τ) :=
  fun _ _ => rel_state (Rel := fun s s' => f s ≤ f s') (fun _ => le_rfl) le_trans hf

/-! ### Clocks and timers in valid runs -/

variable {t δ : ℕ}

/-- After GST, local clocks advance at rate `1`. -/
theorem Valid.clock_add (hρ : ρ.Valid t δ) {p : P} {τ : ℕ} (hτ : ρ.gst ≤ τ) (d : ℕ) :
    ρ.clock p (τ + d) = ρ.clock p τ + d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [← Nat.add_assoc, hρ.clock_succ (by omega), ih, Nat.add_assoc]

/-- After GST, a timer of a correct process set at time `τ` with deadline `T` expires at time
`τ + max 1 (T - clock p τ)`. -/
theorem Valid.timeout_mem_input (hρ : ρ.Valid t δ) {p : P} (hp : p ∉ ρ.faulty) {τ T : ℕ}
    {k : A.Timer} (hτ : ρ.gst ≤ τ) (hk : .setTimer k T ∈ ρ.output p τ) :
    .timeout k ∈ ρ.input p (τ + max 1 (T - ρ.clock p τ)) := by
  refine (hρ.timer hp).2 ⟨τ, T, hk, by omega, by rw [hρ.clock_add hτ]; omega, ?_⟩
  intro τ'' h₁ h₂
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [Nat.add_assoc, hρ.clock_add hτ]
  omega

/-- After GST, a timer of duration `D` set at time `τ'` does not expire before `τ' + D`. -/
theorem Valid.le_of_expires (hρ : ρ.Valid t δ) {p : P} {τ τ' D : ℕ} (hτ' : ρ.gst ≤ τ')
    (h : ρ.Expires p τ' (ρ.clock p τ' + D) τ) : τ' + D ≤ τ := by
  obtain ⟨h₁, h₂, -⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [Nat.add_assoc, hρ.clock_add hτ'] at h₂
  omega

/-- After GST, a timer of duration `D > 0` set at time `τ'` expires exactly at `τ' + D`. -/
theorem Valid.eq_of_expires (hρ : ρ.Valid t δ) {p : P} {τ τ' D : ℕ} (hτ' : ρ.gst ≤ τ')
    (hD : 0 < D) (h : ρ.Expires p τ' (ρ.clock p τ' + D) τ) : τ = τ' + D := by
  have hle := hρ.le_of_expires hτ' h
  obtain ⟨-, -, h₃⟩ := h
  by_contra hne
  have := h₃ (τ' + D) (by omega) (by omega)
  rw [hρ.clock_add hτ'] at this
  omega

/-- A timer of duration `D > 0` set by a correct process at time `τ'` expires at some time in
`(τ', max τ' gst + D]`. -/
theorem Valid.exists_timeout_mem_input (hρ : ρ.Valid t δ) {p : P} (hp : p ∉ ρ.faulty)
    {τ' D : ℕ} {k : A.Timer} (hD : 0 < D) (hk : .setTimer k (ρ.clock p τ' + D) ∈ ρ.output p τ') :
    ∃ τ, τ' < τ ∧ τ ≤ max τ' ρ.gst + D ∧ .timeout k ∈ ρ.input p τ := by
  classical
  have hex : ∃ τ, τ' < τ ∧ ρ.clock p τ' + D ≤ ρ.clock p τ := by
    refine ⟨max τ' ρ.gst + D, by omega, ?_⟩
    rw [hρ.clock_add (le_max_right _ _)]
    have := hρ.clock_mono p (le_max_left τ' ρ.gst)
    omega
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (hρ.timer hp).2 ⟨τ', _, hk, ?_⟩⟩
  · refine Nat.find_min' hex ⟨by omega, ?_⟩
    rw [hρ.clock_add (le_max_right _ _)]
    have := hρ.clock_mono p (le_max_left τ' ρ.gst)
    omega
  · refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun τ'' h₁ h₂ => ?_⟩
    have := Nat.find_min hex h₂
    simp only [not_and, not_le] at this
    exact this h₁

end Run

end Cslib.Distributed
