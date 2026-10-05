/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Run

/-! # Specifications of message-passing protocols

A specification for an interface `I` is a predicate on *histories*: the faulty processes, the
global stabilisation time, and the trace of requests and indications of every process at every
time. Specifications typically have the form "assumptions on the requests made by the
environment imply guarantees on the indications of correct processes", as for the "modules" of
distributed computing textbooks. A protocol satisfies a specification (for resilience `t` and
delay bound `δ`) if the history of each of its valid runs does.

## Main definitions

* `History P I`, `Spec P I`, `Run.history`.
* `Protocol.Satisfies`.
* Vocabulary for stating specifications: `History.Correct`, `History.ReqAt`, `History.ReqBy`,
  `History.IndAt`, `History.IndBy` ("`p` handles request `r` at/by time `τ`", "`p` emits
  indication `i` at/by time `τ`"), `History.events` (the events of a process before a time, in
  order), `History.AtMostOnce` (a process has at most one event of a given kind), and
  `History.HasRequests` (the requests of a history are prescribed).

## Main statements

* `Run.history_reqAt`, `Run.history_indAt`, `Run.history_reqBy`, `Run.history_indBy`: the events
  of the history of a run in terms of the inputs and outputs of the run (`simp` lemmas).
* `History.AtMostOnce.eq_of_mem`: two events of a kind that occurs at most once coincide.
* `History.AtMostOnce.of_countP_trace_le`: at most once, by comparison with another history.
-/

@[expose] public section

namespace Cslib.Distributed

variable {P : Type*} {I : Interface}

/-- The externally observable behaviour of a run at interface `I`. -/
structure History (P : Type*) (I : Interface) where
  /-- The faulty processes. -/
  faulty : Finset P
  /-- The global stabilisation time. -/
  gst : ℕ
  /-- The requests and indications of each process at each time, in processing order. -/
  trace : P → ℕ → List (Event I)

/-- A specification for interface `I`: a predicate on histories. -/
abbrev Spec (P : Type*) (I : Interface) := History P I → Prop

/-- The history of a run. -/
@[simps]
def Run.history {A : Protocol P I} (ρ : Run A) : History P I where
  faulty := ρ.faulty
  gst := ρ.gst
  trace := ρ.trace

/-- Protocol `A` satisfies specification `S` (for at most `t` faulty processes and post-GST
message delay bound `δ`) if the history of each valid run of `A` satisfies `S`. -/
def Protocol.Satisfies (A : Protocol P I) (t δ : ℕ) (S : Spec P I) : Prop :=
  ∀ ρ : Run A, ρ.Valid t δ → S ρ.history

/-! ### Vocabulary for specifications -/

namespace History

variable (H : History P I)

/-- Process `p` is correct, i.e. not faulty. -/
abbrev Correct (p : P) : Prop := p ∉ H.faulty

/-- Process `p` handles request `r` at time `τ`. -/
def ReqAt (p : P) (r : I.Req) (τ : ℕ) : Prop := Event.req r ∈ H.trace p τ

/-- Process `p` handles request `r` at some time `≤ τ`. -/
def ReqBy (p : P) (r : I.Req) (τ : ℕ) : Prop := ∃ τ' ≤ τ, H.ReqAt p r τ'

/-- Process `p` emits indication `i` at time `τ`. -/
def IndAt (p : P) (i : I.Ind) (τ : ℕ) : Prop := Event.ind i ∈ H.trace p τ

/-- Process `p` emits indication `i` at some time `≤ τ`. -/
def IndBy (p : P) (i : I.Ind) (τ : ℕ) : Prop := ∃ τ' ≤ τ, H.IndAt p i τ'

/-- The events of process `p` at the times before `T`, in processing order. -/
def events (p : P) (T : ℕ) : List (Event I) := (List.range T).flatMap (H.trace p)

/-- Process `p` has at most one event satisfying `b` in the whole history (counted with
multiplicity, so two equal events in the same batch count twice). For example,
`H.AtMostOnce p (· matches .ind _)` states that `p` emits at most one indication. -/
def AtMostOnce (p : P) (b : Event I → Bool) : Prop := ∀ T, (H.events p T).countP b ≤ 1

variable {H} {p : P} {r : I.Req} {i : I.Ind} {τ τ' : ℕ}

theorem ReqAt.reqBy (h : H.ReqAt p r τ) (hτ : τ ≤ τ') : H.ReqBy p r τ' := ⟨τ, hτ, h⟩

theorem ReqBy.mono (h : H.ReqBy p r τ) (hτ : τ ≤ τ') : H.ReqBy p r τ' :=
  let ⟨τ'', h₁, h₂⟩ := h
  ⟨τ'', h₁.trans hτ, h₂⟩

theorem IndAt.indBy (h : H.IndAt p i τ) (hτ : τ ≤ τ') : H.IndBy p i τ' := ⟨τ, hτ, h⟩

theorem IndBy.mono (h : H.IndBy p i τ) (hτ : τ ≤ τ') : H.IndBy p i τ' :=
  let ⟨τ'', h₁, h₂⟩ := h
  ⟨τ'', h₁.trans hτ, h₂⟩

@[simp]
theorem events_zero (p : P) : H.events p 0 = [] := rfl

theorem events_succ (p : P) (T : ℕ) : H.events p (T + 1) = H.events p T ++ H.trace p T := by
  simp [events, List.range_succ]

theorem mem_events {e : Event I} {T : ℕ} : e ∈ H.events p T ↔ ∃ τ < T, e ∈ H.trace p τ := by
  simp [events]

/-- A kind of event that occurs at most once occurs at most once in each batch. -/
theorem AtMostOnce.countP_trace_le {b : Event I → Bool} (h : H.AtMostOnce p b) (τ : ℕ) :
    (H.trace p τ).countP b ≤ 1 := by
  have := h (τ + 1)
  rw [events_succ, List.countP_append] at this
  omega

/-- Two events of a kind that occurs at most once happen at the same time and are equal. -/
theorem AtMostOnce.eq_of_mem {b : Event I → Bool} (h : H.AtMostOnce p b) {e₁ e₂ : Event I}
    {τ₁ τ₂ : ℕ} (h₁ : e₁ ∈ H.trace p τ₁) (h₂ : e₂ ∈ H.trace p τ₂) (hb₁ : b e₁) (hb₂ : b e₂) :
    τ₁ = τ₂ ∧ e₁ = e₂ := by
  -- two events at different times would be counted twice
  have key : ∀ {e₁ e₂ τ₁ τ₂}, e₁ ∈ H.trace p τ₁ → e₂ ∈ H.trace p τ₂ → b e₁ → b e₂ →
      ¬ τ₁ < τ₂ := by
    intro e₁ e₂ τ₁ τ₂ h₁ h₂ hb₁ hb₂ hlt
    have := h (τ₂ + 1)
    rw [events_succ, List.countP_append] at this
    have c₁ := List.countP_pos_iff.2 ⟨e₁, mem_events.2 ⟨τ₁, hlt, h₁⟩, hb₁⟩
    have c₂ := List.countP_pos_iff.2 ⟨e₂, h₂, hb₂⟩
    omega
  obtain rfl : τ₁ = τ₂ := by
    rcases lt_trichotomy τ₁ τ₂ with hlt | heq | hgt
    · exact absurd hlt (key h₁ h₂ hb₁ hb₂)
    · exact heq
    · exact absurd hgt (key h₂ h₁ hb₂ hb₁)
  refine ⟨rfl, ?_⟩
  by_contra hne
  have := h.countP_trace_le τ₁
  rw [List.countP_eq_length_filter] at this
  have m₁ : e₁ ∈ (H.trace p τ₁).filter b := List.mem_filter.2 ⟨h₁, hb₁⟩
  have m₂ : e₂ ∈ (H.trace p τ₁).filter b := List.mem_filter.2 ⟨h₂, hb₂⟩
  match hl : (H.trace p τ₁).filter b, m₁, m₂ with
  | [_], m₁, m₂ => simp_all
  | [], m₁, _ => simp at m₁
  | _ :: _ :: _, _, _ => simp [hl] at this

end History

namespace Run

variable {A : Protocol P I} {ρ : Run A} {p : P} {τ : ℕ}

@[simp]
theorem history_reqAt {r : I.Req} : ρ.history.ReqAt p r τ ↔ .req r ∈ ρ.input p τ :=
  req_mem_trace

@[simp]
theorem history_indAt {i : I.Ind} : ρ.history.IndAt p i τ ↔ .ind i ∈ ρ.output p τ :=
  ind_mem_trace

@[simp]
theorem history_reqBy {r : I.Req} : ρ.history.ReqBy p r τ ↔ ∃ τ' ≤ τ, .req r ∈ ρ.input p τ' := by
  simp [History.ReqBy]

@[simp]
theorem history_indBy {i : I.Ind} :
    ρ.history.IndBy p i τ ↔ ∃ τ' ≤ τ, .ind i ∈ ρ.output p τ' := by
  simp [History.IndBy]

end Run

/-! ### Requests of histories -/

/-- The requests of history `H` are given by `env`: at time `τ`, process `p` handles exactly the
requests `env p τ`, in this order. -/
def History.HasRequests (H : History P I) (env : P → ℕ → List I.Req) : Prop :=
  ∀ p τ, (H.trace p τ).filterMap Event.req? = env p τ

theorem History.HasRequests.reqAt_iff {H : History P I} {env : P → ℕ → List I.Req}
    (h : H.HasRequests env) {p : P} {r : I.Req} {τ : ℕ} : H.ReqAt p r τ ↔ r ∈ env p τ := by
  rw [← h p τ, History.ReqAt, List.mem_filterMap]
  simp

/-! ### Counting events -/

/-- Counting the events of a kind that contains no indication is counting requests. -/
theorem Event.countP_eq_countP_filterMap_req? {b : Event I → Bool}
    (hb : ∀ i, b (.ind i) = false) (l : List (Event I)) :
    l.countP b = (l.filterMap Event.req?).countP fun r => b (.req r) := by
  rw [List.countP_filterMap]
  congr 1
  funext e
  cases e <;> simp [hb]

/-- A list of events has at least as many events of a kind as it has indications of that
kind. -/
theorem Event.countP_filterMap_ind?_le (b : Event I → Bool) (l : List (Event I)) :
    (l.filterMap Event.ind?).countP (fun i => b (.ind i)) ≤ l.countP b := by
  rw [List.countP_filterMap]
  refine List.countP_mono_left fun e _ h => ?_
  rcases e with r | i
  · simp at h
  · exact h

/-- If, at every time, process `p` has at most as many events satisfying `b` in `H` as events
satisfying `b'` in `H'`, and at most one of the latter, then also at most one of the former. -/
theorem History.AtMostOnce.of_countP_trace_le {H : History P I} {p : P} {I' : Interface}
    {H' : History P I'} {b : Event I → Bool} {b' : Event I' → Bool} (h' : H'.AtMostOnce p b')
    (h : ∀ τ, (H.trace p τ).countP b ≤ (H'.trace p τ).countP b') : H.AtMostOnce p b := by
  intro T
  refine le_trans ?_ (h' T)
  induction T with
  | zero => simp
  | succ T ih =>
    rw [History.events_succ, History.events_succ, List.countP_append, List.countP_append]
    have := h T
    omega

end Cslib.Distributed
