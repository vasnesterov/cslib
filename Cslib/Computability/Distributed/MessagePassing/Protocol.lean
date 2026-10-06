/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Order.Defs.PartialOrder

/-! # Message-passing protocols

This file defines the syntax of event-driven message-passing protocols, in the style of the
"modules" of distributed computing textbooks: a process reacts to *inputs* (requests from its
environment, messages from other processes, and expired timers) by updating its local state and
emitting *outputs* (messages to other processes, indications to its environment, and timer
requests).

## Main definitions

* `Interface`: the types of requests and indications exchanged with the environment.
* `Input`, `Output`, `Event`: inputs and outputs of a process, and the events of an interface,
  with the accessors `Input.req?`, `Output.ind?`, `Event.req?`, `Event.ind?`.
* `Protocol P I`: a protocol for processes `P` implementing interface `I`, given by message,
  timer and state types, initial states and a per-input step function.
* `Protocol.batch`: processing an ordered list of inputs in zero time, recording the outputs
  produced by every input.
* `Protocol.RequestQuiet`: handling a request never emits an indication.
* `Protocol.Reachable`: the local states reachable from the initial state.

The executions of protocols in a partially synchronous network are defined in
`Cslib.Computability.Distributed.MessagePassing.Run`.
-/

@[expose] public section

namespace Cslib.Distributed

/-! ### Threading a state through a list -/

section foldSteps

variable {α σ β : Type*}

/-- `foldSteps f xs s` processes the elements of `xs` from left to right with `f`, threading the
state (starting from `s`) and concatenating the produced lists. -/
def foldSteps (f : α → σ → σ × List β) : List α → σ → σ × List β
  | [], s => (s, [])
  | x :: xs, s =>
    let r := f x s
    let r' := foldSteps f xs r.1
    (r'.1, r.2 ++ r'.2)

@[simp]
theorem foldSteps_nil (f : α → σ → σ × List β) (s : σ) : foldSteps f [] s = (s, []) := rfl

@[simp]
theorem foldSteps_cons (f : α → σ → σ × List β) (x : α) (xs : List α) (s : σ) :
    foldSteps f (x :: xs) s =
      ((foldSteps f xs (f x s).1).1, (f x s).2 ++ (foldSteps f xs (f x s).1).2) := rfl

theorem foldSteps_append (f : α → σ → σ × List β) (xs ys : List α) (s : σ) :
    foldSteps f (xs ++ ys) s =
      ((foldSteps f ys (foldSteps f xs s).1).1,
        (foldSteps f xs s).2 ++ (foldSteps f ys (foldSteps f xs s).1).2) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A relation between initial states, produced lists and final states that holds for the empty
list and is closed under concatenation holds for `foldSteps f` if it holds for every step. -/
theorem foldSteps_rel {R : σ → List β → σ → Prop} (nil : ∀ s, R s [] s)
    (append : ∀ {s₁ l₁ s₂ l₂ s₃}, R s₁ l₁ s₂ → R s₂ l₂ s₃ → R s₁ (l₁ ++ l₂) s₃)
    {f : α → σ → σ × List β} {xs : List α} (hf : ∀ x ∈ xs, ∀ s, R s (f x s).2 (f x s).1)
    (s : σ) : R s (foldSteps f xs s).2 (foldSteps f xs s).1 := by
  induction xs generalizing s with
  | nil => exact nil s
  | cons x xs ih =>
    exact append (hf x (by simp) s) (ih (fun y hy => hf y (by simp [hy])) _)

/-- If every step produces a list whose image under `flatMap g` does not depend on the state,
then so does `foldSteps`. -/
theorem flatMap_foldSteps {γ : Type*} {g : β → List γ} {h : α → List γ}
    {f : α → σ → σ × List β} {xs : List α} (hf : ∀ x ∈ xs, ∀ s, (f x s).2.flatMap g = h x)
    (s : σ) : (foldSteps f xs s).2.flatMap g = xs.flatMap h := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp [hf x (by simp) s, ih (fun y hy => hf y (by simp [hy]))]

/-- If every step produces lists with equal images under `flatMap g₁` and `flatMap g₂`, then so
does `foldSteps`. -/
theorem flatMap_foldSteps_eq {γ : Type*} {g₁ g₂ : β → List γ} {f : α → σ → σ × List β}
    {xs : List α} (hf : ∀ x ∈ xs, ∀ s, (f x s).2.flatMap g₁ = (f x s).2.flatMap g₂) (s : σ) :
    (foldSteps f xs s).2.flatMap g₁ = (foldSteps f xs s).2.flatMap g₂ :=
  foldSteps_rel (R := fun _ l _ => l.flatMap g₁ = l.flatMap g₂) (fun _ => rfl)
    (fun h₁ h₂ => by simp only [List.flatMap_append, h₁, h₂]) hf s

end foldSteps

/-! ### Interfaces, inputs, outputs -/

/-- The interface of a protocol (or module): the types of *requests* it accepts from its
environment (the user or a parent protocol) and of *indications* it delivers to it. -/
structure Interface where
  /-- Requests from the environment to the protocol. -/
  Req : Type
  /-- Indications from the protocol to the environment. -/
  Ind : Type

/-- An input to a process: a request `r` from the environment, a message `m` received from
process `q` (the network authenticates the sender), or the expiry of the timer with tag `k`. -/
inductive Input (P Msg Timer Req : Type*) where
  /-- A request from the environment. -/
  | req (r : Req)
  /-- Receipt of message `m` from process `q`. -/
  | recv (q : P) (m : Msg)
  /-- The timer with tag `k` has expired. -/
  | timeout (k : Timer)
deriving DecidableEq

/-- An output of a process: sending message `m` to process `q`, an indication `i` to the
environment, or a request to be woken (with `timeout k`) when the local clock reaches `T`. -/
inductive Output (P Msg Timer Ind : Type*) where
  /-- Send message `m` to process `q`. -/
  | send (q : P) (m : Msg)
  /-- An indication to the environment. -/
  | ind (i : Ind)
  /-- Set the timer with tag `k` to expire when the local clock reaches `T`. -/
  | setTimer (k : Timer) (T : ℕ)
deriving DecidableEq

/-- An event of an interface: a request or an indication. Traces of executions are lists of
events. -/
inductive Event (I : Interface) where
  /-- A request. -/
  | req (r : I.Req)
  /-- An indication. -/
  | ind (i : I.Ind)

section Accessors

variable {P Msg Timer Req Ind : Type*}

/-- The request carried by an input, if any. -/
def Input.req? : Input P Msg Timer Req → Option Req
  | .req r => some r
  | _ => none

/-- The indication carried by an output, if any. -/
def Output.ind? : Output P Msg Timer Ind → Option Ind
  | .ind i => some i
  | _ => none

@[simp]
theorem Input.req?_eq_some_iff {x : Input P Msg Timer Req} {r : Req} :
    x.req? = some r ↔ x = .req r := by
  cases x <;> simp [Input.req?]

@[simp]
theorem Output.ind?_eq_some_iff {o : Output P Msg Timer Ind} {i : Ind} :
    o.ind? = some i ↔ o = .ind i := by
  cases o <;> simp [Output.ind?]

section Event

variable {I : Interface}

/-- The request of an event, if any. -/
def Event.req? : Event I → Option I.Req
  | .req r => some r
  | .ind _ => none

/-- The indication of an event, if any. -/
def Event.ind? : Event I → Option I.Ind
  | .req _ => none
  | .ind i => some i

@[simp]
theorem Event.req?_req (r : I.Req) : (Event.req r).req? = some r := rfl

@[simp]
theorem Event.req?_ind (i : I.Ind) : (Event.ind i : Event I).req? = none := rfl

@[simp]
theorem Event.req?_eq_some_iff {e : Event I} {r : I.Req} : e.req? = some r ↔ e = .req r := by
  cases e <;> simp

@[simp]
theorem Event.ind?_req (r : I.Req) : (Event.req r : Event I).ind? = none := rfl

@[simp]
theorem Event.ind?_ind (i : I.Ind) : (Event.ind i : Event I).ind? = some i := rfl

@[simp]
theorem Event.ind?_eq_some_iff {e : Event I} {i : I.Ind} : e.ind? = some i ↔ e = .ind i := by
  cases e <;> simp

end Event

/-- The events of a single processing step, in processing order: the request handled (if the
input is a request) followed by the indications emitted. -/
def stepEvents {I : Interface} (e : Input P Msg Timer I.Req × List (Output P Msg Timer I.Ind)) :
    List (Event I) :=
  (e.1.req?.map Event.req).toList ++ e.2.filterMap fun o => o.ind?.map Event.ind

end Accessors

/-! ### Protocols -/

/-- A protocol for processes `P` implementing the interface `I`.

Each process `p` starts in state `init p` and handles its inputs one at a time: `step p now x s`
is the new state and the list of outputs produced when `p`, in state `s` and with local clock
reading `now`, handles input `x`. Static per-process parameters (e.g. proposals) are modelled by
families of protocols. -/
structure Protocol (P : Type*) (I : Interface) where
  /-- Messages exchanged between processes. -/
  Msg : Type
  /-- Timer tags. -/
  Timer : Type
  /-- Local states. -/
  State : Type
  /-- The initial state of each process. -/
  init : P → State
  /-- The step function: process, local clock reading, input, state ↦ new state and outputs. -/
  step : P → ℕ → Input P Msg Timer I.Req → State → State × List (Output P Msg Timer I.Ind)

namespace Protocol

variable {P : Type*} {I : Interface} (A : Protocol P I)

/-- The inputs of the processes of `A`. -/
abbrev In := Input P A.Msg A.Timer I.Req

/-- The outputs of the processes of `A`. -/
abbrev Out := Output P A.Msg A.Timer I.Ind

/-- Process `p` handles the inputs `xs` one after another, all with local clock reading `now`,
starting from state `s`. Returns the final state and, for each input in order, the input
together with the outputs produced while handling it. -/
def batch (p : P) (now : ℕ) : List A.In → A.State → A.State × List (A.In × List A.Out) :=
  foldSteps fun x s => ((A.step p now x s).1, [(x, (A.step p now x s).2)])

variable {A}

@[simp]
theorem batch_nil (p : P) (now : ℕ) (s : A.State) : A.batch p now [] s = (s, []) := rfl

@[simp]
theorem batch_cons (p : P) (now : ℕ) (x : A.In) (xs : List A.In) (s : A.State) :
    A.batch p now (x :: xs) s =
      ((A.batch p now xs (A.step p now x s).1).1,
        (x, (A.step p now x s).2) :: (A.batch p now xs (A.step p now x s).1).2) := rfl

theorem batch_append (p : P) (now : ℕ) (xs ys : List A.In) (s : A.State) :
    A.batch p now (xs ++ ys) s =
      ((A.batch p now ys (A.batch p now xs s).1).1,
        (A.batch p now xs s).2 ++ (A.batch p now ys (A.batch p now xs s).1).2) :=
  foldSteps_append _ _ _ _

/-- The inputs recorded by `batch` are the inputs processed. -/
@[simp]
theorem map_fst_batch (p : P) (now : ℕ) (xs : List A.In) (s : A.State) :
    (A.batch p now xs s).2.map Prod.fst = xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- An output is produced by a batch iff it is produced by one of its steps, taken in the state
reached after the preceding inputs. -/
theorem mem_flatMap_batch_iff {p : P} {now : ℕ} {xs : List A.In} {s : A.State} {o : A.Out} :
    o ∈ (A.batch p now xs s).2.flatMap Prod.snd ↔
      ∃ xs₁ x xs₂, xs = xs₁ ++ x :: xs₂ ∧ o ∈ (A.step p now x (A.batch p now xs₁ s).1).2 := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [batch_cons, List.flatMap_cons, List.mem_append, ih]
    constructor
    · rintro (h | ⟨xs₁, y, xs₂, rfl, h⟩)
      · exact ⟨[], x, xs, rfl, h⟩
      · exact ⟨x :: xs₁, y, xs₂, rfl, h⟩
    · rintro ⟨_ | ⟨z, xs₁⟩, y, xs₂, h, ho⟩
      · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
        exact .inl ho
      · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
        exact .inr ⟨xs₁, y, xs₂, rfl, ho⟩

/-- A reflexive and transitive relation that relates every state to its successors under steps
relates every state to the state reached after a batch. -/
theorem rel_batch {R : A.State → A.State → Prop} (refl : ∀ s, R s s)
    (trans : ∀ {s₁ s₂ s₃}, R s₁ s₂ → R s₂ s₃ → R s₁ s₃) {p : P}
    (hf : ∀ now x s, R s (A.step p now x s).1) (now : ℕ) (xs : List A.In) (s : A.State) :
    R s (A.batch p now xs s).1 :=
  foldSteps_rel (R := fun s _ s' => R s s')
    (f := fun x s => ((A.step p now x s).1, [(x, (A.step p now x s).2)])) refl trans
    (fun x _ s => hf now x s) s

variable (A)

/-- A protocol is *request-quiet* if handling a request never emits an indication. Composition
(`Cslib.Distributed.Protocol.compose`) routes indications that children emit while handling
messages and timers to the parent; request-quietness of the children guarantees that no
indication is lost. -/
def RequestQuiet : Prop :=
  ∀ (p : P) (now : ℕ) (r : I.Req) (s : A.State) (i : I.Ind), .ind i ∉ (A.step p now (.req r) s).2

/-- The local states of process `p` reachable from its initial state by steps (with arbitrary
inputs and clock readings). Invariants of local states are proved by induction on this
predicate. -/
inductive Reachable (p : P) : A.State → Prop
  /-- The initial state is reachable. -/
  | init : Reachable p (A.init p)
  /-- Reachability is closed under steps. -/
  | step {s : A.State} (now : ℕ) (x : A.In) : Reachable p s → Reachable p (A.step p now x s).1

variable {A}

theorem Reachable.batch {p : P} {s : A.State} (h : A.Reachable p s) (now : ℕ) (xs : List A.In) :
    A.Reachable p (A.batch p now xs s).1 :=
  rel_batch (R := fun s s' => A.Reachable p s → A.Reachable p s') (fun _ => id)
    (fun h₁ h₂ => h₂ ∘ h₁) (fun now x _ hs => hs.step now x) now xs s h

end Protocol

end Cslib.Distributed
