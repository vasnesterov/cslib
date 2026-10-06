/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Spec
public import Cslib.Computability.Distributed.Quorum
public import Mathlib.Data.Fintype.Defs

/-! # Reasoning about runs of concrete protocols

Tools for proving properties of runs (`Cslib.Distributed.Run`) of concrete event-driven
protocols, in the style of pen-and-paper proofs of distributed algorithms.

* **Handled inputs.** `Run.Handles ρ p τ x s`: at time `τ`, process `p` handles input `x` in
  local state `s`. Every output comes from some handled input (`Run.mem_output_iff_handles`), so
  facts about outputs reduce to facts about single steps of the protocol. Inputs are handled in
  order (`Run.Handles.order`, `Run.Handles.order_eq`, `Run.Handles.rel_left`,
  `Run.Handles.rel_right`).
* **Stability and invariants.** A property of local states preserved by every step, once
  established, holds forever (`Run.state_of_stable`, `Run.Handles.state_of_stable`,
  `Run.state_of_mem_output`), or as long as the steps preserve it (`Run.state_of_stable_on`,
  `Run.Handles.state_of_stable_on`); invariants preserved by the inputs actually handled
  (`Run.state_of_inputs`, `Run.Handles.of_forall_inputs`), within a time step in the states in
  which they are handled (`Run.Handles.of_handles`, `Run.state_succ_of_handles`).
* **First-time arguments.** A property of local states that fails initially was established by
  some earlier step, in a state satisfying whatever the steps establishing it require
  (`Run.exists_handles_of_state`, `Run.Handles.exists_handles`); e.g. a flag that is only set
  together with an output implies that the output happened earlier (`Run.exists_output_of_state`).
* **Recorded inputs.** A property established exactly by certain inputs and never revoked (e.g. "a
  message from `q` has been recorded") holds iff such an input was handled earlier
  (`Run.state_iff_exists_input`, `Run.exists_input_of_state`, `Run.Handles.exists_input`,
  `Run.Handles.exists_input_step`).
* **Counting events.** Counters and potentials on local states count the events of the
  history (`Run.add_countP_events`, `Run.countP_events_add_le`); in particular, a once-only flag
  shows that an event occurs at most once (`Run.atMostOnce_of_flag`, or
  `Run.atMostOnce_of_flag_output` with the events counted by outputs). For indications, the events
  of a step are counted by its indication outputs (`countP_stepEvents_eq_countP`,
  `countP_stepEvents`). Outputs are counted by potentials (`Run.countP_output_add_le`), possibly
  with a budget of one output per input of some kind (`Run.countP_output_add_le_add`).
* **Network delivery.** In valid runs, a message sent by time `T` between correct processes has
  been handled by the receiver before `max T gst + δ + 1` (`Run.Valid.exists_recv_le`,
  `Run.Valid.state_of_send`).
* **Recorded senders.** Protocols count the distinct senders of a message `inj m` in a set
  `get s m` of their local state (`Protocol.Records`, or `Protocol.RecordsSound` for first-wins
  buffers). Then a sender is recorded iff its message was received earlier
  (`Run.mem_get_state_iff`); in valid runs, a correct recorded sender sent the message earlier
  (`Run.Valid.exists_send_of_mem_get`, quorum form `Run.Valid.exists_send_of_lt_card_get`), and
  messages sent by correct processes by `T` are recorded after `max T gst + δ`
  (`Run.Valid.subset_get_of_send`).

Besides, `Output.broadcast` sends a message to every process, `Output.dest?` is the recipient
of an output, and `Output.msgTo? q` the message it sends to `q`; counting the outputs to a process
with a potential bounds the messages sent to it (`Run.countP_output_add_le`,
`countP_dest_broadcast`, `length_filterMap_msgTo?`, `count_filterMap_msgTo?_broadcast`).
Communication is also bounded by activity windows: `Protocol.SendsWhileActive` (sending only
between a start and a stop request).
-/

@[expose] public section

namespace Cslib.Distributed

variable {P : Type*} {I : Interface}

/-! ### Broadcast -/

section Broadcast

variable {Msg Timer Ind : Type*}

/-- The outputs sending `m` to every process. -/
noncomputable def Output.broadcast [Fintype P] (m : Msg) : List (Output P Msg Timer Ind) :=
  (Finset.univ : Finset P).toList.map fun q => .send q m

variable [Fintype P] {m m' : Msg} {q : P}

@[simp]
theorem Output.mem_broadcast {o : Output P Msg Timer Ind} :
    o ∈ Output.broadcast m ↔ ∃ q, o = .send q m := by
  simp [Output.broadcast, eq_comm]

-- Not `@[simp]`: `simp` already proves it from `Output.mem_broadcast` (`simpNF` linter).
theorem Output.send_mem_broadcast :
    (.send q m' : Output P Msg Timer Ind) ∈ Output.broadcast m ↔ m' = m := by
  simp

end Broadcast

/-! ### Recipients of outputs -/

section dest

variable {Msg Timer Ind : Type*}

/-- The recipient of an output, if it sends a message. -/
def Output.dest? : Output P Msg Timer Ind → Option P
  | .send q _ => some q
  | _ => none

@[simp] theorem Output.dest?_send (q : P) (m : Msg) :
    Output.dest? (.send q m : Output P Msg Timer Ind) = some q := rfl
@[simp] theorem Output.dest?_ind (i : Ind) :
    Output.dest? (.ind i : Output P Msg Timer Ind) = none := rfl
@[simp] theorem Output.dest?_setTimer (k : Timer) (T : ℕ) :
    Output.dest? (.setTimer k T : Output P Msg Timer Ind) = none := rfl

/-- A broadcast sends exactly one message to each process. -/
theorem countP_dest_broadcast [Fintype P] [DecidableEq P] (m : Msg) (q : P) :
    (Output.broadcast m : List (Output P Msg Timer Ind)).countP
      (fun o => Output.dest? o = some q) = 1 := by
  simp only [Output.broadcast, List.countP_map]
  rw [← List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ q)),
    List.count_eq_countP]
  congr 1
  funext r
  by_cases h : r = q <;> simp [h]

end dest

/-! ### Messages sent to a process -/

section msgTo

variable {Msg Timer Ind : Type*} [DecidableEq P]

/-- The message that an output sends to `q`, if it sends one. The messages sent to `q` by a list
of outputs `l` are `l.filterMap (Output.msgTo? q)`, in order. -/
def Output.msgTo? (q : P) : Output P Msg Timer Ind → Option Msg
  | .send r m => if r = q then some m else none
  | _ => none

@[simp] theorem Output.msgTo?_send (q r : P) (m : Msg) :
    Output.msgTo? q (.send r m : Output P Msg Timer Ind) = if r = q then some m else none := rfl
@[simp] theorem Output.msgTo?_ind (q : P) (i : Ind) :
    Output.msgTo? q (.ind i : Output P Msg Timer Ind) = none := rfl
@[simp] theorem Output.msgTo?_setTimer (q : P) (k : Timer) (T : ℕ) :
    Output.msgTo? q (.setTimer k T : Output P Msg Timer Ind) = none := rfl

/-- An output sends `m` to `q` iff it is `send q m`. -/
theorem Output.msgTo?_eq_some {q : P} {o : Output P Msg Timer Ind} {m : Msg} :
    o.msgTo? q = some m ↔ o = .send q m := by
  rcases o with ⟨r, m'⟩ | i | ⟨k, T⟩
  · by_cases h : r = q
    · subst h; simp [eq_comm]
    · simp [h]
  · simp
  · simp

/-- The messages sent to `q` by a list of outputs are as many as its outputs to `q`. -/
theorem length_filterMap_msgTo? (q : P) (l : List (Output P Msg Timer Ind)) :
    (l.filterMap (Output.msgTo? q)).length = l.countP fun o => o.dest? = some q := by
  rw [List.length_filterMap_eq_countP]
  congr 1
  funext o
  rcases o with ⟨r, m⟩ | i | ⟨k, T⟩
  · by_cases h : r = q <;> simp [h]
  · simp
  · simp

/-- Indications send no messages. -/
theorem filterMap_msgTo?_map_ind (q : P) (l : List Ind) :
    (l.map Output.ind : List (Output P Msg Timer Ind)).filterMap (Output.msgTo? q) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro o ho
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ho
  rfl

/-- A broadcast of `m` sends `m` to `q` exactly once. -/
theorem filterMap_msgTo?_broadcast [Fintype P] (m : Msg) (q : P) :
    (Output.broadcast m : List (Output P Msg Timer Ind)).filterMap (Output.msgTo? q) = [m] := by
  rw [← List.replicate_one, List.eq_replicate_iff]
  refine ⟨by rw [length_filterMap_msgTo?, countP_dest_broadcast], fun b hb => ?_⟩
  obtain ⟨o, ho, h⟩ := List.mem_filterMap.1 hb
  obtain ⟨r, rfl⟩ := Output.mem_broadcast.1 ho
  rw [Output.msgTo?_eq_some] at h
  cases h
  rfl

/-- A broadcast of `m` sends the message `V` to `q` once if `m = V`, and never otherwise. -/
theorem count_filterMap_msgTo?_broadcast [Fintype P] [DecidableEq Msg] [BEq Msg]
    [LawfulBEq Msg] (m V : Msg) (q : P) :
    ((Output.broadcast m : List (Output P Msg Timer Ind)).filterMap (Output.msgTo? q)).count V =
      if m = V then 1 else 0 := by
  rw [filterMap_msgTo?_broadcast, List.count_singleton]
  simp

end msgTo

/-! ### Events of a step -/

section stepEvents

variable {Msg Timer : Type*} {b : Event I → Bool}

/-- Counting the events of a step, for a kind `b` of event that contains no request, is counting
the outputs of the step that are indications of kind `b`. Here `c` is any predicate on outputs
that holds exactly for these indications (e.g. the output counterpart of `b`). -/
theorem countP_stepEvents_eq_countP {c : Output P Msg Timer I.Ind → Bool}
    (hreq : ∀ r, b (.req r) = false) (hc : ∀ o, c o = o.ind?.any fun i => b (.ind i))
    (x : Input P Msg Timer I.Req) (os : List (Output P Msg Timer I.Ind)) :
    (stepEvents (x, os)).countP b = os.countP c := by
  have h₁ : ((x.req?.map Event.req).toList : List (Event I)).countP b = 0 := by
    cases x.req? <;> simp [hreq]
  rw [stepEvents, List.countP_append, h₁, Nat.zero_add, List.countP_filterMap]
  congr 1
  funext o
  rw [hc]
  cases o.ind? <;> rfl

/-- Counting the events of a step, for a kind of event that contains every indication and no
request, is counting the indications emitted by the step. -/
theorem countP_stepEvents (hreq : ∀ r, b (.req r) = false) (hind : ∀ i, b (.ind i) = true)
    (x : Input P Msg Timer I.Req) (os : List (Output P Msg Timer I.Ind)) :
    (stepEvents (x, os)).countP b = (os.filterMap Output.ind?).length := by
  rw [countP_stepEvents_eq_countP hreq (c := fun o => o.ind?.isSome)
    (fun o => by cases o.ind? <;> simp [hind]), List.length_filterMap_eq_countP]

end stepEvents

/-! ### Batches -/

namespace Protocol

variable {A : Protocol P I} {p : P} {Q : A.State → Prop}

/-- A predicate that every step of a batch preserves, in the states reached after the preceding
inputs, holds after every prefix of the batch. -/
theorem batch_prefix_invariant {now : ℕ} :
    ∀ {xs ys zs : List A.In} {s : A.State}, xs = ys ++ zs →
      (∀ ys' y zs', xs = ys' ++ y :: zs' → Q (A.batch p now ys' s).1 →
        Q (A.step p now y (A.batch p now ys' s).1).1) →
      Q s → Q (A.batch p now ys s).1
  | _, [], _, _, _, _, h₀ => h₀
  | _, y :: ys, zs, s, rfl, hQ, h₀ => by
    rw [Protocol.batch_cons]
    exact Protocol.batch_prefix_invariant (xs := ys ++ zs) rfl
      (fun ys' y' zs' h' hq => by
        have := hQ (y :: ys') y' zs' (by simp [h'])
        simpa [Protocol.batch_cons] using this hq)
      (hQ [] y (ys ++ zs) rfl h₀)

/-- A predicate preserved by every input of a batch holds after the batch. -/
theorem batch_invariant {now : ℕ} {xs : List A.In}
    (hQ : ∀ y ∈ xs, ∀ s, Q s → Q (A.step p now y s).1) {s : A.State} (hs : Q s) :
    Q (A.batch p now xs s).1 :=
  batch_prefix_invariant (zs := []) (List.append_nil xs).symm
    (fun _ y _ h hq => hQ y (by simp [h]) _ hq) hs

/-- A property of local states preserved by every step is preserved by batches. -/
theorem batch_of_stable (hQ : ∀ now x s, Q s → Q (A.step p now x s).1) (now : ℕ)
    (xs : List A.In) {s : A.State} (h : Q s) : Q (A.batch p now xs s).1 :=
  batch_invariant (fun y _ s => hQ now y s) h

/-- If an input `x` of a batch establishes `Q` from every state satisfying a guard `G`, and the
inputs of the batch preserve `G` and `Q`, then `Q` holds after the batch (if `G` holds
initially). -/
theorem batch_of_mem {now : ℕ} {G : A.State → Prop} {xs : List A.In} {x : A.In} (hx : x ∈ xs)
    (hG : ∀ y ∈ xs, ∀ s, G s → G (A.step p now y s).1)
    (hQ : ∀ y ∈ xs, ∀ s, Q s → Q (A.step p now y s).1)
    (hxQ : ∀ s, G s → Q (A.step p now x s).1) {s : A.State} (hs : G s) :
    Q (A.batch p now xs s).1 := by
  induction xs generalizing s with
  | nil => simp at hx
  | cons y ys ih =>
    rw [batch_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact batch_invariant (fun z hz => hQ z (by simp [hz])) (hxQ s hs)
    · exact ih hx (fun z hz => hG z (by simp [hz])) (fun z hz => hQ z (by simp [hz]))
        (hG y (by simp) s hs)

/-- A counter on local states that grows at each step by the number of events of a kind
emitted by that step grows along a batch by the number of such events of the batch. -/
theorem add_countP_batch {now : ℕ} {b : Event I → Bool} {f : A.State → ℕ}
    (hf : ∀ x s, f (A.step p now x s).1 = f s + (stepEvents (x, (A.step p now x s).2)).countP b)
    (xs : List A.In) (s : A.State) :
    f (A.batch p now xs s).1 = f s + ((A.batch p now xs s).2.flatMap stepEvents).countP b := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [Protocol.batch_cons, List.flatMap_cons, List.countP_append, ih, hf]
    omega

/-- A potential on local states that grows at each step by at least the number of events of a
kind emitted by that step grows along a batch by at least the number of such events of the
batch. -/
theorem countP_batch_add_le {now : ℕ} {b : Event I → Bool} {f : A.State → ℕ}
    (hf : ∀ x s, (stepEvents (x, (A.step p now x s).2)).countP b + f s ≤ f (A.step p now x s).1)
    (xs : List A.In) (s : A.State) :
    ((A.batch p now xs s).2.flatMap stepEvents).countP b + f s ≤ f (A.batch p now xs s).1 := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    have := hf x s
    have := ih (A.step p now x s).1
    simp only [Protocol.batch_cons, List.flatMap_cons, List.countP_append]
    omega

/-- A potential on local states that grows at each step by at least the number of outputs of
that step satisfying `c`, minus one if the input satisfies `d`, grows along a batch by at least
the number of such outputs minus the number of inputs satisfying `d`. -/
theorem countP_batch_output_add_le_add {now : ℕ} {c : A.Out → Bool} {d : A.In → Bool}
    {f : A.State → ℕ}
    (hf : ∀ x s, (A.step p now x s).2.countP c + f s ≤
      f (A.step p now x s).1 + if d x then 1 else 0)
    (xs : List A.In) (s : A.State) :
    ((A.batch p now xs s).2.flatMap Prod.snd).countP c + f s ≤
      f (A.batch p now xs s).1 + xs.countP d := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    have h₁ := hf x s
    have h₂ := ih (A.step p now x s).1
    simp only [Protocol.batch_cons, List.flatMap_cons, List.countP_append, List.countP_cons]
    split_ifs at h₁ ⊢ <;> omega

/-- A potential on local states that grows at each step by at least the number of outputs of
that step satisfying `c` grows along a batch by at least the number of such outputs of the
batch. -/
theorem countP_batch_output_add_le {now : ℕ} {c : A.Out → Bool} {f : A.State → ℕ}
    (hf : ∀ x s, (A.step p now x s).2.countP c + f s ≤ f (A.step p now x s).1)
    (xs : List A.In) (s : A.State) :
    ((A.batch p now xs s).2.flatMap Prod.snd).countP c + f s ≤ f (A.batch p now xs s).1 := by
  simpa using countP_batch_output_add_le_add (d := fun _ => false) (by simpa using hf) xs s

/-- If a property of local states holds after a batch, then it held before, or some step of the
batch established it from a state satisfying `G`, provided every step establishing it does so
from a state satisfying `G`. -/
theorem batch_cases {now : ℕ} {G : A.In → A.State → Prop}
    (hQ : ∀ x s, Q (A.step p now x s).1 → Q s ∨ G x s) {xs : List A.In} {s : A.State}
    (h : Q (A.batch p now xs s).1) :
    Q s ∨ ∃ xs₁ x xs₂, xs = xs₁ ++ x :: xs₂ ∧ G x (A.batch p now xs₁ s).1 := by
  induction xs generalizing s with
  | nil => exact .inl h
  | cons x xs ih =>
    rcases ih h with h | ⟨xs₁, y, xs₂, rfl, hG⟩
    · rcases hQ x s h with h | h
      · exact .inl h
      · exact .inr ⟨[], x, xs, rfl, h⟩
    · exact .inr ⟨x :: xs₁, y, xs₂, rfl, hG⟩

end Protocol

namespace Run

variable {A : Protocol P I} {ρ : Run A} {p : P} {τ : ℕ} {x : A.In} {s : A.State}

/-! ### Handled inputs -/

variable (ρ) in
/-- `ρ.Handles p τ x s`: at time `τ`, process `p` handles the input `x` in local state `s`, i.e.
`x` occurs in the batch of time `τ` and `s` is the state reached after the inputs preceding it. -/
def Handles (p : P) (τ : ℕ) (x : A.In) (s : A.State) : Prop :=
  ∃ xs ys, ρ.input p τ = xs ++ x :: ys ∧ s = (A.batch p (ρ.clock p τ) xs (ρ.state p τ)).1

/-- A handled input is an input. -/
theorem Handles.mem_input (h : ρ.Handles p τ x s) : x ∈ ρ.input p τ := by
  obtain ⟨xs, ys, h, -⟩ := h
  simp [h]

/-- Every input is handled. -/
theorem exists_handles_of_mem_input (h : x ∈ ρ.input p τ) : ∃ s, ρ.Handles p τ x s := by
  obtain ⟨xs, ys, h⟩ := List.append_of_mem h
  exact ⟨_, xs, ys, h, rfl⟩

/-- Inputs are handled in reachable states, so invariants of reachable states apply. -/
theorem Handles.reachable (h : ρ.Handles p τ x s) : A.Reachable p s := by
  obtain ⟨xs, ys, -, rfl⟩ := h
  exact (ρ.reachable_state p τ).batch _ _

/-- The outputs of `p` at time `τ` are the outputs of the inputs it handles at time `τ`. -/
theorem mem_output_iff_handles {o : A.Out} :
    o ∈ ρ.output p τ ↔ ∃ x s, ρ.Handles p τ x s ∧ o ∈ (A.step p (ρ.clock p τ) x s).2 := by
  rw [mem_output_iff]
  constructor
  · rintro ⟨xs, x, ys, h, ho⟩
    exact ⟨x, _, ⟨xs, ys, h, rfl⟩, ho⟩
  · rintro ⟨x, s, ⟨xs, ys, h, rfl⟩, ho⟩
    exact ⟨xs, x, ys, h, ho⟩

/-- An output that handling `x` produces in every state is produced when `x` is an input. -/
theorem mem_output_of_mem_input {o : A.Out} (hx : x ∈ ρ.input p τ)
    (ho : ∀ s, o ∈ (A.step p (ρ.clock p τ) x s).2) : o ∈ ρ.output p τ := by
  obtain ⟨s, hs⟩ := exists_handles_of_mem_input hx
  exact mem_output_iff_handles.2 ⟨x, s, hs, ho s⟩

/-- An output of a handled input is an output. -/
theorem Handles.mem_output {o : A.Out} (h : ρ.Handles p τ x s)
    (ho : o ∈ (A.step p (ρ.clock p τ) x s).2) : o ∈ ρ.output p τ :=
  mem_output_iff_handles.2 ⟨x, s, h, ho⟩

/-- A predicate preserved by the steps of time `τ`, in the states in which they are handled, holds
in every state in which an input is handled at time `τ`, if it holds at the beginning of `τ`. -/
theorem Handles.of_handles {Q : A.State → Prop} (h : ρ.Handles p τ x s)
    (hQ : ∀ y s', ρ.Handles p τ y s' → Q s' → Q (A.step p (ρ.clock p τ) y s').1)
    (h₀ : Q (ρ.state p τ)) : Q s := by
  obtain ⟨xs, ys, hin, rfl⟩ := h
  exact Protocol.batch_prefix_invariant (zs := x :: ys) hin
    (fun ys' y zs' h' hq => hQ y _ ⟨ys', zs', h', rfl⟩ hq) h₀

/-- A predicate preserved by the steps of time `τ`, in the states in which they are handled, holds
at the end of time `τ` if it holds at its beginning. -/
theorem state_succ_of_handles {Q : A.State → Prop}
    (hQ : ∀ y s', ρ.Handles p τ y s' → Q s' → Q (A.step p (ρ.clock p τ) y s').1)
    (h₀ : Q (ρ.state p τ)) : Q (ρ.state p (τ + 1)) := by
  rw [state_succ]
  exact Protocol.batch_prefix_invariant (zs := []) (by simp)
    (fun ys' y zs' h' hq => hQ y _ ⟨ys', zs', h', rfl⟩ hq) h₀

/-- A predicate preserved by the inputs of time `τ` holds for every state in which an input is
handled at time `τ`, if it holds at the beginning of time `τ`. -/
theorem Handles.of_inputs {Q : A.State → Prop} (h : ρ.Handles p τ x s)
    (hQ : ∀ y ∈ ρ.input p τ, ∀ s, Q s → Q (A.step p (ρ.clock p τ) y s).1)
    (h₀ : Q (ρ.state p τ)) : Q s :=
  h.of_handles (fun y s' hy => hQ y hy.mem_input s') h₀

/-- The state at the end of time `τ` is reached from the state after handling `x` by handling
the inputs following `x`. -/
theorem Handles.exists_state_succ (h : ρ.Handles p τ x s) :
    ∃ ys, (∀ y ∈ ys, y ∈ ρ.input p τ) ∧
      ρ.state p (τ + 1) = (A.batch p (ρ.clock p τ) ys (A.step p (ρ.clock p τ) x s).1).1 := by
  obtain ⟨xs, ys, hi, rfl⟩ := h
  refine ⟨ys, fun y hy => by rw [hi]; simp [hy], ?_⟩
  rw [state_succ, hi, Protocol.batch_append, Protocol.batch_cons]

/-- Two inputs handled by `p` at the same time are the same handled input, or one of them is
handled after the other within the batch. -/
theorem Handles.order_eq {x₁ x₂ : A.In} {s₁ s₂ : A.State} (h₁ : ρ.Handles p τ x₁ s₁)
    (h₂ : ρ.Handles p τ x₂ s₂) :
    (x₁ = x₂ ∧ s₁ = s₂) ∨
      (∃ ys, s₂ = (A.batch p (ρ.clock p τ) ys (A.step p (ρ.clock p τ) x₁ s₁).1).1) ∨
      ∃ ys, s₁ = (A.batch p (ρ.clock p τ) ys (A.step p (ρ.clock p τ) x₂ s₂).1).1 := by
  obtain ⟨xs₁, ys₁, hi₁, rfl⟩ := h₁
  obtain ⟨xs₂, ys₂, hi₂, rfl⟩ := h₂
  rcases List.append_eq_append_iff.mp (hi₁.symm.trans hi₂) with ⟨as, h, h'⟩ | ⟨bs, h, h'⟩
  · subst h
    rcases as with _ | ⟨a, as⟩
    · simp only [List.nil_append, List.cons.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      simp
    · simp only [List.cons_append, List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      refine .inr (.inl ⟨as, ?_⟩)
      rw [Protocol.batch_append, Protocol.batch_cons]
  · subst h
    rcases bs with _ | ⟨b, bs⟩
    · simp only [List.nil_append, List.cons.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      simp
    · simp only [List.cons_append, List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      refine .inr (.inr ⟨bs, ?_⟩)
      rw [Protocol.batch_append, Protocol.batch_cons]

section Rel

variable {Rel : A.State → A.State → Prop} (refl : ∀ s, Rel s s)
  (trans : ∀ {s₁ s₂ s₃}, Rel s₁ s₂ → Rel s₂ s₃ → Rel s₁ s₃)
  (hstep : ∀ now x s, Rel s (A.step p now x s).1)
include refl trans hstep

/-- A reflexive and transitive relation that relates every local state of `p` to its successors
relates the state of `p` at time `τ` to every state in which `p` handles an input at time `τ`. -/
theorem Handles.rel_left (h : ρ.Handles p τ x s) : Rel (ρ.state p τ) s := by
  obtain ⟨xs, ys, -, rfl⟩ := h
  exact Protocol.rel_batch refl trans hstep _ _ _

/-- A reflexive and transitive relation that relates every local state of `p` to its successors
relates the state after an input handled at time `τ` to the state at time `τ + 1`. -/
theorem Handles.rel_right (h : ρ.Handles p τ x s) :
    Rel (A.step p (ρ.clock p τ) x s).1 (ρ.state p (τ + 1)) := by
  obtain ⟨ys, -, h⟩ := h.exists_state_succ
  rw [h]
  exact Protocol.rel_batch refl trans hstep _ _ _

/-- Two inputs handled by `p` are handled in the same state at the same time, or one of them is
handled after the other. -/
theorem Handles.order {τ₁ τ₂ : ℕ} {x₁ x₂ : A.In} {s₁ s₂ : A.State} (h₁ : ρ.Handles p τ₁ x₁ s₁)
    (h₂ : ρ.Handles p τ₂ x₂ s₂) :
    (τ₁ = τ₂ ∧ x₁ = x₂ ∧ s₁ = s₂) ∨ Rel (A.step p (ρ.clock p τ₁) x₁ s₁).1 s₂ ∨
      Rel (A.step p (ρ.clock p τ₂) x₂ s₂).1 s₁ := by
  -- inputs handled at different times
  have later {τ₁ τ₂ : ℕ} {x₁ x₂ : A.In} {s₁ s₂ : A.State} (h₁ : ρ.Handles p τ₁ x₁ s₁)
      (h₂ : ρ.Handles p τ₂ x₂ s₂) (hτ : τ₁ < τ₂) : Rel (A.step p (ρ.clock p τ₁) x₁ s₁).1 s₂ :=
    trans (h₁.rel_right refl trans hstep)
      (trans (rel_state refl trans hstep hτ) (h₂.rel_left refl trans hstep))
  rcases lt_trichotomy τ₁ τ₂ with hτ | rfl | hτ
  · exact .inr (.inl (later h₁ h₂ hτ))
  · rcases h₁.order_eq h₂ with ⟨rfl, rfl⟩ | ⟨ys, rfl⟩ | ⟨ys, rfl⟩
    · exact .inl ⟨rfl, rfl, rfl⟩
    · exact .inr (.inl (Protocol.rel_batch refl trans hstep _ _ _))
    · exact .inr (.inr (Protocol.rel_batch refl trans hstep _ _ _))
  · exact .inr (.inr (later h₂ h₁ hτ))

end Rel

/-- A quantity of local states that does not decrease along steps is, in the state in which an
input is handled at time `τ`, at least its value at time `τ`. -/
theorem Handles.le {α : Type*} [Preorder α] {f : A.State → α}
    (hf : ∀ now x s, f s ≤ f (A.step p now x s).1) (h : ρ.Handles p τ x s) :
    f (ρ.state p τ) ≤ f s :=
  h.rel_left (Rel := fun s s' => f s ≤ f s') (fun _ => le_rfl) le_trans hf

/-- A quantity of local states that does not decrease along steps is, after an input handled at
time `τ`, at most its value at time `τ + 1`. -/
theorem Handles.step_le {α : Type*} [Preorder α] {f : A.State → α}
    (hf : ∀ now x s, f s ≤ f (A.step p now x s).1) (h : ρ.Handles p τ x s) :
    f (A.step p (ρ.clock p τ) x s).1 ≤ f (ρ.state p (τ + 1)) :=
  h.rel_right (Rel := fun s s' => f s ≤ f s') (fun _ => le_rfl) le_trans hf

/-- If every step producing `o₁` also produces `o₂`, then so does every batch (e.g. a send to one
process is part of a broadcast). -/
theorem mem_output_of_forall_step {o₁ o₂ : A.Out}
    (h : ∀ now x s, o₁ ∈ (A.step p now x s).2 → o₂ ∈ (A.step p now x s).2)
    (ho : o₁ ∈ ρ.output p τ) : o₂ ∈ ρ.output p τ := by
  obtain ⟨x, s, hs, ho⟩ := mem_output_iff_handles.1 ho
  exact mem_output_iff_handles.2 ⟨x, s, hs, h _ _ _ ho⟩

/-! ### Stability -/

variable {Q : A.State → Prop}

/-- A property of local states preserved by every step is preserved over time. -/
theorem state_of_stable (hQ : ∀ now x s, Q s → Q (A.step p now x s).1) {τ' : ℕ}
    (h : Q (ρ.state p τ)) (hτ : τ ≤ τ') : Q (ρ.state p τ') :=
  monotone_state (f := Q) (fun now x s => hQ now x s) hτ h

/-- A predicate preserved by all steps at the times in `[τ₁, τ₂)` holds at time `τ₂` if it holds
at time `τ₁`. -/
theorem state_of_stable_on {τ₁ τ₂ : ℕ} (h : τ₁ ≤ τ₂)
    (hQ : ∀ τ, τ₁ ≤ τ → τ < τ₂ → ∀ y s, Q s → Q (A.step p (ρ.clock p τ) y s).1)
    (h₀ : Q (ρ.state p τ₁)) : Q (ρ.state p τ₂) := by
  induction τ₂, h using Nat.le_induction with
  | base => exact h₀
  | succ τ₂ hle ih =>
    rw [state_succ]
    exact Protocol.batch_invariant (fun y _ s hs => hQ τ₂ hle (by omega) y s hs)
      (ih fun τ h₁ h₂ => hQ τ h₁ (by omega))

/-- A predicate established by handling `x` at time `τ` and preserved by all steps at the times in
`[τ, τ')` holds at time `τ' > τ`. -/
theorem Handles.state_of_stable_on (h : ρ.Handles p τ x s)
    (hx : Q (A.step p (ρ.clock p τ) x s).1) {τ' : ℕ} (hτ : τ < τ')
    (hQ : ∀ τ'', τ ≤ τ'' → τ'' < τ' → ∀ y s, Q s → Q (A.step p (ρ.clock p τ'') y s).1) :
    Q (ρ.state p τ') := by
  obtain ⟨ys, -, hst⟩ := h.exists_state_succ
  have : Q (ρ.state p (τ + 1)) := by
    rw [hst]
    exact Protocol.batch_invariant (fun y _ s hs => hQ τ le_rfl hτ y s hs) hx
  exact Run.state_of_stable_on (τ₁ := τ + 1) (by omega)
    (fun τ'' h₁ h₂ => hQ τ'' (by omega) h₂) this

/-- A stable property established by handling an input holds at all later times. -/
theorem Handles.state_of_stable (hQ : ∀ now x s, Q s → Q (A.step p now x s).1)
    (h : ρ.Handles p τ x s) (hx : Q (A.step p (ρ.clock p τ) x s).1) {τ' : ℕ} (hτ : τ < τ') :
    Q (ρ.state p τ') :=
  h.state_of_stable_on hx hτ fun _ _ _ => hQ _

/-- An invariant of the states of `p` that holds initially and is preserved by the inputs of
`p` before time `τ` holds at time `τ`. -/
theorem state_of_inputs (h₀ : Q (A.init p))
    (hQ : ∀ τ' < τ, ∀ y ∈ ρ.input p τ', ∀ s, Q s → Q (A.step p (ρ.clock p τ') y s).1) :
    Q (ρ.state p τ) := by
  induction τ with
  | zero => exact h₀
  | succ τ ih =>
    rw [state_succ]
    exact Protocol.batch_invariant (hQ τ (by omega))
      (ih fun τ' hτ' => hQ τ' (by omega))

/-- An invariant of the states of `p` that holds initially and is preserved by the inputs of
`p` up to time `τ` holds whenever `p` handles an input at time `τ`. -/
theorem Handles.of_forall_inputs (h : ρ.Handles p τ x s) (h₀ : Q (A.init p))
    (hQ : ∀ τ' ≤ τ, ∀ y ∈ ρ.input p τ', ∀ s, Q s → Q (A.step p (ρ.clock p τ') y s).1) : Q s :=
  h.of_inputs (hQ τ le_rfl) (state_of_inputs h₀ fun τ' hτ' => hQ τ' hτ'.le)

/-- If `x` is handled at time `τ` and establishes `Q` from every state satisfying a guard `G`,
and the inputs of time `τ` preserve `G` and `Q`, then `Q` holds at the end of time `τ`. -/
theorem state_succ_of_mem {G : A.State → Prop} (hx : x ∈ ρ.input p τ)
    (hG : ∀ y ∈ ρ.input p τ, ∀ s, G s → G (A.step p (ρ.clock p τ) y s).1)
    (hQ : ∀ y ∈ ρ.input p τ, ∀ s, Q s → Q (A.step p (ρ.clock p τ) y s).1)
    (hxQ : ∀ s, G s → Q (A.step p (ρ.clock p τ) x s).1) (h₀ : G (ρ.state p τ)) :
    Q (ρ.state p (τ + 1)) := by
  rw [state_succ]
  exact Protocol.batch_of_mem hx hG hQ hxQ h₀

/-- A stable property of local states that every step producing the output `o` establishes
holds after `o` has been produced (e.g. the premise of the rule that produced `o`, if it is
monotone). -/
theorem state_of_mem_output {o : A.Out} (hQ : ∀ now x s, Q s → Q (A.step p now x s).1)
    (ho : ∀ now x s, o ∈ (A.step p now x s).2 → Q (A.step p now x s).1)
    {τ' : ℕ} (h : o ∈ ρ.output p τ) (hτ : τ < τ') : Q (ρ.state p τ') := by
  obtain ⟨x, s, hs, hx⟩ := mem_output_iff_handles.1 h
  exact hs.state_of_stable hQ (ho _ _ _ hx) hτ

/-! ### First-time arguments -/

/-- *First-time argument.* If a property of local states fails initially and every step that
establishes it does so in a state satisfying `G`, then whenever it holds, some input was handled
earlier in a state satisfying `G`. -/
theorem exists_handles_of_state {G : ℕ → A.In → A.State → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 → Q s ∨ G now x s) (h : Q (ρ.state p τ)) :
    ∃ τ' < τ, ∃ x s, ρ.Handles p τ' x s ∧ G (ρ.clock p τ') x s := by
  induction τ with
  | zero => exact absurd h hinit
  | succ τ ih =>
    rcases Protocol.batch_cases (hQ _) h with h | ⟨xs, x, ys, hin, hG⟩
    · obtain ⟨τ', hτ', hτ''⟩ := ih h
      exact ⟨τ', by omega, hτ''⟩
    · exact ⟨τ, by omega, x, _, ⟨xs, ys, hin, rfl⟩, hG⟩

/-- The *first-time argument* for the state in which an input is handled at time `τ`. -/
theorem Handles.exists_handles {G : ℕ → A.In → A.State → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 → Q s ∨ G now x s) (hs : ρ.Handles p τ x s)
    (h : Q s) : ∃ τ' ≤ τ, ∃ y s', ρ.Handles p τ' y s' ∧ G (ρ.clock p τ') y s' := by
  obtain ⟨xs, ys, hin, rfl⟩ := hs
  rcases Protocol.batch_cases (hQ _) h with h | ⟨xs₁, y, xs₂, rfl, hG⟩
  · obtain ⟨τ', hτ', hτ''⟩ := exists_handles_of_state hinit hQ h
    exact ⟨τ', hτ'.le, hτ''⟩
  · exact ⟨τ, le_rfl, y, _, ⟨xs₁, xs₂ ++ x :: ys, by simp [hin], rfl⟩, hG⟩

/-- A property of local states that fails initially and is only established by steps with an
output satisfying `O` (e.g. a flag set together with an indication) holds only after such an
output. -/
theorem exists_output_of_state {O : A.Out → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 → Q s ∨ ∃ o ∈ (A.step p now x s).2, O o)
    (h : Q (ρ.state p τ)) : ∃ τ' < τ, ∃ o ∈ ρ.output p τ', O o := by
  obtain ⟨τ', hτ', x, s, hs, o, ho, hO⟩ := exists_handles_of_state hinit hQ h
  exact ⟨τ', hτ', o, mem_output_iff_handles.2 ⟨x, s, hs, ho⟩, hO⟩

/-! ### Recorded inputs -/

/-- *Recorded inputs.* A property of local states that fails initially and is established only by
inputs satisfying `g` holds at time `τ` only if such an input was handled before `τ`. -/
theorem exists_input_of_state {g : A.In → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 → Q s ∨ g x) (h : Q (ρ.state p τ)) :
    ∃ τ' < τ, ∃ x ∈ ρ.input p τ', g x := by
  obtain ⟨τ', hτ', x, s, hs, hx⟩ := exists_handles_of_state (G := fun _ x _ => g x) hinit hQ h
  exact ⟨τ', hτ', x, hs.mem_input, hx⟩

/-- *Recorded inputs.* A property of local states that fails initially, is established exactly by
the inputs satisfying `g` and is never revoked holds at time `τ` iff such an input was handled
before `τ`. -/
theorem state_iff_exists_input {g : A.In → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 ↔ Q s ∨ g x) :
    Q (ρ.state p τ) ↔ ∃ τ' < τ, ∃ x ∈ ρ.input p τ', g x := by
  constructor
  · exact exists_input_of_state hinit fun _ _ _ h => (hQ _ _ _).1 h
  · rintro ⟨τ', hτ', x, hx, hg⟩
    obtain ⟨s, hs⟩ := exists_handles_of_mem_input hx
    exact hs.state_of_stable (fun _ _ _ h => (hQ _ _ _).2 (.inl h)) ((hQ _ _ _).2 (.inr hg)) hτ'

/-- *Recorded inputs* in the state in which an input is handled at time `τ` were handled by
time `τ`. -/
theorem Handles.exists_input {g : A.In → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 → Q s ∨ g x) (hs : ρ.Handles p τ x s) (h : Q s) :
    ∃ τ' ≤ τ, ∃ y ∈ ρ.input p τ', g y := by
  obtain ⟨τ', hτ', y, s', hs', hy⟩ := hs.exists_handles (G := fun _ x _ => g x) hinit hQ h
  exact ⟨τ', hτ', y, hs'.mem_input, hy⟩

/-- *Recorded inputs* in the state right after handling an input at time `τ` were handled by
time `τ`. -/
theorem Handles.exists_input_step {g : A.In → Prop} (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q (A.step p now x s).1 → Q s ∨ g x) (hs : ρ.Handles p τ x s)
    (h : Q (A.step p (ρ.clock p τ) x s).1) : ∃ τ' ≤ τ, ∃ y ∈ ρ.input p τ', g y := by
  rcases hQ _ _ _ h with h | h
  · exact hs.exists_input hinit hQ h
  · exact ⟨τ, le_rfl, x, hs.mem_input, h⟩

/-! ### Counting events -/

/-- A counter on local states that grows at each step by the number of events of a kind
emitted by that step counts these events in the history. -/
theorem add_countP_events {b : Event I → Bool} {f : A.State → ℕ}
    (hf : ∀ now x s,
      f (A.step p now x s).1 = f s + (stepEvents (x, (A.step p now x s).2)).countP b)
    (T : ℕ) : f (ρ.state p T) = f (A.init p) + (ρ.history.events p T).countP b := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [History.events_succ, List.countP_append, state_succ, Protocol.add_countP_batch (hf _),
      ih]
    simp [trace, steps, Nat.add_assoc]

/-- A potential on local states that grows at each step by at least the number of events of a
kind emitted by that step bounds the number of these events in the history. -/
theorem countP_events_add_le {b : Event I → Bool} {f : A.State → ℕ}
    (hf : ∀ now x s,
      (stepEvents (x, (A.step p now x s).2)).countP b + f s ≤ f (A.step p now x s).1)
    (T : ℕ) : (ρ.history.events p T).countP b + f (A.init p) ≤ f (ρ.state p T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have := Protocol.countP_batch_add_le (hf (ρ.clock p T)) (ρ.input p T) (ρ.state p T)
    rw [History.events_succ, List.countP_append, state_succ]
    simp only [history_trace, trace, steps] at ih ⊢
    omega

variable (ρ) in
/-- *Counting outputs with a budget of inputs*: if every step produces at most as many outputs
satisfying `c` as it raises a potential `f`, plus one if its input satisfies `d`, then the outputs
satisfying `c` before time `T` are bounded by the growth of `f` plus the number of inputs
satisfying `d` before `T`. -/
theorem countP_output_add_le_add {c : A.Out → Bool} {d : A.In → Bool} {f : A.State → ℕ}
    (hf : ∀ now x s, (A.step p now x s).2.countP c + f s ≤
      f (A.step p now x s).1 + if d x then 1 else 0) (T : ℕ) :
    ((List.range T).flatMap (ρ.output p)).countP c + f (A.init p) ≤
      f (ρ.state p T) + ((List.range T).flatMap (ρ.input p)).countP d := by
  induction T with
  | zero => simp [Run.state]
  | succ T ih =>
    have := Protocol.countP_batch_output_add_le_add (hf (ρ.clock p T)) (ρ.input p T)
      (ρ.state p T)
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.countP_append,
      List.countP_append, List.flatMap_singleton, List.flatMap_singleton, Run.state_succ]
    simp only [Run.output, Run.steps] at ih ⊢
    omega

variable (ρ) in
/-- *Counting outputs.* A potential on local states that grows at each step by at least the
number of outputs of that step satisfying `c` bounds the number of such outputs before time `T`
(e.g. a once-only flag bounds the number of messages sent). -/
theorem countP_output_add_le {c : A.Out → Bool} {f : A.State → ℕ}
    (hf : ∀ now x s, (A.step p now x s).2.countP c + f s ≤ f (A.step p now x s).1) (T : ℕ) :
    ((List.range T).flatMap (ρ.output p)).countP c + f (A.init p) ≤ f (ρ.state p T) := by
  simpa using ρ.countP_output_add_le_add (d := fun _ => false) (by simpa using hf) T

/-- *At most once, by a once-only flag.* If a stable property `Q` of local states (a flag) fails
initially, and every step emitting an event of kind `b` does so with `Q` unset, sets `Q`, and
emits at most one such event, then process `p` has at most one event of kind `b`. -/
theorem atMostOnce_of_flag {b : Event I → Bool} (Q : A.State → Prop) (hinit : ¬Q (A.init p))
    (hQ : ∀ now x s, Q s → Q (A.step p now x s).1)
    (hb : ∀ now x s, 0 < (stepEvents (x, (A.step p now x s).2)).countP b →
      ¬Q s ∧ Q (A.step p now x s).1 ∧ (stepEvents (x, (A.step p now x s).2)).countP b ≤ 1) :
    ρ.history.AtMostOnce p b := by
  classical
  intro T
  have := countP_events_add_le (ρ := ρ) (p := p) (b := b) (f := fun s => if Q s then 1 else 0)
    (fun now x s => by
      by_cases h : 0 < (stepEvents (x, (A.step p now x s).2)).countP b
      · obtain ⟨h₁, h₂, h₃⟩ := hb now x s h
        simp only [h₁, h₂, ↓reduceIte]
        omega
      · by_cases hs : Q s
        · simp only [hs, hQ now x s hs, ↓reduceIte]
          omega
        · simp only [hs, ↓reduceIte]
          omega) T
  simp only [hinit, ↓reduceIte] at this
  split at this <;> omega

/-- *At most once, by a once-only flag*, counting outputs: `Run.atMostOnce_of_flag` for a kind `b`
of event that contains no request, with the events of a step counted by the outputs of the step
satisfying `c`, a predicate that holds exactly for the indications of kind `b` (as in
`countP_stepEvents_eq_countP`). -/
theorem atMostOnce_of_flag_output {b : Event I → Bool} {c : A.Out → Bool}
    (hreq : ∀ r, b (.req r) = false) (hc : ∀ o, c o = o.ind?.any fun i => b (.ind i))
    (Q : A.State → Prop) (hinit : ¬Q (A.init p)) (hQ : ∀ now x s, Q s → Q (A.step p now x s).1)
    (hb : ∀ now x s, 0 < (A.step p now x s).2.countP c →
      ¬Q s ∧ Q (A.step p now x s).1 ∧ (A.step p now x s).2.countP c ≤ 1) :
    ρ.history.AtMostOnce p b :=
  atMostOnce_of_flag Q hinit hQ fun now x s => by
    rw [countP_stepEvents_eq_countP hreq hc]
    exact hb now x s

/-! ### Network delivery -/

variable {t δ : ℕ}

/-- A message sent by time `T` between correct processes is delivered by `max T gst + δ`. -/
theorem Valid.exists_recv_le (hρ : ρ.Valid t δ) {q : P} {m : A.Msg} {T : ℕ}
    (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty) (h : .send q m ∈ ρ.output p τ) (hτ : τ ≤ T) :
    ∃ τ' ≤ max T ρ.gst + δ, .recv p m ∈ ρ.input q τ' := by
  obtain ⟨τ', -, hτ', h⟩ := hρ.reliable hp hq h
  exact ⟨τ', by omega, h⟩

/-- A message sent by time `T` between correct processes has been handled by the receiver
before `max T gst + δ + 1`: a stable property established by handling it holds from then on. -/
theorem Valid.state_of_send (hρ : ρ.Valid t δ) {q : P} {m : A.Msg} {T : ℕ}
    (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty) (h : .send q m ∈ ρ.output p τ) (hτ : τ ≤ T)
    (hQ : ∀ now x s, Q s → Q (A.step q now x s).1)
    (hrecv : ∀ now s, Q (A.step q now (.recv p m) s).1) :
    Q (ρ.state q (max T ρ.gst + δ + 1)) := by
  obtain ⟨τ', hτ', h⟩ := hρ.exists_recv_le hp hq h hτ
  obtain ⟨s, hs⟩ := exists_handles_of_mem_input h
  exact hs.state_of_stable hQ (hrecv _ _) (by omega)

end Run

/-! ### Recorded senders -/

namespace Protocol

variable {A : Protocol P I} {M : Type*}

/-- `get` *soundly records senders* at process `p`: `get s m` is a set of processes from which
`p`, in local state `s`, has received the message `inj m`. Initially nothing is recorded, and a
step records a new sender `q` of `m` only upon receiving `inj m` from `q`. For example, the first
message of each sender of a certain kind (a *first-wins* buffer). -/
structure RecordsSound (A : Protocol P I) (p : P) (inj : M → A.Msg)
    (get : A.State → M → Finset P) : Prop where
  /-- Initially, no sender is recorded. -/
  init (m : M) : get (A.init p) m = ∅
  /-- A step records a new sender of `m` only upon receiving `inj m` from it. -/
  step {now : ℕ} {x : A.In} {s : A.State} {q : P} {m : M} :
    q ∈ get (A.step p now x s).1 m → q ∈ get s m ∨ x = .recv q (inj m)

/-- `get` *records senders* at process `p`: `get s m` is the set of processes from which `p`, in
local state `s`, has received the message `inj m`. Initially nothing is recorded, every receipt
of `inj m` records its sender, nothing else does, and senders are never forgotten. This is how
protocols count the distinct senders of a message (`#(get s m)`). -/
structure Records (A : Protocol P I) (p : P) (inj : M → A.Msg)
    (get : A.State → M → Finset P) : Prop where
  /-- Initially, no sender is recorded. -/
  init (m : M) : get (A.init p) m = ∅
  /-- A step records exactly the sender of a received `inj m`, in addition to the senders
  recorded before. -/
  mem_step_iff {now : ℕ} {x : A.In} {s : A.State} {q : P} {m : M} :
    q ∈ get (A.step p now x s).1 m ↔ q ∈ get s m ∨ x = .recv q (inj m)

variable {p : P} {inj : M → A.Msg} {get : A.State → M → Finset P}

theorem Records.sound (h : A.Records p inj get) : A.RecordsSound p inj get :=
  ⟨h.init, h.mem_step_iff.1⟩

end Protocol

namespace Run

variable {A : Protocol P I} {ρ : Run A} {p q : P} {τ : ℕ} {x : A.In} {s : A.State} {M : Type*}
  {inj : M → A.Msg} {get : A.State → M → Finset P} {m : M}

/-- A sender recorded at time `τ` sent its message before `τ`. -/
theorem exists_recv_of_mem_get (hR : A.RecordsSound p inj get) (h : q ∈ get (ρ.state p τ) m) :
    ∃ τ' < τ, .recv q (inj m) ∈ ρ.input p τ' := by
  obtain ⟨τ', hτ', x, s, hs, rfl⟩ := exists_handles_of_state (Q := fun s => q ∈ get s m)
    (G := fun _ x _ => x = .recv q (inj m)) (by simp [hR.init]) (fun _ _ _ h => hR.step h) h
  exact ⟨τ', hτ', hs.mem_input⟩

/-- *Recorded senders.* A sender is recorded at time `τ` iff its message was received before
`τ`. -/
theorem mem_get_state_iff (hR : A.Records p inj get) :
    q ∈ get (ρ.state p τ) m ↔ ∃ τ' < τ, .recv q (inj m) ∈ ρ.input p τ' := by
  rw [state_iff_exists_input (Q := fun s => q ∈ get s m) (g := fun x => x = .recv q (inj m))
    (by simp [hR.init]) (fun _ _ _ => hR.mem_step_iff)]
  simp

/-- Recorded senders are never forgotten. -/
theorem get_state_mono (hR : A.Records p inj get) {τ' : ℕ} (h : τ ≤ τ') :
    get (ρ.state p τ) m ⊆ get (ρ.state p τ') m := fun _ hq =>
  state_of_stable (Q := fun s => _ ∈ get s m) (fun _ _ _ h => hR.mem_step_iff.2 (.inl h)) hq h

/-- A sender recorded in the state in which an input is handled at time `τ` sent its message by
time `τ`. -/
theorem Handles.exists_recv_of_mem_get (hR : A.RecordsSound p inj get) (hs : ρ.Handles p τ x s)
    (h : q ∈ get s m) : ∃ τ' ≤ τ, .recv q (inj m) ∈ ρ.input p τ' := by
  obtain ⟨τ', hτ', y, hy, rfl⟩ := hs.exists_input (Q := fun s => q ∈ get s m)
    (g := fun x => x = .recv q (inj m)) (by simp [hR.init]) (fun _ _ _ h => hR.step h) h
  exact ⟨τ', hτ', hy⟩

/-- A sender recorded after handling an input at time `τ` sent its message by time `τ`. -/
theorem Handles.exists_recv_of_mem_get_step (hR : A.RecordsSound p inj get)
    (hs : ρ.Handles p τ x s) (h : q ∈ get (A.step p (ρ.clock p τ) x s).1 m) :
    ∃ τ' ≤ τ, .recv q (inj m) ∈ ρ.input p τ' := by
  rcases hR.step h with h | rfl
  · exact hs.exists_recv_of_mem_get hR h
  · exact ⟨τ, le_rfl, hs.mem_input⟩

variable {t δ : ℕ}

/-- In a valid run, a correct sender recorded by a correct process at time `τ` sent its message
at a time `τ'` with `τ' + 1 < τ`. -/
theorem Valid.exists_send_of_mem_get (hρ : ρ.Valid t δ) (hR : A.RecordsSound p inj get)
    (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty) (h : q ∈ get (ρ.state p τ) m) :
    ∃ τ', τ' + 1 < τ ∧ .send p (inj m) ∈ ρ.output q τ' := by
  obtain ⟨τ₁, hτ₁, h₁⟩ := exists_recv_of_mem_get hR h
  obtain ⟨τ₂, hτ₂, h₂, -⟩ := hρ.authentic hp hq h₁
  exact ⟨τ₂, by omega, h₂⟩

/-- In a valid run, a correct sender recorded by a correct process after handling an input at
time `τ` sent its message before `τ`. -/
theorem Valid.exists_send_of_mem_get_step (hρ : ρ.Valid t δ) (hR : A.RecordsSound p inj get)
    (hp : p ∉ ρ.faulty) (hs : ρ.Handles p τ x s) (hq : q ∉ ρ.faulty)
    (h : q ∈ get (A.step p (ρ.clock p τ) x s).1 m) :
    ∃ τ' < τ, .send p (inj m) ∈ ρ.output q τ' := by
  obtain ⟨τ₁, hτ₁, h₁⟩ := hs.exists_recv_of_mem_get_step hR h
  obtain ⟨τ₂, hτ₂, h₂, -⟩ := hρ.authentic hp hq h₁
  exact ⟨τ₂, by omega, h₂⟩

/-- In a valid run, if a correct process has recorded more than `t` senders of a message at time
`τ`, one of them is correct and sent the message at a time `τ'` with `τ' + 1 < τ`. -/
theorem Valid.exists_send_of_lt_card_get (hρ : ρ.Valid t δ) (hR : A.RecordsSound p inj get)
    (hp : p ∉ ρ.faulty) (h : t < (get (ρ.state p τ) m).card) :
    ∃ q ∈ get (ρ.state p τ) m, q ∉ ρ.faulty ∧
      ∃ τ', τ' + 1 < τ ∧ .send p (inj m) ∈ ρ.output q τ' := by
  obtain ⟨q, hq, hqF⟩ := Quorum.exists_notMem_of_lt_card hρ.card_faulty_le h
  exact ⟨q, hq, hqF, hρ.exists_send_of_mem_get hR hp hqF hq⟩

/-- In a valid run, a message sent by time `T` between correct processes has been recorded by
the receiver after `max T gst + δ`. -/
theorem Valid.mem_get_of_send (hρ : ρ.Valid t δ) (hR : A.Records q inj get) (hp : p ∉ ρ.faulty)
    (hq : q ∉ ρ.faulty) (h : .send q (inj m) ∈ ρ.output p τ) {T : ℕ} (hτ : τ ≤ T) :
    p ∈ get (ρ.state q (max T ρ.gst + δ + 1)) m :=
  hρ.state_of_send hp hq h hτ (Q := fun s => p ∈ get s m)
    (fun _ _ _ h => hR.mem_step_iff.2 (.inl h)) fun _ _ => hR.mem_step_iff.2 (.inr rfl)

/-- In a valid run, if the correct processes in `S` have all sent a message to the correct
process `q` by time `T`, then they are recorded by `q` after `max T gst + δ`. -/
theorem Valid.subset_get_of_send (hρ : ρ.Valid t δ) (hR : A.Records q inj get)
    (hq : q ∉ ρ.faulty) {S : Finset P} {T : ℕ}
    (hS : ∀ r ∈ S, r ∉ ρ.faulty ∧ ∃ τ ≤ T, .send q (inj m) ∈ ρ.output r τ) :
    S ⊆ get (ρ.state q (max T ρ.gst + δ + 1)) m := fun r hr =>
  let ⟨hr, _, hτ, h⟩ := hS r hr
  hρ.mem_get_of_send hR hr hq h hτ

end Run

/-! ### Activity windows -/

/-- `A.SendsWhileActive start stop`: in every run, a process sends a message only at a tick by
which it has received a `start` request, and never after a tick at which it received a `stop`
request. Used to bound communication: a process sends messages of an instance only while it
participates in it. This is a property of the local state machine; it does not depend on the
validity of the run. -/
def Protocol.SendsWhileActive {P : Type*} {I : Interface} (A : Protocol P I)
    (start stop : I.Req → Prop) : Prop :=
  ∀ (ρ : Run A) (p : P) (τ : ℕ) (q : P) (m : A.Msg), .send q m ∈ ρ.output p τ →
    (∃ τ' ≤ τ, ∃ r, start r ∧ .req r ∈ ρ.input p τ') ∧
      ∀ τ' < τ, ∀ r, stop r → .req r ∉ ρ.input p τ'

/-- `SendsWhileActive` for a weaker start predicate and a stronger stop predicate (e.g. to pass
from `(· matches .propose _)` to `fun r => ∃ v, r = .propose v`). -/
theorem Protocol.SendsWhileActive.mono {P : Type*} {I : Interface} {A : Protocol P I}
    {start stop start' stop' : I.Req → Prop} (h : A.SendsWhileActive start stop)
    (hstart : ∀ r, start r → start' r) (hstop : ∀ r, stop' r → stop r) :
    A.SendsWhileActive start' stop' := by
  intro ρ p τ q m hm
  obtain ⟨⟨τ', hτ', r, hr, hin⟩, hstop'⟩ := h ρ p τ q m hm
  exact ⟨⟨τ', hτ', r, hstart r hr, hin⟩, fun τ'' hτ'' r hr => hstop' τ'' hτ'' r (hstop r hr)⟩

end Cslib.Distributed
