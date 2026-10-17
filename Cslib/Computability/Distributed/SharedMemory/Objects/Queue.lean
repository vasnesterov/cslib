/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Stacks and queues

* `stackObj V` — an atomic stack (`push v` / `pop`; `pop` on the empty stack returns `none`);
* `queueObj V` — an atomic FIFO queue (`enq v` / `deq`; `deq` on the empty queue returns
  `none`).

Both are initially empty; the state is the list of elements (top / oldest first), and
`push` / `enq` return `none` as acknowledgement.
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- Operations of a stack. -/
inductive StackOp (V : Type) where
  | push (v : V)
  | pop
  deriving DecidableEq

/-- An atomic stack over `V` (top = head of the list). `push` returns `none`. -/
abbrev stackObj (V : Type) : ObjSpec where
  State := List V
  Op := StackOp V
  Resp := Option V
  init := []
  δ s
    | .push v => (v :: s, none)
    | .pop => (s.tail, s.head?)

@[simp] lemma stackObj_push (V : Type) (s : List V) (v : V) :
    (stackObj V).δ s (.push v) = (v :: s, none) := rfl

@[simp] lemma stackObj_pop (V : Type) (s : List V) :
    (stackObj V).δ s .pop = (s.tail, s.head?) := rfl

/-- Operations of a queue. -/
inductive FifoOp (V : Type) where
  | enq (v : V)
  | deq
  deriving DecidableEq

/-- An atomic FIFO queue over `V` (oldest = head of the list). `enq` returns `none`. -/
abbrev queueObj (V : Type) : ObjSpec where
  State := List V
  Op := FifoOp V
  Resp := Option V
  init := []
  δ s
    | .enq v => (s ++ [v], none)
    | .deq => (s.tail, s.head?)

@[simp] lemma queueObj_enq (V : Type) (s : List V) (v : V) :
    (queueObj V).δ s (.enq v) = (s ++ [v], none) := rfl

@[simp] lemma queueObj_deq (V : Type) (s : List V) :
    (queueObj V).δ s .deq = (s.tail, s.head?) := rfl

end Cslib.SharedMemory
