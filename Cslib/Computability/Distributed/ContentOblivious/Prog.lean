/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Model
public import Mathlib.Logic.Encodable.Basic

/-!
# Content-oblivious programs with arbitrary inputs

`Cslib.ContentOblivious.Algo` gives every node a natural-number ID. Many algorithms instead give
nodes an input from some other type (a leader flag, a bit to transmit, a message, …). A
`Prog I` is a deterministic content-oblivious program whose nodes start from an input of type `I`;
it runs in the model of `ContentOblivious/Model.lean` through `Prog.toAlgo`, which passes the input
encoded as a natural number (`Encodable`). An input assignment `x : V → I` then plays the role of
the ID map.
-/

@[expose] public section

namespace Cslib.ContentOblivious

/-- A deterministic content-oblivious program for two-port nodes whose initial state depends on an
input of type `I`. -/
structure Prog (I : Type*) where
  /-- Local states. -/
  State : Type
  /-- Initial state and number of pulses sent on each port at start-up. -/
  init : I → State × (Bool → ℕ)
  /-- Reaction to consuming one pulse from a port: new state, number of pulses sent on each port. -/
  recv : State → Bool → State × (Bool → ℕ)
  /-- Whether the node is willing to read a pulse from the given port (blocking receive). -/
  ready : State → Bool → Bool := fun _ _ => true
  /-- Terminated states: a terminated node never reads, changes state or sends again. -/
  terminated : State → Bool := fun _ => false

namespace Prog

variable {I : Type*} [Encodable I] [Inhabited I] (P : Prog I)

/-- Run a program in the model of `ContentOblivious/Model.lean`: the "ID" of a node is its encoded
input. -/
abbrev toAlgo : Algo where
  State := P.State
  init i := P.init ((Encodable.decode i).getD default)
  recv := P.recv
  ready := P.ready
  terminated := P.terminated
  leader _ := false

/-- A node started with the encoding of `a` starts as the program with input `a`. -/
lemma toAlgo_init_encode (a : I) : P.toAlgo.init (Encodable.encode a) = P.init a := by
  simp [toAlgo]

/-- Receptions of the induced algorithm are those of the program. -/
@[simp] lemma toAlgo_recv : P.toAlgo.recv = P.recv := rfl
/-- Readiness of the induced algorithm is that of the program. -/
@[simp] lemma toAlgo_ready : P.toAlgo.ready = P.ready := rfl
/-- Termination of the induced algorithm is that of the program. -/
@[simp] lemma toAlgo_terminated : P.toAlgo.terminated = P.terminated := rfl

variable {V : Type*} [DecidableEq V] (W : Wiring V)

/-- Reachable configurations of the program `P` on wiring `W` with input assignment `x`. -/
def Reach (x : V → I) (c : Config V P.State) : Prop :=
  Cslib.ContentOblivious.Reach W P.toAlgo (fun v => Encodable.encode (x v)) c

/-- One step of `P` (adversarial delivery of one pulse). -/
abbrev Step (c c' : Config V P.State) : Prop := Cslib.ContentOblivious.Step W P.toAlgo c c'

/-- A final configuration of `P`: no pulse can be consumed. -/
abbrev Final (c : Config V P.State) : Prop := Cslib.ContentOblivious.Final W P.toAlgo c

/-- Quiescence: no pulse is in transit. -/
abbrev Quiescent (c : Config V P.State) : Prop := Cslib.ContentOblivious.Quiescent W P.toAlgo c

/-- The initial configuration for the input assignment `x`. -/
def initCfg (x : V → I) : Config V P.State where
  st v := (P.init (x v)).1
  sent p := (P.init (x p.1)).2 p.2
  recvd _ := 0

omit [DecidableEq V] in
/-- The initial configuration of the induced algorithm is the program's initial configuration. -/
lemma initCfg_eq (x : V → I) :
    Cslib.ContentOblivious.initCfg P.toAlgo (fun v => Encodable.encode (x v)) = P.initCfg x := by
  ext <;> simp [Cslib.ContentOblivious.initCfg, initCfg]

variable {P W}

/-- The initial configuration is reachable. -/
lemma Reach.init (x : V → I) : P.Reach W x (P.initCfg x) := by
  unfold Reach; rw [← initCfg_eq]; exact Relation.ReflTransGen.refl

/-- Reachability is closed under steps. -/
lemma Reach.tail {x : V → I} {c c' : Config V P.State} (h : P.Reach W x c) (hs : P.Step W c c') :
    P.Reach W x c' := Relation.ReflTransGen.tail h hs

/-- Induction principle for reachable configurations. -/
@[elab_as_elim]
lemma Reach.induction {x : V → I} {motive : Config V P.State → Prop}
    (init : motive (P.initCfg x))
    (step : ∀ c c', P.Reach W x c → P.Step W c c' → motive c → motive c')
    {c : Config V P.State} (h : P.Reach W x c) : motive c := by
  unfold Reach at h
  induction h with
  | refl => rw [initCfg_eq]; exact init
  | tail hr hs ih => exact step _ _ hr hs ih

end Prog

end Cslib.ContentOblivious
