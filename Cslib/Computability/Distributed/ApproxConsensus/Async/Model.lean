/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Asynchronous message passing on a directed graph (Byzantine or crash faults)

The system model of Sakavalas–Tseng–Vaidya (PODC 2020, Section 2), also used for the crash-fault
results of Tseng–Vaidya (PODC 2015, Section 4).

* Nodes `V` (finite), communication digraph `G`: node `x` can send to `y` iff `G.Adj x y`
  (self-loops are ignored). Every node knows `G` (the algorithm may depend on it).
* A deterministic event-driven algorithm (`Algorithm V M S`): local states `S`, messages `M`;
  `start x input` gives the initial state and the initial messages, `recv y s x m` processes a
  message `m` received from in-neighbour `x`, `out y s` is the (optional) output. A node's
  first output is irrevocable (`Config.dec`).
* Links are reliable FIFO channels with arbitrary (adversarial, finite) delays: a `deliver x y`
  event delivers the oldest message in transit on `x → y`. FIFO channels only restrict the
  adversary, so impossibility results in this model also hold for non-FIFO links.
* A static set `B` of faulty nodes (`run A G B inp ev`). They take no steps and have no channels:
  at any time the adversary may make a faulty `x` deliver an arbitrary message `m` to an
  out-neighbour `y` (`byz x y m`). Without `byz` events the faulty nodes are *initially dead*
  (crashed before the start). The event sequence is arbitrary (full-information adversary,
  unbounded delays).
* `Fair`: on every link between correct nodes, a non-empty channel is eventually served.
* `SolvesOn I A G f ε` (Definition 1 of [STV20]): asynchronous approximate Byzantine consensus
  with at most `f` faults for inputs in `I`.
-/

@[expose] public section

open Finset

namespace Cslib.ApproxConsensus.Async

/-- A deterministic asynchronous message-passing algorithm. -/
structure Algorithm (V M S : Type*) where
  /-- Initial state and initial messages `(destination, message)` of a node with given input. -/
  start : V → ℝ → S × List (V × M)
  /-- `recv y s x m`: node `y` in state `s` processes `m` received from `x`; returns the new
  state and the messages sent. -/
  recv : V → S → V → M → S × List (V × M)
  /-- The output of a node in a given state, if any. -/
  out : V → S → Option ℝ

/-- Global configuration: local states, FIFO channel contents, (irrevocable) decisions. -/
structure Config (V M S : Type*) where
  /-- Local states. -/
  st : V → S
  /-- `chan x y`: the messages in transit on the link `x → y`, oldest first. -/
  chan : V → V → List M
  /-- The (irrevocable) decisions. -/
  dec : V → Option ℝ

/-- Events of an execution. -/
inductive Event (V M : Type*) where
  /-- Deliver the oldest message in transit on the link `x → y`. -/
  | deliver (x y : V)
  /-- Byzantine node `x` delivers `m` to `y`. -/
  | byz (x y : V) (m : M)
  /-- Nothing happens. -/
  | skip

variable {V M S : Type*} [DecidableEq V]

section Semantics

variable (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj] (B : Finset V)

/-- The messages of the list `outs` (sent by `y`) that are put on the link `y → b`: only links of
`G` between distinct nodes, and only to correct nodes (messages to Byzantine nodes are
irrelevant: the adversary knows everything). -/
def sendTo (y : V) (outs : List (V × M)) (b : V) : List M :=
  if b ∉ B ∧ G.Adj y b ∧ y ≠ b then (outs.filter fun o => o.1 = b).map Prod.snd else []

/-- Correct node `y` processes the message `m` from `x`. -/
def process (C : Config V M S) (y x : V) (m : M) : Config V M S :=
  let r := A.recv y (C.st y) x m
  { st := Function.update C.st y r.1
    chan := fun a b => if a = y then C.chan a b ++ sendTo G B y r.2 b else C.chan a b
    dec := Function.update C.dec y ((C.dec y).or (A.out y r.1)) }

/-- Remove the head of the channel `x → y`. -/
def Config.pop (C : Config V M S) (x y : V) (rest : List M) : Config V M S :=
  { C with chan := fun a b => if a = x ∧ b = y then rest else C.chan a b }

/-- One step. -/
def step (C : Config V M S) : Event V M → Config V M S
  | .deliver x y =>
    match C.chan x y with
    | [] => C
    | m :: rest => if y ∈ B then C else process A G B (C.pop x y rest) y x m
  | .byz x y m => if x ∈ B ∧ y ∉ B ∧ G.Adj x y ∧ x ≠ y then process A G B C y x m else C
  | .skip => C

/-- The initial configuration for inputs `inp`. -/
def init (inp : V → ℝ) : Config V M S where
  st x := (A.start x (inp x)).1
  chan x b := if x ∈ B then [] else sendTo G B x (A.start x (inp x)).2 b
  dec x := A.out x (A.start x (inp x)).1

/-- The execution determined by the inputs and the event sequence. -/
def run (inp : V → ℝ) (ev : ℕ → Event V M) : ℕ → Config V M S
  | 0 => init A G B inp
  | t + 1 => step A G B (run inp ev t) (ev t)

/-- Fairness: on every link between correct nodes, a non-empty channel is eventually served. -/
def Fair (inp : V → ℝ) (ev : ℕ → Event V M) : Prop :=
  ∀ x y, x ∉ B → y ∉ B → ∀ t, (run A G B inp ev t).chan x y ≠ [] →
    ∃ t' ≥ t, ev t' = .deliver x y

end Semantics

/-- **Asynchronous Byzantine approximate consensus** (Definition 1) with parameter `ε`, for inputs
in the set `I`: for every set `B` of at most `f` Byzantine nodes, all inputs in `I` and all event
sequences,
* (convergence) the decisions of any two correct nodes are within `ε`,
* (validity) every decision of a correct node lies between two inputs of correct nodes,
* (termination) in every fair execution every correct node eventually decides. -/
def SolvesOn (I : Set ℝ) (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj] (f : ℕ)
    (ε : ℝ) : Prop :=
  ∀ B : Finset V, B.card ≤ f → ∀ (inp : V → ℝ), (∀ w, inp w ∈ I) → ∀ (ev : ℕ → Event V M),
    (∀ t v u y z, v ∉ B → u ∉ B → (run A G B inp ev t).dec v = some y →
      (run A G B inp ev t).dec u = some z → |y - z| ≤ ε) ∧
    (∀ t v y, v ∉ B → (run A G B inp ev t).dec v = some y →
      (∃ w ∉ B, inp w ≤ y) ∧ ∃ w ∉ B, y ≤ inp w) ∧
    (Fair A G B inp ev → ∀ v ∉ B, ∃ t y, (run A G B inp ev t).dec v = some y)

/-- Definition 1 for arbitrary real inputs. -/
def Solves (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj] (f : ℕ) (ε : ℝ) : Prop :=
  SolvesOn Set.univ A G f ε

end Cslib.ApproxConsensus.Async
