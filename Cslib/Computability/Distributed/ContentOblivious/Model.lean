/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ZMod.Defs

/-!
# Content-oblivious asynchronous two-port networks (rings)

A *content-oblivious* (fully defective) network: messages carry no content, only their existence
(*pulses*). Each node has two ports, `false` = `Port0` and `true` = `Port1`. A link joins two ports;
`Wiring.peer p` is the port at the other end of the link attached to port `p`.

Since pulses on one link are indistinguishable, a channel is just a counter. A configuration
stores each node's local state and, as ghost counters, the number of pulses sent from and received
at each port; the number of pulses in transit towards port `p` is `sent (peer p) - recvd p`.

Nodes are deterministic and event driven: a node acts once at the start (`Algo.init`, a function of
its ID) and afterwards only when it consumes a pulse (`Algo.recv`). The adversarial asynchronous
scheduler chooses, at each step, any node `v` and port `j` such that a pulse is in transit to
`(v, j)`, the node has not terminated and is willing to read from `j` (`Algo.ready`, which models
the polling `recv*()` calls of pseudo-code: a pulse that is not read stays in the incoming queue,
i.e. in transit). Every pulse is eventually delivered or stays forever in transit; pulses are never
lost nor created by the channel.
-/

@[expose] public section

namespace Cslib.ContentOblivious

open Finset

/-- Port wiring of a network in which every node has exactly two ports. -/
structure Wiring (V : Type*) where
  /-- The port at the other end of the link attached to a port. -/
  peer : V × Bool → V × Bool
  /-- Links are symmetric: the peer of the peer of a port is the port. -/
  peer_peer : ∀ p, peer (peer p) = p

/-- The oriented ring on `ZMod n`: `Port1` of `v` is its clockwise port, linked to `Port0` of
`v + 1`. For `n = 1` this is a self-loop, for `n = 2` two parallel links. -/
def oriented (n : ℕ) : Wiring (ZMod n) where
  peer p := if p.2 then (p.1 + 1, false) else (p.1 - 1, true)
  peer_peer p := by rcases p with ⟨v, _ | _⟩ <;> simp

/-- On the oriented ring, `Port1` of `v` is linked to `Port0` of `v + 1`. -/
@[simp] lemma oriented_peer_true (n : ℕ) (v : ZMod n) :
    (oriented n).peer (v, true) = (v + 1, false) :=
  rfl

/-- On the oriented ring, `Port0` of `v` is linked to `Port1` of `v - 1`. -/
@[simp] lemma oriented_peer_false (n : ℕ) (v : ZMod n) :
    (oriented n).peer (v, false) = (v - 1, true) :=
  rfl

/-- A non-oriented ring: node `v`'s physical `Port_i` is the oriented port `i xor flip v`. -/
def flipped (n : ℕ) (flip : ZMod n → Bool) : Wiring (ZMod n) where
  peer p :=
    let q := (oriented n).peer (p.1, xor p.2 (flip p.1))
    (q.1, xor q.2 (flip q.1))
  peer_peer p := by
    rcases p with ⟨v, i⟩
    cases i <;> cases h : flip v <;> simp [oriented, h]

/-- A deterministic content-oblivious algorithm for two-port nodes. Nodes know only their own ID. -/
structure Algo where
  /-- Local states. -/
  State : Type
  /-- Initial state and number of pulses sent on each port at start-up, as a function of the ID. -/
  init : ℕ → State × (Bool → ℕ)
  /-- Reaction to consuming one pulse from a port: new state, number of pulses sent on each port. -/
  recv : State → Bool → State × (Bool → ℕ)
  /-- Whether the node is willing to read a pulse from the given port (polling). -/
  ready : State → Bool → Bool := fun _ _ => true
  /-- Terminated states: a terminated node never reads, changes state or sends again. -/
  terminated : State → Bool := fun _ => false
  /-- Output: `true` = `Leader`, `false` = `Non-Leader`. -/
  leader : State → Bool

/-- The pulses sent by an action that sends exactly one pulse, on port `p`. -/
def onePulse (p : Bool) : Bool → ℕ := fun p' => if p' = p then 1 else 0

/-- Relabel the IDs of an algorithm by a function `π` (each node runs `A` with ID `π ID`). -/
def Algo.relabel (A : Algo) (π : ℕ → ℕ) : Algo :=
  { A with init := fun i => A.init (π i) }

/-- A configuration: local states plus ghost counters of sent and received pulses per port. -/
@[ext] structure Config (V S : Type*) where
  /-- The local state of each node. -/
  st : V → S
  /-- The number of pulses sent from each port. -/
  sent : V × Bool → ℕ
  /-- The number of pulses received (consumed) at each port. -/
  recvd : V × Bool → ℕ

variable {V : Type*} [DecidableEq V] (W : Wiring V) (A : Algo)

/-- The initial configuration: every node has performed its initial action. -/
def initCfg (id : V → ℕ) : Config V A.State where
  st v := (A.init (id v)).1
  sent p := (A.init (id p.1)).2 p.2
  recvd _ := 0

/-- Pulses in transit towards port `p`. -/
def Config.inTransit (c : Config V A.State) (p : V × Bool) : ℕ := c.sent (W.peer p) - c.recvd p

/-- Node `v` can consume a pulse from port `j`. -/
def Enabled (c : Config V A.State) (v : V) (j : Bool) : Prop :=
  A.terminated (c.st v) = false ∧ A.ready (c.st v) j = true ∧
    c.recvd (v, j) < c.sent (W.peer (v, j))

/-- The configuration after node `v` consumes a pulse from port `j`. -/
def deliver (c : Config V A.State) (v : V) (j : Bool) : Config V A.State :=
  let r := A.recv (c.st v) j
  { st := Function.update c.st v r.1
    sent := fun p => c.sent p + if p.1 = v then r.2 p.2 else 0
    recvd := fun p => c.recvd p + if p = (v, j) then 1 else 0 }

/-- One asynchronous step: delivery of one pulse chosen by the adversary. -/
inductive Step : Config V A.State → Config V A.State → Prop
  /-- Node `v` consumes a pulse at its enabled port `j`. -/
  | mk (c : Config V A.State) (v : V) (j : Bool) : Enabled W A c v j → Step c (deliver A c v j)

/-- Reachable configurations (finite executions from the initial configuration). -/
def Reach (id : V → ℕ) (c : Config V A.State) : Prop :=
  Relation.ReflTransGen (Step W A) (initCfg A id) c

/-- A final configuration: no step is possible (the execution is maximal). -/
def Final (c : Config V A.State) : Prop := ∀ v j, ¬ Enabled W A c v j

/-- Quiescence: no pulse is in transit. -/
def Quiescent (c : Config V A.State) : Prop := ∀ p, c.recvd p = c.sent (W.peer p)

variable [Fintype V]

/-- Total number of pulses sent (the message complexity of an execution). -/
def totalSent {S : Type*} (c : Config V S) : ℕ := ∑ p, c.sent p

/-- Total number of pulses received. -/
def totalRecvd {S : Type*} (c : Config V S) : ℕ := ∑ p, c.recvd p

omit [DecidableEq V] in
/-- A sum over all ports is the sum over the nodes of the values at their two ports. -/
lemma sum_ports {M : Type*} [AddCommMonoid M] (f : V × Bool → M) :
    ∑ p, f p = ∑ v, (f (v, false) + f (v, true)) := by
  rw [Fintype.sum_prod_type]; simp [add_comm]

section basic

variable {W A}

omit [DecidableEq V] [Fintype V] in
/-- The peer map is an involution. -/
lemma Wiring.peer_involutive : Function.Involutive W.peer := W.peer_peer

/-- The peer map as a permutation of ports. -/
def Wiring.perm : Equiv.Perm (V × Bool) := W.peer_involutive.toPerm

omit [DecidableEq V] in
/-- Summing over the peers of all ports is summing over all ports. -/
lemma Wiring.sum_peer (f : V × Bool → ℕ) : ∑ p, f (W.peer p) = ∑ p, f p :=
  Equiv.sum_comp W.perm f

omit [Fintype V] in
/-- Delivery increments the received counter of the delivering port. -/
lemma deliver_recvd (c : Config V A.State) (v : V) (j : Bool) (p : V × Bool) :
    (deliver A c v j).recvd p = c.recvd p + if p = (v, j) then 1 else 0 := rfl

omit [Fintype V] in
/-- Delivery adds the pulses sent by the receiving node. -/
lemma deliver_sent (c : Config V A.State) (v : V) (j : Bool) (p : V × Bool) :
    (deliver A c v j).sent p = c.sent p + if p.1 = v then (A.recv (c.st v) j).2 p.2 else 0 := rfl

omit [Fintype V] in
/-- The receiving node takes its new state. -/
lemma deliver_st_self (c : Config V A.State) (v : V) (j : Bool) :
    (deliver A c v j).st v = (A.recv (c.st v) j).1 := by simp [deliver]

omit [Fintype V] in
/-- The other nodes keep their states. -/
lemma deliver_st_ne (c : Config V A.State) (v w : V) (j : Bool) (h : w ≠ v) :
    (deliver A c v j).st w = c.st w := by simp [deliver, h]

omit [Fintype V] in
/-- Channels never create pulses: at most as many pulses are received as were sent. -/
lemma Reach.recvd_le {id : V → ℕ} {c : Config V A.State} (h : Reach W A id c) :
    ∀ p, c.recvd p ≤ c.sent (W.peer p) := by
  induction h with
  | refl => intro p; simp [initCfg]
  | tail _ hs ih =>
    obtain ⟨v, j, hen⟩ := hs
    intro p
    rw [deliver_recvd, deliver_sent]
    by_cases hp : p = (v, j)
    · subst hp; simp only [ite_true]; have := hen.2.2; omega
    · simp only [hp, ite_false]; have := ih p; omega

omit [Fintype V] in
/-- Sent counters only grow. -/
lemma Step.sent_le {c c' : Config V A.State} (h : Step W A c c') : ∀ p, c.sent p ≤ c'.sent p := by
  obtain ⟨v, j, -⟩ := h
  intro p; rw [deliver_sent]; omega

/-- Every step consumes exactly one pulse. -/
lemma Step.totalRecvd_succ {c c' : Config V A.State} (h : Step W A c c') :
    totalRecvd c' = totalRecvd c + 1 := by
  obtain ⟨v, j, -⟩ := h
  simp only [ContentOblivious.totalRecvd, deliver_recvd, sum_add_distrib]
  rw [Finset.sum_ite_eq']; simp

/-- No more pulses are received than sent. -/
lemma Reach.totalRecvd_le_totalSent {id : V → ℕ} {c : Config V A.State} (h : Reach W A id c) :
    totalRecvd c ≤ totalSent c := by
  calc totalRecvd c ≤ ∑ p, c.sent (W.peer p) := sum_le_sum fun p _ => h.recvd_le p
    _ = totalSent c := W.sum_peer _

omit [DecidableEq V] in
/-- In a quiescent configuration, all sent pulses have been received. -/
lemma Quiescent.totalRecvd_eq {c : Config V A.State} (h : Quiescent W A c) :
    totalRecvd c = totalSent c := by
  unfold ContentOblivious.totalRecvd
  rw [Finset.sum_congr rfl fun p _ => h p]; exact W.sum_peer c.sent

/-- If the message complexity is bounded by `B` on all reachable configurations, there is no
infinite execution. -/
theorem no_infinite_execution {id : V → ℕ} {B : ℕ}
    (hB : ∀ c, Reach W A id c → totalSent c ≤ B) :
    ¬ ∃ f : ℕ → Config V A.State, f 0 = initCfg A id ∧ ∀ k, Step W A (f k) (f (k + 1)) := by
  rintro ⟨f, h0, hf⟩
  have hreach : ∀ k, Reach W A id (f k) := by
    intro k; induction k with
    | zero => rw [h0]; exact Relation.ReflTransGen.refl
    | succ k ih => exact ih.tail (hf k)
  have hrec : ∀ k, totalRecvd (f k) = k := by
    intro k; induction k with
    | zero => rw [h0]; simp [totalRecvd, initCfg]
    | succ k ih => rw [(hf k).totalRecvd_succ, ih]
  have := (hreach (B + 1)).totalRecvd_le_totalSent.trans (hB _ (hreach (B + 1)))
  rw [hrec] at this; omega

/-- If the message complexity is bounded, every reachable configuration can be extended to a final
configuration (every maximal execution is finite). -/
theorem exists_final {id : V → ℕ} {B : ℕ} (hB : ∀ c, Reach W A id c → totalSent c ≤ B)
    {c : Config V A.State} (hc : Reach W A id c) :
    ∃ c', Relation.ReflTransGen (Step W A) c c' ∧ Final W A c' := by
  suffices ∀ m c, Reach W A id c → B - totalRecvd c ≤ m →
      ∃ c', Relation.ReflTransGen (Step W A) c c' ∧ Final W A c' from this _ c hc le_rfl
  intro m
  induction m with
  | zero =>
    intro c hc hm
    refine ⟨c, .refl, fun v j hen => ?_⟩
    have hr : Reach W A id (deliver A c v j) := hc.tail (Step.mk c v j hen)
    have h1 := hr.totalRecvd_le_totalSent.trans (hB _ hr)
    rw [(Step.mk c v j hen).totalRecvd_succ] at h1; omega
  | succ m ih =>
    intro c hc hm
    by_cases hfin : Final W A c
    · exact ⟨c, .refl, hfin⟩
    · simp only [Final, not_forall, not_not] at hfin
      obtain ⟨v, j, hen⟩ := hfin
      have hs := Step.mk c v j hen
      obtain ⟨c', h1, h2⟩ := ih _ (hc.tail hs) (by rw [hs.totalRecvd_succ]; omega)
      exact ⟨c', Relation.ReflTransGen.head hs h1, h2⟩

omit [Fintype V] in
/-- Relabelling the IDs does not change the steps. -/
lemma step_relabel (π : ℕ → ℕ) {c c' : Config V A.State} :
    Step W (A.relabel π) c c' ↔ Step W A c c' := by
  constructor <;> rintro ⟨v, j, h⟩ <;> exact Step.mk _ v j h

omit [Fintype V] in
/-- Running `A` with IDs relabelled by `π` is running `A` on the IDs `π ∘ id`. -/
lemma reach_relabel (π : ℕ → ℕ) (id : V → ℕ) (c : Config V A.State) :
    Reach W (A.relabel π) id c ↔ Reach W A (π ∘ id) c := by
  have e : Step W (A.relabel π) = Step W A := by
    funext c c'; exact propext (step_relabel π)
  unfold Reach
  rw [e]; rfl

omit [DecidableEq V] [Fintype V] in
/-- Relabelling the IDs does not change finality. -/
lemma final_relabel (π : ℕ → ℕ) (c : Config V A.State) :
    Final W (A.relabel π) c ↔ Final W A c := Iff.rfl

end basic

end Cslib.ContentOblivious
