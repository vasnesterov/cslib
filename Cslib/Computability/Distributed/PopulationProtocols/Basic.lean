/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Relation
public import Cslib.Computability.Distributed.SelfStabilization.TransitionSystem
import Mathlib.Basic.Finite.Prod

/-! # Population protocols

A framework for deterministic two-way population protocols in the sense of
Angluin, Aspnes, Diamadi, Fischer and Peralta [Angluin2006], on the complete interaction graph.

## Main definitions

* `PopulationProtocol.Protocol`: a protocol over a state type `Q` is a transition function
  `δ : Q → Q → Q × Q` (initiator state, responder state ↦ new initiator state, new responder
  state).
* `PopulationProtocol.Config`: a configuration over a type of agents `A` is a function `A → Q`
  (agents are labelled).
* `PopulationProtocol.Protocol.interact`: an interaction of two distinct agents updates their
  states by `δ`; `Protocol.Step` and `Protocol.Reachable` are the induced one-step and
  reachability relations on configurations.
* `PopulationProtocol.Protocol.Execution`: an infinite sequence of configurations together with
  the schedule of interacting pairs.
* `Execution.WeaklyFair`: every unordered pair of distinct agents interacts infinitely often.
* `Execution.GloballyFair`: every one-step successor of a configuration occurring infinitely often
  also occurs infinitely often.
* `Execution.toRun`: an execution as a run of the step relation, so that the generic notions of
  `Cslib.TransitionSystem` apply (`reachable_iff_reach`, `closed_iff_isTrap`,
  `outputStable_iff_stablyIn`, `Execution.globallyFair_iff`).
* `PopulationProtocol.Protocol.Hom`: maps of states commuting with the transition functions;
  they map executions to executions (`Execution.map`).

## Main results

* `Execution.GloballyFair.exists_eq`: under global fairness (finitely many agents and states), a
  configuration reachable from every configuration reachable from the start is eventually reached.
* `Execution.GloballyFair.eventually_mem`: under global fairness, if a closed set of
  configurations is reachable from every reachable configuration, then the execution eventually
  enters it and stays there forever.

These are instances of the corresponding results for global fairness of runs of a transition
system (`Cslib.TransitionSystem.Run.GloballyFair`), via `Execution.globallyFair_iff`.

## References

* [D. Angluin, J. Aspnes, Z. Diamadi, M. J. Fischer, R. Peralta, *Computation in networks of
  passively mobile finite-state sensors*][Angluin2006]
-/

@[expose] public section

namespace Cslib.PopulationProtocol

/-- A deterministic population protocol: a transition function on pairs of states. -/
structure Protocol (Q : Type*) where
  /-- `δ p q = (p', q')`: the initiator in state `p` meets the responder in state `q`. -/
  δ : Q → Q → Q × Q

variable {Q A : Type*} [DecidableEq A]

/-- Configurations: every agent is mapped to a state. -/
abbrev Config (A Q : Type*) := A → Q

namespace Protocol

variable (P : Protocol Q)

/-- The configuration obtained when the initiator `a` interacts with the responder `b`.
(Only meaningful for `a ≠ b`.) -/
def interact (C : Config A Q) (a b : A) : Config A Q :=
  fun x => if x = a then (P.δ (C a) (C b)).1 else if x = b then (P.δ (C a) (C b)).2 else C x

@[simp] lemma interact_self_left (C : Config A Q) (a b : A) :
    P.interact C a b a = (P.δ (C a) (C b)).1 := by simp [interact]

@[simp] lemma interact_self_right (C : Config A Q) {a b : A} (h : a ≠ b) :
    P.interact C a b b = (P.δ (C a) (C b)).2 := by simp [interact, Ne.symm h]

lemma interact_other (C : Config A Q) {a b x : A} (ha : x ≠ a) (hb : x ≠ b) :
    P.interact C a b x = C x := by simp [interact, ha, hb]

/-- One step of the protocol: some pair of distinct agents interacts. -/
def Step (C C' : Config A Q) : Prop := ∃ a b, a ≠ b ∧ C' = P.interact C a b

/-- Reachability: the reflexive-transitive closure of `Step`. -/
def Reachable : Config A Q → Config A Q → Prop := Relation.ReflTransGen P.Step

/-- An execution: configurations `config t` and interacting pairs `sched t`, such that
`config (t+1)` is obtained from `config t` by the interaction `sched t`. -/
structure Execution (A : Type*) [DecidableEq A] where
  /-- The configuration at time `t`. -/
  config : ℕ → Config A Q
  /-- The pair `(initiator, responder)` interacting at time `t`. -/
  sched : ℕ → A × A
  /-- The two interacting agents are distinct. -/
  sched_ne : ∀ t, (sched t).1 ≠ (sched t).2
  /-- Each configuration is obtained from the previous one by the scheduled interaction. -/
  step : ∀ t, config (t + 1) = P.interact (config t) (sched t).1 (sched t).2

variable {P}

/-- Weak fairness: every pair of distinct agents interacts infinitely often (in one of the two
roles). -/
def Execution.WeaklyFair (E : P.Execution A) : Prop :=
  ∀ a b, a ≠ b → ∀ T, ∃ t ≥ T, E.sched t = (a, b) ∨ E.sched t = (b, a)

/-- Global fairness: if `C` occurs infinitely often and `C → C'` in one step, then `C'` occurs
infinitely often. -/
def Execution.GloballyFair (E : P.Execution A) : Prop :=
  ∀ C C', P.Step C C' → (∀ T, ∃ t ≥ T, E.config t = C) → ∀ T, ∃ t ≥ T, E.config t = C'

lemma Execution.step_rel (E : P.Execution A) (t : ℕ) : P.Step (E.config t) (E.config (t + 1)) :=
  ⟨_, _, E.sched_ne t, E.step t⟩

/-! ### Executions as runs of the step relation -/

open Cslib.TransitionSystem Filter

/-- CSLib's reachability is `Reach` of the step relation. -/
theorem reachable_iff_reach {C D : Config A Q} : P.Reachable C D ↔ Reach P.Step C D := Iff.rfl

/-- An execution of a deterministic protocol as a run of its step relation. -/
def Execution.toRun (E : P.Execution A) : Run (P.Step (A := A)) := ⟨E.config, E.step_rel⟩

/-- The configurations of the induced run. -/
@[simp] theorem Execution.toRun_st (E : P.Execution A) : E.toRun.st = E.config := rfl

/-- CSLib's global fairness of executions is global fairness of the induced run. -/
theorem Execution.globallyFair_iff (E : P.Execution A) : E.GloballyFair ↔ E.toRun.GloballyFair :=
  (Run.globallyFair_iff (E := E.toRun)).symm

lemma Execution.reachable_of_le (E : P.Execution A) {s t : ℕ} (h : s ≤ t) :
    P.Reachable (E.config s) (E.config t) :=
  E.toRun.reach_of_le h

/-- A set of configurations is closed if every step from it stays in it. -/
def Closed (S : Config A Q → Prop) : Prop := ∀ C C', S C → P.Step C C' → S C'

/-- CSLib's closed sets are the closed sets of the step relation. -/
theorem closed_iff_isTrap {S : Set (Config A Q)} : P.Closed S ↔ IsTrap P.Step S := Iff.rfl

lemma Closed.reachable {S : Config A Q → Prop} (hS : P.Closed S) {C C' : Config A Q}
    (hC : S C) (h : P.Reachable C C') : S C' :=
  IsTrap.reach (S := S) (fun _ _ => hS _ _) hC h

lemma Closed.execution {S : Config A Q → Prop} (hS : P.Closed S) (E : P.Execution A) {T : ℕ}
    (hT : S (E.config T)) : ∀ t ≥ T, S (E.config t) :=
  fun _ ht => hS.reachable hT (E.reachable_of_le ht)

/-- The output of a configuration (given an output map on states) is *stable* if it can never
change again: every configuration reachable from `C` has the same output as `C`. -/
def OutputStable {O : Type*} (out : Q → O) (C : Config A Q) : Prop :=
  ∀ C', P.Reachable C C' → ∀ a, out (C' a) = out (C a)

/-- CSLib's output stability is stability of the set of configurations with the same output. -/
theorem outputStable_iff_stablyIn {O : Type*} (out : Q → O) (C : Config A Q) :
    P.OutputStable out C ↔ StablyIn P.Step {D | ∀ a, out (D a) = out (C a)} C := Iff.rfl

/-- With finitely many agents and states, some configuration occurs infinitely often in every
execution. -/
lemma Execution.exists_infinitely_often [Finite A] [Finite Q] (E : P.Execution A) :
    ∃ C, ∀ T, ∃ t ≥ T, E.config t = C :=
  let ⟨C, hC⟩ := exists_frequently_eq E.config
  ⟨C, frequently_atTop.1 hC⟩

/-- Under global fairness, every configuration reachable from a configuration occurring infinitely
often also occurs infinitely often. -/
lemma Execution.GloballyFair.infinitely_often_of_reachable {E : P.Execution A}
    (hE : E.GloballyFair) {C C' : Config A Q} (hC : ∀ T, ∃ t ≥ T, E.config t = C)
    (h : P.Reachable C C') : ∀ T, ∃ t ≥ T, E.config t = C' :=
  frequently_atTop.1 <|
    (E.globallyFair_iff.1 hE).frequently_of_reach (E := E.toRun) (frequently_atTop.2 hC) h

/-- Under global fairness, with finitely many configurations, a configuration reachable from
every configuration reachable from the start is reached. -/
lemma Execution.GloballyFair.exists_eq [Finite A] [Finite Q] {E : P.Execution A}
    (hE : E.GloballyFair) (X : Config A Q)
    (hX : ∀ C, P.Reachable (E.config 0) C → P.Reachable C X) :
    ∃ t, E.config t = X :=
  (E.globallyFair_iff.1 hE).exists_eq (E := E.toRun) hX

/-- Under global fairness (finitely many agents and states): if from every configuration
reachable from the start some configuration of a closed set `S` is reachable, then the execution
eventually enters `S` and stays there forever. -/
lemma Execution.GloballyFair.eventually_mem [Finite A] [Finite Q] {E : P.Execution A}
    (hE : E.GloballyFair) {S : Config A Q → Prop} (hS : P.Closed S)
    (hX : ∀ C, P.Reachable (E.config 0) C → ∃ C', S C' ∧ P.Reachable C C') :
    ∃ T, ∀ t ≥ T, S (E.config t) :=
  eventually_atTop.1 <|
    (E.globallyFair_iff.1 hE).eventually_mem (E := E.toRun) (S := S) (fun _ _ => hS _ _) hX

/-! ### Projections (protocol homomorphisms) -/

/-- A map of states commuting with the transition functions: the image of an execution of `P`
is an execution of `P'` (`Execution.map`). Used to analyse a sub-protocol running "in parallel"
inside a larger protocol. -/
structure Hom {Q' : Type*} (P : Protocol Q) (P' : Protocol Q') where
  /-- The map on states. -/
  f : Q → Q'
  /-- `f` commutes with the initiator component of the transition functions. -/
  map_fst : ∀ p q, f (P.δ p q).1 = (P'.δ (f p) (f q)).1
  /-- `f` commutes with the responder component of the transition functions. -/
  map_snd : ∀ p q, f (P.δ p q).2 = (P'.δ (f p) (f q)).2

lemma Hom.interact {Q' : Type*} {P : Protocol Q} {P' : Protocol Q'} (φ : P.Hom P')
    (C : Config A Q) {a b : A} (hab : a ≠ b) :
    (fun x => φ.f (P.interact C a b x)) = P'.interact (fun x => φ.f (C x)) a b := by
  funext x
  by_cases hxa : x = a
  · subst hxa; simp [φ.map_fst]
  · by_cases hxb : x = b
    · subst hxb; simp [interact_self_right _ _ hab, φ.map_snd]
    · simp [interact_other _ _ hxa hxb]

/-- The image of an execution under a protocol homomorphism. -/
def Execution.map {Q' : Type*} {P : Protocol Q} {P' : Protocol Q'} (E : P.Execution A)
    (φ : P.Hom P') : P'.Execution A where
  config t x := φ.f (E.config t x)
  sched := E.sched
  sched_ne := E.sched_ne
  step t := by rw [E.step t]; exact φ.interact _ (E.sched_ne t)

@[simp] lemma Execution.map_config {Q' : Type*} {P : Protocol Q} {P' : Protocol Q'}
    (E : P.Execution A) (φ : P.Hom P') (t : ℕ) (x : A) :
    (E.map φ).config t x = φ.f (E.config t x) := rfl

lemma Execution.WeaklyFair.map {Q' : Type*} {P : Protocol Q} {P' : Protocol Q'}
    {E : P.Execution A} (h : E.WeaklyFair) (φ : P.Hom P') : (E.map φ).WeaklyFair := h

end Protocol

end Cslib.PopulationProtocol
