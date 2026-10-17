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
* `PopulationProtocol.Protocol.ClosedStates P H`: interactions between states of `H` only produce
  states of `H`.
* `PopulationProtocol.Protocol.PairReach P`, `PopulationProtocol.Protocol.TripleReach P`:
  reachability of the states of two (three) agents when only these agents interact.

## Main results

* `Execution.GloballyFair.exists_eq`: under global fairness (finitely many agents and states), a
  configuration reachable from every configuration reachable from the start is eventually reached.
* `Execution.GloballyFair.eventually_mem`: under global fairness, if a closed set of
  configurations is reachable from every reachable configuration, then the execution eventually
  enters it and stays there forever.

These are instances of the corresponding results for global fairness of runs of a transition
system (`Cslib.TransitionSystem.Run.GloballyFair`), via `Execution.globallyFair_iff`.
* `ClosedStates.reachable`, `ClosedStates.execution`: every configuration reachable from a
  configuration using only states of a closed set `H` uses only states of `H` (the usual way to
  prove a per-agent invariant).
* `PairReach.lift`, `TripleReach.lift`: runs of two (three) agents lift to the whole population,
  the other agents being idle; used to build runs by hand from small "gadgets" (e.g. reachability
  proofs of self-stabilization).

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

/-! ### Closed sets of states -/

/-- A set of states `H` is *closed* under `P` if an interaction of two agents in states of `H`
only produces states of `H`. -/
def ClosedStates (P : Protocol Q) (H : Set Q) : Prop :=
  ∀ p ∈ H, ∀ q ∈ H, (P.δ p q).1 ∈ H ∧ (P.δ p q).2 ∈ H

variable {H : Set Q}

/-- An interaction keeps a configuration inside a closed set of states. -/
theorem ClosedStates.interact (hH : P.ClosedStates H) {C : Config A Q} (hC : ∀ x, C x ∈ H)
    {a b : A} (hab : a ≠ b) : ∀ x, P.interact C a b x ∈ H := by
  have h := hH _ (hC a) _ (hC b)
  intro x
  by_cases hxa : x = a
  · subst hxa; rw [interact_self_left]; exact h.1
  · by_cases hxb : x = b
    · subst hxb; rw [interact_self_right _ _ hab]; exact h.2
    · rw [interact_other _ _ hxa hxb]; exact hC x

/-- A step keeps a configuration inside a closed set of states. -/
theorem ClosedStates.step (hH : P.ClosedStates H) {C D : Config A Q} (hC : ∀ x, C x ∈ H)
    (h : P.Step C D) : ∀ x, D x ∈ H := by
  obtain ⟨a, b, hab, rfl⟩ := h
  exact hH.interact hC hab

/-- **Closed sets of states are invariant.** If `C` only uses states of a closed set `H`, so does
every configuration reachable from `C`. -/
theorem ClosedStates.reachable (hH : P.ClosedStates H) {C D : Config A Q} (hC : ∀ x, C x ∈ H)
    (h : P.Reachable C D) : ∀ x, D x ∈ H := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact hH.step ih hst

/-- Along an execution starting in a closed set of states, every configuration stays in it. -/
theorem ClosedStates.execution (hH : P.ClosedStates H) (E : P.Execution A)
    (h0 : ∀ x, E.config 0 x ∈ H) (t : ℕ) : ∀ x, E.config t x ∈ H :=
  hH.reachable h0 (E.reachable_of_le t.zero_le)

/-! ### Runs of two or three agents -/

/-- Reachability of pairs of states under repeated interactions of one ordered pair of agents
(the first one initiating). -/
def PairReach (P : Protocol Q) : Q × Q → Q × Q → Prop :=
  Relation.ReflTransGen fun u v => v = P.δ u.1 u.2

/-- One interaction inside a triple of agents (any of the six ordered pairs). -/
inductive TripleStep (P : Protocol Q) : Q × Q × Q → Q × Q × Q → Prop
  | xy (a b c : Q) : TripleStep P (a, b, c) ((P.δ a b).1, (P.δ a b).2, c)
  | yx (a b c : Q) : TripleStep P (a, b, c) ((P.δ b a).2, (P.δ b a).1, c)
  | xz (a b c : Q) : TripleStep P (a, b, c) ((P.δ a c).1, b, (P.δ a c).2)
  | zx (a b c : Q) : TripleStep P (a, b, c) ((P.δ c a).2, b, (P.δ c a).1)
  | yz (a b c : Q) : TripleStep P (a, b, c) (a, (P.δ b c).1, (P.δ b c).2)
  | zy (a b c : Q) : TripleStep P (a, b, c) (a, (P.δ c b).2, (P.δ c b).1)

/-- Reachability inside a triple of agents. -/
def TripleReach (P : Protocol Q) : Q × Q × Q → Q × Q × Q → Prop :=
  Relation.ReflTransGen (TripleStep P)

/-- Transport of a run of two agents along a map that turns each interaction into a step of
`S`. -/
theorem PairReach.map {R : Type*} {S : R → R → Prop} (f : Q × Q → R)
    (hf : ∀ u, S (f u) (f (P.δ u.1 u.2))) {u v : Q × Q} (h : PairReach P u v) :
    Relation.ReflTransGen S (f u) (f v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => subst hst; exact ih.tail (hf _)

/-- A run of the first two agents of a triple (the first one initiating). -/
theorem PairReach.xy {a b a' b' : Q} (c : Q) (h : PairReach P (a, b) (a', b')) :
    TripleReach P (a, b, c) (a', b', c) :=
  PairReach.map (S := TripleStep P) (fun u => (u.1, u.2, c)) (fun _ => TripleStep.xy _ _ _) h

/-- A run of the first two agents of a triple (the second one initiating). -/
theorem PairReach.yx {a b a' b' : Q} (c : Q) (h : PairReach P (b, a) (b', a')) :
    TripleReach P (a, b, c) (a', b', c) :=
  PairReach.map (S := TripleStep P) (fun u => (u.2, u.1, c)) (fun _ => TripleStep.yx _ _ _) h

/-- A run of the first and third agents of a triple (the first one initiating). -/
theorem PairReach.xz {a c a' c' : Q} (b : Q) (h : PairReach P (a, c) (a', c')) :
    TripleReach P (a, b, c) (a', b, c') :=
  PairReach.map (S := TripleStep P) (fun u => (u.1, b, u.2)) (fun _ => TripleStep.xz _ _ _) h

/-- A run of the first and third agents of a triple (the third one initiating). -/
theorem PairReach.zx {a c a' c' : Q} (b : Q) (h : PairReach P (c, a) (c', a')) :
    TripleReach P (a, b, c) (a', b, c') :=
  PairReach.map (S := TripleStep P) (fun u => (u.2, b, u.1)) (fun _ => TripleStep.zx _ _ _) h

/-- A run of the last two agents of a triple (the second one initiating). -/
theorem PairReach.yz {b c b' c' : Q} (a : Q) (h : PairReach P (b, c) (b', c')) :
    TripleReach P (a, b, c) (a, b', c') :=
  PairReach.map (S := TripleStep P) (fun u => (a, u.1, u.2)) (fun _ => TripleStep.yz _ _ _) h

/-- A run of the last two agents of a triple (the third one initiating). -/
theorem PairReach.zy {b c b' c' : Q} (a : Q) (h : PairReach P (c, b) (c', b')) :
    TripleReach P (a, b, c) (a, b', c') :=
  PairReach.map (S := TripleStep P) (fun u => (a, u.2, u.1)) (fun _ => TripleStep.zy _ _ _) h

/-- A run of two agents `a ≠ b` lifts to the whole population (the other agents are idle). -/
theorem PairReach.lift {C : Config A Q} {a b : A} (hab : a ≠ b) {u : Q × Q}
    (h : PairReach P (C a, C b) u) :
    ∃ D, P.Reachable C D ∧ D a = u.1 ∧ D b = u.2 ∧ ∀ z, z ≠ a → z ≠ b → D z = C z := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl, rfl, fun _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDa, hDb, hDz⟩ := ih
    subst hst
    refine ⟨P.interact D a b, hD.tail ⟨a, b, hab, rfl⟩, ?_, ?_, ?_⟩
    · rw [interact_self_left, hDa, hDb]
    · rw [interact_self_right _ _ hab, hDa, hDb]
    · intro z hza hzb; rw [interact_other _ _ hza hzb, hDz z hza hzb]

/-- A run of three distinct agents lifts to the whole population (the other agents are idle). -/
theorem TripleReach.lift {C : Config A Q} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {u : Q × Q × Q} (h : TripleReach P (C x, C y, C z) u) :
    ∃ D, P.Reachable C D ∧ D x = u.1 ∧ D y = u.2.1 ∧ D z = u.2.2 ∧
      ∀ w, w ≠ x → w ≠ y → w ≠ z → D w = C w := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDx, hDy, hDz, hDw⟩ := ih
    have hyx := hxy.symm
    have hzx := hxz.symm
    have hzy := hyz.symm
    cases hst with
    | xy a b c =>
      refine ⟨P.interact D x y, hD.tail ⟨x, y, hxy, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | yx a b c =>
      refine ⟨P.interact D y x, hD.tail ⟨y, x, hyx, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | xz a b c =>
      refine ⟨P.interact D x z, hD.tail ⟨x, z, hxz, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | zx a b c =>
      refine ⟨P.interact D z x, hD.tail ⟨z, x, hzx, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | yz a b c =>
      refine ⟨P.interact D y z, hD.tail ⟨y, z, hyz, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | zy a b c =>
      refine ⟨P.interact D z y, hD.tail ⟨z, y, hzy, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]

end Protocol

end Cslib.PopulationProtocol
