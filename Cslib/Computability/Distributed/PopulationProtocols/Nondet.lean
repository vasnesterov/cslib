/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.PopulationProtocols.Basic

/-!
# Nondeterministic population protocols on interaction graphs

Population protocols whose transitions may be randomized are modelled by their **support**:
`NProtocol Q` has `δ p q : Set (Q × Q)`, the possible new states `(initiator, responder)` when an
initiator in state `p` meets a responder in state `q`. Under global fairness, and for "with
probability `1`" statements over finitely many configurations (`SelfStabilization/Markov.lean`,
`PopulationProtocols/RandomScheduler.lean`), only the support matters.

Interactions are restricted by an *interaction relation* `I : A → A → Prop` on agents
(`NProtocol.StepOn I`): `I a b` means that `a` may initiate an interaction with responder `b`.
* the complete interaction graph of CSLib's `Cslib.PopulationProtocol.Protocol` is `I = (· ≠ ·)`
  (`NProtocol.Step`; deterministic protocols embed via `Protocol.toN`, `Protocol.toN_step_iff`);
* population protocols on a graph `G` use `I = G.Adj`;
* sub-populations `S` use `I a b = (a ∈ S ∧ b ∈ S ∧ a ≠ b)`.

All notions of the stabilization layer (`Cslib.TransitionSystem`) apply to the relation
`P.StepOn I`; deterministic protocols are connected to them through `Protocol.toN` (and, for
executions and global fairness, through `Protocol.Execution.toRun` in `PopulationProtocols/Basic`).

## Main definitions

* `NProtocol`, `upd` (two agents take new states), `NProtocol.StepOn`, `NProtocol.Step`,
  `NProtocol.Reachable`.
* `Protocol.toN`: a deterministic protocol as a nondeterministic one.
* `numLeaders`: the number of agents in a leader state.

## Main results

* `NProtocol.exists_reach_of_embedding`: a run of a sub-population embeds into the whole
  population (the other agents being idle); `NProtocol.reach_stepOn_apply_eq`: idle agents keep
  their states.
* `Protocol.toN_step_iff`, `Protocol.toN_reachable_iff`, `Protocol.Hom.reachable`.
-/

@[expose] public section

open Cslib.TransitionSystem

namespace Cslib.PopulationProtocol

/-- A population protocol whose transitions may be randomized: `δ p q` is the set of possible
new states `(initiator, responder)` (the support of the transition distribution) when an initiator
in state `p` meets a responder in state `q`. -/
structure NProtocol (Q : Type*) where
  /-- Possible outcomes of an interaction. -/
  δ : Q → Q → Set (Q × Q)

variable {Q A : Type*}

section Upd

variable [DecidableEq A]

/-- The configuration after the initiator `a` and the responder `b` take the states `o`. -/
def upd (C : Config A Q) (a b : A) (o : Q × Q) : Config A Q :=
  Function.update (Function.update C a o.1) b o.2

/-- The initiator takes the first component of the outcome. -/
theorem upd_left (C : Config A Q) {a b : A} (h : a ≠ b) (o : Q × Q) : upd C a b o a = o.1 := by
  simp [upd, h]

/-- The responder takes the second component of the outcome. -/
@[simp] theorem upd_right (C : Config A Q) (a b : A) (o : Q × Q) : upd C a b o b = o.2 := by
  simp [upd]

/-- The other agents keep their states. -/
theorem upd_other (C : Config A Q) {a b x : A} (ha : x ≠ a) (hb : x ≠ b) (o : Q × Q) :
    upd C a b o x = C x := by
  simp [upd, ha, hb]

/-- The null outcome leaves the configuration unchanged. -/
theorem upd_self (C : Config A Q) {a b : A} (h : a ≠ b) : upd C a b (C a, C b) = C := by
  funext x
  by_cases hxb : x = b
  · subst hxb; simp
  · by_cases hxa : x = a
    · subst hxa; rw [upd_left _ h]
    · rw [upd_other _ hxa hxb]

end Upd

namespace NProtocol

variable [DecidableEq A] (P : NProtocol Q)

/-- One interaction along the interaction relation `I`: some `a` initiates an interaction with
some responder `b` such that `I a b`, and both take one of the possible outcomes. -/
def StepOn (I : A → A → Prop) (C D : Config A Q) : Prop :=
  ∃ a b, I a b ∧ ∃ o ∈ P.δ (C a) (C b), D = upd C a b o

/-- One interaction of an ordered pair of distinct agents (complete interaction graph). -/
abbrev Step : Config A Q → Config A Q → Prop := P.StepOn (· ≠ ·)

/-- Reachability on the complete interaction graph. -/
abbrev Reachable : Config A Q → Config A Q → Prop := Reach P.Step

variable {P} {I J : A → A → Prop} {C D : Config A Q}

/-- Steps along `I` are steps along any larger interaction relation. -/
theorem StepOn.mono (hIJ : ∀ a b, I a b → J a b) (h : P.StepOn I C D) : P.StepOn J C D := by
  obtain ⟨a, b, hab, o, ho, rfl⟩ := h
  exact ⟨a, b, hIJ a b hab, o, ho, rfl⟩

/-- Runs along `I` are runs along any larger interaction relation. -/
theorem reach_stepOn_mono (hIJ : ∀ a b, I a b → J a b) (h : Reach (P.StepOn I) C D) :
    Reach (P.StepOn J) C D :=
  Relation.ReflTransGen.mono (fun _ _ => StepOn.mono hIJ) _ _ h

/-- An agent that interacts with nobody keeps its state. -/
theorem StepOn.apply_eq {x : A} (hx : ∀ y, ¬ I x y ∧ ¬ I y x) (h : P.StepOn I C D) :
    D x = C x := by
  obtain ⟨a, b, hab, o, -, rfl⟩ := h
  refine upd_other _ (fun h => ?_) (fun h => ?_) _ <;> subst h
  exacts [(hx b).1 hab, (hx a).2 hab]

/-- An agent that interacts with nobody keeps its state along every run. -/
theorem reach_stepOn_apply_eq {x : A} (hx : ∀ y, ¬ I x y ∧ ¬ I y x)
    (h : Reach (P.StepOn I) C D) : D x = C x := by
  induction h with
  | refl => rfl
  | tail _ hst ih => rw [hst.apply_eq hx, ih]

/-- **Embedding a run of a sub-population.** Along an injective map `e : A' ↪ A` that maps
interacting pairs to interacting pairs, a run of the population `A'` from `C ∘ e` lifts to a run of
`A` from `C` whose restriction to the image of `e` is the given run. -/
theorem exists_reach_of_embedding {A' : Type*} [DecidableEq A'] {I' : A' → A' → Prop}
    (e : A' ↪ A) (hI : ∀ a b, I' a b → I (e a) (e b)) (C : Config A Q) {D' : Config A' Q}
    (h : Reach (P.StepOn I') (fun x => C (e x)) D') :
    ∃ D, Reach (P.StepOn I) C D ∧ (fun x => D (e x)) = D' := by
  induction h with
  | refl => exact ⟨C, .refl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, rfl⟩ := ih
    obtain ⟨a, b, hab, o, ho, rfl⟩ := hst
    refine ⟨upd D (e a) (e b) o, hD.tail ⟨e a, e b, hI a b hab, o, ho, rfl⟩, ?_⟩
    funext x
    simp only [upd, Function.update_apply, e.injective.eq_iff]

end NProtocol

/-! ### Deterministic protocols -/

namespace Protocol

variable [DecidableEq A] (P : Protocol Q)

/-- A deterministic protocol as a nondeterministic one (singleton outcomes). -/
def toN : NProtocol Q := ⟨fun p q => {P.δ p q}⟩

/-- The outcomes of `P.toN` are the singletons of the outcomes of `P`. -/
@[simp] theorem toN_δ (p q : Q) : P.toN.δ p q = {P.δ p q} := rfl

/-- An interaction of a deterministic protocol is the update by its outcome. -/
theorem interact_eq_upd (C : Config A Q) {a b : A} (h : a ≠ b) :
    P.interact C a b = upd C a b (P.δ (C a) (C b)) := by
  funext x
  by_cases hxb : x = b
  · subst hxb; simp [interact_self_right _ _ h]
  · by_cases hxa : x = a
    · subst hxa; rw [upd_left _ h]; simp
    · rw [upd_other _ hxa hxb, interact_other _ _ hxa hxb]

variable {P}

/-- Steps of `P.toN` are the steps of `P`. -/
theorem toN_step_iff {C D : Config A Q} : P.toN.Step C D ↔ P.Step C D := by
  constructor
  · rintro ⟨a, b, hab, o, rfl, rfl⟩
    exact ⟨a, b, hab, (P.interact_eq_upd C hab).symm⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, b, hab, _, rfl, P.interact_eq_upd C hab⟩

/-- Steps of `P.toN` are the steps of `P` (as relations). -/
theorem toN_step : P.toN.Step (A := A) = P.Step := by
  funext C D; exact propext toN_step_iff

/-- Reachability for `P.toN` is reachability for `P`. -/
theorem toN_reachable_iff {C D : Config A Q} : P.toN.Reachable C D ↔ P.Reachable C D := by
  rw [NProtocol.Reachable, toN_step]; rfl

/-- Protocol homomorphisms map runs to runs. -/
theorem Hom.reachable {Q' : Type*} {P' : Protocol Q'} (φ : P.Hom P') {C C' : Config A Q}
    (h : P.Reachable C C') : P'.Reachable (fun x => φ.f (C x)) (fun x => φ.f (C' x)) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨a, b, hab, rfl⟩ := hst
    exact ih.tail ⟨a, b, hab, φ.interact _ hab⟩

end Protocol

/-! ### Leaders -/

/-- The number of agents whose state is a leader state. -/
def numLeaders [Fintype A] (leader : Q → Bool) (C : Config A Q) : ℕ :=
  (Finset.univ.filter fun a => leader (C a) = true).card

end Cslib.PopulationProtocol
