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
* `NProtocol.ClosedStates P H`: every possible outcome of an interaction between states of `H`
  consists of states of `H`.
* `NProtocol.StepIn P S`, `NProtocol.ReachIn P S`: interactions inside the sub-population `S` (the
  other agents are idle).
* `NProtocol.SilentOn P I C` (`NProtocol.Silent` for the complete interaction graph): every
  possible interaction leaves both states unchanged.
* `NProtocol.OutputStable P I out C`: the output can never change again.

## Main results

* `NProtocol.exists_reach_of_embedding`: a run of a sub-population embeds into the whole
  population (the other agents being idle); `NProtocol.reach_stepOn_apply_eq`: idle agents keep
  their states.
* `Protocol.toN_step_iff`, `Protocol.toN_reachable_iff`, `Protocol.Hom.reachable`.
* `NProtocol.ClosedStates.reach`: runs starting inside a closed set of states stay inside it;
  deterministic protocols: `Protocol.toN_closedStates_iff`.
* `NProtocol.exists_reachIn_of_embedding`: a run of a population `A'` embeds into a
  sub-population of `A`.
* `NProtocol.silentOn_iff_isSilent`: for irreflexive `I`, silence is silence of the step relation.
* `Protocol.toN_outputStable_iff`: output stability of `P.toN` is `Protocol.OutputStable`.
* `NProtocol.exists_stepOn`: with nonempty transition sets and some interacting pair, every
  configuration has a successor (needed for fair runs).
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

/-! ### Closed sets of states, sub-populations, silence, output stability -/

namespace NProtocol

/-! ### Closed sets of states -/

/-- A set of states `H` is *closed* under `P` if every possible outcome of an interaction
between two states of `H` consists of states of `H`. -/
def ClosedStates (P : NProtocol Q) (H : Set Q) : Prop :=
  ∀ p ∈ H, ∀ q ∈ H, ∀ o ∈ P.δ p q, o.1 ∈ H ∧ o.2 ∈ H

variable [DecidableEq A] {P : NProtocol Q} {I J : A → A → Prop} {H : Set Q} {C D : Config A Q}

/-- A step keeps a configuration inside a closed set of states. -/
theorem ClosedStates.stepOn (hH : P.ClosedStates H) (hC : ∀ x, C x ∈ H)
    (h : P.StepOn I C D) : ∀ x, D x ∈ H := by
  obtain ⟨a, b, -, o, ho, rfl⟩ := h
  have h := hH _ (hC a) _ (hC b) o ho
  intro x
  by_cases hxb : x = b
  · subst hxb; rw [upd_right]; exact h.2
  · by_cases hxa : x = a
    · subst hxa; rw [upd, Function.update_of_ne hxb, Function.update_self]; exact h.1
    · rw [upd_other _ hxa hxb]; exact hC x

/-- **Closed sets of states are invariant.** If `C` only uses states of a closed set `H`, so does
every configuration reachable from `C`. -/
theorem ClosedStates.reach (hH : P.ClosedStates H) (hC : ∀ x, C x ∈ H)
    (h : Reach (P.StepOn I) C D) : ∀ x, D x ∈ H := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact hH.stepOn ih hst

/-! ### Sub-populations -/

variable (P) in
/-- One interaction of two distinct agents of the sub-population `S` (the other agents are
idle). -/
abbrev StepIn (S : A → Prop) : Config A Q → Config A Q → Prop :=
  P.StepOn fun a b => S a ∧ S b ∧ a ≠ b

variable (P) in
/-- Reachability inside the sub-population `S` (the other agents are idle). -/
abbrev ReachIn (S : A → Prop) : Config A Q → Config A Q → Prop := Reach (P.StepIn S)

/-- A run of a sub-population is a run of the population. -/
theorem ReachIn.reachable {S : A → Prop} (h : P.ReachIn S C D) : P.Reachable C D :=
  reach_stepOn_mono (fun _ _ h => h.2.2) h

/-- A run of a sub-population is a run of any larger sub-population. -/
theorem ReachIn.mono {S S' : A → Prop} (hS : ∀ x, S x → S' x) (h : P.ReachIn S C D) :
    P.ReachIn S' C D :=
  reach_stepOn_mono (fun a b h => ⟨hS a h.1, hS b h.2.1, h.2.2⟩) h

/-- Agents outside the sub-population keep their states. -/
theorem ReachIn.apply_eq {S : A → Prop} (h : P.ReachIn S C D) {x : A} (hx : ¬ S x) :
    D x = C x :=
  reach_stepOn_apply_eq (fun _ => ⟨fun h => hx h.1, fun h => hx h.2.1⟩) h

/-- **Embedding a run of another population.** If `e : A' ↪ A` and the population `A'` can go
from `C ∘ e` to `D'`, then the image of `e` can go from `C` to a configuration that agrees with
`D'` on the image of `e` (and with `C` elsewhere, `ReachIn.apply_eq`). -/
theorem exists_reachIn_of_embedding {A' : Type*} [DecidableEq A'] (e : A' ↪ A) (C : Config A Q)
    {D' : Config A' Q} (h : P.Reachable (fun x => C (e x)) D') :
    ∃ D, P.ReachIn (fun x => ∃ y, e y = x) C D ∧ (fun x => D (e x)) = D' :=
  P.exists_reach_of_embedding e (fun a b hab => ⟨⟨a, rfl⟩, ⟨b, rfl⟩, e.injective.ne hab⟩) C h

/-! ### Silent configurations -/

variable (P) in
/-- A configuration is *silent* along `I` if every possible interaction along `I` leaves both
states unchanged. -/
def SilentOn (I : A → A → Prop) (C : Config A Q) : Prop :=
  ∀ a b, I a b → ∀ o ∈ P.δ (C a) (C b), o = (C a, C b)

variable (P) in
/-- A silent configuration on the complete interaction graph. -/
abbrev Silent : Config A Q → Prop := P.SilentOn (· ≠ ·)

/-- For an irreflexive interaction relation, silence is silence of the step relation. -/
theorem silentOn_iff_isSilent (hI : ∀ a, ¬ I a a) : P.SilentOn I C ↔ IsSilent (P.StepOn I) C := by
  constructor
  · rintro hC D ⟨a, b, hab, o, ho, rfl⟩
    have hne : a ≠ b := by rintro rfl; exact hI a hab
    rw [hC a b hab o ho, upd_self _ hne]
  · intro hC a b hab o ho
    have hne : a ≠ b := by rintro rfl; exact hI a hab
    have h := hC _ ⟨a, b, hab, o, ho, rfl⟩
    rw [← congrFun h a, ← congrFun h b, upd_left _ hne, upd_right]

/-- Silence on the complete interaction graph is silence of `P.Step`. -/
theorem silent_iff_isSilent : P.Silent C ↔ IsSilent P.Step C :=
  silentOn_iff_isSilent fun _ h => h rfl

/-- Nothing changes from a silent configuration. -/
theorem SilentOn.reach_eq (hI : ∀ a, ¬ I a a) (hC : P.SilentOn I C)
    (h : Reach (P.StepOn I) C D) : D = C :=
  ((silentOn_iff_isSilent hI).1 hC).reach_eq h

/-- A silent configuration in a set `S` is stably in `S`. -/
theorem SilentOn.stablyIn (hI : ∀ a, ¬ I a a) {S : Set (Config A Q)} (hC : P.SilentOn I C)
    (hS : C ∈ S) : StablyIn (P.StepOn I) S C :=
  ((silentOn_iff_isSilent hI).1 hC).stablyIn hS

/-- Nothing changes from a silent configuration (complete interaction graph). -/
theorem Silent.reach_eq (hC : P.Silent C) (h : P.Reachable C D) : D = C :=
  SilentOn.reach_eq (fun _ h => h rfl) hC h

/-- A silent configuration in a set `S` is stably in `S` (complete interaction graph). -/
theorem Silent.stablyIn {S : Set (Config A Q)} (hC : P.Silent C) (hS : C ∈ S) :
    StablyIn P.Step S C :=
  SilentOn.stablyIn (fun _ h => h rfl) hC hS

/-! ### Output stability -/

variable (P) in
/-- The output of `C` (for an output map `out` on states) is *stable* along `I`: no configuration
reachable from `C` has a different output. -/
def OutputStable {O : Type*} (I : A → A → Prop) (out : Q → O) (C : Config A Q) : Prop :=
  ∀ D, Reach (P.StepOn I) C D → ∀ a, out (D a) = out (C a)

/-- Output stability is the stability of the set of configurations with the same output. -/
theorem outputStable_iff_stablyIn {O : Type*} {out : Q → O} :
    P.OutputStable I out C ↔ StablyIn (P.StepOn I) {D | ∀ a, out (D a) = out (C a)} C :=
  Iff.rfl

/-- Output-stable configurations are closed under steps. -/
theorem isTrap_outputStable {O : Type*} (out : Q → O) :
    IsTrap (P.StepOn I) {C | P.OutputStable I out C} := by
  intro C D hC hCD E hDE v
  rw [hC E (Relation.ReflTransGen.head hCD hDE) v, hC D (Relation.ReflTransGen.single hCD) v]

/-- The output stays the same along runs from an output-stable configuration. -/
theorem OutputStable.apply_eq {O : Type*} {out : Q → O} (hC : P.OutputStable I out C)
    (h : Reach (P.StepOn I) C D) (a : A) : out (D a) = out (C a) :=
  hC D h a

/-- The number of leaders does not change along runs from an output-stable configuration. -/
theorem OutputStable.numLeaders_eq [Fintype A] {leader : Q → Bool}
    (hC : P.OutputStable I leader C) (h : Reach (P.StepOn I) C D) :
    numLeaders leader D = numLeaders leader C := by
  unfold numLeaders
  congr 1
  ext v
  simp [hC D h v]

/-! ### Totality -/

/-- If some pair of agents may interact and every transition set is nonempty, every
configuration has a successor. -/
theorem exists_stepOn (hI : ∃ a b, I a b) (hδ : ∀ p q, (P.δ p q).Nonempty) (C : Config A Q) :
    ∃ D, P.StepOn I C D := by
  obtain ⟨a, b, hab⟩ := hI
  obtain ⟨o, ho⟩ := hδ (C a) (C b)
  exact ⟨_, a, b, hab, o, ho, rfl⟩

end NProtocol

/-! ### Deterministic protocols -/

namespace Protocol

variable {P : Protocol Q} {H : Set Q}

/-- A closed set of states of `P` is a closed set of states of `P.toN`. -/
theorem toN_closedStates_iff : P.toN.ClosedStates H ↔ P.ClosedStates H := by
  simp [NProtocol.ClosedStates, ClosedStates]

variable [DecidableEq A]

/-- Output stability for `P.toN` (complete interaction graph) is CSLib's output stability. -/
theorem toN_outputStable_iff {O : Type*} {out : Q → O} {C : Config A Q} :
    P.toN.OutputStable (· ≠ ·) out C ↔ P.OutputStable out C :=
  ⟨fun h D hD => h D (toN_reachable_iff.2 hD), fun h D hD => h D (toN_reachable_iff.1 hD)⟩

end Protocol

end Cslib.PopulationProtocol
