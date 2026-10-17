/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Basic

/-!
# Covering (FLM / "shifting scenario") simulation

The classical impossibility technique of Fischer, Lynch and Merritt [FischerLynchMerritt1986]: run
the protocol on a larger *covering system* `Q` in which every node `q̃` runs the code of the party
`φ q̃`; for each potential sender `p` the node `q̃` listens to a designated node `nbr q̃ p` (or to
nobody, modelling a silent/crashed party). If a set of honest parties `H` can be *lifted* into `Q`
by `σ` consistently (honest neighbours of honest parties are lifted to the designated neighbours),
then the Byzantine parties can simulate the rest of `Q`, so that every honest party has exactly the
history of its lift. Hence its decision is the decision of the lift in the covering system.

Compared to the usual formulation via graph covering maps, `nbr` may be partial (`none` = silent
neighbour), which also covers "split-brain" arguments where some copies are crashed.
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

variable {P I M O Q : Type*} (G : SimpleGraph P) (alg : Protocol P I M O)

/-- A covering system: node `q̃ : Q` runs the code of `φ q̃` on input `xq q̃`; its inbox entry for
the sender `p` is filled by the node `nbr q̃ p` (nobody if `none`). -/
structure CoverSystem (P I Q : Type*) where
  /-- The party whose code a node runs. -/
  φ : Q → P
  /-- The node a node listens to as sender `p`. -/
  nbr : Q → P → Option Q
  /-- The input of each node. -/
  xq : Q → I

namespace CoverSystem

variable {G alg}
variable (C : CoverSystem P I Q)

open Classical in
/-- Histories in the covering system (everybody runs the protocol). -/
noncomputable def hist (G : SimpleGraph P) (alg : Protocol P I M O) : ℕ → Q → History P M
  | 0, _ => []
  | r + 1, q => hist G alg r q ++
      [fun p => if G.Adj p (C.φ q) then
          (C.nbr q p).bind fun q' => alg.send (C.φ q') (C.xq q') (hist G alg r q') (C.φ q)
        else none]

/-- First decision of a node of the covering system. -/
def Decides (G : SimpleGraph P) (alg : Protocol P I M O) (q : Q) (o : O) : Prop :=
  FirstSome (fun r => alg.decide (C.φ q) (C.xq q) (C.hist G alg r q)) o

/-- A *lift* of the honest parties (the complement of `B`): they are
mapped to nodes running their code, consistently with honest-to-honest edges. -/
structure Lift (G : SimpleGraph P) (B : Set P) (σ : P → Q) : Prop where
  φ_σ : ∀ p, p ∉ B → C.φ (σ p) = p
  nbr_σ : ∀ p q, p ∉ B → q ∉ B → G.Adj p q → C.nbr (σ q) p = some (σ p)

open Classical in
/-- The real scenario simulated by the Byzantine parties `B`: honest parties get the inputs of their
lifts, Byzantine parties send what the designated nodes of the covering system send. -/
noncomputable def scenario (G : SimpleGraph P) (alg : Protocol P I M O) (B : Set P) (σ : P → Q)
    (x₀ : P → I) : Scenario P I M where
  byz := B
  input := fun p => if p ∈ B then x₀ p else C.xq (σ p)
  adv := fun r b q => (C.nbr (σ q) b).bind fun q' =>
    alg.send (C.φ q') (C.xq q') (C.hist G alg r q') q

variable {B : Set P} {σ : P → Q}

open Classical in
/-- **FLM simulation lemma**: honest parties have the histories of their lifts. -/
theorem hist_scenario (hL : C.Lift G B σ) (x₀ : P → I) :
    ∀ r p, p ∉ B → LockStep.hist G alg (C.scenario G alg B σ x₀) r p = C.hist G alg r (σ p) := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro q hq
    rw [LockStep.hist_succ, CoverSystem.hist, ih q hq]
    congr 1
    refine congrArg (fun f => [f]) (funext fun p => ?_)
    simp only [deliver, hL.φ_σ q hq]
    by_cases hadj : G.Adj p q
    · simp only [hadj, ite_true]
      by_cases hp : p ∈ B
      · simp [hp, scenario]
      · simp only [scenario, hp, ite_false]
        rw [hL.nbr_σ p q hp hq hadj, Option.bind_some, hL.φ_σ p hp]
        exact congrArg (fun h => alg.send p _ h q) (ih p hp)
    · simp [hadj]

/-- Honest parties decide exactly as their lifts do in the covering system. -/
theorem decides_scenario_iff (hL : C.Lift G B σ) (x₀ : P → I) {p : P} (hp : p ∉ B) (o : O) :
    LockStep.Decides G alg (C.scenario G alg B σ x₀) p o ↔ C.Decides G alg (σ p) o := by
  unfold LockStep.Decides CoverSystem.Decides status
  apply FirstSome.congr
  intro r
  rw [hist_scenario C hL x₀ r p hp]
  simp [scenario, hp, hL.φ_σ p hp]

@[simp] lemma scenario_byz (x₀ : P → I) : (C.scenario G alg B σ x₀).byz = B := rfl

lemma scenario_reliable (x₀ : P → I) : (C.scenario G alg B σ x₀).Reliable := fun _ _ _ h => h

lemma scenario_input_of_not_mem (x₀ : P → I) {p : P} (hp : p ∉ B) :
    (C.scenario G alg B σ x₀).input p = C.xq (σ p) := by simp [scenario, hp]

end CoverSystem

end Cslib.Byzantine.LockStep
