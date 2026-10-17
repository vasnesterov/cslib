/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.PopulationProtocols.Nondet
public import Cslib.Probability.Markov.Absorption

/-!
# The uniformly random scheduler

The standard probabilistic semantics of population protocols: at each step an ordered pair of
distinct agents is drawn uniformly at random and interacts. For a deterministic protocol this is
the Markov kernel `uniformKernel P` on configurations (`Cslib.Probability.Markov.randomMap`).

* `uniformKernel_mem`: it is row-stochastic (at least two agents);
* `uniformKernel_pos_iff`: its positive entries are exactly the protocol's steps, so the
  reachability/probability-`1` bridge of `SelfStabilization/Markov.lean` applies to it.
-/

@[expose] public section

open Cslib.Probability.Markov Matrix

namespace Cslib.PopulationProtocol

variable {Q A : Type*} [DecidableEq A] [Fintype A] [DecidableEq Q]

/-- Ordered pairs of distinct agents. -/
abbrev Pairs (A : Type*) := {p : A × A // p.1 ≠ p.2}

/-- The Markov kernel of a deterministic protocol under the uniformly random scheduler: an ordered
pair of distinct agents is drawn uniformly and interacts. -/
noncomputable def uniformKernel (P : Protocol Q) : Matrix (Config A Q) (Config A Q) ℝ :=
  randomMap (fun _ : Pairs A => 1 / (Fintype.card (Pairs A) : ℝ))
    (fun ω C => P.interact C ω.1.1 ω.1.2)

/-- With at least two agents, `uniformKernel P` is row-stochastic. -/
theorem uniformKernel_mem [Fintype Q] (P : Protocol Q) (hA : 2 ≤ Fintype.card A) :
    uniformKernel (A := A) P ∈ rowStochastic ℝ (Config A Q) := by
  have hne : Nonempty (Pairs A) := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hA
    exact ⟨⟨(a, b), hab⟩⟩
  refine randomMap_mem_rowStochastic (fun _ => by positivity) ?_ _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Pairs A) : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := Pairs A); positivity
  field_simp

/-- The positive entries of `uniformKernel P` are exactly the steps of the protocol. -/
theorem uniformKernel_pos_iff (P : Protocol Q) (C D : Config A Q) :
    0 < uniformKernel (A := A) P C D ↔ P.toN.Step C D := by
  rw [Protocol.toN_step_iff]
  constructor
  · intro h
    obtain ⟨ω, -, hω⟩ := exists_of_randomMap_pos h
    exact ⟨ω.1.1, ω.1.2, ω.2, hω.symm⟩
  · rintro ⟨a, b, hab, rfl⟩
    have : Nonempty (Pairs A) := ⟨⟨(a, b), hab⟩⟩
    have hc : (0 : ℝ) < Fintype.card (Pairs A) := by exact_mod_cast Fintype.card_pos
    have hμ : ∀ ω : Pairs A, (0 : ℝ) ≤ 1 / (Fintype.card (Pairs A) : ℝ) := fun _ => by positivity
    exact randomMap_pos hμ (fun ω C => P.interact C ω.1.1 ω.1.2)
      (ω := (⟨(a, b), hab⟩ : Pairs A)) (by positivity) C

end Cslib.PopulationProtocol
