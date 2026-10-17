/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.SelfStabilization.TransitionSystem
public import Cslib.Probability.Markov.Absorption

/-!
# Random schedulers: reachability versus probability one

For a transition relation `R` on a *finite* set of configurations, a random scheduler is a
row-stochastic kernel `T` whose positive-probability moves are transitions of `R`
(`hstep : ∀ x y, 0 < T x y → R x y`); if moreover every transition has positive probability
(`hpos`), qualitative "with probability `1`" statements reduce to reachability:

* `tendsto_compl_of_reach`: if a closed set `S` is reachable from every configuration, the
  probability of being outside `S` after `t` steps tends to `0`;
* `SelfStabilizes.tendsto`: in particular, self-stabilization (reachability of configurations
  stably in `S`) implies stabilization with probability `1`;
* `prob_eq_zero_of_not_reach`: conversely, if `S` is not reachable from `x`, the probability of
  being in `S` is `0` at all times (only `hstep` is needed).

The proofs are applications of `Cslib.Probability.Markov.tendsto_sum_compl_of_absorbing` and
`Cslib.Probability.Markov.pow_eq_zero_of_closed`.
-/

@[expose] public section

open Cslib.Probability.Markov Matrix Filter Topology

namespace Cslib.TransitionSystem

variable {X : Type*} [Fintype X] [DecidableEq X] {R : X → X → Prop} {T : Matrix X X ℝ}
  {S : Set X}

/-- **Reachability implies probability `1`.** For a Markov kernel whose positive-probability
moves are exactly the transitions: if a closed set `S` is reachable from every configuration, the
probability of being outside `S` after `t` steps tends to `0`. -/
theorem tendsto_compl_of_reach [Fintype S] (hT : T ∈ rowStochastic ℝ X)
    (hstep : ∀ x y, 0 < T x y → R x y) (hpos : ∀ x y, R x y → 0 < T x y) (hS : IsTrap R S)
    (h : ∀ x, ∃ y ∈ S, Reach R x y) (x : X) :
    Tendsto (fun t => ∑ y ∈ S.toFinsetᶜ, (T ^ t) x y) atTop (𝓝 0) := by
  refine tendsto_sum_compl_of_absorbing hT (fun a ha b hb => ?_) (fun a => ?_) x
  · by_contra hne
    have : 0 < T a b := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hT) (Ne.symm hne)
    exact hb (Set.mem_toFinset.2 (hS (Set.mem_toFinset.1 ha) (hstep _ _ this)))
  · obtain ⟨y, hy, hr⟩ := h a
    exact ⟨y, Set.mem_toFinset.2 hy, Relation.ReflTransGen.mono hpos _ _ hr⟩

/-- **Self-stabilization implies stabilization with probability `1`.** For a Markov kernel whose
positive-probability moves are exactly the transitions: if the system self-stabilizes to `S`, the
probability of not being stably in `S` after `t` steps tends to `0`. -/
theorem SelfStabilizes.tendsto [Fintype {x | StablyIn R S x}] (hT : T ∈ rowStochastic ℝ X)
    (hstep : ∀ x y, 0 < T x y → R x y) (hpos : ∀ x y, R x y → 0 < T x y)
    (h : SelfStabilizes R S) (x : X) :
    Tendsto (fun t => ∑ y ∈ {y | StablyIn R S y}.toFinsetᶜ, (T ^ t) x y) atTop (𝓝 0) :=
  tendsto_compl_of_reach hT hstep hpos isTrap_stablyIn
    (fun x => (h x).imp fun _ hy => ⟨hy.2, hy.1⟩) x

/-- **Unreachability implies probability `0`.** If no configuration of `S` is reachable from `x`,
then for every Markov kernel supported on the transitions the probability of being in `S` is `0`
at every time. -/
theorem prob_eq_zero_of_not_reach [Fintype S] (hT : T ∈ rowStochastic ℝ X)
    (hstep : ∀ x y, 0 < T x y → R x y) {x : X} (hx : ∀ y, Reach R x y → y ∉ S) (t : ℕ) :
    ∑ y ∈ S.toFinset, (T ^ t) x y = 0 :=
  Finset.sum_eq_zero fun y hy =>
    pow_eq_zero_of_closed hT (Reach R x) (fun _ _ ha hab => ha.tail (hstep _ _ hab)) .refl t
      fun h => hx y h (Set.mem_toFinset.1 hy)

end Cslib.TransitionSystem
