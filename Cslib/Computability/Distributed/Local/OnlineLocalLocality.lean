/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.Local.Locality
public import Cslib.Computability.Distributed.Local.OnlineLocal
public import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner

/-!
# Online-LOCAL balls and LOCAL locality

Bridges between the Online-LOCAL model (`Cslib.Computability.Distributed.Local.OnlineLocal`) and
the extensional locality of LOCAL algorithms (`Cslib.Computability.Distributed.Local.Locality`).

## Main results

* `Cslib.OnlineLocal.mem_ball_singleton_iff`, `Cslib.OnlineLocal.ball_eq_biUnion_closedBall`: the
  Online-LOCAL ball around a set is the union of the closed balls around its nodes.
* `Cslib.OnlineLocal.AgreeOn.gAgree`: Online-LOCAL indistinguishability around a node implies
  LOCAL agreement (`Cslib.Local.GAgree`).
-/

@[expose] public section

namespace Cslib.OnlineLocal

open SimpleGraph Cslib.Local

variable {V : Type*} {G H₁ H₂ : SimpleGraph V} {U : Set V} {u x : V} {k : ℕ}

/-- The Online-LOCAL ball around one node is the closed ball. -/
lemma mem_ball_singleton_iff : x ∈ ball G {u} k ↔ G.edist u x ≤ k := by
  rw [mem_ball_iff_walk, edist_le_coe_iff]
  constructor
  · rintro ⟨u', rfl, p, hp⟩; exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩; exact ⟨u, rfl, p, hp⟩

/-- The Online-LOCAL ball around a set is the union of the closed balls around its nodes. -/
lemma ball_eq_biUnion_closedBall : ball G U k = ⋃ u ∈ U, G.closedBall u k := by
  ext x
  simp only [mem_ball_iff_walk, Set.mem_iUnion, mem_closedBall', edist_le_coe_iff, exists_prop]

/-- Online-LOCAL indistinguishability around a single node implies LOCAL agreement. (The converse
fails: `AgreeOn` also requires agreement of the edges between two nodes at distance `T`.) -/
lemma AgreeOn.gAgree (h : AgreeOn H₁ H₂ {u} k) : GAgree H₁ H₂ u k := by
  intro x hx y
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)
  rw [← hj] at hx
  exact h.inner j (by exact_mod_cast hx) x (mem_ball_singleton_iff.2 hj.ge) y

end Cslib.OnlineLocal

