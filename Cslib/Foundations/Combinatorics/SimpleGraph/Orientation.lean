/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity

/-!
# Orientations of simple graphs

An orientation of a simple graph `G` gives every edge exactly one direction. It is the output of
the *sinkless orientation* problem and of low out-degree orientation algorithms.

## Main definitions

* `SimpleGraph.Orientation G`: `o.out u v` means that the edge `uv` is oriented from `u` to `v`;
  every edge gets exactly one direction.
* `Orientation.IsSink o v`: `v` has no outgoing edge; `Orientation.IsSinkless o`: there is no sink.
* `SimpleGraph.OutOrientation.toOrientation`: CSLib's out-degree-bounded orientations
  (`SimpleGraph.OutOrientation`, where an edge may be oriented both ways) give orientations with
  the same out-degree bound (`OutOrientation.toOrientation_out`).

## Main results

* `Orientation.out_iff_not_out`: on an edge, exactly one direction holds.
* `SimpleGraph.hasOutDegLE_iff`: for locally finite graphs, `G.HasOutDegLE α` iff some orientation
  has all out-degrees at most `α`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

variable (G) in
/-- An orientation of the edges of `G`: `o.out u v` means that the edge `uv` is oriented from `u`
to `v` (it is an *outgoing* edge of `u`). Every edge gets exactly one direction. -/
structure Orientation where
  /-- `out u v`: the edge `uv` is oriented from `u` to `v`. -/
  out : V → V → Prop
  /-- Only edges of `G` are oriented. -/
  adj_of_out : ∀ ⦃u v⦄, out u v → G.Adj u v
  /-- Every edge gets a direction. -/
  out_or_out : ∀ ⦃u v⦄, G.Adj u v → out u v ∨ out v u
  /-- No edge gets both directions. -/
  not_out_of_out : ∀ ⦃u v⦄, out u v → ¬ out v u

namespace Orientation

variable (o : G.Orientation) {u v : V}

/-- On an edge, `uv` is oriented from `u` to `v` iff it is not oriented from `v` to `u`. -/
lemma out_iff_not_out (h : G.Adj u v) : o.out u v ↔ ¬ o.out v u :=
  ⟨fun h' => o.not_out_of_out h', fun h' => (o.out_or_out h).resolve_right h'⟩

/-- `v` is a sink: it has no outgoing edge. -/
def IsSink (v : V) : Prop := ∀ u, ¬ o.out v u

/-- The orientation is sinkless: every vertex has an outgoing edge. -/
def IsSinkless : Prop := ∀ v, ¬ o.IsSink v

/-- An orientation is sinkless iff every vertex has an out-neighbour. -/
lemma isSinkless_iff : o.IsSinkless ↔ ∀ v, ∃ u, o.out v u := by
  simp [IsSinkless, IsSink]

/-- The out-neighbours of `v`. -/
def outSet (v : V) : Set V := {u | o.out v u}

/-- Out-neighbours are neighbours. -/
lemma outSet_subset_neighborSet (v : V) : o.outSet v ⊆ G.neighborSet v :=
  fun _ h => o.adj_of_out h

end Orientation

/-! ### Bridge to out-degree-bounded orientations -/

namespace OutOrientation

variable {α : ℕ} (O : G.OutOrientation α)

/-- An out-degree-bounded orientation in which edges may be oriented both ways gives an
orientation: an edge oriented both ways is kept in the direction given by a fixed well-order on
`V`. -/
def toOrientation : G.Orientation where
  out u v := v ∈ O.out u ∧ (u ∈ O.out v → WellOrderingRel u v)
  adj_of_out _ _ h := O.adj_of_mem h.1
  out_or_out u v h := by
    rcases O.mem_or_mem h with h1 | h1
    · by_cases h2 : u ∈ O.out v
      · rcases trichotomous_of WellOrderingRel u v with h3 | rfl | h3
        · exact Or.inl ⟨h1, fun _ => h3⟩
        · exact absurd h (G.loopless.irrefl _)
        · exact Or.inr ⟨h2, fun _ => h3⟩
      · exact Or.inl ⟨h1, fun h' => absurd h' h2⟩
    · by_cases h2 : v ∈ O.out u
      · rcases trichotomous_of WellOrderingRel u v with h3 | rfl | h3
        · exact Or.inl ⟨h2, fun _ => h3⟩
        · exact absurd h (G.loopless.irrefl _)
        · exact Or.inr ⟨h1, fun _ => h3⟩
      · exact Or.inr ⟨h1, fun h' => absurd h' h2⟩
  not_out_of_out _ _ h h' := asymm_of WellOrderingRel (h.2 h'.1) (h'.2 h.1)

/-- An edge oriented from `u` to `v` by `toOrientation` is an out-edge of `u` in `O`. -/
lemma toOrientation_out {u v : V} (h : O.toOrientation.out u v) : v ∈ O.out u := h.1

/-- `toOrientation` keeps the out-degree bound. -/
lemma ncard_outSet_toOrientation_le (v : V) : (O.toOrientation.outSet v).ncard ≤ α :=
  calc (O.toOrientation.outSet v).ncard ≤ ((O.out v : Finset V) : Set V).ncard :=
        Set.ncard_le_ncard (fun _ h => O.toOrientation_out h) (Finset.finite_toSet _)
    _ = (O.out v).card := Set.ncard_coe_finset _
    _ ≤ α := O.card_out_le v

end OutOrientation

/-- For a locally finite graph, `G.HasOutDegLE α` iff `G` has an orientation with all
out-degrees at most `α`. -/
theorem hasOutDegLE_iff [G.LocallyFinite] {α : ℕ} :
    G.HasOutDegLE α ↔ ∃ o : G.Orientation, ∀ v, (o.outSet v).ncard ≤ α := by
  classical
  constructor
  · rintro ⟨O⟩
    exact ⟨O.toOrientation, O.ncard_outSet_toOrientation_le⟩
  · rintro ⟨o, ho⟩
    refine ⟨{ out := fun v => (G.neighborFinset v).filter (o.out v)
              adj_of_mem := fun u v h => ?_
              mem_or_mem := fun u v h => ?_
              card_out_le := fun v => ?_ }⟩
    · exact (mem_neighborFinset _ _ _).1 (Finset.mem_filter.1 h).1
    · rcases o.out_or_out h with h' | h'
      · exact Or.inl (Finset.mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 h, h'⟩)
      · exact Or.inr (Finset.mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 h.symm, h'⟩)
    · refine le_trans (le_of_eq ?_) (ho v)
      rw [← Set.ncard_coe_finset]
      congr 1
      ext u
      simpa [Orientation.outSet] using fun h => o.adj_of_out (u := v) (v := u) h

end SimpleGraph
