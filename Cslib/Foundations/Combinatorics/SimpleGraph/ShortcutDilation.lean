/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.Shortcut
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Dilation of tree-restricted shortcuts

* `RootedTree.exists_walk_climb`: climbing along `H`-edges from `x` takes at most `depth x` steps.
* `RootedTree.climb_eq_of_reachable`: `climb H` is constant on the blocks (components of
  `blockGraph H`) when `H` is `T`-restricted.
* `RootedTree.exists_partGraph_walk_of_reachable`: two vertices of one block are at distance
  `≤ 2D` in `G[P] + H` (for a tree of depth `≤ D`).
* `RootedTree.exists_partGraph_walk_numBlocks`, `RootedTree.dilationLE_of_numBlocks_le`: a
  `T`-restricted shortcut with `b` blocks (each meeting the part) has dilation `≤ b (2D + 1)`
  (Observation 2.6 of Ghaffari–Haeupler, PODC'21).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- If the shortcut edges are edges of `G`, the block graph is a subgraph of `G[P] + H`. -/
theorem blockGraph_le_partGraph {P : Finset V} {H : Finset (Sym2 V)}
    (hH : ∀ e ∈ H, e ∈ G.edgeSet) : blockGraph H ≤ partGraph G P H := by
  intro x y h
  rw [blockGraph, fromEdgeSet_adj] at h
  exact ⟨(G.mem_edgeSet).1 (hH _ h.1), Or.inr h.1⟩

namespace RootedTree

variable {T : G.RootedTree}

theorem Restricts.subset_edgeSet {H : Finset (Sym2 V)} (hH : T.Restricts H) :
    ∀ e ∈ H, e ∈ G.edgeSet :=
  fun e he => edge_mem_graph_edgeSet (hH e he)

variable [DecidableEq V]

/-- Climbing from `x` along `H`-edges reaches `climb H x` after at most `depth x` steps. -/
theorem exists_walk_climb (H : Finset (Sym2 V)) (x : V) :
    ∃ q : (blockGraph H).Walk x (T.climb H x), q.length ≤ T.depth x := by
  induction hd : T.depth x using Nat.strong_induction_on generalizing x with
  | _ d ih =>
    by_cases h : x ≠ T.root ∧ T.edge x ∈ H
    · obtain ⟨q, hq⟩ := ih _ (hd ▸ depth_parent_lt h.1) (T.parent x) rfl
      have hadj : (blockGraph H).Adj x (T.parent x) := by
        rw [blockGraph, fromEdgeSet_adj]; exact ⟨h.2, (parent_ne_self h.1).symm⟩
      rw [climb_of_mem h.1 h.2]
      refine ⟨Walk.cons hadj q, ?_⟩
      have := T.depth_parent x h.1
      simp only [Walk.length_cons]; omega
    · rw [climb_of_not_mem h]
      exact ⟨Walk.nil, by simp⟩

/-- For a `T`-restricted `H`, the climb is the same at both ends of an `H`-edge. -/
theorem climb_eq_of_adj {H : Finset (Sym2 V)} (hH : T.Restricts H) {u v : V}
    (h : (blockGraph H).Adj u v) : T.climb H u = T.climb H v := by
  rw [blockGraph, fromEdgeSet_adj] at h
  obtain ⟨w, hw, he⟩ := hH _ h.1
  have hw' : T.climb H w = T.climb H (T.parent w) := climb_of_mem hw (by rw [← he]; exact h.1)
  unfold edge at he
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hw'
  · exact hw'.symm

/-- For a `T`-restricted `H`, the climb is constant on each block. -/
theorem climb_eq_of_reachable {H : Finset (Sym2 V)} (hH : T.Restricts H) {u v : V}
    (h : (blockGraph H).Reachable u v) : T.climb H u = T.climb H v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (climb_eq_of_adj hH ha).trans ih

omit [DecidableEq V] in
/-- Two vertices of one block are joined in `G[P] + H` by a walk of length `≤ 2D`. -/
theorem exists_partGraph_walk_of_reachable {D : ℕ} (hT : T.DepthLE D) {P : Finset V}
    {H : Finset (Sym2 V)} (hH : T.Restricts H) {x y : V} (h : (blockGraph H).Reachable x y) :
    ∃ q : (partGraph G P H).Walk x y, q.length ≤ 2 * D := by
  classical
  obtain ⟨q1, h1⟩ := exists_walk_climb (T := T) H x
  obtain ⟨q2, h2⟩ := exists_walk_climb (T := T) H y
  have he := climb_eq_of_reachable hH h
  refine ⟨(q1.append (q2.reverse.copy he.symm rfl)).mapLe
    (blockGraph_le_partGraph hH.subset_edgeSet), ?_⟩
  simp only [Walk.length_mapLe, Walk.length_append, Walk.length_copy, Walk.length_reverse]
  have := hT x; have := hT y; omega

omit [DecidableEq V] in
/-- A `T`-restricted shortcut `H` for a connected part `P` whose blocks all meet `P`: any two
vertices of `P ∪ V(H)` are joined in `G[P] + H` by a walk of length `< numBlocks P H * (2D + 1)`.
-/
theorem exists_partGraph_walk_numBlocks {D : ℕ} (hT : T.DepthLE D) {P : Finset V}
    (hP : (G.induce (P : Set V)).Connected) {H : Finset (Sym2 V)} (hH : T.Restricts H)
    (hB : BlocksMeetPart P H) {x y : V} (hx : x ∈ partVerts P H) (hy : y ∈ partVerts P H) :
    ∃ q : (partGraph G P H).Walk x y, q.length + 1 ≤ numBlocks P H * (2 * D + 1) := by
  classical
  let S : Set (blockGraph H).ConnectedComponent :=
    (blockGraph H).connectedComponentMk '' (P : Set V)
  have hS : (blockGraph H).connectedComponentMk '' partVerts P H = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hzy⟩ := hB z hz
      exact ⟨y, hy, (ConnectedComponent.eq.2 hzy).symm⟩
    · exact Set.image_mono Set.subset_union_left
  -- The graph on the blocks: two blocks are adjacent if a `G`-edge inside `P` joins them.
  let Bg : SimpleGraph S := fromRel fun c c' => ∃ u ∈ P, ∃ v ∈ P, G.Adj u v ∧
    (blockGraph H).connectedComponentMk u = c.1 ∧ (blockGraph H).connectedComponentMk v = c'.1
  have hfin : S.Finite := (P.finite_toSet).image _
  have : Fintype S := hfin.fintype
  have hcard : Fintype.card S = numBlocks P H := by
    rw [numBlocks, hS, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- Lifting a walk in the block graph to a walk in `G[P] + H`.
  have lift : ∀ (c c' : S) (p : Bg.Walk c c') (x y : V),
      (blockGraph H).connectedComponentMk x = c.1 →
      (blockGraph H).connectedComponentMk y = c'.1 →
      ∃ q : (partGraph G P H).Walk x y, q.length ≤ p.length * (2 * D + 1) + 2 * D := by
    intro c c' p
    induction p with
    | nil =>
      intro x y hx hy
      obtain ⟨q, hq⟩ := exists_partGraph_walk_of_reachable (P := P) hT hH
        (ConnectedComponent.exact (hx.trans hy.symm))
      exact ⟨q, by simpa using hq⟩
    | @cons c c'' c' h p ih =>
      intro x y hx hy
      rw [fromRel_adj] at h
      obtain ⟨u, hu, v, hv, huv, hcu, hcv⟩ : ∃ u ∈ P, ∃ v ∈ P, G.Adj u v ∧
          (blockGraph H).connectedComponentMk u = c.1 ∧
          (blockGraph H).connectedComponentMk v = c''.1 := by
        rcases h.2 with h | ⟨u, hu, v, hv, huv, h1, h2⟩
        · exact h
        · exact ⟨v, hv, u, hu, huv.symm, h2, h1⟩
      obtain ⟨q1, hq1⟩ := exists_partGraph_walk_of_reachable (P := P) hT hH
        (ConnectedComponent.exact (hx.trans hcu.symm))
      obtain ⟨q2, hq2⟩ := ih v y hcv hy
      have hadj : (partGraph G P H).Adj u v := ⟨huv, Or.inl ⟨hu, hv⟩⟩
      refine ⟨q1.append (Walk.cons hadj q2), ?_⟩
      simp only [Walk.length_append, Walk.length_cons]
      have : (p.length + 1) * (2 * D + 1) = p.length * (2 * D + 1) + 2 * D + 1 := by ring
      omega
  -- The block graph is connected since `G[P]` is.
  let f : ↥(P : Set V) → S := fun a => ⟨(blockGraph H).connectedComponentMk a.1, a.1, a.2, rfl⟩
  have conn : ∀ a b : ↥(P : Set V), Bg.Reachable (f a) (f b) := by
    intro a b
    obtain ⟨p⟩ := hP.preconnected a b
    induction p with
    | nil => rfl
    | @cons a c b h p ih =>
      refine Reachable.trans ?_ ih
      by_cases hac : f a = f c
      · rw [hac]
      · apply Adj.reachable
        rw [fromRel_adj]
        exact ⟨hac, Or.inl ⟨a.1, a.2, c.1, c.2, by simpa using h, rfl, rfl⟩⟩
  obtain ⟨x', hx', hxx'⟩ := hB x hx
  obtain ⟨y', hy', hyy'⟩ := hB y hy
  obtain ⟨p⟩ := conn ⟨x', hx'⟩ ⟨y', hy'⟩
  have hlen : p.bypass.length < Fintype.card S := p.bypass_isPath.length_lt
  obtain ⟨q, hq⟩ := lift _ _ p.bypass x y (ConnectedComponent.eq.2 hxx')
    (ConnectedComponent.eq.2 hyy')
  refine ⟨q, ?_⟩
  rw [← hcard]
  calc q.length + 1 ≤ (p.bypass.length + 1) * (2 * D + 1) := by
        have : (p.bypass.length + 1) * (2 * D + 1) = p.bypass.length * (2 * D + 1) + 2 * D + 1 :=
          by ring
        omega
    _ ≤ Fintype.card S * (2 * D + 1) := Nat.mul_le_mul_right _ hlen

omit [DecidableEq V] in
/-- A `T`-restricted shortcut for a connected part `P`, with at most `b` blocks each meeting `P`,
has dilation at most `b (2D + 1)` when `T` has depth `≤ D`. -/
theorem dilationLE_of_numBlocks_le {D : ℕ} (hT : T.DepthLE D) {P : Finset V}
    (hP : (G.induce (P : Set V)).Connected) {H : Finset (Sym2 V)} (hH : T.Restricts H)
    (hB : BlocksMeetPart P H) {b : ℝ} (hb : (numBlocks P H : ℝ) ≤ b) :
    G.DilationLE P H (b * (2 * D + 1)) := by
  classical
  intro x hx y hy
  obtain ⟨q, hq⟩ := exists_partGraph_walk_numBlocks hT hP hH hB hx hy
  refine ⟨q.reachable, ?_⟩
  have h1 : (partGraph G P H).dist x y ≤ q.length := dist_le q
  have h2 : (partGraph G P H).dist x y ≤ numBlocks P H * (2 * D + 1) := by omega
  calc ((partGraph G P H).dist x y : ℝ) ≤ (numBlocks P H : ℝ) * (2 * D + 1) := by
        exact_mod_cast h2
    _ ≤ b * (2 * D + 1) := by gcongr

end RootedTree

end SimpleGraph
