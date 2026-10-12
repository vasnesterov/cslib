/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# BFS trees

A connected graph has, for every root `r`, a rooted spanning tree in which the depth of a vertex
is its distance to `r` (a BFS tree): the parent of `v ≠ r` is any neighbour one step closer to
`r`. In particular, if all distances are at most `D`, the tree has depth at most `D`.

## Main definitions

* `SimpleGraph.Connected.bfsTree`: the BFS tree rooted at `r`.

## Main results

* `SimpleGraph.Connected.bfsTree_depth`: its depths are the distances to the root.
* `SimpleGraph.exists_rootedTree_depthLE`: a connected graph with all distances `≤ D` has a
  rooted spanning tree of depth `≤ D` (with any prescribed root).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- In a connected graph, every vertex `v ≠ r` has a neighbour one step closer to `r`. -/
theorem Connected.exists_adj_dist_succ (hG : G.Connected) (r : V) {v : V} (hv : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.dist r w + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact absurd rfl hv
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    have h1 : G.dist r w ≤ q.length := by rw [dist_comm]; exact dist_le q
    have h2 : G.dist r v ≤ G.dist r w + G.dist w v := hG.dist_triangle
    rw [dist_comm (u := w), dist_eq_one_iff_adj.2 h] at h2
    rw [dist_comm (u := v)] at hp
    simp only [Walk.length_cons] at hp
    omega

/-- The BFS tree of a connected graph rooted at `r`: the depth of `v` is `G.dist r v`, and the
parent of `v ≠ r` is a neighbour one step closer to `r`. -/
noncomputable def Connected.bfsTree [DecidableEq V] (hG : G.Connected) (r : V) : G.RootedTree where
  root := r
  parent v := if hv : v = r then r else (hG.exists_adj_dist_succ r hv).choose
  depth v := G.dist r v
  parent_root := by simp
  depth_root := dist_self
  depth_parent v hv := by
    simp only [hv, ↓reduceDIte]; exact (hG.exists_adj_dist_succ r hv).choose_spec.2
  adj_parent v hv := by
    simp only [hv, ↓reduceDIte]; exact (hG.exists_adj_dist_succ r hv).choose_spec.1

@[simp] theorem Connected.bfsTree_root [DecidableEq V] (hG : G.Connected) (r : V) :
    (hG.bfsTree r).root = r := rfl

@[simp] theorem Connected.bfsTree_depth [DecidableEq V] (hG : G.Connected) (r v : V) :
    (hG.bfsTree r).depth v = G.dist r v := rfl

/-- A connected graph in which all distances are at most `D` has, for every vertex `r`, a (BFS)
rooted spanning tree of depth at most `D` rooted at `r`. -/
theorem exists_rootedTree_root_depthLE (hG : G.Connected) {D : ℕ} (hD : ∀ u v, G.dist u v ≤ D)
    (r : V) : ∃ T : G.RootedTree, T.root = r ∧ T.DepthLE D := by
  classical
  exact ⟨hG.bfsTree r, rfl, fun v => hD r v⟩

/-- A connected graph in which all distances are at most `D` has a (BFS) rooted spanning tree of
depth at most `D`. -/
theorem exists_rootedTree_depthLE (hG : G.Connected) {D : ℕ} (hD : ∀ u v, G.dist u v ≤ D) :
    ∃ T : G.RootedTree, T.DepthLE D := by
  obtain ⟨r⟩ := hG.nonempty
  obtain ⟨T, -, hT⟩ := exists_rootedTree_root_depthLE hG hD r
  exact ⟨T, hT⟩

end SimpleGraph
